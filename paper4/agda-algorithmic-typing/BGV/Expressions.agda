module BGV.Expressions where

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)

open import BGV.Id
open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Types

data System : Set where
  log alg : System

variable
  § §₁ §₂ §₃ §' §₁' §₂' §₃' : System

data Label : Set where
  [1] [2] : Label

selectₗ : ∀ {ℓ} {A : Set ℓ} → Label → A → A → A
selectₗ [1] x _ = x
selectₗ [2] _ y = y

data Expr : System → Set where
  `_                        : Id → Expr §
  λ[_]_⇒_                   : Mult → Id → Expr § → Expr §
  _`·_                      : Expr § → Expr § → Expr §

  let[_≔_]in_               : Id → Expr § → Expr § → Expr §

  _,[_]_                    : Expr § → PMult → Expr § → Expr §
  let[_`,_≔_]in_            : Id → Id → Expr § → Expr § → Expr §

  `inj                      : Label → Expr § → Expr §
  case_of[_⇒_⍮_⇒_]          : Expr § → Id → Expr § → Id → Expr § → Expr §

  spawn                     : Expr § → Expr §
  new                       : SessionO → Expr §
  send                      : Expr § → Expr § → Expr §
  recv                      : Expr § → Expr §
  select                    : Label → Expr § → Expr §
  branch                    : Expr § → Expr §
  drop                      : Expr § → Expr §
  close                     : Op → Expr § → Expr §
  unit                      : Expr §

  -- Exclusively in logical system

  split[_]_                 : SessionB → Expr log → Expr log

  -- Exclusively in algorithmic system

  &_                        : Id → Expr alg
  _`∶_                      : Expr alg → Type → Expr alg
  _▸_                       : Expr alg → Expr alg → Expr alg

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' e₂₁ e₂₂ : Expr §

open import Data.List as L using (List; []; _∷_; _++_)
open import BGV.Util.List
open import BGV.Util.Decidable
open import Function using (case_of_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

fvs : Expr § → List Id
fvs (` x)                            = x ∷ []
fvs (λ[ _ ] x ⇒ e)                   = fvs e -ˡ x
fvs (e₁ `· e₂)                       = fvs e₁ ++ fvs e₂
fvs (let[ x ≔ e₁ ]in e₂)             = fvs e₁ ++ (fvs e₂ -ˡ x)
fvs (e₁ ,[ _ ] e₂)                   = fvs e₁ ++ fvs e₂
fvs (let[ x `, y ≔ e₁ ]in e₂)        = fvs e₁ ++ (fvs e₂ -ˡ x -ˡ y)
fvs (`inj l e)                       = fvs e
fvs (case e of[ x₁ ⇒ e₁ ⍮ x₂ ⇒ e₂ ]) = fvs e ++ (fvs e₁ -ˡ x₁) ++ (fvs e₂ -ˡ x₂)
fvs (spawn e)                        = fvs e
fvs (new _)                          = []
fvs (send e₁ e₂)                     = fvs e₁ ++ fvs e₂
fvs (recv e)                         = fvs e
fvs (select l e)                     = fvs e
fvs (branch e)                       = fvs e
fvs (drop e)                         = fvs e
fvs (close _ e)                      = fvs e
fvs unit                             = []
fvs (split[ _ ] e)                   = fvs e
fvs (& x)                            = x ∷ []
fvs (e `∶ _)                         = fvs e
fvs (e₁ ▸ e₂)                        = fvs e₁ ++ fvs e₂

bvs : Expr § → List Id
bvs (` x)                            = []
bvs (λ[ _ ] x ⇒ e)                   = x ∷ bvs e
bvs (e₁ `· e₂)                       = bvs e₁ ++ bvs e₂
bvs (let[ x ≔ e₁ ]in e₂)             = x ∷ bvs e₁ ++ bvs e₂
bvs (e₁ ,[ _ ] e₂)                   = bvs e₁ ++ bvs e₂
bvs (let[ x `, y ≔ e₁ ]in e₂)        = x ∷ y ∷ bvs e₁ ++ bvs e₂
bvs (`inj l e)                       = bvs e
bvs (case e of[ x₁ ⇒ e₁ ⍮ x₂ ⇒ e₂ ]) = x₁ ∷ x₂ ∷ bvs e ++ bvs e₁ ++ bvs e₂
bvs (spawn e)                        = bvs e
bvs (new _)                          = []
bvs (send e₁ e₂)                     = bvs e₁ ++ bvs e₂
bvs (recv e)                         = bvs e
bvs (select l e)                     = bvs e
bvs (branch e)                       = bvs e
bvs (drop e)                         = bvs e
bvs (close _ e)                      = bvs e
bvs unit                             = []
bvs (split[ _ ] e)                   = bvs e
bvs (& x)                            = []
bvs (e `∶ _)                         = bvs e
bvs (e₁ ▸ e₂)                        = bvs e₁ ++ bvs e₂

vars : Expr § → List Id
vars (` x)                            = x ∷ []
vars (λ[ _ ] x ⇒ e)                   = x ∷ vars e
vars (e₁ `· e₂)                       = vars e₁ ++ vars e₂
vars (let[ x ≔ e₁ ]in e₂)             = x ∷ vars e₁ ++ vars e₂
vars (e₁ ,[ _ ] e₂)                   = vars e₁ ++ vars e₂
vars (let[ x `, y ≔ e₁ ]in e₂)        = x ∷ y ∷ vars e₁ ++ vars e₂
vars (`inj l e)                       = vars e
vars (case e of[ x₁ ⇒ e₁ ⍮ x₂ ⇒ e₂ ]) = x₁ ∷ x₂ ∷ vars e ++ vars e₁ ++ vars e₂
vars (spawn e)                        = vars e
vars (new _)                          = []
vars (send e₁ e₂)                     = vars e₁ ++ vars e₂
vars (recv e)                         = vars e
vars (select l e)                     = vars e
vars (branch e)                       = vars e
vars (drop e)                         = vars e
vars (close _ e)                      = vars e
vars unit                             = []
vars (split[ _ ] e)                   = vars e
vars (& x)                            = x ∷ []
vars (e `∶ _)                         = vars e
vars (e₁ ▸ e₂)                        = vars e₁ ++ vars e₂

fvss : List (Expr §) → List Id
fvss es = L.foldl _++_ [] (L.map fvs es)

varss : List (Expr §) → List Id
varss es = L.foldl _++_ [] (L.map vars es)

open import BGV.Util.List

fvs⊆vars : ∀ (e : Expr §) → fvs e ⊆ vars e
fvs⊆vars (` x) = ⊆-refl
fvs⊆vars (λ[ m ] x ⇒ e) =
  let open ⊆-Reasoning in
  begin
    fvs e -ˡ x
  ⊆⟨ ⊆-ˡ' ⟩
    fvs e
  ⊆⟨ fvs⊆vars e ⟩
    vars e
  ⊆⟨ ⊆-∷ ⟩
    x ∷ vars e
  ∎
fvs⊆vars (e₁ `· e₂) = ⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂)
fvs⊆vars (e₁ ▸ e₂) = ⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂)
fvs⊆vars (let[ x ≔ e₁ ]in e₂) =
  let open ⊆-Reasoning in
  begin
    fvs e₁ ++ (fvs e₂ -ˡ x)
  ⊆⟨ ⊆-++ (⊆-refl {xs = fvs e₁}) ⊆-ˡ' ⟩
    fvs e₁ ++ fvs e₂
  ⊆⟨ ⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂) ⟩
    vars e₁ ++ vars e₂
  ⊆⟨ ⊆-∷ ⟩
    x ∷ vars e₁ ++ vars e₂
  ∎
fvs⊆vars (e₁ ,[ p ] e₂) = ⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂)
fvs⊆vars (let[ x `, y ≔ e₁ ]in e₂) =
  let open ⊆-Reasoning in
  begin
    fvs e₁ ++ (fvs e₂ -ˡ x -ˡ y)
  ⊆⟨ ⊆-++ (⊆-refl {xs = fvs e₁}) (⊆-trans ⊆-ˡ' ⊆-ˡ') ⟩
    fvs e₁ ++ fvs e₂
  ⊆⟨ ⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂) ⟩
    vars e₁ ++ vars e₂
  ⊆⟨ ⊆-∷ ⟩
    y ∷ vars e₁ ++ vars e₂
  ⊆⟨ ⊆-∷ ⟩
    x ∷ y ∷ vars e₁ ++ vars e₂
  ∎
fvs⊆vars (`inj x e) = fvs⊆vars e
fvs⊆vars (case e of[ x ⇒ e₁ ⍮ y ⇒ e₂ ]) =
  let open ⊆-Reasoning in
  begin
    fvs e ++ (fvs e₁ -ˡ x) ++ (fvs e₂ -ˡ y)
  ⊆⟨ ⊆-++ (⊆-refl {xs = fvs e}) (⊆-++ (⊆-ˡ' {ys = fvs e₁}) ⊆-ˡ') ⟩
    fvs e ++ fvs e₁ ++ fvs e₂
  ⊆⟨ ⊆-++ (fvs⊆vars e) (⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂)) ⟩
    vars e ++ vars e₁ ++ vars e₂
  ⊆⟨ ⊆-trans ⊆-∷ ⊆-∷ ⟩
    x ∷ y ∷ vars e ++ vars e₁ ++ vars e₂
  ∎
fvs⊆vars (spawn e) = fvs⊆vars e
fvs⊆vars (new x) = ⊆-refl
fvs⊆vars (send e₁ e₂) = ⊆-++ (fvs⊆vars e₁) (fvs⊆vars e₂)
fvs⊆vars (select l e) = fvs⊆vars e
fvs⊆vars (branch e) = fvs⊆vars e
fvs⊆vars (recv e) = fvs⊆vars e
fvs⊆vars (drop e) = fvs⊆vars e
fvs⊆vars (close o e) = fvs⊆vars e
fvs⊆vars unit = ⊆-refl
fvs⊆vars (split[ s ] e) = fvs⊆vars e
fvs⊆vars (& x) = ⊆-refl
fvs⊆vars (e `∶ x) = fvs⊆vars e
