open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Logical.Expression {M : OPM} (DM : DecidableOPM M) where

private module M = DecidableOPM DM

open import Data.List as L using (List; []; _∷_; _++_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.String as String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)
open import Level using (Level; 0ℓ) renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

open import LawAndOrder.Multiplicities
open import LawAndOrder.Effect
open import LawAndOrder.Id
open import LawAndOrder.Util.List
open import LawAndOrder.Util.Decidable

-- Specification

data Const : Set where
  unit  : Const
  new   : M.Carrier → Const
  send  : M.Carrier → Const
  split : M.Carrier → M.Carrier → Const
  drop : Const

infixr 5 λ[_]_⇒_ let[_,[_]_≡_]in_
infixl 7 _,[_]_
infixl 8 _·[_]_
infix  9 `_

data Expr : Set where
  const            : Const → Expr
  `_               : Id → Expr
  λ[_]_⇒_          : Mult → Id → Expr → Expr
  _·[_]_           : Expr → Mult → Expr → Expr
  _,[_]_           : Expr → Mult → Expr → Expr
  let[_,[_]_≡_]in_ : Id → Mult → Id → Expr → Expr → Expr

variable
  e e₁ e₂ e₃ e' e₁' e₂' e₃' : Expr
  c c₁ c₂ c₃ c' c₁' c₂' c₃' : Const

fvs : Expr → List Id
fvs (const x)                     = []
fvs (` x)                         = L.[ x ]
fvs (λ[ m ] x ⇒ e)                = fvs e -ˡ x
fvs (e₁ ·[ m ] e₂)                = fvs e₁ ++ fvs e₂
fvs (e₁ ,[ m ] e₂)                = fvs e₁ ++ fvs e₂
fvs (let[ x ,[ m ] y ≡ e₁ ]in e₂) = fvs e₁ ++ (fvs e₂ -ˡ x -ˡ y)
