open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Algorithmic.Expression {M : OPM} (DM : DecidableOPM M) where

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

open import LawAndOrder.Util.Decidable
open import LawAndOrder.Multiplicities
open import LawAndOrder.Effect
open import LawAndOrder.Type DM
open import LawAndOrder.Id
open import LawAndOrder.Util.List

-- Specification

mutual
  data Expr↓ : Set where
    `λ_⇒_            : Id → Expr↓ → Expr↓
    ↑_               : Expr↑ → Expr↓ 

  data Expr↑ : Set where
    unit             : Expr↑
    new              : M.Carrier → Expr↑
    send             : M.Carrier → Expr↑ → Expr↑
    split            : M.Carrier → Expr↑ → Expr↑
    drop             : Expr↑ → Expr↑
    `_               : Id → Expr↑
    _`·_             : Expr↑ → Expr↑ → Expr↑
    _,_              : Expr↑ → Expr↑ → Expr↑
    let[_,_≡_]in_    : Id → Id → Expr↑ → Expr↑ → Expr↑
    _∶_              : Expr↓ → Type → Expr↑

variable
  eⁱ eⁱ₁ eⁱ₂ eⁱ₃ eⁱ' eⁱ₁' eⁱ₂' eⁱ₃' : Expr↑
  eᶜ eᶜ₁ eᶜ₂ eᶜ₃ eᶜ' eᶜ₁' eᶜ₂' eᶜ₃' : Expr↓

mutual
  fvs↓ : Expr↓ → List Id
  fvs↓ (`λ x ⇒ e)               = fvs↓ e -ˡ x
  fvs↓ (↑ e )                   = fvs↑ e

  fvs↑ : Expr↑ → List Id
  fvs↑ unit                     = []
  fvs↑ (new r)                  = []
  fvs↑ (send r e)               = fvs↑ e
  fvs↑ (split r e)              = fvs↑ e
  fvs↑ (drop e)                 = fvs↑ e
  fvs↑ (` x)                    = L.[ x ]
  fvs↑ (e₁ `· e₂)               = fvs↑ e₁ ++ fvs↑ e₂
  fvs↑ (e₁ , e₂)                = fvs↑ e₁ ++ fvs↑ e₂
  fvs↑ (let[ x , y ≡ e₁ ]in e₂) = fvs↑ e₁ ++ (fvs↑ e₂ -ˡ x -ˡ y)
  fvs↑ (e ∶ t)                  = fvs↓ e

