module LawAndOrder.Multiplicities where

open import Data.List using (List; []; _∷_; _++_)
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

-- Specification

data Mult : Set where
  ∞ 𝟙 ≻ ≺ : Mult

variable
  m m₁ m₂ m₃ m' m₁' m₂' m₃' : Mult

-- Properties

_≟ᵐ_ : ∀ (m₁ m₂ : Mult) → Dec (m₁ ≡ m₂)
∞ ≟ᵐ ∞ = yes refl ; ∞ ≟ᵐ 𝟙 = no λ()   ; ∞ ≟ᵐ ≻ = no λ()   ; ∞ ≟ᵐ ≺ = no λ()
𝟙 ≟ᵐ ∞ = no λ()   ; 𝟙 ≟ᵐ 𝟙 = yes refl ; 𝟙 ≟ᵐ ≻ = no λ()   ; 𝟙 ≟ᵐ ≺ = no λ()
≻ ≟ᵐ ∞ = no λ()   ; ≻ ≟ᵐ 𝟙 = no λ()   ; ≻ ≟ᵐ ≻ = yes refl ; ≻ ≟ᵐ ≺ = no λ()
≺ ≟ᵐ ∞ = no λ()   ; ≺ ≟ᵐ 𝟙 = no λ()   ; ≺ ≟ᵐ ≻ = no λ()   ; ≺ ≟ᵐ ≺ = yes refl

instance
  DecEq-Mult : DecEq Mult
  DecEq-Mult = _ ≟ᵐ _

_≢?ᵐ_ : ∀ (m₁ m₂ : Mult) → Dec (m₁ ≢ m₂)
m₁ ≢?ᵐ m₂ with m₁ ≟ᵐ m₂
... | yes m₁≡m₂ = no (λ ¬m₁≡m₂ → ¬m₁≡m₂ m₁≡m₂)
... | no ¬m₁≡m₂ = yes (λ m₁≡m₂ → ¬m₁≡m₂ m₁≡m₂)
