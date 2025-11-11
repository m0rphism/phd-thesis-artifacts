open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Type {M : OPM} (DM : DecidableOPM M) where

private module M = DecidableOPM DM

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
open import LawAndOrder.Multiplicities
open import LawAndOrder.Effect

-- Specification

infixr 5 _–[_⍮_]→_
infixl 7 _×[_]_
infix  9 #_

data Type : Set where
  Unit      : Type
  #_        : M.Carrier → Type
  _–[_⍮_]→_ : Type → Mult → Effect → Type → Type
  _×[_]_    : Type → Mult → Type → Type

variable
  t t₁ t₂ t₃ t' t₁' t₂' t₃' t₁₁ t₁₂ t₂₁ t₂₂ : Type
  r r₁ r₂ r₃ r' r₁' r₂' r₃' : M.Carrier

data Unr : Type → Set where
  unr-Unit : Unr Unit
  unr-→    : Unr (t₁ –[ ∞ ⍮ ϕ ]→ t₂)
  unr-×    : Unr t₁ → Unr t₂ → Unr (t₁ ×[ m ] t₂)
  
Ord : Type → Set
Ord t = ¬ Unr t

-- Properties

Unr? : ∀ t → Dec (Unr t)
Unr? Unit = yes unr-Unit
Unr? (# x) = no λ()
Unr? (t₁ –[ m ⍮ ϕ ]→ t₂) with m
…                           | ∞ = yes unr-→
…                           | 𝟙 = no λ ()
…                           | ≻ = no λ ()
…                           | ≺ = no λ ()
Unr? (t₁ ×[ m ] t₂) with Unr? t₁ | Unr? t₂
…                      | yes u₁  | yes u₂ = yes (unr-× u₁ u₂)
…                      | no ¬u₁  | _      = no λ { (unr-× u₁ u₂) → ¬u₁ u₁ }
…                      | _       | no ¬u₂ = no λ { (unr-× u₁ u₂) → ¬u₂ u₂ }

_≟ᵗ_ : ∀ (x y : Type) → Dec (x ≡ y)
Unit                 ≟ᵗ Unit                  = yes refl
(# r₁)               ≟ᵗ (# r₂) with r₁ M.≟ r₂
…                              | yes r₁≡r₂    = yes (cong #_ r₁≡r₂)
…                              | no ¬r₁≡r₂    = no (λ { refl → ¬r₁≡r₂ refl})
(t₁₁ –[ m₁ ⍮ ϕ₁ ]→ t₁₂) ≟ᵗ (t₂₁ –[ m₂ ⍮ ϕ₂ ]→ t₂₂)
  with t₁₁ ≟ᵗ t₂₁  | m₁ ≟ m₂  | ϕ₁ ≟ ϕ₂   | t₁₂ ≟ᵗ t₂₂
…   | yes refl    | yes refl  | yes refl  | yes refl    = yes refl
…   | no ¬t₁₁≡t₂₁ | _         | _         | _           = no λ { refl → ¬t₁₁≡t₂₁ refl }
…   | _           | no ¬m₁≡m₂ | _         | _           = no λ { refl → ¬m₁≡m₂ refl }
…   | _           | _         | no ¬ϕ₁≡ϕ₂ | _           = no λ { refl → ¬ϕ₁≡ϕ₂ refl }
…   | _           | _         | _         | no ¬t₂₁≡t₂₂ = no λ { refl → ¬t₂₁≡t₂₂ refl }
(t₁₁ ×[ m₁ ] t₁₂)    ≟ᵗ (t₂₁ ×[ m₂ ] t₂₂)
  with t₁₁ ≟ᵗ t₂₁ | m₁ ≟ m₂   | t₁₂ ≟ᵗ t₂₂
…   | yes refl    | yes refl  | yes refl    = yes refl
…   | no ¬t₁₁≡t₂₁ | _         | _           = no λ { refl → ¬t₁₁≡t₂₁ refl }
…   | _           | no ¬m₁≡m₂ | _           = no λ { refl → ¬m₁≡m₂ refl }
…   | _           | _         | no ¬t₂₁≡t₂₂ = no λ { refl → ¬t₂₁≡t₂₂ refl }
Unit                 ≟ᵗ (# x)                 = no λ()
Unit                 ≟ᵗ (t₂ –[ x ⍮ x₁ ]→ t₃)  = no λ()
Unit                 ≟ᵗ (t₂ ×[ x ] t₃)        = no λ()
(# r₁)               ≟ᵗ Unit                  = no λ()
(# r₁)               ≟ᵗ (t₂ –[ x₁ ⍮ x₂ ]→ t₃) = no λ()
(# r₁)               ≟ᵗ (t₂ ×[ x₁ ] t₃)       = no λ()
(t₁ –[ x ⍮ x₁ ]→ t₂) ≟ᵗ Unit                  = no λ()
(t₁ –[ x ⍮ x₁ ]→ t₂) ≟ᵗ (# x₂)                = no λ()
(t₁ –[ x ⍮ x₁ ]→ t₂) ≟ᵗ (t₃ ×[ x₂ ] t₄)       = no λ()
(t₁ ×[ x ] t₂)       ≟ᵗ Unit                  = no λ()
(t₁ ×[ x ] t₂)       ≟ᵗ (# x₁)                = no λ()
(t₁ ×[ x ] t₂)       ≟ᵗ (t₃ –[ x₁ ⍮ x₂ ]→ t₄) = no λ()

instance
  DecEq-Type : DecEq Type
  DecEq-Type = _ ≟ᵗ _
