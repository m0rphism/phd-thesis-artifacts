module LawAndOrder.Util.Decidable where

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Level using (Level)

private variable
  ℓ ℓ₁ ℓ₂ : Level
  A B C : Set ℓ

decide : ⦃ Dec A ⦄ → Dec A
decide ⦃ p ⦄ = p

-- Decidable Equality

DecEq : ∀ {ℓ} (A : Set ℓ) → Set ℓ
DecEq A = ∀ {x y : A} → Dec (x ≡ y)

_≟_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ → ∀ (x y : A) → Dec (x ≡ y)
x ≟ y = decide

-- Instances

open import Data.Nat as Nat using (ℕ; suc; zero)
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as ListP
open import Data.String as String using (String)
open import Data.Char as Char using (Char)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)

decide-¬ : Dec A → Dec (¬ A)
decide-¬ (yes a) = no λ ¬a → ¬a a
decide-¬ (no ¬a) = yes ¬a

_≟L_ : ⦃ _ : DecEq A ⦄ → (xs ys : List A) → Dec (xs ≡ ys)
[]       ≟L []       = yes refl
[]       ≟L (y ∷ ys) = no (λ ())
(x ∷ xs) ≟L []       = no (λ ())
(x ∷ xs) ≟L (y ∷ ys) with x ≟ y   | xs ≟L ys
…                       | yes x≡y | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
…                       | no ¬x≡y | _         = no (λ { refl → ¬x≡y refl })
…                       | _       | no ¬xs≡ys = no (λ { refl → ¬xs≡ys refl })

_∈?_ : ⦃ _ : DecEq A ⦄ (x : A) (xs : List A) → Dec (x ∈ xs)
x ∈? []       = no (λ ())
x ∈? (y ∷ xs) with x ≟ y
…                | yes x≡y = yes (here x≡y)
…                | no ¬x≡y with x ∈? xs
…                             | yes x∈xs = yes (there x∈xs)
…                             | no ¬x∈xs = no λ where (here px) → ¬x≡y px
                                                      (there x) → ¬x∈xs x

_∉?_ : ⦃ _ : DecEq A ⦄ (x : A) (xs : List A) → Dec (¬ (x ∈ xs))
x ∉? xs = decide-¬ (x ∈? xs)

_≟×_ : ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ (x y : A × B) → Dec (x ≡ y)
(a₁ , b₁) ≟× (a₂ , b₂) with a₁ ≟ a₂ | b₁ ≟ b₂
… | yes a₁≡a₂ | yes b₁≡b₂ = yes (cong₂ _,_ a₁≡a₂ b₁≡b₂)
… | no ¬a₁≡a₂ | _         = no λ { refl → ¬a₁≡a₂ refl }
… | _         | no ¬b₁≡b₂ = no λ { refl → ¬b₁≡b₂ refl }

instance
  DecEq-ℕ : DecEq ℕ
  DecEq-ℕ = _ Nat.≟ _

  DecEq-List : ⦃ _ : DecEq A ⦄ → DecEq (List A)
  DecEq-List = _ ≟L _

  DecEq-String : DecEq String
  DecEq-String = _ String.≟ _

  DecEq-Char : DecEq Char
  DecEq-Char = _ Char.≟ _

  Dec-∈ : ⦃ _ : DecEq A ⦄ {x : A} {xs : List A} → Dec (x ∈ xs)
  Dec-∈ = _ ∈? _

  Dec-¬ : ⦃ _ : Dec A ⦄ → Dec (¬ A)
  Dec-¬ = decide-¬ decide

  Dec-× : ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄ → DecEq (A × B)
  Dec-× = _ ≟× _

