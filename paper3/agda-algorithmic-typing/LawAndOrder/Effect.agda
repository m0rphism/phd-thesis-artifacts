module LawAndOrder.Effect where

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

data Effect : Set where
  𝟎 𝟏 : Effect

variable
  ϕ ϕ₁ ϕ₂ ϕ₃ ϕ' ϕ₁' ϕ₂' ϕ₃' : Effect

infix 3 _⊑_
data _⊑_ : Effect → Effect → Set where
  ϕ⊑ϕ : ϕ ⊑ ϕ
  𝟎⊑𝟏 : 𝟎 ⊑ 𝟏

infixl 5 _⊔_
_⊔_ : Effect → Effect → Effect
𝟎 ⊔ ϕ₂ = ϕ₂
𝟏 ⊔ ϕ₂ = 𝟏

-- Properties

⊔-comm : ∀ ϕ₁ ϕ₂ → ϕ₁ ⊔ ϕ₂ ≡ ϕ₂ ⊔ ϕ₁
⊔-comm 𝟎 𝟎 = refl
⊔-comm 𝟎 𝟏 = refl
⊔-comm 𝟏 𝟎 = refl
⊔-comm 𝟏 𝟏 = refl

⊔-assoc : ∀ ϕ₁ ϕ₂ ϕ₃ → ((ϕ₁ ⊔ ϕ₂) ⊔ ϕ₃) ≡ (ϕ₁ ⊔ (ϕ₂ ⊔ ϕ₃))
⊔-assoc 𝟎 ϕ₂ ϕ₃ = refl
⊔-assoc 𝟏 ϕ₂ ϕ₃ = refl

⊔-neutralʳ : ∀ ϕ → ϕ ⊔ 𝟎 ≡ ϕ
⊔-neutralʳ 𝟎 = refl
⊔-neutralʳ 𝟏 = refl

⊔-absorbʳ : ∀ ϕ → ϕ ⊔ 𝟏 ≡ 𝟏
⊔-absorbʳ 𝟎 = refl
⊔-absorbʳ 𝟏 = refl

𝟎⊑ϕ : ∀ ϕ → 𝟎 ⊑ ϕ
𝟎⊑ϕ 𝟎 = ϕ⊑ϕ
𝟎⊑ϕ 𝟏 = 𝟎⊑𝟏

ϕ⊑𝟏 : ∀ ϕ → ϕ ⊑ 𝟏
ϕ⊑𝟏 𝟎 = 𝟎⊑𝟏
ϕ⊑𝟏 𝟏 = ϕ⊑ϕ

ϕ₁⊑ϕ₁⊔ϕ₂ : ∀ ϕ₁ ϕ₂ → ϕ₁ ⊑ ϕ₁ ⊔ ϕ₂  
ϕ₁⊑ϕ₁⊔ϕ₂ 𝟎 ϕ₂ = 𝟎⊑ϕ ϕ₂
ϕ₁⊑ϕ₁⊔ϕ₂ 𝟏 ϕ₂ = ϕ⊑ϕ

ϕ₂⊑ϕ₁⊔ϕ₂ : ∀ ϕ₁ ϕ₂ → ϕ₂ ⊑ ϕ₁ ⊔ ϕ₂  
ϕ₂⊑ϕ₁⊔ϕ₂ 𝟎 ϕ₂ = ϕ⊑ϕ
ϕ₂⊑ϕ₁⊔ϕ₂ 𝟏 ϕ₂ = ϕ⊑𝟏 ϕ₂

⊑-refl : ϕ ⊑ ϕ
⊑-refl = ϕ⊑ϕ

⊑-trans : ϕ₁ ⊑ ϕ₂ → ϕ₂ ⊑ ϕ₃ → ϕ₁ ⊑ ϕ₃
⊑-trans ϕ⊑ϕ q = q
⊑-trans 𝟎⊑𝟏 ϕ⊑ϕ = 𝟎⊑𝟏

⊑-mono-⊔ : ϕ₁ ⊑ ϕ₁' → ϕ₂ ⊑ ϕ₂' → (ϕ₁ ⊔ ϕ₂) ⊑ (ϕ₁' ⊔ ϕ₂')
⊑-mono-⊔ {𝟎} {𝟎} {𝟎} {𝟎} p q = ϕ⊑ϕ
⊑-mono-⊔ {𝟎} {𝟎} {𝟎} {𝟏} p q = 𝟎⊑𝟏
⊑-mono-⊔ {𝟎} {𝟎} {𝟏} {𝟏} p q = ϕ⊑ϕ
⊑-mono-⊔ {𝟎} {𝟏} {𝟎} {𝟎} p q = 𝟎⊑𝟏
⊑-mono-⊔ {𝟎} {𝟏} {𝟎} {𝟏} p q = 𝟎⊑𝟏
⊑-mono-⊔ {𝟎} {𝟏} {𝟏} {𝟏} p q = ϕ⊑ϕ
⊑-mono-⊔ {𝟏} {𝟏} {𝟎} {𝟎} p q = ϕ⊑ϕ
⊑-mono-⊔ {𝟏} {𝟏} {𝟎} {𝟏} p q = ϕ⊑ϕ
⊑-mono-⊔ {𝟏} {𝟏} {𝟏} {𝟏} p q = ϕ⊑ϕ

module ⊑-Reasoning where
  infix 1 begin_
  infixr 2 _⊑⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ϕ₁ ⊑ ϕ₂ → ϕ₁ ⊑ ϕ₂
  begin p = p

  _⊑⟨_⟩_ : ∀ (A : Effect) {B : Effect} {C : Effect} → A ⊑ B → B ⊑ C → A ⊑ C
  _ ⊑⟨ p ⟩ q = ⊑-trans p q

  _≡⟨_⟩_ : ∀ (A : Effect) {B : Effect} {C : Effect} → A ≡ B → B ⊑ C → A ⊑ C
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (A : Effect) {C : Effect} → A ⊑ C → A ⊑ C
  _ ≡⟨⟩ q = q

  _∎ : ∀ (A : Effect) → A ⊑ A
  _ ∎ = ⊑-refl

_≟ᵉ_ : ∀ (x y : Effect) → Dec (x ≡ y)
𝟎 ≟ᵉ 𝟎 = yes refl
𝟎 ≟ᵉ 𝟏 = no λ()
𝟏 ≟ᵉ 𝟎 = no λ()
𝟏 ≟ᵉ 𝟏 = yes refl

instance
  DecEq-Effect : DecEq Effect
  DecEq-Effect = _ ≟ᵉ _

_⊑?_ : ∀ ϕ₁ ϕ₂ → Dec (ϕ₁ ⊑ ϕ₂)
𝟎 ⊑? 𝟎 = yes ϕ⊑ϕ
𝟎 ⊑? 𝟏 = yes 𝟎⊑𝟏
𝟏 ⊑? 𝟎 = no λ()
𝟏 ⊑? 𝟏 = yes ϕ⊑ϕ
