module LawAndOrder.Util.List where

open import Data.List as L using (List; []; _∷_; _++_)
import Data.List.Properties as ListP
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import LawAndOrder.Util.Decidable

private variable
  ℓ : Level
  A B C : Set ℓ

-- infixl 5 _-ˡ*_
-- _-ˡ*_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ → List A → List A → List A
-- []       -ˡ* ys = []
-- (x ∷ xs) -ˡ* ys with x ∈? ys
-- …                | yes x≡y = xs -ˡ* ys
-- …                | no ¬x≡y = x ∷ (xs -ˡ* ys)

infixl 5 _-ˡ_
_-ˡ_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ → List A → A → List A
-- xs -ˡ y = xs -ˡ* L.[ y ]
[]       -ˡ y = []
(x ∷ xs) -ˡ y with x ≟ y
…                | yes x≡y = xs -ˡ y
…                | no ¬x≡y = x ∷ (xs -ˡ y)

infix 3 _⊆_ _≈ˡ_

_⊆_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
xs ⊆ ys = ∀ {x} → x ∈ xs → x ∈ ys

_≈ˡ_ : ∀ {ℓ} {A : Set ℓ} → List A → List A → Set ℓ
xs ≈ˡ ys = xs ⊆ ys × ys ⊆ xs

_⊆?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ → (xs ys : List A) → Dec (xs ⊆ ys)
[]       ⊆? ys = yes λ ()
(x ∷ xs) ⊆? ys with x ∈? ys | xs ⊆? ys
… | yes x∈ys | yes xs⊆ys = yes λ where (here refl)  → x∈ys
                                       (there x∈xs) → xs⊆ys x∈xs
… | no ¬x∈ys | _         = no λ x∷xs⊆ys → ¬x∈ys (x∷xs⊆ys (here refl))
… | _        | no ¬xs⊆ys = no λ x∷xs⊆ys → ¬xs⊆ys λ z → x∷xs⊆ys (there z)

_≈ˡ?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ → (xs ys : List A) → Dec (xs ≈ˡ ys)
xs ≈ˡ? ys with xs ⊆? ys | ys ⊆? xs
… | yes xs⊆ys | yes ys⊆xs = yes (xs⊆ys , ys⊆xs)
… | no ¬xs⊆ys | _         = no λ (xs⊆ys , ys⊆xs) → ¬xs⊆ys xs⊆ys
… | _         | no ¬ys⊆xs = no λ (xs⊆ys , ys⊆xs) → ¬ys⊆xs ys⊆xs

-- Disjoint : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → Set ℓ
-- Disjoint xs ys = (∀ x → x ∈ xs → x ∉ ys) × (∀ y → y ∈ ys → y ∉ xs)

-- Disjoint? : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) → Dec (Disjoint xs ys)
-- Disjoint? xs ys = {!!}

-- instance
--   Dec-Disjoint : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs ys : List A} → Dec (Disjoint xs ys)
--   Dec-Disjoint = Disjoint? _ _

_¬⊎_ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → Set ℓ
xs ¬⊎ ys = ∃[ x ] x ∈ xs × x ∈ ys

_¬⊎?_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) → Dec (xs ¬⊎ ys)
[]       ¬⊎? ys = no (λ ())
(x ∷ xs) ¬⊎? ys with x ∈? ys | xs ¬⊎? ys
… | no ¬x∈ys | no ¬xs¬⊎ys               = no λ where (x' , here refl  , x∈ys) → ¬x∈ys x∈ys
                                                     (x' , there x∈xs , x∈ys) → ¬xs¬⊎ys (x' , x∈xs , x∈ys)
… | yes x∈ys | _                        = yes (x , here refl , x∈ys)
… | _        | yes (x' , x'∈xs , x'∈ys) = yes (x' , there x'∈xs , x'∈ys)

instance
  Dec-¬⊎ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs ys : List A} → Dec (xs ¬⊎ ys)
  Dec-¬⊎ = _ ¬⊎? _

⊆-refl : ∀ {ℓ} {A : Set ℓ} {xs : List A} → xs ⊆ xs 
⊆-refl p = p

⊆-trans : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A} → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans p q r = q (p r)

⊆-++ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₁' xs₂ xs₂' : List A} → xs₁ ⊆ xs₁' → xs₂ ⊆ xs₂' → (xs₁ ++ xs₂) ⊆ (xs₁' ++ xs₂')
⊆-++ p q x
 with AnyP.++⁻ _ x
... | inj₁ x = AnyP.++⁺ˡ (p x)
... | inj₂ x = AnyP.++⁺ʳ _ (q x)

⊆-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ⊆ (xs ++ (ys ++ zs))
⊆-assoc xs ys zs x
 with AnyP.++⁻ (xs ++ ys) x
... | inj₂ x = AnyP.++⁺ʳ xs (AnyP.++⁺ʳ ys x)
... | inj₁ x with AnyP.++⁻ xs x
...   | inj₁ x = AnyP.++⁺ˡ x
...   | inj₂ x = AnyP.++⁺ʳ xs (AnyP.++⁺ˡ x)

⊆-assoc' : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → (xs ++ (ys ++ zs)) ⊆ ((xs ++ ys) ++ zs)
⊆-assoc' xs ys zs x
 with AnyP.++⁻ xs x
... | inj₁ x = AnyP.++⁺ˡ (AnyP.++⁺ˡ x)
... | inj₂ x with AnyP.++⁻ ys x
...   | inj₁ x = AnyP.++⁺ˡ (AnyP.++⁺ʳ xs x)
...   | inj₂ x = AnyP.++⁺ʳ (xs ++ ys) x

⊆-comm : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → (xs ++ ys) ⊆ (ys ++ xs)
⊆-comm xs ys x with AnyP.++⁻ xs x
... | inj₁ x∈xs = AnyP.++⁺ʳ ys x∈xs
... | inj₂ x∈ys = AnyP.++⁺ˡ x∈ys

⊆-dist-∥-⸴ : ∀ {ℓ} {A : Set ℓ} (xs₁₁ xs₁₂ xs₂₁ xs₂₂ : List A) → (xs₁₁ ++ xs₂₁) ++ (xs₁₂ ++ xs₂₂) ⊆ (xs₁₁ ++ xs₁₂) ++ (xs₂₁ ++ xs₂₂)
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x with AnyP.++⁻ (xs₁₁ ++ xs₂₁) x
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x | inj₁ y with AnyP.++⁻ xs₁₁ y
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x | inj₁ y | inj₁ z = AnyP.++⁺ˡ (AnyP.++⁺ˡ z)
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x | inj₁ y | inj₂ z = AnyP.++⁺ʳ (xs₁₁ ++ xs₁₂) (AnyP.++⁺ˡ z)
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x | inj₂ y with AnyP.++⁻ xs₁₂ y
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x | inj₂ y | inj₁ z = AnyP.++⁺ˡ (AnyP.++⁺ʳ xs₁₁ z)
⊆-dist-∥-⸴ xs₁₁ xs₁₂ xs₂₁ xs₂₂ x | inj₂ y | inj₂ z = AnyP.++⁺ʳ (xs₁₁ ++ xs₁₂) (AnyP.++⁺ʳ xs₂₁ z)


≈ˡ-refl : ∀ {ℓ} {A : Set ℓ} {xs : List A} → xs ≈ˡ xs 
≈ˡ-refl = ⊆-refl , ⊆-refl

≈ˡ-sym : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ≈ˡ ys → ys ≈ˡ xs
≈ˡ-sym (p₁ , p₂) = (p₂ , p₁)

≈ˡ-trans : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A} → xs ≈ˡ ys → ys ≈ˡ zs → xs ≈ˡ zs
≈ˡ-trans (p₁ , p₂) (q₁ , q₂) = (λ z → q₁ (p₁ z)) , (λ z → p₂ (q₂ z))

≈ˡ-identityʳ : ∀ {ℓ} {A : Set ℓ} (xs : List A) → xs ≈ˡ xs ++ []
≈ˡ-identityʳ xs = subst (xs ≈ˡ_) (sym (ListP.++-identityʳ xs)) ≈ˡ-refl

≈ˡ-dup : ∀ {ℓ} {A : Set ℓ} (a : A) → (a ∷ a ∷ []) ≈ˡ (a ∷ [])
≈ˡ-dup a = (λ { (here px) → here px ; (there x) → x }) , (λ x → there x)

≈ˡ-++ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₁' xs₂ xs₂' : List A} → xs₁ ≈ˡ xs₁' → xs₂ ≈ˡ xs₂' → (xs₁ ++ xs₂) ≈ˡ (xs₁' ++ xs₂')
≈ˡ-++ (p₁ , p₂) (q₁ , q₂) = (⊆-++ p₁ q₁) , (⊆-++ p₂ q₂)

≈ˡ-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≈ˡ (xs ++ (ys ++ zs))
≈ˡ-assoc xs ys zs = (⊆-assoc xs ys zs) , (⊆-assoc' xs ys zs)

≈ˡ-comm : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → (xs ++ ys) ≈ˡ (ys ++ xs)
≈ˡ-comm xs ys = (⊆-comm xs ys) , (⊆-comm ys xs)

≈ˡ→⊆ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ≈ˡ ys → xs ⊆ ys
≈ˡ→⊆ p = proj₁ p

module ⊆-Reasoning where
  infix 1 begin_
  infixr 2 _≈⟨_⟩_ _⊆⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {xs ys : List A} → xs ⊆ ys → xs ⊆ ys
  begin p = p

  _⊆⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
  _ ⊆⟨ p ⟩ q = ⊆-trans p q

  _≈⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≈ˡ ys → ys ⊆ zs → xs ⊆ zs
  _ ≈⟨ p ⟩ q = ⊆-trans (≈ˡ→⊆ p) q

  _≡⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≡ ys → ys ⊆ zs → xs ⊆ zs
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (xs {ys} : List A) → xs ⊆ ys → xs ⊆ ys
  _ ≡⟨⟩ q = q

  _∎ : ∀ (xs : List A) → xs ⊆ xs
  _ ∎ = ⊆-refl

module ≈ˡ-Reasoning where
  infix 1 begin_
  infixr 2 _≈⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {xs ys : List A} → xs ≈ˡ ys → xs ≈ˡ ys
  begin p = p

  _≈⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≈ˡ ys → ys ≈ˡ zs → xs ≈ˡ zs
  _ ≈⟨ p ⟩ q = ≈ˡ-trans p q

  _≡⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≡ ys → ys ≈ˡ zs → xs ≈ˡ zs
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (xs {ys} : List A) → xs ≈ˡ ys → xs ≈ˡ ys
  _ ≡⟨⟩ q = q

  _∎ : ∀ (xs : List A) → xs ≈ˡ xs
  _ ∎ = ≈ˡ-refl
