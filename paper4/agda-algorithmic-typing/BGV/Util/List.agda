module BGV.Util.List where

import Data.Nat.Properties as NatP
open import Data.List as L using (List; []; _∷_; _++_)
import Data.List.Properties as ListP
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
import Relation.Binary.PropositionalEquality.Properties as EqP
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
import Data.Sum.Properties as SumP
import Data.Product.Properties as ProdP
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe as Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_; _∘_) renaming (_∋_ to _by_)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; module ≅-Reasoning)

open import BGV.Util.Decidable

private variable
  ℓ : Level
  A B C : Set ℓ

∉-tail : ∀ {ℓ} {A : Set ℓ} {z x} {xs : List A} →
  z ∉ (x ∷ xs) →
  z ∉ xs
∉-tail p q = p (there q)

map₁₂ : ∀ {ℓ₁} {ℓ₂} {ℓ₁'} {ℓ₂'} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} {B₁ : Set ℓ₁'} {B₂ : Set ℓ₂'} → (A₁ → A₂) → (B₁ → B₂) → A₁ × B₁ → A₂ × B₂
map₁₂ f g (x , y) = (f x , g y)

map₁ : ∀ {ℓ} {ℓ₁} {ℓ₂} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} {B : Set ℓ} → (A₁ → A₂) → A₁ × B → A₂ × B  
map₁ f (x , y) = (f x , y)

map₂ : ∀ {ℓ} {ℓ₁} {ℓ₂} {A : Set ℓ} {B₁ : Set ℓ₁} {B₂ : Set ℓ₂} → (B₁ → B₂) → A × B₁ → A × B₂  
map₂ f (x , y) = (x , f y)

map-∈-inv : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {y} (f : A → B) (xs : List A) →
  y ∈ L.map f xs →
  ∃[ x ] x ∈ xs × f x ≡ y
map-∈-inv f (x ∷ xs) (here px) = x , here refl , sym px
map-∈-inv f (x ∷ xs) (there y∈fxs) =
  let (x , x∈ , eq) = map-∈-inv f xs y∈fxs in
  x , there x∈ , eq

∈∉→≢ : ∀ {ℓ} {A : Set ℓ} {x y} {xs : List A} →
  x ∈ xs →
  y ∉ xs →
  x ≢ y
∈∉→≢ x∈xs y∉xs refl = y∉xs x∈xs

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

⊆-++₁ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys : List A} → (xs₁ ++ xs₂) ⊆ ys → xs₁ ⊆ ys
⊆-++₁ sub x∈ = sub (AnyP.++⁺ˡ x∈)

⊆-++₂ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys : List A} → (xs₁ ++ xs₂) ⊆ ys → xs₂ ⊆ ys
⊆-++₂ sub x∈ = sub (AnyP.++⁺ʳ _ x∈)

⊆-++₁' : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ : List A} → xs₁ ⊆ (xs₁ ++ xs₂)
⊆-++₁' = ⊆-++₁ ⊆-refl

⊆-++₂' : ∀ {ℓ} {A : Set ℓ} xs₁ {xs₂ : List A} → xs₂ ⊆ (xs₁ ++ xs₂)
⊆-++₂' _ = ⊆-++₂ ⊆-refl

⊆-++⁺ˡ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys : List A} →
  xs₁ ⊆ ys →
  xs₂ ⊆ ys →
  xs₁ ++ xs₂ ⊆ ys
⊆-++⁺ˡ {xs₁ = xs₁} xs₁⊆ys xs₂⊆ys x∈xs₁++xs₂
  with AnyP.++⁻ xs₁ x∈xs₁++xs₂
… | inj₁ x∈xs₁ = xs₁⊆ys x∈xs₁
… | inj₂ x∈xs₂ = xs₂⊆ys x∈xs₂

⊆-++⁻ˡ : ∀ {ℓ} {A : Set ℓ} (xs₁ xs₂ {ys} : List A) →
  xs₁ ++ xs₂ ⊆ ys →
  xs₁ ⊆ ys × xs₂ ⊆ ys
⊆-++⁻ˡ xs₁ xs₂ xs₁++xs₂⊆ys =
  ⊆-++₁ xs₁++xs₂⊆ys , ⊆-++₂ xs₁++xs₂⊆ys

⊆-∷ : ∀ {ℓ} {A : Set ℓ} {x} {xs : List A} → xs ⊆ (x ∷ xs)
⊆-∷ {x = x} {xs = xs} = ⊆-++₂' (x ∷ []) 

∈-map : ∀ {ℓ} {A : Set ℓ} {x} {xs : List A} (f : A → B) → x ∈ xs → f x ∈ L.map f xs
∈-map f (here refl) = here refl
∈-map f (there x∈xs) = there (∈-map f x∈xs)

⊆-map : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} (f : A → B) → xs ⊆ ys → L.map f xs ⊆ L.map f ys
⊆-map {xs = x ∷ xs} f sub (here px) = subst (_∈ _) (sym px) (∈-map f (sub (here refl))) 
⊆-map {xs = x ∷ xs} f sub (there x∈) = ⊆-map f (⊆-++₂ {xs₁ = x ∷ []} sub) x∈

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

≈ˡ-dup-++ : ∀ {ℓ} {A : Set ℓ} (xs : List A) → (xs ++ xs) ≈ˡ xs
≈ˡ-dup-++ xs =
  (λ x∈xs++xs → case AnyP.++⁻ xs x∈xs++xs of λ where
                  (inj₁ x∈xs) → x∈xs
                  (inj₂ x∈xs) → x∈xs) ,
  (λ x∈xs → AnyP.++⁺ˡ x∈xs)

≈ˡ-++ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₁' xs₂ xs₂' : List A} → xs₁ ≈ˡ xs₁' → xs₂ ≈ˡ xs₂' → (xs₁ ++ xs₂) ≈ˡ (xs₁' ++ xs₂')
≈ˡ-++ (p₁ , p₂) (q₁ , q₂) = (⊆-++ p₁ q₁) , (⊆-++ p₂ q₂)

≈ˡ-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≈ˡ (xs ++ (ys ++ zs))
≈ˡ-assoc xs ys zs = (⊆-assoc xs ys zs) , (⊆-assoc' xs ys zs)

≈ˡ-comm : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → (xs ++ ys) ≈ˡ (ys ++ xs)
≈ˡ-comm xs ys = (⊆-comm xs ys) , (⊆-comm ys xs)

≈ˡ-map : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} (f : A → B) → xs ≈ˡ ys → L.map f xs ≈ˡ L.map f ys
≈ˡ-map f (xs⊆ys , ys⊆xs) = ⊆-map f xs⊆ys , ⊆-map f ys⊆xs

≈ˡ→⊆ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ≈ˡ ys → xs ⊆ ys
≈ˡ→⊆ p = proj₁ p

∈-ˡ⁻ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs : List A} {x} {y} →
  y ∈ (xs -ˡ x) →
  y ∈ xs × y ≢ x
∈-ˡ⁻ {xs = x' ∷ xs} {x = x} {y = y} p with x' ≟ x
∈-ˡ⁻ {xs = x' ∷ xs} {x = x} {y = y} p | yes refl = map₁ there (∈-ˡ⁻ p)
∈-ˡ⁻ {A = _} ⦃ _ ⦄ {x' ∷ xs} {x = x} {y = y} (here refl) | no x'≢x = here refl , x'≢x
∈-ˡ⁻ {A = _} ⦃ _ ⦄ {x' ∷ xs} {x = x} {y = y} (there p) | no _ = map₁ there (∈-ˡ⁻ p)

∈-ˡ⁺ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs : List A} {x} {y} →
  x ∈ xs →
  x ≢ y →
  x ∈ (xs -ˡ y)
∈-ˡ⁺ {xs = x' ∷ xs} {x} {y} (here refl) x≢y
  with x ≟ y
… | yes refl = ⊥-elim (x≢y refl)
… | no ¬x'≡y = here refl
∈-ˡ⁺ {xs = x' ∷ xs} {x} {y} (there x∈xs) x≢y
  with x' ≟ y
… | yes refl = ∈-ˡ⁺ x∈xs x≢y
… | no ¬x'≡y = there (∈-ˡ⁺ x∈xs x≢y)

∉-ˡ' : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs : List A) x →
  x ∉ xs -ˡ x
∉-ˡ' xs x x∈xs-x =
  let x∈xs , x≢x = ∈-ˡ⁻ {xs = xs} {x = x} x∈xs-x in
  ⊥-elim (x≢x refl)

⊆-ˡ-∉ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs ys : List A} {y} →
  xs ⊆ (ys -ˡ y) →
  y ∉ xs
⊆-ˡ-∉ {ys = ys} {y = y} xs⊆ys-y y∈xs = ∉-ˡ' ys y (xs⊆ys-y y∈xs)

⊆-ˡ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs ys : List A} {x} →
  xs ⊆ (ys -ˡ x) →
  xs ⊆ ys
⊆-ˡ {xs = xs} {ys = ys} {x = x} p q = proj₁ (∈-ˡ⁻ (p q))

⊆-ˡ' : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {ys : List A} {x} →
  (ys -ˡ x) ⊆ ys
⊆-ˡ' = ⊆-ˡ ⊆-refl

⊆-ˡ-both : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs ys : List A} {z} →
  xs ⊆ ys →
  (xs -ˡ z) ⊆ (ys -ˡ z)
⊆-ˡ-both {xs = xs} {ys = ys} {z = z} xs⊆ys {x = x} x∈xs-z =
  let x∈xs , x≢z = ∈-ˡ⁻ x∈xs-z in
  ∈-ˡ⁺ (xs⊆ys x∈xs) x≢z

∉-ˡ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs : List A} {x} →
  x ∉ xs →
  xs -ˡ x ≡ xs
∉-ˡ {xs = []} {x = x} x∉xs = refl
∉-ˡ {xs = y ∷ xs} {x = x} x∉xs with y ≟ x
… | yes refl = ⊥-elim (x∉xs (here refl))
… | no ¬y≡x  = cong (y ∷_) (∉-ˡ (∉-tail x∉xs))

-ˡ-self : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x : A} →
  (x ∷ []) -ˡ x ≡ []
-ˡ-self {x = x} with x ≟ x
… | yes _ = refl
… | no ¬x≡x = ⊥-elim (¬x≡x refl)

-ˡ-self-twice : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x y : A} →
  x ≢ y →
  (x ∷ y ∷ []) -ˡ x -ˡ y ≡ []
-ˡ-self-twice {x = x} {y = y} x≢y
  with x ≟ x
… | no ¬x≡x = ⊥-elim (¬x≡x refl)
… | yes _
  with y ≟ x
… | yes refl = ⊥-elim (x≢y refl)
… | no _
  with y ≟ y
… | no ¬y≡y = ⊥-elim (¬y≡y refl)
… | yes _ = refl

-ˡ-dist-++ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) z →
  (xs ++ ys) -ˡ z ≡ (xs -ˡ z) ++ (ys -ˡ z)
-ˡ-dist-++ [] ys z = refl
-ˡ-dist-++ (x ∷ xs) ys z with x ≟ z
… | yes refl = -ˡ-dist-++ xs ys z
… | no ¬x≡z  = cong (x ∷_) (-ˡ-dist-++ xs ys z)

[]⊆ : ∀ {ℓ} {A : Set ℓ} (xs : List A) →
  [] ⊆ xs
[]⊆ xs ()

⊆-∈ : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} → xs ⊆ ys → x ∈ xs → x ∈ ys
⊆-∈ xs⊆ys x∈xs = xs⊆ys x∈xs

⊆-∉ : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} → xs ⊆ ys → x ∉ ys → x ∉ xs
⊆-∉ xs⊆ys x∉ys x∈xs = x∉ys (xs⊆ys x∈xs)

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

infixr 5 _∷?_
_∷?_ : Maybe A → List A → List A
some x ∷? xs = x ∷ xs
none   ∷? xs = xs

Disjoint : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → Set ℓ
Disjoint xs ys = ∀ x → x ∈ xs → ¬ x ∈ ys

Disjoint-sym : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} →
  Disjoint xs ys →
  Disjoint ys xs
Disjoint-sym xs⊎ys y y∈ys y∈xs = xs⊎ys y y∈xs y∈ys

Disjoint-⊆ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys₁ ys₂ : List A} →
  xs₁ ⊆ xs₂ →
  ys₁ ⊆ ys₂ →
  Disjoint xs₂ ys₂ →
  Disjoint xs₁ ys₁
Disjoint-⊆ sub₁ sub₂ dis x x∈xs₁ x∈ys₁ = dis x (sub₁ x∈xs₁) (sub₂ x∈ys₁) 

Disjoint-⊆₁ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys : List A} →
  xs₁ ⊆ xs₂ →
  Disjoint xs₂ ys →
  Disjoint xs₁ ys
Disjoint-⊆₁ sub dis x x∈xs₁ = dis x (sub x∈xs₁) 

Disjoint-⊆₂ : ∀ {ℓ} {A : Set ℓ} {xs ys₁ ys₂ : List A} →
  ys₁ ⊆ ys₂ →
  Disjoint xs ys₂ →
  Disjoint xs ys₁
Disjoint-⊆₂ sub dis = Disjoint-sym (Disjoint-⊆₁ sub (Disjoint-sym dis))

Disjoint-≈₁ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys : List A} →
  xs₁ ≈ˡ xs₂ →
  Disjoint xs₂ ys →
  Disjoint xs₁ ys
Disjoint-≈₁ (sub , _) = Disjoint-⊆₁ sub

Disjoint-≈₂ : ∀ {ℓ} {A : Set ℓ} {xs ys₁ ys₂ : List A} →
  ys₁ ≈ˡ ys₂ →
  Disjoint xs ys₂ →
  Disjoint xs ys₁
Disjoint-≈₂ (sub , _) = Disjoint-⊆₂ sub

Disjoint-tail₁ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {x} →
  Disjoint (x ∷ xs) ys →
  Disjoint xs ys
Disjoint-tail₁ d x x∈xs x∈ys = d x (there x∈xs) x∈ys

Disjoint-tail₂ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {y} →
  Disjoint xs (y ∷ ys) →
  Disjoint xs ys
Disjoint-tail₂ d = Disjoint-sym (Disjoint-tail₁ (Disjoint-sym d))

Disjoint-[]₁ : ∀ {ℓ} {A : Set ℓ} {xs : List A} →
  Disjoint [] xs
Disjoint-[]₁ x ()

Disjoint-[]₂ : ∀ {ℓ} {A : Set ℓ} {xs : List A} →
  Disjoint xs []
Disjoint-[]₂ = Disjoint-sym Disjoint-[]₁

Disjoint-∷₁ : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} →
  x ∉ ys →
  Disjoint xs ys →
  Disjoint (x ∷ xs) ys
Disjoint-∷₁ x∉ys D-xs-ys x (here refl) = x∉ys
Disjoint-∷₁ x∉ys D-xs-ys x (there p) = D-xs-ys x p

Disjoint-∷₂ : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} →
  x ∉ xs →
  Disjoint xs ys →
  Disjoint xs (x ∷ ys)
Disjoint-∷₂ x∉ys D-xs-ys = Disjoint-sym (Disjoint-∷₁ x∉ys (Disjoint-sym D-xs-ys))

Disjoint-++₁ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₂ ys : List A} →
  Disjoint xs₁ ys →
  Disjoint xs₂ ys →
  Disjoint (xs₁ ++ xs₂) ys
Disjoint-++₁ {xs₁ = xs₁} d₁ d₂ x x∈xs₁++xs₂
  with AnyP.++⁻ xs₁ x∈xs₁++xs₂
… | inj₁ x∈xs₁ = d₁ x x∈xs₁ 
… | inj₂ x∈xs₂ = d₂ x x∈xs₂

Disjoint-++₂ : ∀ {ℓ} {A : Set ℓ} {xs ys₁ ys₂ : List A} →
  Disjoint xs ys₁ →
  Disjoint xs ys₂ →
  Disjoint xs (ys₁ ++ ys₂)
Disjoint-++₂ d₁ d₂ = Disjoint-sym (Disjoint-++₁ (Disjoint-sym d₁) (Disjoint-sym d₂))

Disjoint-∈-≢ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x y} {xs ys : List A} →
  Disjoint xs ys →
  x ∈ xs →
  y ∈ ys →
  x ≢ y
Disjoint-∈-≢ {x = x} {y = y} d x∈xs y∈ys
  with x ≟ y
… | yes refl = ⊥-elim (d x x∈xs y∈ys)
… | no ¬x≡y  = ¬x≡y

∈-++⁻-disjoint : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {x} →
  Disjoint xs ys →
  x ∈ xs ++ ys →
  x ∈ xs × x ∉ ys ⊎
  x ∉ xs × x ∈ ys
∈-++⁻-disjoint {xs = []}      {x = x} d x∈ = inj₂ ((λ ()) , x∈)
∈-++⁻-disjoint {xs = x₁ ∷ xs} {x = x} d (here refl) =
  inj₁ (here refl , (λ x∈ys → d x (here refl) x∈ys))
∈-++⁻-disjoint {xs = x₁ ∷ xs} {x = x} d (there x∈)
  with ∈-++⁻-disjoint (Disjoint-⊆₁ ⊆-∷ d) x∈
… | inj₁ (x∈xs , x∉ys) = inj₁ ((there x∈xs) , x∉ys)
… | inj₂ (x∉xs , x∈ys) = inj₂ ((λ { (here refl) → d x (here refl) x∈ys ; (there x∈xs) → x∉xs x∈xs }) , x∈ys)

Disjoint-++⁻⁻ : ∀ {ℓ} {A : Set ℓ} (xs₁ xs₂ ys₁ ys₂ : List A) →
  Disjoint (xs₁ ++ xs₂) (ys₁ ++ ys₂) →
  Disjoint xs₁ ys₁ × Disjoint xs₂ ys₂
Disjoint-++⁻⁻ xs₁ xs₂ ys₁ ys₂ d =
  Disjoint-⊆ ⊆-++₁' ⊆-++₁' d , Disjoint-⊆ (⊆-++₂' _) (⊆-++₂' _) d

Unique : ∀ {ℓ} {A : Set ℓ} → List A → Set ℓ
Unique xs = ∀ x (p q : x ∈ xs) → p ≡ q

Unique-[] : ∀ {ℓ} {A : Set ℓ} → Unique {A = A} []
Unique-[] x ()

Unique-∷ : ∀ {ℓ} {A : Set ℓ} {x} {xs : List A} →
  x ∉ xs →
  Unique xs →
  Unique (x ∷ xs)
Unique-∷ x∉xs U-xs x (here refl) (here refl) = refl
Unique-∷ x∉xs U-xs x (here refl) (there x∈xs) = ⊥-elim (x∉xs x∈xs)
Unique-∷ x∉xs U-xs x (there x∈xs) (here refl) = ⊥-elim (x∉xs x∈xs)
Unique-∷ x∉xs U-xs x (there p) (there q) = cong there (U-xs x p q)

Unique-single : ∀ {ℓ} {A : Set ℓ} (x : A) →
  Unique (x ∷ [])
Unique-single x = Unique-∷ (λ ()) Unique-[]

Unique-tail : ∀ {ℓ} {A : Set ℓ} {x} {xs : List A} → Unique (x ∷ xs) → Unique xs
Unique-tail {x = x} {xs = xs} U-ys y p q = AnyP.there-injective (U-ys y (there p) (there q))

Unique-∈-∷ : ∀ {ℓ} {A : Set ℓ} x (xs : List A) →
  Unique (x ∷ xs) →
  x ∉ xs
Unique-∈-∷ x xs U p with () ← U x (here refl) (there p)

Unique-∈-prop : ∀ {ℓ} {A : Set ℓ} {xs : List A} {x} → Unique xs → (p q : x ∈ xs) → p ≡ q
Unique-∈-prop {xs = x' ∷ xs} {x = x} U-xs (here refl) (here refl) = refl
Unique-∈-prop {xs = x' ∷ xs} {x = x} U-xs (here refl) (there q)   = ⊥-elim (Unique-∈-∷ x' xs U-xs q)
Unique-∈-prop {xs = x' ∷ xs} {x = x} U-xs (there p)   (here refl) = ⊥-elim (Unique-∈-∷ x' xs U-xs p)
Unique-∈-prop {xs = x' ∷ xs} {x = x} U-xs (there p)   (there q)   = cong there (Unique-∈-prop (Unique-tail U-xs) p q)

LocalInj : ∀ {ℓ ℓ'} {A : Set ℓ} xs {B : A → Set ℓ'} → (∀ {x} → x ∈ xs → B x) → Set (ℓ ⊔ ℓ')
LocalInj xs f = ∀ x → (p q : x ∈ xs) → f p ≡ f q → p ≡ q

infix 4 _⊆ⁱ_
record _⊆ⁱ_ {ℓ} {A : Set ℓ} (xs ys : List A) : Set ℓ where
  constructor mk-⊆ⁱ
  field
    ⊆ⁱ→⊆ : xs ⊆ ys
    ⊆ⁱ-inj : LocalInj xs ⊆ⁱ→⊆

open _⊆ⁱ_ public

⊆-refl-inj : ∀ {ℓ} {A : Set ℓ} {xs : List A} → LocalInj xs ⊆-refl
⊆-refl-inj x p q eq = eq

⊆ⁱ-refl : ∀ {ℓ} {A : Set ℓ} {xs : List A} → xs ⊆ⁱ xs
⊆ⁱ-refl = mk-⊆ⁱ ⊆-refl ⊆-refl-inj

⊆-trans-inj : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A} {xs⊆ys : xs ⊆ ys} {ys⊆zs : ys ⊆ zs} →
  LocalInj xs xs⊆ys →
  LocalInj ys ys⊆zs →
  LocalInj xs (⊆-trans xs⊆ys ys⊆zs)
⊆-trans-inj {xs⊆ys = xs⊆ys} {ys⊆zs = ys⊆zs} xs⊆ys-inj ys⊆zs-inj x p q eq =
  let eq' = ys⊆zs-inj x (xs⊆ys p) (xs⊆ys q) eq in
  xs⊆ys-inj x p q eq' 

⊆ⁱ-trans : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A} → xs ⊆ⁱ ys → ys ⊆ⁱ zs → xs ⊆ⁱ zs
⊆ⁱ-trans (mk-⊆ⁱ xs⊆ys xs⊆ys-inj) (mk-⊆ⁱ ys⊆zs ys⊆zs-inj) =
  mk-⊆ⁱ (⊆-trans xs⊆ys ys⊆zs) (⊆-trans-inj xs⊆ys-inj ys⊆zs-inj)

infix 4 _≈ⁱ_
record _≈ⁱ_ {ℓ} {A : Set ℓ} (xs ys : List A) : Set ℓ where
  constructor mk-≈ⁱ
  field
    ≈ⁱ→⊆ⁱ : xs ⊆ⁱ ys
    ≈ⁱ→⊇ⁱ : ys ⊆ⁱ xs

  ≈ⁱ→⊆ : xs ⊆ ys
  ≈ⁱ→⊆ = ⊆ⁱ→⊆ ≈ⁱ→⊆ⁱ

  ≈ⁱ→⊇ : ys ⊆ xs
  ≈ⁱ→⊇ = ⊆ⁱ→⊆ ≈ⁱ→⊇ⁱ

  ≈ⁱ→≈ˡ : xs ≈ˡ ys
  ≈ⁱ→≈ˡ = ≈ⁱ→⊆ , ≈ⁱ→⊇

  ≈ⁱ→⊆-inj : LocalInj xs ≈ⁱ→⊆
  ≈ⁱ→⊆-inj = ⊆ⁱ-inj ≈ⁱ→⊆ⁱ

  ≈ⁱ→⊇-inj : LocalInj ys ≈ⁱ→⊇
  ≈ⁱ→⊇-inj = ⊆ⁱ-inj ≈ⁱ→⊇ⁱ

open _≈ⁱ_ public

≈ⁱ-refl : ∀ {ℓ} {A : Set ℓ} {xs : List A} → xs ≈ⁱ xs
≈ⁱ-refl = mk-≈ⁱ ⊆ⁱ-refl ⊆ⁱ-refl

≈ⁱ-sym : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ≈ⁱ ys → ys ≈ⁱ xs
≈ⁱ-sym (mk-≈ⁱ p q) = mk-≈ⁱ q p

≈ⁱ-trans : ∀ {ℓ} {A : Set ℓ} {xs ys zs : List A} → xs ≈ⁱ ys → ys ≈ⁱ zs → xs ≈ⁱ zs
≈ⁱ-trans (mk-≈ⁱ xs⊆ys ys⊆xs) (mk-≈ⁱ ys⊆zs zs⊆ys) = mk-≈ⁱ (⊆ⁱ-trans xs⊆ys ys⊆zs) (⊆ⁱ-trans zs⊆ys ys⊆xs)

module ⊆ⁱ-Reasoning where
  infix 1 begin_
  infixr 2 _≈⟨_⟩_ _⊆⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {xs ys : List A} → xs ⊆ⁱ ys → xs ⊆ⁱ ys
  begin p = p

  _⊆⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ⊆ⁱ ys → ys ⊆ⁱ zs → xs ⊆ⁱ zs
  _ ⊆⟨ p ⟩ q = ⊆ⁱ-trans p q

  _≈⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≈ⁱ ys → ys ⊆ⁱ zs → xs ⊆ⁱ zs
  _ ≈⟨ p ⟩ q = ⊆ⁱ-trans (≈ⁱ→⊆ⁱ p) q

  _≡⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≡ ys → ys ⊆ⁱ zs → xs ⊆ⁱ zs
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (xs {ys} : List A) → xs ⊆ⁱ ys → xs ⊆ⁱ ys
  _ ≡⟨⟩ q = q

  _∎ : ∀ (xs : List A) → xs ⊆ⁱ xs
  _ ∎ = ⊆ⁱ-refl

module ≈ⁱ-Reasoning where
  infix 1 begin_
  infixr 2 _≈⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {xs ys : List A} → xs ≈ⁱ ys → xs ≈ⁱ ys
  begin p = p

  _≈⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≈ⁱ ys → ys ≈ⁱ zs → xs ≈ⁱ zs
  _ ≈⟨ p ⟩ q = ≈ⁱ-trans p q

  _≡⟨_⟩_ : ∀ (xs {ys zs} : List A) → xs ≡ ys → ys ≈ⁱ zs → xs ≈ⁱ zs
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (xs {ys} : List A) → xs ≈ⁱ ys → xs ≈ⁱ ys
  _ ≡⟨⟩ q = q

  _∎ : ∀ (xs : List A) → xs ≈ⁱ xs
  _ ∎ = ≈ⁱ-refl

++⁺ˡ-injective : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} {p q : x ∈ xs} →
  AnyP.++⁺ˡ {ys = ys} p ≡ AnyP.++⁺ˡ {ys = ys} q →
  p ≡ q 
++⁺ˡ-injective {xs = x' ∷ xs} {p = here refl} {q = here refl} eq = refl
++⁺ˡ-injective {xs = x' ∷ xs} {p = there p}   {q = there q}   eq = cong there (++⁺ˡ-injective (AnyP.there-injective eq))

++⁺ʳ-injective : ∀ {ℓ} {A : Set ℓ} {y} {xs ys : List A} {p q : y ∈ ys} →
  AnyP.++⁺ʳ xs {ys = ys} p ≡ AnyP.++⁺ʳ xs {ys = ys} q →
  p ≡ q 
++⁺ʳ-injective {xs = []}     eq = eq
++⁺ʳ-injective {xs = x ∷ xs} eq = ++⁺ʳ-injective (AnyP.there-injective eq)

++⁻-injective : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} {p q : x ∈ xs ++ ys} →
  AnyP.++⁻ xs {ys = ys} p ≡ AnyP.++⁻ xs {ys = ys} q →
  p ≡ q 
++⁻-injective {xs = []}     {p = p} {q = q} eq = SumP.inj₂-injective eq
++⁻-injective {xs = x ∷ xs} {p = here refl} {q = here refl} eq = refl
++⁻-injective {xs = x ∷ xs} {p = here refl} {q = there q}   eq
  with AnyP.++⁻ xs q
… | inj₁ q' with () ← eq
… | inj₂ q' with () ← eq
++⁻-injective {xs = x ∷ xs} {p = there p}   {q = here refl} eq
  with AnyP.++⁻ xs p
… | inj₁ p' with () ← eq
… | inj₂ p' with () ← eq
++⁻-injective {xs = x ∷ xs} {p = there p}   {q = there q}   eq
  with AnyP.++⁻ xs p in eq-p | AnyP.++⁻ xs q in eq-q
… | inj₁ p' | inj₁ q' with refl ← eq = cong there (++⁻-injective {p = p} {q = q} (trans eq-p (sym eq-q))) 
… | inj₁ p' | inj₂ q' with () ← eq
… | inj₂ p' | inj₁ q' with () ← eq
… | inj₂ p' | inj₂ q' with refl ← eq = cong there (++⁻-injective {p = p} {q = q} (trans eq-p (sym eq-q)))

⊆-++₁'-inj : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → LocalInj xs (⊆-++₁' {xs₂ = ys})
⊆-++₁'-inj x p q = ++⁺ˡ-injective

⊆-++₂'-inj : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → LocalInj ys (⊆-++₂' xs {xs₂ = ys})
⊆-++₂'-inj x p q = ++⁺ʳ-injective

⊆ⁱ-++₁ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ⊆ⁱ xs ++ ys
⊆ⁱ-++₁ = mk-⊆ⁱ ⊆-++₁' ⊆-++₁'-inj

⊆ⁱ-++₂ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → ys ⊆ⁱ xs ++ ys
⊆ⁱ-++₂ = mk-⊆ⁱ (⊆-++₂' _) ⊆-++₂'-inj

++⁺ʳ≢++⁺ˡ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {z} {z∈xs : z ∈ xs} {z∈ys : z ∈ ys} → AnyP.++⁺ʳ ys z∈xs ≢ AnyP.++⁺ˡ z∈ys
++⁺ʳ≢++⁺ˡ {ys = y ∷ ys} {z∈xs = z∈xs} {z∈ys = here refl} ()
++⁺ʳ≢++⁺ˡ {ys = y ∷ ys} {z∈xs = z∈xs} {z∈ys = there z∈ys} eq = ++⁺ʳ≢++⁺ˡ (AnyP.there-injective eq)

⊆-comm-inj : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → LocalInj (xs ++ ys) (⊆-comm xs ys)
⊆-comm-inj xs ys x p q eq with AnyP.++⁻ xs p in eq-p | AnyP.++⁻ xs q in eq-q
… | inj₁ x∈xs | inj₁ x∈xs' = let x∈xs≡x∈xs' = ++⁺ʳ-injective eq in
                             let eq' = trans eq-p (trans (cong inj₁ x∈xs≡x∈xs') (sym eq-q)) in
                             ++⁻-injective eq'
… | inj₁ x∈xs | inj₂ x∈ys' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
… | inj₂ x∈ys | inj₁ x∈xs' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq))
… | inj₂ x∈ys | inj₂ x∈ys' = let x∈xs≡x∈xs' = ++⁺ˡ-injective eq in
                             let eq' = trans eq-p (trans (cong inj₂ x∈xs≡x∈xs') (sym eq-q)) in
                             ++⁻-injective eq'

⊆ⁱ-comm : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → xs ++ ys ⊆ⁱ ys ++ xs
⊆ⁱ-comm xs ys = mk-⊆ⁱ (⊆-comm xs ys) (⊆-comm-inj xs ys)

≈ⁱ-comm : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → xs ++ ys ≈ⁱ ys ++ xs
≈ⁱ-comm xs ys = mk-≈ⁱ (⊆ⁱ-comm xs ys) (⊆ⁱ-comm ys xs)

⊆-assoc-inj : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → LocalInj ((xs ++ ys) ++ zs) (⊆-assoc xs ys zs)
⊆-assoc-inj xs ys zs x p q eq with AnyP.++⁻ (xs ++ ys) p in eq-p | AnyP.++⁻ (xs ++ ys) q in eq-q
⊆-assoc-inj xs ys zs x p q eq | inj₂ p' | inj₂ q' = let p'≡q' = ++⁺ʳ-injective {ys = zs} (++⁺ʳ-injective {xs = xs} eq) in
                                                    ++⁻-injective (trans eq-p (trans (cong inj₂ p'≡q') (sym eq-q)))
⊆-assoc-inj xs ys zs x p q eq | inj₂ p' | inj₁ q'
  with AnyP.++⁻ xs q' 
… | inj₂ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (++⁺ʳ-injective {xs = xs} eq))
… | inj₁ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
⊆-assoc-inj xs ys zs x p q eq | inj₁ p' | inj₂ q'
  with AnyP.++⁻ xs p' 
… | inj₂ p'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym (++⁺ʳ-injective {xs = xs} eq)))
… | inj₁ p'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq))
⊆-assoc-inj xs ys zs x p q eq | inj₁ p' | inj₁ q'
  with AnyP.++⁻ xs p' in eq-p' | AnyP.++⁻ xs q' in eq-q'
… | inj₂ p'' | inj₂ q'' = let p''≡q'' = ++⁺ˡ-injective (++⁺ʳ-injective {xs = xs} eq) in
                          let p'≡q' = ++⁻-injective (trans eq-p' (trans (cong inj₂ p''≡q'') (sym eq-q'))) in
                          ++⁻-injective (trans eq-p (trans (cong inj₁ p'≡q') (sym eq-q))) 
… | inj₂ p'' | inj₁ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
… | inj₁ p'' | inj₂ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq))
… | inj₁ p'' | inj₁ q'' = let p''≡q'' = ++⁺ˡ-injective eq in
                          let p'≡q' = ++⁻-injective (trans eq-p' (trans (cong inj₁ p''≡q'') (sym eq-q'))) in
                          ++⁻-injective (trans eq-p (trans (cong inj₁ p'≡q') (sym eq-q)))

⊆-assoc'-inj : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → LocalInj (xs ++ (ys ++ zs)) (⊆-assoc' xs ys zs)
⊆-assoc'-inj xs ys zs x p q eq with AnyP.++⁻ xs p in eq-p | AnyP.++⁻ xs q in eq-q
⊆-assoc'-inj xs ys zs x p q eq | inj₁ p' | inj₁ q' = let p'≡q' = ++⁺ˡ-injective (++⁺ˡ-injective eq) in
                                                     ++⁻-injective (trans eq-p (trans (cong inj₁ p'≡q') (sym eq-q)))
⊆-assoc'-inj xs ys zs x p q eq | inj₁ p' | inj₂ q'
  with AnyP.++⁻ ys q' 
… | inj₁ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym (++⁺ˡ-injective eq))) -- ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
… | inj₂ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq)) -- ⊥-elim (++⁺ʳ≢++⁺ˡ (++⁺ʳ-injective {xs = xs} eq))
⊆-assoc'-inj xs ys zs x p q eq | inj₂ p' | inj₁ q'
  with AnyP.++⁻ ys p' 
… | inj₁ p'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (++⁺ˡ-injective eq))
… | inj₂ p'' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
⊆-assoc'-inj xs ys zs x p q eq | inj₂ p' | inj₂ q'
  with AnyP.++⁻ ys p' in eq-p' | AnyP.++⁻ ys q' in eq-q'
… | inj₁ p'' | inj₁ q'' = let p''≡q'' = ++⁺ʳ-injective (++⁺ˡ-injective eq) in
                          let p'≡q' = ++⁻-injective (trans eq-p' (trans (cong inj₁ p''≡q'') (sym eq-q'))) in
                          ++⁻-injective (trans eq-p (trans (cong inj₂ p'≡q') (sym eq-q)))
… | inj₁ p'' | inj₂ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq))
… | inj₂ p'' | inj₁ q'' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
… | inj₂ p'' | inj₂ q'' = let p''≡q'' = ++⁺ʳ-injective eq in
                          let p'≡q' = ++⁻-injective (trans eq-p' (trans (cong inj₂ p''≡q'') (sym eq-q'))) in
                          ++⁻-injective (trans eq-p (trans (cong inj₂ p'≡q') (sym eq-q)))

⊆ⁱ-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ⊆ⁱ (xs ++ (ys ++ zs))
⊆ⁱ-assoc xs ys zs = mk-⊆ⁱ (⊆-assoc xs ys zs) (⊆-assoc-inj xs ys zs)

⊆ⁱ-assoc' : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → (xs ++ (ys ++ zs)) ⊆ⁱ ((xs ++ ys) ++ zs)
⊆ⁱ-assoc' xs ys zs = mk-⊆ⁱ (⊆-assoc' xs ys zs) (⊆-assoc'-inj xs ys zs)

≈ⁱ-assoc : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → ((xs ++ ys) ++ zs) ≈ⁱ (xs ++ (ys ++ zs))
≈ⁱ-assoc xs ys zs = mk-≈ⁱ (⊆ⁱ-assoc xs ys zs) (⊆ⁱ-assoc' xs ys zs)

⊆-++-inj : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₁' xs₂ xs₂' : List A} {xs₁⊆xs₁' : xs₁ ⊆ xs₁'} {xs₂⊆xs₂' : xs₂ ⊆ xs₂'} →
  LocalInj xs₁ xs₁⊆xs₁' →
  LocalInj xs₂ xs₂⊆xs₂' →
  LocalInj (xs₁ ++ xs₂) (⊆-++ xs₁⊆xs₁' xs₂⊆xs₂')
⊆-++-inj {xs₁ = xs₁} {xs₂ = xs₂} {xs₁⊆xs₁' = xs₁⊆xs₁'} {xs₂⊆xs₂' = xs₂⊆xs₂'} inj1 inj2 x p q eq
  with AnyP.++⁻ xs₁ p in eq-p | AnyP.++⁻ xs₁ q in eq-q
… | inj₁ p' | inj₁ q' = let p'≡q' = inj1 x p' q' (++⁺ˡ-injective eq) in
                        ++⁻-injective (trans eq-p (trans (cong inj₁ p'≡q') (sym eq-q)))
… | inj₁ p' | inj₂ q' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq))
… | inj₂ p' | inj₁ q' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
… | inj₂ p' | inj₂ q' = let p'≡q' = inj2 x p' q' (++⁺ʳ-injective eq) in
                        ++⁻-injective (trans eq-p (trans (cong inj₂ p'≡q') (sym eq-q)))

⊆ⁱ-++ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₁' xs₂ xs₂' : List A} → xs₁ ⊆ⁱ xs₁' → xs₂ ⊆ⁱ xs₂' → (xs₁ ++ xs₂) ⊆ⁱ (xs₁' ++ xs₂')
⊆ⁱ-++ (mk-⊆ⁱ p p') (mk-⊆ⁱ q q') = mk-⊆ⁱ (⊆-++ p q) (⊆-++-inj p' q')

≈ⁱ-++ : ∀ {ℓ} {A : Set ℓ} {xs₁ xs₁' xs₂ xs₂' : List A} → xs₁ ≈ⁱ xs₁' → xs₂ ≈ⁱ xs₂' → (xs₁ ++ xs₂) ≈ⁱ (xs₁' ++ xs₂')
≈ⁱ-++ (mk-≈ⁱ p p') (mk-≈ⁱ q q') = mk-≈ⁱ (⊆ⁱ-++ p q) (⊆ⁱ-++ p' q')

-- ⊆-map-inj : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {xs⊆ys : xs ⊆ ys} (f : A → B) →
--   LocalInj xs xs⊆ys →
--   LocalInj (L.map f xs) (⊆-map f xs⊆ys)
-- ⊆-map-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x p q eq = {!!}
-- ⊆-map-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (here refl) (here refl) eq = refl
-- ⊆-map-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (here refl) (there q)   eq = {!!}
-- ⊆-map-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (there p)   (here refl) eq = {!!}
-- ⊆-map-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (there p)   (there q)   eq = {!⊆-map-inj f !}

⊆-map' : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} (f : A → B) → xs ⊆ ys → L.map f xs ⊆ L.map f ys
⊆-map' {xs = xs} f sub x∈fxs =
  let x' , x'∈xs , fx'≡x = map-∈-inv f xs x∈fxs in
  let x'∈ys = sub x'∈xs in
  subst (_∈ _) fx'≡x (∈-map f x'∈ys) 

∈-map-injective : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x} {xs : List A} (f : A → B) {p q : x ∈ xs} →
  ∈-map f p ≡ ∈-map f q →
  p ≡ q 
∈-map-injective f {p = here refl} {q = here refl} eq = refl
∈-map-injective f {p = here refl} {q = there q}   eq with () ← eq
∈-map-injective f {p = there p}   {q = here refl} eq with () ← eq
∈-map-injective f {p = there p}   {q = there q}   eq = cong there (∈-map-injective f (AnyP.there-injective eq))

subst-injective : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x y : A} (eq₁ eq₂ : x ≡ y) {p q : P x} →
                  subst P eq₁ p ≡ subst P eq₂ q → p ≡ q
subst-injective refl refl p≡q = p≡q

-- there-injective-heq : ∀ {ℓ} {A : Set ℓ} {x x' : A} {xs : List A} {y : A} {ys : List A}
--                         {p : x ∈ xs} {q : y ∈ xs} → there {x = x'} p ≅ there {x = x'} q → p ≅ q
-- there-injective-heq refl = refl

-- map-∈-inv-injective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {y} (f : A → B) (xs : List A) →
--   (p q : y ∈ L.map f xs) →
--   proj₁ (map-∈-inv f xs p) ≡ proj₁ (map-∈-inv f xs q) →
--   proj₁ (proj₂ (map-∈-inv f xs p)) ≅ proj₁ (proj₂ (map-∈-inv f xs q)) →
--   p ≡ q
-- map-∈-inv-injective f (x ∷ xs) (here refl) (here refl) eq₁ eq₂ = refl
-- map-∈-inv-injective f (x ∷ xs) (here refl) (there q)   eq₁ ()
-- map-∈-inv-injective f (x ∷ xs) (there p)   (here refl) eq₁ ()
-- map-∈-inv-injective f (x ∷ xs) (there p)   (there q)   eq₁ eq₂ =
--   cong there (map-∈-inv-injective f xs p q eq₁ {!there-injective-heq eq₂!}) 
-- -- map-∈-inv f (x ∷ xs) (here px) = x , here refl , sym px
-- -- map-∈-inv f (x ∷ xs) (there y∈fxs) =
-- --   let (x , x∈ , eq) = map-∈-inv f xs y∈fxs in
-- --   x , there x∈ , eq

subst-wtf : ∀ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} {x : A} (eq : x ≡ x) {p q : P x} →
                  subst P eq p ≡ q → p ≡ q
subst-wtf refl p≡q = p≡q

≡-prop : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p q : x ≡ y) → p ≡ q
≡-prop refl refl = refl

map-∈-inv-injective : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} {y} (f : A → B) (xs : List A) →
  (p q : y ∈ L.map f xs) →
  map-∈-inv f xs p ≡ map-∈-inv f xs q →
  p ≡ q
map-∈-inv-injective f (x ∷ xs) (here refl) (here refl) eq = refl
map-∈-inv-injective f (x ∷ xs) (here refl) (there q)   ()
map-∈-inv-injective f (x ∷ xs) (there p)   (here refl) ()
map-∈-inv-injective f (x ∷ xs) (there p)   (there q)   eq
  with x' , x'∈ , fx'≡x ← map-∈-inv f xs p in eq-p
  with y' , y'∈ , fy'≡x ← map-∈-inv f xs q in eq-q
  using x'≡y' ← ProdP.,-injectiveˡ eq
  using x'∈≡y'∈' ← ProdP.,-injectiveʳ-≡ ≡-prop eq x'≡y'
  with refl ← x'≡y' in eq'
  using xx ← (there x'∈ , fx'≡x) ≡ (there y'∈ , fy'≡x) by subst-wtf x'≡y' x'∈≡y'∈'
  using yy ← there x'∈ ≡ there y'∈ by ProdP.,-injectiveˡ xx
  using zz ← x'∈ ≡ y'∈ by AnyP.there-injective yy
  using ww ← fx'≡x ≡ fy'≡x by ProdP.,-injectiveʳ xx
  rewrite eq'
  =
  cong there (map-∈-inv-injective f xs p q (trans eq-p (trans (cong (y' ,_) (cong₂ _,_ zz ww)) (sym eq-q))))

-- -- ⊆-map : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} (f : A → B) → xs ⊆ ys → L.map f xs ⊆ L.map f ys
-- -- ⊆-map {xs = x ∷ xs} f sub (here refl) = ∈-map f (sub (here refl))
-- -- ⊆-map {xs = x ∷ xs} f sub (there x∈) = ⊆-map f (⊆-++₂ {xs₁ = x ∷ []} sub) x∈

-- ∈-map-subst : ∀ {ℓ} {A : Set ℓ} {x y} {xs : List A} (f : A → B) (eq : f x ≡ f y) (p : x ∈ xs) (q : x ∈ xs) →
--   ∈-map f p ≡ subst (_∈ L.map f xs) eq (∈-map f q) →
--   p ≡ q
-- ∈-map-subst = ?

-- ∈-map-subst : ∀ {ℓ} {A : Set ℓ} {x y} {xs : List A} (f : A → B) (eq : f x ≡ y) (p : x ∈ xs) (q : x ∈ xs) →
--   ∈-map f (xs⊆ys (here refl)) ≢
--     subst (_∈ L.map f ys) (sym fx'≡fx) (∈-map f (xs⊆ys (there (AnyP.++⁺ʳ xs' (here refl)))))
-- ∈-map-subst = ?

-- ⊆-map'-inj' : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {x'} xs' (xs⊆ys : x' ∷ xs' ++ xs ⊆ ys) (f : A → B) (q : f x' ∈ L.map f xs) →
--   ∈-map f (xs⊆ys (here refl)) ≢ ⊆-map f (λ x∈ → xs⊆ys (there (AnyP.++⁺ʳ xs' x∈))) q
-- ⊆-map'-inj' {xs = x ∷ xs} xs' xs⊆ys f (here fx'≡fx) =
--   {!(xs⊆ys (there (AnyP.++⁺ʳ xs' (here refl))))!}
-- ⊆-map'-inj' {xs = x ∷ xs} xs' xs⊆ys f (there q) =
--   ⊆-map'-inj' (xs' ++ (x ∷ [])) {!xs⊆ys!} f q
-- -- ⊆-map'-inj' {xs = x ∷ xs} f (here px) = {!!}
-- -- ⊆-map'-inj' {xs = x ∷ xs} {x' = x'} {xs⊆ys = xs⊆ys} f (there q) = {!⊆-map'-inj' {xs⊆ys = ⊆-++₂ {xs₁ = x ∷ []} {!xs⊆ys!}} f q!}

-- ⊆-map'-inj : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {xs⊆ys : xs ⊆ ys} (f : A → B) →
--   LocalInj xs xs⊆ys →
--   LocalInj (L.map f xs) (⊆-map f xs⊆ys)
-- ⊆-map'-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (here refl) (here refl) eq =
--   refl
-- ⊆-map'-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (here refl) (there q)   eq =
--   ⊥-elim (⊆-map'-inj' [] xs⊆ys f q eq)
-- ⊆-map'-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (there p)   (here refl) eq =
--   {!!}
-- ⊆-map'-inj {xs = x' ∷ xs} {xs⊆ys = xs⊆ys} f inj x (there p)   (there q)   eq =
--   cong there (⊆-map'-inj f
--     (λ x₁ p₁ q₁ eq' → AnyP.there-injective (inj x₁ (there p₁) (there q₁) eq'))
--     x p q eq)

⊆-map-inj : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} {xs⊆ys : xs ⊆ ys} (f : A → B) →
  (∀ x y → x ∈ xs → y ∈ xs → f x ≡ f y → x ≡ y) →
  LocalInj xs xs⊆ys →
  LocalInj (L.map f xs) (⊆-map' f xs⊆ys)
⊆-map-inj {xs = xs} {xs⊆ys = xs⊆ys} f inj-f inj x p q eq
  with x' , x'∈xs , fx'≡x ← map-∈-inv f xs p in eq-p
  with y' , y'∈xs , fy'≡x ← map-∈-inv f xs q in eq-q
  using x'≡y' ← inj-f x' y' x'∈xs y'∈xs (trans fx'≡x (sym fy'≡x))
  with refl ← x'≡y'
  using x'∈ys ← xs⊆ys x'∈xs
  using y'∈ys ← xs⊆ys y'∈xs
  =
  let x'∈ys≡y'∈ys = ∈-map-injective f (subst-injective fx'≡x fy'≡x eq) in
  let x'∈xs≡y'∈xs = inj x' x'∈xs y'∈xs x'∈ys≡y'∈ys in
  map-∈-inv-injective f xs p q (trans eq-p (trans (cong (y' ,_) (cong₂ _,_ x'∈xs≡y'∈xs (≡-prop fx'≡x fy'≡x))) (sym eq-q)))

⊆ⁱ-map : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} (f : A → B) →
  (∀ x y → x ∈ xs → y ∈ xs → f x ≡ f y → x ≡ y) →
  xs ⊆ⁱ ys →
  L.map f xs ⊆ⁱ L.map f ys
⊆ⁱ-map f f-inj (mk-⊆ⁱ s s-inj) = mk-⊆ⁱ (⊆-map' f s) (⊆-map-inj f f-inj s-inj)

Unique-cod→Injective : ∀ (xs : List (A × B)) →
  Unique (L.map proj₁ xs) →
  (∀ x y → x ∈ xs → y ∈ xs → proj₁ x ≡ proj₁ y → x ≡ y)
Unique-cod→Injective (x' ∷ xs) U-cod x y (here refl) (here refl) ρx≡ρy =
  refl
Unique-cod→Injective (_  ∷ xs) U-cod x y (here refl) (there y∈xs) ρx≡ρy =
  ⊥-elim (Unique-∈-∷ (proj₁ y) _ (subst (λ ■ → Unique (■ ∷ L.map proj₁ xs)) ρx≡ρy U-cod) (∈-map proj₁ y∈xs))
Unique-cod→Injective (_ ∷ xs) U-cod x y (there x∈xs) (here refl) ρx≡ρy =
  ⊥-elim (Unique-∈-∷ (proj₁ x) _ (subst (λ ■ → Unique (■ ∷ L.map proj₁ xs)) (sym ρx≡ρy) U-cod) (∈-map proj₁ x∈xs))
Unique-cod→Injective (x' ∷ xs) U-cod x y (there x∈xs) (there y∈xs) ρx≡ρy =
  Unique-cod→Injective xs (Unique-tail U-cod) x y x∈xs y∈xs ρx≡ρy

Unique-⊆ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ⊆ⁱ ys → Unique ys → Unique xs
Unique-⊆ xs⊆ys U-ys x p q = ⊆ⁱ-inj xs⊆ys x p q (U-ys x (⊆ⁱ→⊆ xs⊆ys p) (⊆ⁱ→⊆ xs⊆ys q)) 

Unique-≈ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → xs ≈ⁱ ys → Unique ys → Unique xs
Unique-≈ (mk-≈ⁱ xs⊆ys _) = Unique-⊆ xs⊆ys

Unique-++₁ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → Unique (xs ++ ys) → Unique xs
Unique-++₁ U-xs++ys = Unique-⊆ ⊆ⁱ-++₁ U-xs++ys

Unique-++₂ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} → Unique (xs ++ ys) → Unique ys
Unique-++₂ U-xs++ys = Unique-⊆ ⊆ⁱ-++₂ U-xs++ys

Unique-∈-++₁ : ∀ {ℓ} {A : Set ℓ} {x} (xs ys : List A) →
  Unique (xs ++ ys) →
  x ∈ xs →
  x ∉ ys
Unique-∈-++₁ (x ∷ xs) ys U (here refl) x∈ys with () ← U x (here refl) (there (AnyP.++⁺ʳ xs x∈ys))
Unique-∈-++₁ (y ∷ xs) ys U (there x∈xs) x∈ys = Unique-∈-++₁ xs ys (Unique-tail U) x∈xs x∈ys

Unique-∈-++₂ : ∀ {ℓ} {A : Set ℓ} {x} (xs ys : List A) →
  Unique (xs ++ ys) →
  x ∈ ys →
  x ∉ xs
Unique-∈-++₂ xs ys U = Unique-∈-++₁ ys xs (Unique-⊆ (⊆ⁱ-comm ys xs) U)

∉-++ : ∀ {ℓ} {A : Set ℓ} x (xs ys : List A) →
  x ∉ xs →
  x ∉ ys →
  x ∉ (xs ++ ys)
∉-++ x xs ys x∉xs x∉ys x∈xs++ys
  with AnyP.++⁻ xs x∈xs++ys
… | inj₁ x∈xs = x∉xs x∈xs
… | inj₂ x∈ys = x∉ys x∈ys

∉-++⁻ : ∀ {ℓ} {A : Set ℓ} {x} (xs ys : List A) →
  x ∉ (xs ++ ys) →
  x ∉ xs × x ∉ ys
∉-++⁻ xs ys x∉xs++ys =
  (λ x∈xs → x∉xs++ys (AnyP.++⁺ˡ x∈xs)) , (λ x∈xs → x∉xs++ys (AnyP.++⁺ʳ _ x∈xs))

Unique-++ : ∀ {ℓ} {A : Set ℓ} {xs ys : List A} →
  Unique xs →
  Unique ys →
  Disjoint xs ys →
  Unique (xs ++ ys)
Unique-++ {xs = []} U-xs U-ys D = U-ys
Unique-++ {xs = x ∷ xs} U-xs U-ys D =
  Unique-∷ (∉-++ x xs _ (Unique-∈-∷ x xs U-xs) (D x (here refl)))
           (Unique-++ (Unique-tail U-xs) U-ys (Disjoint-⊆₁ ⊆-∷ D))

Unique-++-Disjoint : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) →
  Unique (xs ++ ys) →
  Disjoint xs ys
Unique-++-Disjoint [] ys u = Disjoint-[]₁
Unique-++-Disjoint (x ∷ xs) ys u =
  Disjoint-∷₁
    (λ x∈ys → Unique-∈-∷ x (xs ++ ys) u (AnyP.++⁺ʳ xs x∈ys))
    (Unique-++-Disjoint xs ys (Unique-tail u))

Unique-++⁻ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) →
  Unique (xs ++ ys) →
  Unique xs × Unique ys × Disjoint xs ys
Unique-++⁻ xs ys U-xs++ys =
  Unique-⊆ ⊆ⁱ-++₁ U-xs++ys ,
  Unique-⊆ ⊆ⁱ-++₂ U-xs++ys ,
  (Unique-++-Disjoint xs ys U-xs++ys)

⊆ⁱ-tail : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} → (x ∷ xs) ⊆ⁱ ys → xs ⊆ⁱ ys
⊆ⁱ-tail (mk-⊆ⁱ sub sub-inj) = mk-⊆ⁱ (⊆-trans ⊆-∷ sub) λ y p q eq →
  AnyP.there-injective (sub-inj y (there p) (there q) eq)

⊆-ext : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} → x ∈ ys → xs ⊆ ys → x ∷ xs ⊆ ys
⊆-ext x∈ys xs⊆ys = λ where
  (here refl) → x∈ys
  (there x∈xs) → xs⊆ys x∈xs

⊆-ext-inj : ∀ {ℓ} {A : Set ℓ} {x} {xs ys : List A} →
  (x∈ys : x ∈ ys) →
  (x∉xs : x ∉ xs) →
  (xs⊆ys : xs ⊆ ys) →
  LocalInj xs xs⊆ys →
  LocalInj (x ∷ xs) (⊆-ext x∈ys xs⊆ys)
⊆-ext-inj x∈ys x∉xs xs⊆ys xs⊆ys-inj y (here refl) (here refl) eq = refl
⊆-ext-inj x∈ys x∉xs xs⊆ys xs⊆ys-inj y (here refl) (there q)   eq = ⊥-elim (x∉xs q)
⊆-ext-inj x∈ys x∉xs xs⊆ys xs⊆ys-inj y (there p)   (here refl) eq = ⊥-elim (x∉xs p)
⊆-ext-inj x∈ys x∉xs xs⊆ys xs⊆ys-inj y (there p)   (there q)   eq =
  cong there (xs⊆ys-inj y p q eq)

_⊆ⁱ?_⊣_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) → Unique ys → Dec (xs ⊆ⁱ ys)
[] ⊆ⁱ? ys ⊣ U-yx = yes (mk-⊆ⁱ (λ()) (λ _ ()))
(x ∷ xs) ⊆ⁱ? ys ⊣ U-ys
  with xs ⊆ⁱ? ys ⊣ U-ys
… | no ¬xs⊆ⁱys = no λ x∷xs⊆ⁱys → ¬xs⊆ⁱys (⊆ⁱ-tail x∷xs⊆ⁱys)
… | yes xs⊆ⁱys
  with x ∈? ys
… | no ¬x∈ys = no λ x∷xs⊆ⁱys → ¬x∈ys (⊆ⁱ→⊆ x∷xs⊆ⁱys (here refl))
… | yes x∈ys
  with x ∈? xs
… | yes x∈xs =
  no λ x∷xs⊆ⁱys →
       let U-x∷xs = Unique-⊆ x∷xs⊆ⁱys U-ys in
       Unique-∈-∷ x xs U-x∷xs x∈xs 
… | no ¬x∈xs =
  yes (mk-⊆ⁱ (⊆-ext x∈ys (⊆ⁱ→⊆ xs⊆ⁱys)) (⊆-ext-inj x∈ys ¬x∈xs (⊆ⁱ→⊆ xs⊆ⁱys) (⊆ⁱ-inj xs⊆ⁱys)))

-- ∈?-yes : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x} {xs : List A} →
--   x ∈ xs →
--   ∃[ p ] x ∈? xs ≡ yes p
-- ∈?-yes {x = x} (here refl) with x ≟ x
-- … | yes refl  = (here refl) , refl
-- … | no ¬x≡x  = ⊥-elim (¬x≡x refl)
-- ∈?-yes {x = x} {xs = y ∷ xs} (there p) with x ≟ y
-- … | yes refl =
--   here refl , refl
-- … | no ¬x≡y rewrite proj₂ (∈?-yes {xs = xs} p) =
--   let (q , eq) = ∈?-yes {xs = xs} p in
--   there q , {!eq!}
-- -- … | no ¬x≡y =
-- --   let (q , eq) = ∈?-yes {xs = xs} p in
-- --   there q , {!eq!}

infixr 5 _∩ˡ_
_∩ˡ_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ → List A → List A → List A 
[]       ∩ˡ ys = []
(x ∷ xs) ∩ˡ ys
  with x ∈? ys
… | no ¬x∈ys = xs ∩ˡ ys
… | yes x∈ys
  with x ∈? (xs ∩ˡ ys)
… | yes x∈xs∩ys = xs ∩ˡ ys
… | no ¬x∈xs∩ys = x ∷ (xs ∩ˡ ys)

∩ˡ-∈-prop : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x} (xs ys : List A) →
  (p q : x ∈ xs ∩ˡ ys) →
  p ≡ q
∩ˡ-∈-prop (x ∷ xs) ys p q
  with x ∈? ys
… | no ¬x∈ys = ∩ˡ-∈-prop xs ys p q
… | yes x∈ys
  with x ∈? (xs ∩ˡ ys)
… | yes x∈xs∩ys = ∩ˡ-∈-prop xs ys p q
… | no ¬x∈xs∩ys
  with p | q
… | here refl | here refl = refl
… | here refl | there q   = ⊥-elim (¬x∈xs∩ys q)
… | there p   | here refl = ⊥-elim (¬x∈xs∩ys p)
… | there p   | there q   = cong there (∩ˡ-∈-prop xs ys p q)

∩ˡ-unique : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) →
  Unique (xs ∩ˡ ys)
∩ˡ-unique xs ys x p q = ∩ˡ-∈-prop xs ys p q

∩ˡ-∈⁺ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {z} {xs ys : List A} →
  z ∈ xs →
  z ∈ ys →
  z ∈ xs ∩ˡ ys
∩ˡ-∈⁺ {z = z} {x ∷ xs} {ys} p z∈ys
  with x ∈? ys
… | no ¬x∈ys = case p of λ where
  (here refl) → ⊥-elim (¬x∈ys z∈ys)
  (there z∈xs) → ∩ˡ-∈⁺ z∈xs z∈ys
… | yes x∈ys
  with x ∈? (xs ∩ˡ ys)
… | yes x∈xs∩ys = case p of λ where
  (here refl) → x∈xs∩ys
  (there z∈xs) → ∩ˡ-∈⁺ z∈xs z∈ys
… | no ¬x∈xs∩ys = case p of λ where
  (here refl) → here refl
  (there z∈xs) → there (∩ˡ-∈⁺ z∈xs z∈ys)

∩ˡ-∈⁻ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {z} (xs ys : List A) →
  z ∈ xs ∩ˡ ys →
  z ∈ xs × z ∈ ys
∩ˡ-∈⁻ {z = z} (x ∷ xs) ys z∈∩
  with x ∈? ys
… | no ¬x∈ys = map₁ there (∩ˡ-∈⁻ xs ys z∈∩)
… | yes x∈ys
  with x ∈? (xs ∩ˡ ys)
… | yes x∈xs∩ys = map₁ there (∩ˡ-∈⁻ xs ys z∈∩)
… | no ¬x∈xs∩ys
  with z∈∩
… | here refl = (here refl) , x∈ys
… | there z∈∩' = map₁ there (∩ˡ-∈⁻ xs ys z∈∩')

∩ˡ-∉⁺ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {z} (xs ys : List A) →
  z ∉ xs ⊎ z ∉ ys →
  z ∉ xs ∩ˡ ys
∩ˡ-∉⁺ xs ys (inj₁ z∉xs) z∈xs∩ys = ⊥-elim (z∉xs (proj₁ (∩ˡ-∈⁻ xs ys z∈xs∩ys)))
∩ˡ-∉⁺ xs ys (inj₂ z∉ys) z∈xs∩ys = ⊥-elim (z∉ys (proj₂ (∩ˡ-∈⁻ xs ys z∈xs∩ys)))

∩ˡ-∉⁻ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {z} (xs ys : List A) →
  z ∉ xs ∩ˡ ys →
  z ∉ xs ⊎ z ∉ ys
∩ˡ-∉⁻ {z = z} xs ys z∉xs∩ys
  with z ∈? xs | z ∈? ys
… | yes z∈xs | yes z∈ys = ⊥-elim (z∉xs∩ys (∩ˡ-∈⁺ z∈xs z∈ys))
… | no ¬z∈xs | _        = inj₁ ¬z∈xs
… | _        | no ¬z∈ys = inj₂ ¬z∈ys

∩ˡ-⊆₁ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) →
  (xs ∩ˡ ys) ⊆ xs
∩ˡ-⊆₁ xs ys {x} x∈xs∩ys = proj₁ (∩ˡ-∈⁻ xs ys x∈xs∩ys)

∩ˡ-⊆₂ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) →
  (xs ∩ˡ ys) ⊆ ys
∩ˡ-⊆₂ xs ys {x} x∈xs∩ys = proj₂ (∩ˡ-∈⁻ xs ys x∈xs∩ys)

∩ˡ-dist-map-⊆ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
                (f : A → B) (xs ys : List A) →
  L.map f (xs ∩ˡ ys) ⊆ L.map f xs ∩ˡ L.map f ys
∩ˡ-dist-map-⊆ f xs ys x∈f[xs∩ys] =
  let
    x' , x'∈xs∩ys , fx'≡x = map-∈-inv f (xs ∩ˡ ys) x∈f[xs∩ys]
    x'∈xs , x'∈ys = ∩ˡ-∈⁻ xs ys x'∈xs∩ys
    x∈fxs = subst (_∈ L.map f xs) fx'≡x (∈-map f x'∈xs)
    x∈fys = subst (_∈ L.map f ys) fx'≡x (∈-map f x'∈ys)
    x∈fxs∩fys = ∩ˡ-∈⁺ x∈fxs x∈fys
  in
  x∈fxs∩fys

∩ˡ-dist-map-⊇ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} ⦃ _ : DecEq A ⦄ ⦃ _ : DecEq B ⦄
                    (f : A → B) (xs ys : List A) →
  (∀ z₁ z₂ → z₁ ∈ xs ++ ys → z₂ ∈ xs ++ ys → f z₁ ≡ f z₂ → z₁ ≡ z₂) →
  L.map f xs ∩ˡ L.map f ys ⊆ L.map f (xs ∩ˡ ys)
∩ˡ-dist-map-⊇ f xs ys f-inj x∈fxs∩fys =
  let
    x∈fxs , x∈fys = ∩ˡ-∈⁻ (L.map f xs) (L.map f ys) x∈fxs∩fys
    x' , x'∈xs , fx'≡x = map-∈-inv f xs x∈fxs
    y' , y'∈ys , fy'≡x = map-∈-inv f ys x∈fys
    x'≡y' = f-inj x' y' (AnyP.++⁺ˡ x'∈xs) (AnyP.++⁺ʳ _ y'∈ys) (trans fx'≡x (sym fy'≡x))
    x'∈xs∩ys = ∩ˡ-∈⁺ x'∈xs (subst (_∈ ys) (sym x'≡y') y'∈ys)
    x∈f[xs∩ys] = subst (_∈ _) fx'≡x (∈-map f x'∈xs∩ys)
  in
  x∈f[xs∩ys]

zip-proj₁ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (xs : List A) (ys : List B) →
  L.length xs ≡ L.length ys →
  L.map proj₁ (L.zip xs ys) ≡ xs
zip-proj₁ []       []       eq = refl
zip-proj₁ (x ∷ xs) (y ∷ ys) eq = cong (x ∷_) (zip-proj₁ xs ys (NatP.suc-injective eq))

zip-proj₂ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (xs : List A) (ys : List B) →
  L.length xs ≡ L.length ys →
  L.map proj₂ (L.zip xs ys) ≡ ys
zip-proj₂ []       []       eq = refl
zip-proj₂ (x ∷ xs) (y ∷ ys) eq = cong (y ∷_) (zip-proj₂ xs ys (NatP.suc-injective eq))

_\\_ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) → List A
[] \\ ys = []
(x ∷ xs) \\ ys
  with x ∈? ys
… | yes x∈ys = xs \\ ys
… | no ¬x∈ys = x ∷ (xs \\ ys) 

∈-\\⁺ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {xs ys : List A} {x} →
  x ∈ xs →
  x ∉ ys →
  x ∈ (xs \\ ys)
∈-\\⁺ {xs = xs} {ys} {x} (here refl) x∉ys
  with x ∈? ys 
… | yes x∈ys = ⊥-elim (x∉ys x∈ys)
… | no ¬x∈ys = here refl
∈-\\⁺ {xs = xs} {ys} {x} (there {x = x'} x∈xs) x∉ys
  with x' ∈? ys 
… | yes x'∈ys = ∈-\\⁺ x∈xs x∉ys
… | no ¬x'∈ys = there (∈-\\⁺ x∈xs x∉ys)

∈-\\⁻ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ (xs ys : List A) {x} →
  x ∈ (xs \\ ys) →
  x ∈ xs × x ∉ ys
∈-\\⁻ (x' ∷ xs) ys {x} x∈xs\\ys
  with x' ∈? ys 
… | yes x'∈ys = map₁ there (∈-\\⁻ xs ys x∈xs\\ys)
… | no ¬x'∈ys
  with x∈xs\\ys
… | here refl = here refl , ¬x'∈ys
… | there x∈xs\\ys = map₁ there (∈-\\⁻ xs ys x∈xs\\ys)

map-proj₁ : ∀ {ℓ₁ ℓ₂ ℓ} {A₁ : Set ℓ₁} {A₂ : Set ℓ₂} {B : Set ℓ}
              (f : A₁ → A₂) (xs : List (A₁ × B)) →
  L.map proj₁ (L.map (map₁ f) xs) ≡ L.map f (L.map proj₁ xs)
map-proj₁ f xs =
  let open ≡-Reasoning in
  begin
    L.map proj₁ (L.map (map₁ f) xs)
  ≡⟨ sym (ListP.map-∘ xs) ⟩
    L.map (proj₁ ∘ map₁ f) xs
  ≡⟨⟩
    L.map (f ∘ proj₁) xs
  ≡⟨ ListP.map-∘ xs ⟩
    L.map f (L.map proj₁ xs)
  ∎


