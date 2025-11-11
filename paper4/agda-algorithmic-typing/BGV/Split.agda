module BGV.Split where

import Data.List.Properties as ListP
import Data.List.Relation.Unary.Any.Properties as AnyP
import Data.Nat.Properties as NatP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_; case_of_) renaming (_∋_ to _by_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open import BGV.Context
open import BGV.Expressions
open import BGV.Id
open import BGV.Ren
open import BGV.UsageMap
open import BGV.Types
open import BGV.Util.Decidable
open import BGV.Util.List
open import BGV.Util.Map as Map using (Map)

-- Definitions -----------------------------------------------------------------

_·ʳᶜ_ : Ren → UsageMap → UsageMap
(ρ ·ʳᶜ u) x = u (ρ x)

-- ↓ᵘ --------------------------------------------------------------------------

_↓ᵘ_ : List Id → UsageMap → List (Id × SessionB)
[] ↓ᵘ u = []
(x ∷ xs) ↓ᵘ u
  with u x
… | none                = xs ↓ᵘ u
… | some (owned , s)    = xs ↓ᵘ u
… | some (borrowed , s) = (x , s) ∷ (xs ↓ᵘ u)

↓ᵘ-∈⁻ : ∀ {x s} xs u →
  (x , s) ∈ xs ↓ᵘ u →
  x ∈ xs × u x ≡ some (_ , s)
↓ᵘ-∈⁻ (x ∷ xs) u p
  with u x in eq
… | none                = map₁ there (↓ᵘ-∈⁻ xs u p)
… | some (owned , s)    = map₁ there (↓ᵘ-∈⁻ xs u p)
… | some (borrowed , s)
  with p
… | here refl           = here refl , eq
… | there p'            = map₁ there (↓ᵘ-∈⁻ xs u p')

↓ᵘ-∈⁺ : ∀ {x s} xs u →
  x ∈ xs →
  u x ≡ some (_ , s) →
  (x , s) ∈ xs ↓ᵘ u
↓ᵘ-∈⁺ (y ∷ xs) u (here refl) eq rewrite eq = here refl
↓ᵘ-∈⁺ (y ∷ xs) u (there x∈xs) eq
  with u y
… | none                = ↓ᵘ-∈⁺ xs u x∈xs eq
… | some (owned , s)    = ↓ᵘ-∈⁺ xs u x∈xs eq
… | some (borrowed , s) = there (↓ᵘ-∈⁺ xs u x∈xs eq)

↓ᵘ-⊆ : ∀ xs u →
  map proj₁ (xs ↓ᵘ u) ⊆ xs
↓ᵘ-⊆ xs u x∈ =
  let (y , y∈xs↓u , y₁≡x) = map-∈-inv proj₁ (xs ↓ᵘ u) x∈ in
  let (y∈xs , _) = ↓ᵘ-∈⁻ xs u y∈xs↓u in
  subst (_∈ xs) y₁≡x y∈xs

_⋯ˢⁱ_ : List (Id × SessionB) → Ren → List (Id × SessionB)
xs ⋯ˢⁱ ρ = map (map₁ ρ) xs

↓ᵘ-pres-Unique : ∀ xs u →
  Unique xs →
  Unique (map proj₁ (xs ↓ᵘ u))
↓ᵘ-pres-Unique (x ∷ xs) u U-xs y y∈↓ y∈↓'
  with u x
… | none                = ↓ᵘ-pres-Unique xs u (Unique-tail U-xs) y y∈↓ y∈↓'
… | some (owned , s)    = ↓ᵘ-pres-Unique xs u (Unique-tail U-xs) y y∈↓ y∈↓'
… | some (borrowed , s)
  with y∈↓ | y∈↓'
… | here refl | here refl  = refl
… | here refl | there y∈↓' = let s₁ , y,s₁∈xs↓u = Map.∈dom→∈ (xs ↓ᵘ u) y∈↓' in
                             let x∈xs , _ = ↓ᵘ-∈⁻ xs u y,s₁∈xs↓u in
                             ⊥-elim (Unique-∈-∷ x _ U-xs x∈xs)
… | there y∈↓ | here refl  = let s₁ , y,s₁∈xs↓u = Map.∈dom→∈ (xs ↓ᵘ u) y∈↓ in
                             let x∈xs , _ = ↓ᵘ-∈⁻ xs u y,s₁∈xs↓u in
                             ⊥-elim (Unique-∈-∷ x _ U-xs x∈xs)
… | there y∈↓ | there y∈↓' = cong there (↓ᵘ-pres-Unique xs u (Unique-tail U-xs) y y∈↓ y∈↓')

-- freshs ----------------------------------------------------------------------

freshs : ℕ → List Id → List Id
freshs zero xs = []
freshs (suc n) xs = fresh (freshs n xs ++ xs) ∷ freshs n xs

freshs-disjoint : ∀ n xs →
  Disjoint (freshs n xs) xs
freshs-disjoint zero xs =
  Disjoint-[]₁
freshs-disjoint (suc n) xs =
  Disjoint-∷₁ (⊆-∉ (⊆-++₂' _) (fresh-∉ (freshs n xs ++ xs)))
              (freshs-disjoint n xs)

freshs-unique : ∀ n xs →
  Unique (freshs n xs)
freshs-unique zero xs =
  Unique-[]
freshs-unique (suc n) xs =
  Unique-∷ (⊆-∉ ⊆-++₁' (fresh-∉ (freshs n xs ++ xs)))
           (freshs-unique n xs)

freshs-length : ∀ n xs → List.length (freshs n xs) ≡ n
freshs-length zero    xs = refl
freshs-length (suc n) xs = cong suc (freshs-length n xs)

-- list-to-ren -----------------------------------------------------------------

list-to-ren : List (Id × Id) → Ren
list-to-ren [] = idʳ
list-to-ren ((x , y) ∷ xs) = (x , y) ∷ᶠ list-to-ren xs

list-to-ren-cod : ∀ g →
  Unique (map proj₁ g) → 
  codʳ (map proj₁ g) (list-to-ren g) ≡ map proj₂ g
list-to-ren-cod [] U-dom = refl
list-to-ren-cod ((x , y) ∷ g) U-dom rewrite ≟-yes x =
  cong (y ∷_) (trans
    (map-∷ᶠ-∉ x y (list-to-ren g) (map proj₁ g) (Unique-∈-∷ x _ U-dom))
    (list-to-ren-cod g (Unique-tail U-dom)))

list-to-ren-unique : ∀ g →
  Unique (map proj₁ g) → 
  Unique (map proj₂ g) →
  Unique (codʳ (map proj₁ g) (list-to-ren g))
list-to-ren-unique g U-dom U-cod =
  subst Unique (sym (list-to-ren-cod g U-dom)) U-cod

list-to-ren-disjoint : ∀ g ys →
  Unique (map proj₁ g) → 
  Disjoint (map proj₂ g) ys →
  Disjoint (codʳ (map proj₁ g) (list-to-ren g)) ys
list-to-ren-disjoint g ys U-dom d =
  subst (λ ■ → Disjoint ■ ys) (sym (list-to-ren-cod g U-dom)) d

list-to-ren-id : ∀ x g →
  x ∉ map proj₁ g →
  list-to-ren g x ≡ x
list-to-ren-id x []      x∉g₁ = refl
list-to-ren-id x ((x' , y) ∷ g) x∉g₁ with x' ≟ x
… | yes x'≡x = ⊥-elim (x∉g₁ (here (sym x'≡x)))
… | no ¬x'≡x = list-to-ren-id x g (∉-tail x∉g₁)

--------------------------------------------------------------------------------

fresh-pairs : List Id → List Id → List (Id × Id)
fresh-pairs xs ys = List.zip xs (freshs (List.length xs) ys)

fresh-pairs-map₁ : ∀ xs ys →
  map proj₁ (fresh-pairs xs ys) ≡ xs
fresh-pairs-map₁ xs ys = zip-proj₁ xs _ (sym (freshs-length _ ys))

fresh-pairs-map₂ : ∀ xs ys →
  map proj₂ (fresh-pairs xs ys) ≡ freshs (List.length xs) ys
fresh-pairs-map₂ xs ys = zip-proj₂ xs _ (sym (freshs-length _ ys))

fresh-pairs-disjoint : ∀ xs ys →
  Disjoint (map proj₂ (fresh-pairs xs ys)) ys
fresh-pairs-disjoint xs ys =
  subst (λ ■ → Disjoint ■ ys)
        (sym (fresh-pairs-map₂ xs ys))
        (freshs-disjoint (List.length xs) ys)

fresh-pairs-unique : ∀ xs ys →
  Unique (map proj₂ (fresh-pairs xs ys))
fresh-pairs-unique xs ys =
  subst Unique
        (sym (fresh-pairs-map₂ xs ys))
        (freshs-unique (List.length xs) ys)

-- fresh-pairs-∈⁻ : ∀ {x y} xs ys →
--   (x , y) ∈ fresh-pairs xs ys →
--   x ∈ xs × y ∈ freshs (List.length xs) ys
-- fresh-pairs-∈⁻ xs ys p = {!!}

--------------------------------------------------------------------------------

split-ren-graphs : List Id → List Id → List (Id × Id) × List (Id × Id)
split-ren-graphs xs ys =
  let g₁ = fresh-pairs xs ys in
  let g₂ = fresh-pairs xs (map proj₂ g₁ ++ ys) in
  g₁ , g₂

split-ren-graphs-disjoint : ∀ xs ys →
  let (g₁ , g₂) = split-ren-graphs xs ys in
  Disjoint (map proj₂ g₁ ++ map proj₂ g₂) ys
split-ren-graphs-disjoint xs ys =
  let g₁ = fresh-pairs xs ys in
  let g₂ = fresh-pairs xs (map proj₂ g₁ ++ ys) in
  let d₁ = fresh-pairs-disjoint xs ys in
  let d₂ = fresh-pairs-disjoint xs (map proj₂ g₁ ++ ys) in
  Disjoint-++₁ d₁ (Disjoint-⊆₂ (⊆-++₂' _) d₂)

split-ren-graphs-unique : ∀ xs ys →
  let (g₁ , g₂) = split-ren-graphs xs ys in
  Unique (map proj₂ g₁ ++ map proj₂ g₂)
split-ren-graphs-unique xs ys =
  let g₁ = fresh-pairs xs ys in
  let g₂ = fresh-pairs xs (map proj₂ g₁ ++ ys) in
  let u₁ = fresh-pairs-unique xs ys in
  let u₂ = fresh-pairs-unique xs (map proj₂ g₁ ++ ys) in
  let d₂ = fresh-pairs-disjoint xs (map proj₂ g₁ ++ ys) in
  Unique-++ u₁ u₂ (Disjoint-sym (Disjoint-⊆₂ ⊆-++₁' d₂))

-- split-rens-id : ∀ xs ys →
--   z ∉ xs →
--   let (g₁ , g₂) = split-ren-graphs xs ys in
--   ρ₁ z ≡ z × ρ₂ z ≡ z
-- split-rens-id xs ys z∉xs = {!!}

-- split-ren-graphs-injective : ∀ xs ys →
--   let (ρ₁ , ρ₂) = split-ren-graphs xs ys in
--   Injectiveʳ ys ρ₁ × Injectiveʳ ys ρ₁
-- split-ren-graphs-injective xs ys = {!!}

-- split-rens ------------------------------------------------------------------

split-rens : List Id → List Id → Ren × Ren
split-rens xs ys = map₁₂ list-to-ren list-to-ren (split-ren-graphs xs ys)

split-ren₁ : List Id → List Id → Ren
split-ren₁ xs ys = proj₁ (split-rens xs ys)

split-ren₂ : List Id → List Id → Ren
split-ren₂ xs ys = proj₂ (split-rens xs ys)

split-rens-disjoint : ∀ xs ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  Disjoint (codʳ xs ρ₁ ++ codʳ xs ρ₂) ys
split-rens-disjoint xs ys U-xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let d = split-ren-graphs-disjoint xs ys in
  let d₁ = Disjoint-⊆₁ ⊆-++₁' d in
  let d₂ = Disjoint-⊆₁ (⊆-++₂' _) d in
  let U-dom-g₁ = subst Unique (sym (fresh-pairs-map₁ xs ys)) U-xs in
  let U-dom-g₂ = subst Unique (sym (fresh-pairs-map₁ xs (map proj₂ g₁ ++ ys))) U-xs in
  let d₁' = list-to-ren-disjoint g₁ _ U-dom-g₁ d₁ in
  let d₂' = list-to-ren-disjoint g₂ _ U-dom-g₂ d₂ in
  let d₁'' = subst (λ ■ → Disjoint (codʳ ■ (list-to-ren g₁)) ys) (fresh-pairs-map₁ xs ys) d₁' in 
  let d₂'' = subst (λ ■ → Disjoint (codʳ ■ (proj₂ (split-rens xs ys))) ys) (fresh-pairs-map₁ xs _) d₂' in 
  Disjoint-++₁ d₁'' d₂''

split-rens-unique : ∀ xs ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  Unique (codʳ xs ρ₁ ++ codʳ xs ρ₂)
split-rens-unique xs ys U-xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let u = split-ren-graphs-unique xs ys in
  let (u₁ , u₂ , d) = Unique-++⁻ (map proj₂ g₁) (map proj₂ g₂) u in
  let U-dom-g₁ = subst Unique (sym (fresh-pairs-map₁ xs ys)) U-xs in
  let U-dom-g₂ = subst Unique (sym (fresh-pairs-map₁ xs (map proj₂ g₁ ++ ys))) U-xs in
  let u₁' = list-to-ren-unique g₁ U-dom-g₁ u₁ in
  let u₂' = list-to-ren-unique g₂ U-dom-g₂ u₂ in
  let u₁'' = subst (λ ■ → Unique (codʳ ■ (list-to-ren g₁))) (fresh-pairs-map₁ xs ys) u₁' in
  let u₂'' = subst (λ ■ → Unique (codʳ ■ (proj₂ (split-rens xs ys)))) (fresh-pairs-map₁ xs _) u₂' in 
  let d' = subst₂ Disjoint
                  (trans (sym (list-to-ren-cod g₁ U-dom-g₁)) (cong (λ ■ → codʳ ■ (list-to-ren g₁)) (fresh-pairs-map₁ xs ys)))
                  (trans (sym (list-to-ren-cod g₂ U-dom-g₂)) (cong (λ ■ → codʳ ■ (proj₂ (split-rens xs ys))) (fresh-pairs-map₁ xs _)))
                  d in
  Unique-++ {xs = codʳ xs (split-rens xs ys .proj₁)} u₁'' u₂'' d'

split-rens-id : ∀ xs ys →
  z ∉ xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  ρ₁ z ≡ z × ρ₂ z ≡ z
split-rens-id {z = z} xs ys z∉xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  list-to-ren-id z g₁ (subst (z ∉_) (sym (fresh-pairs-map₁ xs ys)) z∉xs) ,
  list-to-ren-id z g₂ (subst (z ∉_) (sym (fresh-pairs-map₁ xs _)) z∉xs)

split-rens-injective' : ∀ xs ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  Injectiveʳ xs ρ₁ × Injectiveʳ xs ρ₂
split-rens-injective' xs ys U-xs =
  let (ρ₁ , ρ₂) = split-rens xs ys in
  let u = split-rens-unique xs ys U-xs in
  Unique-cod→Injectiveʳ xs ρ₁ (Unique-⊆ ⊆ⁱ-++₁ u) ,
  Unique-cod→Injectiveʳ xs ρ₂ (Unique-⊆ ⊆ⁱ-++₂ u)

split-rens-injective₁ : ∀ xs ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  Injectiveʳ ys ρ₁
split-rens-injective₁ xs ys U-xs x y x∈ys y∈ys ρ₁x≡ρ₁y
  with x ∈? xs | y ∈? xs
… | yes x∈xs | yes y∈xs =
  proj₁ (split-rens-injective' xs ys U-xs) x y x∈xs y∈xs ρ₁x≡ρ₁y
… | yes x∈xs | no ¬y∈xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let ρ₁ = list-to-ren g₁ in
  let ρ₁y≡y = list-to-ren-id y g₁ (subst (y ∉_) (sym (fresh-pairs-map₁ xs ys)) ¬y∈xs) in
  let ρ₁x≡y = trans ρ₁x≡ρ₁y ρ₁y≡y in
  let d : Disjoint (codʳ xs ρ₁) ys
      d = Disjoint-⊆₁ ⊆-++₁' (split-rens-disjoint xs ys U-xs) in
  ⊥-elim (d (ρ₁ x) (∈dom→∈cod ρ₁ x∈xs) (subst (_∈ ys) (sym ρ₁x≡y) y∈ys))
… | no ¬x∈xs | yes y∈xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let ρ₁ = list-to-ren g₁ in
  let ρ₁x≡x = list-to-ren-id x g₁ (subst (x ∉_) (sym (fresh-pairs-map₁ xs ys)) ¬x∈xs) in
  let ρ₁y≡x = trans (sym ρ₁x≡ρ₁y) ρ₁x≡x in
  let d : Disjoint (codʳ xs ρ₁) ys
      d = Disjoint-⊆₁ ⊆-++₁' (split-rens-disjoint xs ys U-xs) in
  ⊥-elim (d (ρ₁ y) (∈dom→∈cod ρ₁ y∈xs) (subst (_∈ ys) (sym ρ₁y≡x) x∈ys))
… | no ¬x∈xs | no ¬y∈xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let open ≡-Reasoning in
  begin
    x
  ≡⟨ sym (list-to-ren-id x g₁ (subst (x ∉_) (sym (fresh-pairs-map₁ xs ys)) ¬x∈xs)) ⟩
    list-to-ren g₁ x
  ≡⟨ ρ₁x≡ρ₁y ⟩
    list-to-ren g₁ y
  ≡⟨ list-to-ren-id y g₁ (subst (y ∉_) (sym (fresh-pairs-map₁ xs ys)) ¬y∈xs) ⟩
    y
  ∎

split-rens-injective₂ : ∀ xs ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  Injectiveʳ ys ρ₂
split-rens-injective₂ xs ys U-xs x y x∈ys y∈ys ρ₂x≡ρ₂y
  with x ∈? xs | y ∈? xs
… | yes x∈xs | yes y∈xs =
  proj₂ (split-rens-injective' xs ys U-xs) x y x∈xs y∈xs ρ₂x≡ρ₂y
… | yes x∈xs | no ¬y∈xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let ρ₂ = list-to-ren g₂ in
  let ρ₂y≡y = list-to-ren-id y g₂ (subst (y ∉_) (sym (fresh-pairs-map₁ xs _)) ¬y∈xs) in
  let ρ₂x≡y = trans ρ₂x≡ρ₂y ρ₂y≡y in
  let d : Disjoint (codʳ xs ρ₂) ys
      d = Disjoint-⊆₁ (⊆-++₂' _) (split-rens-disjoint xs ys U-xs) in
  ⊥-elim (d (ρ₂ x) (∈dom→∈cod ρ₂ x∈xs) (subst (_∈ ys) (sym ρ₂x≡y) y∈ys))
… | no ¬x∈xs | yes y∈xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let ρ₂ = list-to-ren g₂ in
  let ρ₂x≡x = list-to-ren-id x g₂ (subst (x ∉_) (sym (fresh-pairs-map₁ xs _)) ¬x∈xs) in
  let ρ₂y≡x = trans (sym ρ₂x≡ρ₂y) ρ₂x≡x in
  let d : Disjoint (codʳ xs ρ₂) ys
      d = Disjoint-⊆₁ (⊆-++₂' _) (split-rens-disjoint xs ys U-xs) in
  ⊥-elim (d (ρ₂ y) (∈dom→∈cod ρ₂ y∈xs) (subst (_∈ ys) (sym ρ₂y≡x) x∈ys))
… | no ¬x∈xs | no ¬y∈xs =
  let (g₁ , g₂) = split-ren-graphs xs ys in
  let open ≡-Reasoning in
  begin
    x
  ≡⟨ sym (list-to-ren-id x g₂ (subst (x ∉_) (sym (fresh-pairs-map₁ xs _)) ¬x∈xs)) ⟩
    list-to-ren g₂ x
  ≡⟨ ρ₂x≡ρ₂y ⟩
    list-to-ren g₂ y
  ≡⟨ list-to-ren-id y g₂ (subst (y ∉_) (sym (fresh-pairs-map₁ xs _)) ¬y∈xs) ⟩
    y
  ∎

split-rens-injective : ∀ xs ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  Injectiveʳ ys ρ₁ × Injectiveʳ ys ρ₂
split-rens-injective xs ys U-xs =
  let (ρ₁ , ρ₂) = split-rens xs ys in
  let u = split-rens-unique xs ys U-xs in
  split-rens-injective₁ xs ys U-xs , 
  split-rens-injective₂ xs ys U-xs

⊢ʳ-split-rens₁ : ∀ xs ys → 
  xs ⊆ ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  ys % xs ⊢ʳ ρ₁
⊢ʳ-split-rens₁ xs ys xs⊆ys U-xs = record
  { ⊢ʳ-∉xs-id   = λ x∉xs → list-to-ren-id _ (proj₁ (split-ren-graphs xs ys))
                             (subst (_ ∉_) (sym (fresh-pairs-map₁ xs ys)) x∉xs)
  ; ⊢ʳ-ρxs⊎ys   = Disjoint-⊆₁ ⊆-++₁' (split-rens-disjoint xs ys U-xs)
  ; ⊢ʳ-inj-ys-ρ = split-rens-injective₁ xs ys U-xs
  ; ⊢ʳ-xs⊆ys    = xs⊆ys
  }

⊢ʳ-split-rens₂ : ∀ xs ys → 
  xs ⊆ ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  ys % xs ⊢ʳ ρ₂
⊢ʳ-split-rens₂ xs ys xs⊆ys U-xs = record
  { ⊢ʳ-∉xs-id   = λ x∉xs → list-to-ren-id _ (proj₂ (split-ren-graphs xs ys))
                             (subst (_ ∉_) (sym (fresh-pairs-map₁ xs _)) x∉xs)
  ; ⊢ʳ-ρxs⊎ys   = Disjoint-⊆₁ (⊆-++₂' _) (split-rens-disjoint xs ys U-xs)
  ; ⊢ʳ-inj-ys-ρ = split-rens-injective₂ xs ys U-xs
  ; ⊢ʳ-xs⊆ys    = xs⊆ys
  }

⊢ʳ-split-rens : ∀ xs ys → 
  xs ⊆ ys →
  Unique xs →
  let (ρ₁ , ρ₂) = split-rens xs ys in
  ys % xs ⊢ʳ ρ₁ ×
  ys % xs ⊢ʳ ρ₂ ×
  Disjoint (codʳ xs ρ₁ ++ codʳ xs ρ₂) ys
⊢ʳ-split-rens xs ys xs⊆ys U-xs =
  ⊢ʳ-split-rens₁ xs ys xs⊆ys U-xs ,
  ⊢ʳ-split-rens₂ xs ys xs⊆ys U-xs ,
  split-rens-disjoint xs ys U-xs

Injectiveʳ-· : ∀ xs ρ₁ ρ₂ →
  Injectiveʳ xs ρ₁ →
  Injectiveʳ (map ρ₁ xs) ρ₂ →
  Injectiveʳ xs (ρ₁ ·ʳ ρ₂)
Injectiveʳ-· xs ρ₁ ρ₂ inj-ρ₁ inj-ρ₂ x y x∈xs y∈xs ρ₂ρ₁x≡ρ₂ρ₁y =
  let ρ₁x≡ρ₁y = inj-ρ₂ (ρ₁ x) (ρ₁ y) (∈-map ρ₁ x∈xs) (∈-map ρ₁ y∈xs) ρ₂ρ₁x≡ρ₂ρ₁y in
  inj-ρ₁ x y x∈xs y∈xs ρ₁x≡ρ₁y

-- -- Lemmas about split-ren

-- split-ren-cod : ∀ xs u ys →
--   Map.lookup x (split-infos xs u ys) ≡ some (x₁ , x₂ , s₁) →
--   let (ρ₁ , ρ₂) = split-rens (split-infos xs u ys) in
--   x₁ ∈ codʳ xs ρ₁ × x₂ ∈ codʳ xs ρ₂ 
-- split-ren-cod {x = x} {x₁ = x₁} {x₂ = x₂} (x' ∷ xs) u ys eq
--   with u x'
-- … | none = map₁₂ there there (split-ren-cod xs u ys eq)
-- … | some (owned , s₁') = map₁₂ there there (split-ren-cod xs u ys eq)
-- … | some (borrowed , s₁')
--   with x ≟ x'
-- … | yes refl with refl ← eq rewrite ≟-yes x' = here refl , here refl
-- … | no ¬x≡x' rewrite ≟-yes x' =
--   let (ρ₁ , ρ₂) = split-rens (split-infos xs u (fresh (fresh ys ∷ ys) ∷ fresh ys ∷ ys)) in
--   let (p , q) = split-ren-cod xs u _ eq in
--   subst (_∈ _) {!!} (there (subst (_ ∈_) {!ListP.map-∘ {g = (x₁ , fresh ys) ∷ᶠ_} {f = ρ₁}!} (∈-map {!!} p))) , {!!}

-- splitsₙ ---------------------------------------------------------------------

splitsₙ : List (Id × SessionB) → Ren → Ren → (Expr log → Expr log) 
splitsₙ [] ρ₁ ρ₂ e =
  e
splitsₙ ((x , s) ∷ xs) ρ₁ ρ₂ e =
  let[ ρ₁ x `, ρ₂ x ≔ split[ s ] (` x) ]in splitsₙ xs ρ₁ ρ₂ e

-- split-ctx -------------------------------------------------------------------

split-bind : List (Id × SessionB) → Ren → Ren → Id → Type → Ctx
split-bind xs ρ₁ ρ₂ x t
 with Chan? t
… | no _ = x ∶ t
… | yes (b , s , refl)
 with Map.lookup x xs
… | none = x ∶ t
… | some s₁
 with s % s₁
… | none = x ∶ t
… | some s₂ = (ρ₁ x ∶ Chan _ s₁) ⸴ (ρ₂ x ∶ Chan _ s₂)

split-ctx : List (Id × SessionB) → Ren → Ren → Ctx → Ctx
split-ctx xs ρ₁ ρ₂ Γ = Γ >>=ᶜ split-bind xs ρ₁ ρ₂

split-ctx-ctx : List (Id × SessionB) → Ren → Ren → CtxPat → CtxPat
split-ctx-ctx xs ρ₁ ρ₂ C = C >>=ᶜᶜ split-bind xs ρ₁ ρ₂

split-bind-[] : ∀ x t {ρ₁ ρ₂} →
  split-bind [] ρ₁ ρ₂ x t ≡ x ∶ t
split-bind-[] x t
  with Chan? t
… | no _ = refl
… | yes (b , s , refl) = refl

split-ctx-[] : ∀ Γ {ρ₁ ρ₂} →
  split-ctx [] ρ₁ ρ₂ Γ ≡ Γ

split-ctx-[] ·              = refl
split-ctx-[] (x ∶ t)        = split-bind-[] x t
split-ctx-[] (Γ₁ ⸴[ o ] Γ₂) = (cong₂ (_⸴[ o ]_)) (split-ctx-[] Γ₁) (split-ctx-[] Γ₂)

Disjoint-dom-split : ∀ Γ₁ o Γ₂ →
  Disjoint xs (dom (Γ₁ ⸴[ o ] Γ₂)) →
  Disjoint xs (dom Γ₁) × Disjoint xs (dom Γ₂)
Disjoint-dom-split {xs = xs} Γ₁ o Γ₂ d =
  let sub = subst (Disjoint xs) (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) in
  Disjoint-⊆₂ ⊆-++₁' (sub d) ,
  Disjoint-⊆₂ (⊆-++₂' _) (sub d)

Unique-dom-split : ∀ Γ₁ o Γ₂ →
  Unique (dom (Γ₁ ⸴[ o ] Γ₂)) →
  Unique (dom Γ₁) × Unique (dom Γ₂) × Disjoint (dom Γ₁) (dom Γ₂)
Unique-dom-split Γ₁ o Γ₂ d =
  let sub = subst Unique (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) in
  Unique-++⁻ (dom Γ₁) (dom Γ₂) (sub d) 

split-bind-Disjoint : ∀ sis x t {ρ₁ ρ₂} →
  Disjoint (Map.dom sis) (dom (x ∶ t)) →
  split-bind sis ρ₁ ρ₂ x t ≡ x ∶ t
split-bind-Disjoint sis x t {ρ₁} {ρ₂} d
  with Chan? t
… | no ¬Chan-t = refl
… | yes (b , s , refl)
  with x ∈? map proj₁ sis
… | yes x∈dom = ⊥-elim (d x x∈dom (here refl))
… | no ¬x∈dom rewrite Map.lookup-∉ sis ¬x∈dom = refl

split-ctx-Disjoint : ∀ sis Γ {ρ₁ ρ₂} →
  Disjoint (Map.dom sis) (dom Γ) →
  split-ctx sis ρ₁ ρ₂ Γ ≡ Γ
split-ctx-Disjoint sis · d = refl
split-ctx-Disjoint sis (x ∶ t) d = split-bind-Disjoint sis x t d
split-ctx-Disjoint sis (Γ₁ ⸴[ o ] Γ₂) d =
  let (d₁ , d₂) = Disjoint-dom-split Γ₁ o Γ₂ d in
  cong₂ (_⸴[ o ]_) (split-ctx-Disjoint sis Γ₁ d₁)
                   (split-ctx-Disjoint sis Γ₂ d₂)

split-ctx-∈ : ∀ {b} ρ₁ ρ₂ x s₁ (s₂ : Session b) Γ C →
  Unique (dom Γ) →
  Γ ≡ C [ x ∶ Chan b (s₁ ++ˢ s₂) ] →
  split-ctx ((x , s₁) ∷ []) ρ₁ ρ₂ Γ ≡ C [ (ρ₁ x ∶ Chan _ s₁) ⸴ (ρ₂ x ∶ Chan _ s₂) ]
split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ _ []           U-Γ refl
 with x ≟ x
… | no ¬x≡x = ⊥-elim (¬x≡x refl)
… | yes x≡x
 with (s₁ ++ˢ s₂) %? s₁
… | no p = ⊥-elim (p (_ , refl))
… | yes (_ , eq) rewrite ++ˢ-injective₂ s₁ eq = refl
split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ _ (C ⸴[ o ]₁ Γ) U-Γ refl =
  let (U-Γ₁ , U-Γ₂ , D-Γ₁-Γ₂) = Unique-dom-split (C [ x ∶ Chan _ (s₁ ++ˢ s₂) ]) o Γ U-Γ in
  let x∈C[x] = C[]-pres-∈dom C (x ∶ Chan _ (s₁ ++ˢ s₂)) (here refl) in
  let D-x-Γ₂ = Disjoint-⊆₁ (λ { (here refl) → x∈C[x] }) D-Γ₁-Γ₂ in 
  cong₂ (_⸴[ o ]_)
        (split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ _ C U-Γ₁ refl)
        (split-ctx-Disjoint ((x , s₁) ∷ []) Γ D-x-Γ₂)
split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ _ (Γ ⸴[ o ]₂ C) U-Γ refl =
  let (U-Γ₁ , U-Γ₂ , D-Γ₁-Γ₂) = Unique-dom-split Γ o (C [ x ∶ Chan _ (s₁ ++ˢ s₂) ]) U-Γ in
  let x∈C[x] = C[]-pres-∈dom C (x ∶ Chan _ (s₁ ++ˢ s₂)) (here refl) in
  let D-Γ₁-x = Disjoint-⊆₂ (λ { (here refl) → x∈C[x] }) D-Γ₁-Γ₂ in 
  cong₂ (_⸴[ o ]_)
        (split-ctx-Disjoint ((x , s₁) ∷ []) Γ (Disjoint-sym D-Γ₁-x))
        (split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ _ C U-Γ₂ refl)

split-bind-∈' : ∀ x t sis ρ₁ ρ₂ →
  x ∉ map proj₁ sis → 
  (x , t) ∈ binds (split-bind sis ρ₁ ρ₂ x t)
split-bind-∈' x t sis ρ₁ ρ₂ x∉sis
 with Chan? t
… | no _  = here refl
… | yes (b , s , refl) rewrite Map.lookup-∉ sis x∉sis = here refl

split-ctx-∈' : ∀ Γ sis ρ₁ ρ₂ →
  x ∉ map proj₁ sis → 
  (x , t) ∈ binds Γ →
  (x , t) ∈ binds (split-ctx sis ρ₁ ρ₂ Γ)
split-ctx-∈' (x ∶ t) sis ρ₁ ρ₂ x∉sis (here refl) = split-bind-∈' x t sis ρ₁ ρ₂ x∉sis
split-ctx-∈' (Γ₁ ⸴[ o ] Γ₂) sis ρ₁ ρ₂ x∉sis xt∈Γ with AnyP.++⁻ (binds Γ₁) xt∈Γ
… | inj₁ xt∈Γ₁ = AnyP.++⁺ˡ (split-ctx-∈' Γ₁ sis ρ₁ ρ₂ x∉sis xt∈Γ₁)
… | inj₂ xt∈Γ₂ = AnyP.++⁺ʳ _ (split-ctx-∈' Γ₂ sis ρ₁ ρ₂ x∉sis xt∈Γ₂)

UniqueVars : List (Id × SessionB) → Ren → Ren → Set
UniqueVars sis ρ₁ ρ₂ = 
  let xs = map proj₁ sis in
  Unique (xs ++ map ρ₁ xs ++ map ρ₂ xs)

split-bind-++ : ∀ sis₁ sis₂ ρ₁ ρ₂ x t →
  UniqueVars (sis₁ ++ sis₂) ρ₁ ρ₂ →
  split-bind (sis₁ ++ sis₂) ρ₁ ρ₂ x t ≡ split-ctx sis₂ ρ₁ ρ₂ (split-bind sis₁ ρ₁ ρ₂ x t)
split-bind-++ sis₁ sis₂ ρ₁ ρ₂ x t u with Chan? t in eq-chan
… | no ¬chan rewrite eq-chan = refl
… | yes (b , s , refl)
  with Map.lookup x (sis₁ ++ sis₂) in eql
… | none with (eql₁ , eql₂) ← Map.lookup-++⁻-none x sis₁ sis₂ eql
         rewrite eql₁ | eql₂ = refl
… | some s₁
  using x∈dom ← ∈-map proj₁ (Map.lookup-some→∈ (sis₁ ++ sis₂) eql)
  using x∈dom' ← subst (x ∈_) (ListP.map-++ proj₁ sis₁ sis₂) x∈dom 
  using u₁₂ ← subst Unique (ListP.map-++ proj₁ sis₁ sis₂) (Unique-⊆ ⊆ⁱ-++₁ u)
  using (_u₁ , _u₂ , d₁₂) ← Unique-++⁻ (map proj₁ sis₁) (map proj₁ sis₂) u₁₂ 
  with Map.lookup-++⁻-some-disjoint x sis₁ sis₂ s₁ d₁₂ eql
split-bind-++ sis₁ sis₂ ρ₁ ρ₂ x t u | yes (b , s , refl) | some s₁ | inj₂ (eql₁ , eql₂) rewrite eql₁ | eql₂
  with s % s₁ in eq%
… | none = refl
… | some s₂ = refl
split-bind-++ sis₁ sis₂ ρ₁ ρ₂ x t u | yes (b , s , refl) | some s₁ | inj₁ (eql₁ , eql₂) rewrite eql₁ | eql₂
  with Map.lookup (ρ₁ x) sis₂ in eqlρ₁ | Map.lookup (ρ₂ x) sis₂ in eqlρ₂
… | some _ | _      =
  let ρ₁x∈ρ₁dom = ∈-map ρ₁ x∈dom in
  let ρ₁x∈dom₁ = ∈-map proj₁ (Map.lookup-some→∈ sis₂ eqlρ₁) in
  let ρ₁x∈dom = subst (ρ₁ x ∈_) (sym (ListP.map-++ proj₁ sis₁ sis₂)) (AnyP.++⁺ʳ _ ρ₁x∈dom₁) in
  ⊥-elim (Unique-∈-++₁ (map proj₁ (sis₁ ++ sis₂)) _ u ρ₁x∈dom (AnyP.++⁺ˡ ρ₁x∈ρ₁dom))
… | _      | some _ =
  let ρ₂x∈ρ₂dom = ∈-map ρ₂ x∈dom in
  let ρ₂x∈dom₁ = ∈-map proj₁ (Map.lookup-some→∈ sis₂ eqlρ₂) in
  let ρ₂x∈dom = subst (ρ₂ x ∈_) (sym (ListP.map-++ proj₁ sis₁ sis₂)) (AnyP.++⁺ʳ _ ρ₂x∈dom₁) in
  ⊥-elim (Unique-∈-++₁ (map proj₁ (sis₁ ++ sis₂)) _ u ρ₂x∈dom (AnyP.++⁺ʳ _ ρ₂x∈ρ₂dom))
… | none   | none   
  with s % s₁ in eq%
… | none rewrite eql₂ = refl
… | some s₂ rewrite eqlρ₁ | eqlρ₂ = refl

split-ctx-++ : ∀ sis₁ sis₂ ρ₁ ρ₂ Γ →
  UniqueVars (sis₁ ++ sis₂) ρ₁ ρ₂ →
  split-ctx (sis₁ ++ sis₂) ρ₁ ρ₂ Γ ≡ (split-ctx sis₂ ρ₁ ρ₂ ∘ split-ctx sis₁ ρ₁ ρ₂) Γ 
split-ctx-++ sis₁ sis₂ ρ₁ ρ₂ · u = refl
split-ctx-++ sis₁ sis₂ ρ₁ ρ₂ (x ∶ t) u = split-bind-++ sis₁ sis₂ ρ₁ ρ₂ x t u
split-ctx-++ sis₁ sis₂ ρ₁ ρ₂ (Γ₁ ⸴[ o ] Γ₂) u =
  cong₂ (_⸴[ o ]_) (split-ctx-++ sis₁ sis₂ ρ₁ ρ₂ Γ₁ u)
                   (split-ctx-++ sis₁ sis₂ ρ₁ ρ₂ Γ₂ u)

split-bind-dom : ∀ sis ρ₁ ρ₂ x t →
  dom (split-bind sis ρ₁ ρ₂ x t) ⊆
  (x ∷ []) ++ map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis)
split-bind-dom sis ρ₁ ρ₂ x t
 with Chan? t
… | no _ = ⊆-++₁'
… | yes (b , s , refl)
 with Map.lookup x sis in eq
… | none = ⊆-++₁'
… | some s₁
 with s % s₁
… | none = ⊆-++₁'
… | some s₂ =
  let x,s₁∈sis = Map.lookup-some→∈ sis eq in
  let x∈sis₁ = ∈-map proj₁ x,s₁∈sis in
  λ where
    (here refl)         → there (AnyP.++⁺ˡ   (∈-map ρ₁ x∈sis₁))
    (there (here refl)) → there (AnyP.++⁺ʳ _ (∈-map ρ₂ x∈sis₁))

split-ctx-dom : ∀ sis ρ₁ ρ₂ Γ →
  dom (split-ctx sis ρ₁ ρ₂ Γ) ⊆
  dom Γ ++ map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis)
split-ctx-dom sis ρ₁ ρ₂ · = λ ()
split-ctx-dom sis ρ₁ ρ₂ (x ∶ t) = split-bind-dom sis ρ₁ ρ₂ x t
split-ctx-dom sis ρ₁ ρ₂ (Γ₁ ⸴[ o ] Γ₂) =
  let open ⊆-Reasoning in
  begin
    dom (split-ctx sis ρ₁ ρ₂ (Γ₁ ⸴[ o ] Γ₂))
  ≡⟨ ListP.map-++ proj₁ (binds (split-ctx sis ρ₁ ρ₂ Γ₁)) (binds (split-ctx sis ρ₁ ρ₂ Γ₂)) ⟩
    dom (split-ctx sis ρ₁ ρ₂ Γ₁) ++ dom (split-ctx sis ρ₁ ρ₂ Γ₂)
  ⊆⟨ ⊆-++ (split-ctx-dom sis ρ₁ ρ₂ Γ₁) (split-ctx-dom sis ρ₁ ρ₂ Γ₂) ⟩
    (dom Γ₁ ++ map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis)) ++
    (dom Γ₂ ++ map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis))
  ≈⟨ eq ⟩
    (dom Γ₁ ++ dom Γ₂) ++ map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis)
  ≡⟨ cong (_++ _) (sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))) ⟩
    dom (Γ₁ ⸴[ o ] Γ₂) ++ map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis)
  ∎
  where
    eq =
      let a = dom Γ₁ in
      let b = dom Γ₂ in
      let c = map ρ₁ (map proj₁ sis) in
      let d = map ρ₂ (map proj₁ sis) in
      let open ≈ˡ-Reasoning in
      begin
        (a ++ (c ++ d)) ++ (b ++ (c ++ d))
      ≈⟨ ≈ˡ-assoc a (c ++ d) (b ++ (c ++ d)) ⟩
        a ++ ((c ++ d) ++ (b ++ (c ++ d)))
      ≈⟨ ≈ˡ-++ (≈ˡ-refl {xs = a}) (≈ˡ-comm (c ++ d) (b ++ (c ++ d)) ) ⟩
        a ++ ((b ++ (c ++ d)) ++ (c ++ d))
      ≈⟨ ≈ˡ-++ (≈ˡ-refl {xs = a}) (≈ˡ-assoc b (c ++ d) (c ++ d)) ⟩
        a ++ (b ++ ((c ++ d) ++ (c ++ d)))
      ≈⟨ ≈ˡ-sym (≈ˡ-assoc a b _) ⟩
        (a ++ b) ++ ((c ++ d) ++ (c ++ d))
      ≈⟨ ≈ˡ-++ (≈ˡ-refl {xs = a ++ b}) (≈ˡ-dup-++ (c ++ d)) ⟩
        (a ++ b) ++ (c ++ d)
      ∎

-- split-ctx-ren ---------------------------------------------------------------

split-bind-ren-∉ : ∀ ρ xs u ys ys' x t → 
  let sis = xs ↓ᵘ u in
  let ρ₁ , ρ₂ = split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys in
  let ρ₁' , ρ₂' = split-rens (map proj₁ sis) ys' in
  let ρ' = split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ in
  Injectiveʳ (x ∷ map proj₁ sis) ρ →
  x ∉ map ρ₁' (map proj₁ sis) →
  x ∉ map ρ₂' (map proj₁ sis) →
  x ∉ map proj₁ sis →
  split-bind (sis ⋯ˢⁱ ρ) ρ₁ ρ₂ (ρ x) t ≡ split-bind sis ρ₁' ρ₂' x t ⋯ʳ ρ'
split-bind-ren-∉ ρ xs u ys ys' x t inj-ρ-sis₁ x∉ρ₁sis₁ x∉ρ₂sis₁ x∉sis₁
  using sis ← xs ↓ᵘ u
  using ρ₁ , ρ₂ ← split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys
  using ρ₁' , ρ₂' ← split-rens (map proj₁ sis) ys'
  using ρ' ← split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ
  with Chan? t
… | no _ =
  let open ≡-Reasoning in
  begin
    ρ x ∶ t 
  ≡⟨ cong (_∶ t) (sym (split-replaceʳ-∉cod (map proj₁ sis) (map proj₁ sis)
                                           ρ₁' ρ₂' ρ₁ ρ₂ ρ x x∉ρ₁sis₁ x∉ρ₂sis₁)) ⟩
    split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ x ∶ t
  ∎
… | yes (b , s , refl)
  using lookup-x-sis≡none ← Map.∉dom→lookup-none sis x∉sis₁
  using eqρl ← Map.lookup (ρ x) (sis ⋯ˢⁱ ρ) ≡ Map.lookup x sis by
               Map.lookup-map-dom ρ sis inj-ρ-sis₁
  rewrite lookup-x-sis≡none
        | trans eqρl lookup-x-sis≡none
  =
  let open ≡-Reasoning in
  begin
    ρ x ∶ t 
  ≡⟨ cong (_∶ t) (sym (split-replaceʳ-∉cod (map proj₁ sis) (map proj₁ sis)
                                           ρ₁' ρ₂' ρ₁ ρ₂ ρ x x∉ρ₁sis₁ x∉ρ₂sis₁)) ⟩
    split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ x ∶ t
  ∎

split-bind-ren-∈ : ∀ ρ xs u ys ys' x t {b} {s₁} {s₂ : Session b} → 
  let sis = xs ↓ᵘ u in
  let ρ₁ , ρ₂ = split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys in
  let ρ₁' , ρ₂' = split-rens (map proj₁ sis) ys' in
  let ρ' = split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ in
  Injectiveʳ (x ∷ map proj₁ sis) ρ →
  Unique (map proj₁ sis) →
  (x , s₁) ∈ sis →
  t ≡ Chan b (s₁ ++ˢ s₂) →
  split-bind (sis ⋯ˢⁱ ρ) ρ₁ ρ₂ (ρ x) t ≡ split-bind sis ρ₁' ρ₂' x t ⋯ʳ ρ'
split-bind-ren-∈ ρ xs u ys ys' x t {s₁ = s₁} {s₂ = s₂} inj-ρ-sis₁ U-sis x,s₁∈sis refl
  using sis ← xs ↓ᵘ u
  using ρ₁ , ρ₂ ← split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys
  using ρ₁' , ρ₂' ← split-rens (map proj₁ sis) ys'
  using ρ' ← split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ
  using lookup-x-sis≡some-s₁ ← Map.lookup-∈-unique U-sis x,s₁∈sis
  using eqρl ← Map.lookup (ρ x) (sis ⋯ˢⁱ ρ) ≡ Map.lookup x sis by
               Map.lookup-map-dom ρ sis inj-ρ-sis₁
  rewrite lookup-x-sis≡some-s₁
        | trans eqρl lookup-x-sis≡some-s₁
        | %-some s₁ s₂
  =
    let x∈sis₁ = ∈-map proj₁ x,s₁∈sis in
    let (inj-ρ₁' , inj-ρ₂') = split-rens-injective' (map proj₁ sis) ys' U-sis in
    let u-ρ₁'-ρ₂' = split-rens-unique (map proj₁ sis) ys' U-sis in
    let (_ , _ , d-ρ₁'-ρ₂') = Unique-++⁻ (map ρ₁' (map proj₁ sis)) (map ρ₂' (map proj₁ sis)) u-ρ₁'-ρ₂'  in
    let open ≡-Reasoning in
    begin
      ρ₁ (ρ x) ∶ Chan _ s₁ ⸴ ρ₂ (ρ x) ∶ Chan _ s₂
    ≡⟨ cong₂ (λ ■₁ ■₂ → ■₁ ∶ Chan _ s₁ ⸴ ■₂ ∶ Chan _ s₂)
             (sym (split-replaceʳ-lem₁ (map proj₁ sis) (map proj₁ sis)
                                       ρ₁' ρ₂' ρ₁ ρ₂ ρ inj-ρ₁' x x∈sis₁))
             (sym (split-replaceʳ-lem₂ (map proj₁ sis) (map proj₁ sis)
                                       ρ₁' ρ₂' ρ₁ ρ₂ ρ d-ρ₁'-ρ₂' inj-ρ₂' x x∈sis₁))
             ⟩
      ρ' (ρ₁' x) ∶ Chan _ s₁ ⸴ ρ' (ρ₂' x) ∶ Chan _ s₂
    ≡⟨⟩
      (ρ₁' x ∶ Chan _ s₁ ⸴ ρ₂' x ∶ Chan _ s₂) ⋯ʳ ρ'
    ∎

split-bind-ren : ∀ ρ xs u ys ys' x t → 
  let sis = xs ↓ᵘ u in
  let ρ₁ , ρ₂ = split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys in
  let ρ₁' , ρ₂' = split-rens (map proj₁ sis) ys' in
  let ρ' = split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ in
  Unique (map proj₁ sis) →
  Injectiveʳ (x ∷ map proj₁ sis) ρ →
  x ∉ map ρ₁' (map proj₁ sis) →
  x ∉ map ρ₂' (map proj₁ sis) →
  (∀ s₁ → (x , s₁) ∈ sis → ∃[ b ] Σ[ s₂ ∈ Session b ] t ≡ Chan b (s₁ ++ˢ s₂)) →
  split-bind (sis ⋯ˢⁱ ρ) ρ₁ ρ₂ (ρ x) t ≡ split-bind sis ρ₁' ρ₂' x t ⋯ʳ ρ'
split-bind-ren ρ xs u ys ys' x t U-sis inj-ρ x∉ρ₁'sis₁ x∉ρ₂'sis₁ u-good
  using sis ← xs ↓ᵘ u
  using ρ₁ , ρ₂ ← split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys
  using ρ₁' , ρ₂' ← split-rens (map proj₁ sis) ys'
  using ρ' ← split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ
  with x ∈? map proj₁ sis
… | no ¬x∈sis₁ = split-bind-ren-∉ ρ xs u ys ys' x t inj-ρ x∉ρ₁'sis₁ x∉ρ₂'sis₁ ¬x∈sis₁
… | yes x∈sis₁ =
  let (s₁ , x,s₁∈sis) = Map.∈dom→∈ sis x∈sis₁ in
  let (b , s₂ , eq) = u-good _ x,s₁∈sis in
  split-bind-ren-∈ ρ xs u ys ys' x t inj-ρ U-sis x,s₁∈sis eq

split-ctx-ren : ∀ ρ xs u ys ys' Γ → 
  let sis = xs ↓ᵘ u in
  let ρ₁ , ρ₂ = split-rens (map proj₁ (sis ⋯ˢⁱ ρ)) ys in
  let ρ₁' , ρ₂' = split-rens (map proj₁ sis) ys' in
  let ρ' = split-replaceʳ (map proj₁ sis) (map proj₁ sis) ρ₁' ρ₂' ρ₁ ρ₂ ρ in
  Unique (map proj₁ sis) →
  Injectiveʳ (dom Γ ++ map proj₁ sis) ρ →
  Disjoint (dom Γ) (map ρ₁' (map proj₁ sis) ++ map ρ₂' (map proj₁ sis)) →
  (∀ x t s₁ → (x , t) ∈ binds Γ → (x , s₁) ∈ sis →
      ∃[ b ] Σ[ s₂ ∈ Session b ] t ≡ Chan b (s₁ ++ˢ s₂)) →
  split-ctx (sis ⋯ˢⁱ ρ) ρ₁ ρ₂ (Γ ⋯ʳ ρ) ≡ split-ctx sis ρ₁' ρ₂' Γ ⋯ʳ ρ'
split-ctx-ren ρ xs u ys ys' · U-sis inj-ρ d u-good = refl
split-ctx-ren ρ xs u ys ys' (x ∶ t) U-sis inj-ρ d u-good =
  let x∉ρ₁sis₁ = Disjoint-⊆₂ ⊆-++₁' d x (here refl) in
  let x∉ρ₂sis₁ = Disjoint-⊆₂ (⊆-++₂' _) d x (here refl) in
  split-bind-ren ρ xs u ys ys' x t U-sis inj-ρ x∉ρ₁sis₁ x∉ρ₂sis₁
  λ s₁ x,s₁∈sis → u-good x t s₁ (here refl) x,s₁∈sis
split-ctx-ren ρ xs u ys ys' (Γ₁ ⸴[ o ] Γ₂) U-sis inj-ρ d u-good =
  let dom[Γ₁⸴Γ₂]≡domΓ₁++domΓ₂ = ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂) in
  let inj-ρ' = subst (λ ■ → Injectiveʳ (■ ++ _) ρ) dom[Γ₁⸴Γ₂]≡domΓ₁++domΓ₂ inj-ρ in
  let inj-ρ₁ = Injectiveʳ-⊆ (⊆-++ ⊆-++₁' (⊆-refl {xs = map proj₁ (xs ↓ᵘ u)})) inj-ρ' in
  let inj-ρ₂ = Injectiveʳ-⊆ (⊆-++ (⊆-++₂' _) (⊆-refl {xs = map proj₁ (xs ↓ᵘ u)})) inj-ρ' in
  let d' = subst (λ ■ → Disjoint ■ _) dom[Γ₁⸴Γ₂]≡domΓ₁++domΓ₂ d in
  let d₁ = Disjoint-⊆₁ ⊆-++₁' d' in
  let d₂ = Disjoint-⊆₁ (⊆-++₂' _) d' in
  let u-good₁ = λ x t s₁ x∶t∈Γ₁ x,s₁∈sis → u-good x t s₁ (AnyP.++⁺ˡ x∶t∈Γ₁) x,s₁∈sis in
  let u-good₂ = λ x t s₁ x∶t∈Γ₂ x,s₁∈sis → u-good x t s₁ (AnyP.++⁺ʳ _ x∶t∈Γ₂) x,s₁∈sis in
  cong₂ (_⸴[ o ]_)
        (split-ctx-ren ρ xs u ys ys' Γ₁ U-sis inj-ρ₁ d₁ u-good₁)
        (split-ctx-ren ρ xs u ys ys' Γ₂ U-sis inj-ρ₂ d₂ u-good₂)

--------------------------------------------------------------------------------

-- splits' : List Id → UsageMap → List Id → List Id × Ren × Ren × (Expr log → Expr log) 
-- splits' xs u zs =
--   let sis = xs ↓ᵘ u in
--   let dom-ρᵢ = map proj₁ sis in
--   let ρ₁ , ρ₂ = split-rens dom-ρᵢ zs in
--   dom-ρᵢ , ρ₁ , ρ₂ , splitsₙ sis ρ₁ ρ₂

-- splits : List Id → List Id → UsageMap → List Id → List Id → Ren → List Id × Ren × Ren × (Expr log → Expr log) 
-- splits xs₁ xs₂ u zs dom-ρ ρ =
--   let dom-ρᵢ , ρ₁ , ρ₂ , E = splits' ((xs₁ ∩ˡ xs₂) ⋯ˡ ρ) (ρ ·ʳᶜ u) (zs ++ dom-ρ ++ codʳ dom-ρ ρ) in
--   dom-ρᵢ ++ dom-ρ , (ρ ·ʳ ρ₁) ↓ʳ xs₁ , (ρ ·ʳ ρ₂) ↓ʳ xs₂ , E

splits : List Id → List Id → UsageMap → List Id → List Id → Ren → Ctx → Ctx →
         List Id × Ren × List Id × Ren × (Expr log → Expr log) 
splits xs₁ xs₂ u zs dom-ρ ρ Γ₁ Γ₂ =
  let sis = ((xs₁ ∩ˡ xs₂) ↓ᵘ u) ⋯ˢⁱ ρ in
  let dom-ρᵢ = map proj₁ sis in
  let ρ₁ , ρ₂ = split-rens dom-ρᵢ (zs ++ map ρ dom-ρ) in
  ((dom-ρᵢ ++ dom-ρ) ∩ˡ dom Γ₁) , (ρ ·ʳ ρ₁) ↓ʳ dom Γ₁ ,
  ((dom-ρᵢ ++ dom-ρ) ∩ˡ dom Γ₂) , (ρ ·ʳ ρ₂) ↓ʳ dom Γ₂ ,
  splitsₙ sis ρ₁ ρ₂

--------------------------------------------------------------------------------

⊢ʳ-pres-unique : ∀ {ρ xs ys zs} →
  map proj₁ zs ⊆ ys →
  ys % xs ⊢ʳ ρ →
  Unique (map proj₁ zs) →
  Unique (map proj₁ (zs ⋯ˢⁱ ρ))
⊢ʳ-pres-unique {ρ = ρ} {zs = []} zs⊆ys ⊢ρ U-zs = Unique-[]
⊢ʳ-pres-unique {ρ = ρ} {zs = (x , s) ∷ zs} zs⊆ys ⊢ρ U-zs =
  let x∉zs₁ = Unique-∈-∷ x _ U-zs in
  let ρx∉ρzs₁ = Injecitveʳ-∉ (⊆-trans ⊆-∷ zs⊆ys) (⊢ʳ-inj-ys-ρ ⊢ρ) (zs⊆ys (here refl)) x∉zs₁ in
  let ρx∉[ρzs]₁ = subst (ρ x ∉_) (sym (map-proj₁ ρ zs)) ρx∉ρzs₁ in
  Unique-∷ ρx∉[ρzs]₁ (⊢ʳ-pres-unique (⊆-trans ⊆-∷ zs⊆ys) ⊢ρ (Unique-tail U-zs))

sis⊆ : ∀ Γ (e₁ : Expr §) (e₂s : List (Expr §)) u  →
  map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⊆ dom Γ ++ vars e₁ ++ varss e₂s
sis⊆ Γ e₁ e₂s u =
  let open ⊆-Reasoning in
  begin
    map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u)
  ⊆⟨ ↓ᵘ-⊆ (fvs e₁ ∩ˡ fvss e₂s) u ⟩
    fvs e₁ ∩ˡ fvss e₂s
  ⊆⟨ ∩ˡ-⊆₁ (fvs e₁) (fvss e₂s) ⟩
    fvs e₁
  ⊆⟨ fvs⊆vars e₁ ⟩
    vars e₁
  ⊆⟨ ⊆-++₁' ⟩
    vars e₁ ++ varss e₂s
  ⊆⟨ ⊆-++₂' (dom Γ) ⟩
    dom Γ ++ vars e₁ ++ varss e₂s
  ∎

sis⊆ρ : ∀ {dom-ρ ρ} Γ (e₁ : Expr §) (e₂s : List (Expr §)) u →
  (dom Γ ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⋯ˢⁱ ρ) ⊆ (dom Γ ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
sis⊆ρ {dom-ρ = dom-ρ} {ρ = ρ} Γ e₁ e₂s u ⊢ρ =
  let open ⊆-Reasoning in
  begin
    map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⋯ˢⁱ ρ)
  ≡⟨ map-proj₁ ρ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⟩
    (map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u)) ⋯ˡ ρ
  ⊆⟨ ⊆-map ρ (sis⊆ Γ e₁ e₂s u) ⟩
    (dom Γ ++ vars e₁ ++ varss e₂s) ⋯ˡ ρ
  ⊆⟨ ⊢ʳ-ρys⊆ys++ρxs ⊢ρ ⟩
    (dom Γ ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
  ∎

sis⊆ρ-extra : ∀ {dom-ρ ρ} Γ (e₁ : Expr §) (e₂s : List (Expr §)) u extra →
  (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⋯ˢⁱ ρ) ⊆ (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
sis⊆ρ-extra {dom-ρ = dom-ρ} {ρ = ρ} Γ e₁ e₂s u extra ⊢ρ =
  let open ⊆-Reasoning in
  begin
    map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⋯ˢⁱ ρ)
  ≡⟨ map-proj₁ ρ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u) ⟩
    (map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u)) ⋯ˡ ρ
  ⊆⟨ ⊆-map ρ (sis⊆ Γ e₁ e₂s u) ⟩
    (dom Γ ++ vars e₁ ++ varss e₂s) ⋯ˡ ρ
  ⊆⟨ ⊆-map ρ (⊆-++ (⊆-refl {xs = dom Γ}) (⊆-++₂' extra)) ⟩
    (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ⋯ˡ ρ
  ⊆⟨ ⊢ʳ-ρys⊆ys++ρxs ⊢ρ ⟩
    (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
  ∎

Unique-sisₐ : ∀ (e₁ : Expr §) (e₂s : List (Expr §)) u₁  →
  Unique (map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁))
Unique-sisₐ e₁ e₂s u₁ =
  ↓ᵘ-pres-Unique (fvs e₁ ∩ˡ fvss e₂s) u₁ $
  ∩ˡ-unique (fvs e₁) (fvss e₂s)

Unique-sis : ∀ {dom-ρ ρ} Γ (e₁ : Expr §) (e₂s : List (Expr §)) u₁  →
  (dom Γ ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  Unique (map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ))
Unique-sis {dom-ρ = dom-ρ} {ρ = ρ} Γ e₁ e₂s u₁ ⊢ρ =
  ⊢ʳ-pres-unique (sis⊆ Γ e₁ e₂s u₁) ⊢ρ $
  Unique-sisₐ e₁ e₂s u₁

Unique-sis-extra : ∀ {dom-ρ ρ} Γ (e₁ : Expr §) (e₂s : List (Expr §)) u₁ extra →
  (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  Unique (map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ))
Unique-sis-extra {dom-ρ = dom-ρ} {ρ = ρ} Γ e₁ e₂s u₁ extra ⊢ρ =
  ⊢ʳ-pres-unique (⊆-trans (sis⊆ Γ e₁ e₂s u₁)
                          (⊆-++ (⊆-refl {xs = dom Γ}) (⊆-++₂' extra))) ⊢ρ $
  Unique-sisₐ e₁ e₂s u₁

--------------------------------------------------------------------------------

⊢ʳ⁻-· : ∀ {ρ ρ₁ dom-ρ dom-ρ> xs} →
  dom-ρ> % dom-ρ ⊢ʳ ρ →
  (dom-ρ> ++ map ρ dom-ρ) % map ρ xs ⊢ʳ ρ₁ →
  dom-ρ> % (map ρ xs ++ dom-ρ) ⊢ʳ⁻ (ρ ·ʳ ρ₁)
⊢ʳ⁻-· {ρ} {ρ₁} {dom-ρ} {dom-ρ>} {xs} ⊢ρ ⊢ρ₁ = record
  { ⊢ʳ⁻-∉xs-id = λ {x} x∉ρxs++dom-ρ →
      let (x∉ρxs , x∉dom-ρ) = ∉-++⁻ (map ρ xs) dom-ρ x∉ρxs++dom-ρ in
      let open ≡-Reasoning in
      begin
        ρ₁ (ρ x)
      ≡⟨ cong ρ₁ (⊢ʳ-∉xs-id ⊢ρ x∉dom-ρ) ⟩
        ρ₁ x
      ≡⟨ ⊢ʳ-∉xs-id ⊢ρ₁ x∉ρxs ⟩
        x
      ∎
  ; ⊢ʳ⁻-ρxs⊎ys = λ x x∈[ρ·ρ₁][ρxs++dom-ρ] x∈dom-ρ> →
      let
        x∈ : x ∈ map (ρ ·ʳ ρ₁) (map ρ xs) ++ map (ρ ·ʳ ρ₁) dom-ρ
        x∈ = subst (x ∈_) (ListP.map-++ (ρ ·ʳ ρ₁) (map ρ xs) dom-ρ) x∈[ρ·ρ₁][ρxs++dom-ρ]

        x∈₁ : x ∈ map ρ₁ (map ρ (map ρ xs)) ++ map (ρ ·ʳ ρ₁) dom-ρ
        x∈₁ = subst (λ ■ → x ∈ ■ ++ map (ρ ·ʳ ρ₁) dom-ρ) (ListP.map-∘ (map ρ xs)) x∈ 

        x∈₂ : x ∈ map ρ₁ (map ρ xs) ++ map (ρ ·ʳ ρ₁) dom-ρ
        x∈₂ = ⊆-++ (⊆-map ρ₁ (⊢ʳ-ρρ⊆ρ ⊢ρ xs)) (⊆-refl {xs = map (ρ ·ʳ ρ₁) dom-ρ}) x∈₁

        x∈₃ : x ∈ map (ρ ·ʳ ρ₁) xs ++ map (ρ ·ʳ ρ₁) dom-ρ
        x∈₃ = subst (λ ■ → x ∈ ■ ++ map (ρ ·ʳ ρ₁) dom-ρ) (sym (ListP.map-∘ xs)) x∈₂ 

        x∉₁ : x ∉ map ρ₁ (map ρ xs)
        x∉₁ = Disjoint-sym (⊢ʳ-ρxs⊎ys ⊢ρ₁) x (AnyP.++⁺ˡ x∈dom-ρ>)
      in
      case AnyP.++⁻ (map (ρ ·ʳ ρ₁) xs) x∈₃ of λ where
        (inj₁ x∈[ρ·ρ₁]xs) → x∉₁ $ subst (x ∈_) (ListP.map-∘ xs) x∈[ρ·ρ₁]xs
        (inj₂ x∈[ρ·ρ₁]dom-ρ) →
          let x∈ρ₁ρdom-ρ = subst (x ∈_) (ListP.map-∘ {g = ρ₁} dom-ρ) x∈[ρ·ρ₁]dom-ρ in
          let (y , y∈ρdom-ρ , ρ₁y≡x) = map-∈-inv ρ₁ (map ρ dom-ρ) x∈ρ₁ρdom-ρ in
          case y ∈? map ρ xs of λ where
            (yes y∈ρxs) → x∉₁ $ subst (_∈ _) ρ₁y≡x $ ∈-map ρ₁ y∈ρxs
            (no ¬y∈ρxs) →
              let
                ρ₁y≡y : ρ₁ y ≡ y
                ρ₁y≡y = ⊢ʳ-∉xs-id ⊢ρ₁ ¬y∈ρxs
                y≡x : y ≡ x
                y≡x = trans (sym ρ₁y≡y) ρ₁y≡x
                ρ₁x≡x : ρ₁ x ≡ x
                ρ₁x≡x = trans (cong ρ₁ (sym y≡x)) ρ₁y≡x
                ρ₁x∈ρ₁ρdom-ρ : ρ₁ x ∈ map ρ₁ (map ρ dom-ρ)
                ρ₁x∈ρ₁ρdom-ρ = subst (_∈ _) (sym ρ₁x≡x) x∈ρ₁ρdom-ρ
                x∈ρdom-ρ : x ∈ map ρ dom-ρ
                x∈ρdom-ρ = Injecitveʳ-∈ (⊆-++₂' _) (⊢ʳ-inj-ys-ρ ⊢ρ₁) (AnyP.++⁺ˡ x∈dom-ρ>) ρ₁x∈ρ₁ρdom-ρ
              in
              ⊢ʳ-ρxs⊎ys ⊢ρ x x∈ρdom-ρ x∈dom-ρ>
  ; ⊢ʳ⁻-inj-ys-ρ =
      Injectiveʳ-· dom-ρ> ρ ρ₁
                   (⊢ʳ-inj-ys-ρ ⊢ρ)
                   (Injectiveʳ-⊆ (⊢ʳ-ρys⊆ys++ρxs ⊢ρ) (⊢ʳ-inj-ys-ρ ⊢ρ₁))
  }

⊢ʳ-· : ∀ {ρ ρ₁ dom-ρ dom-ρ> xs ys zs} →
  ys ⊆ zs →
  zs ⊆ dom-ρ> →
  dom-ρ> % dom-ρ ⊢ʳ ρ →
  (dom-ρ> ++ map ρ dom-ρ) % map ρ xs ⊢ʳ ρ₁ →
  zs % ((map ρ xs ++ dom-ρ) ∩ˡ ys) ⊢ʳ ((ρ ·ʳ ρ₁) ↓ʳ ys)
⊢ʳ-· {ρ = ρ} {dom-ρ = dom-ρ} {xs = xs} {ys = ys} ys⊆zs zs⊆dom-ρ> ⊢ρ ⊢ρ₁ =
  let ⊢ρρ₁⁻ = ⊢ʳ⁻-⊆-ys zs⊆dom-ρ> $ ⊢ʳ⁻-↓ʳ' ys $ ⊢ʳ⁻-· ⊢ρ ⊢ρ₁ in
  record
    { ⊢ʳ-∉xs-id   = ⊢ʳ⁻-∉xs-id   ⊢ρρ₁⁻
    ; ⊢ʳ-ρxs⊎ys   = ⊢ʳ⁻-ρxs⊎ys   ⊢ρρ₁⁻
    ; ⊢ʳ-inj-ys-ρ = ⊢ʳ⁻-inj-ys-ρ ⊢ρρ₁⁻
    ; ⊢ʳ-xs⊆ys    = ⊆-trans (∩ˡ-⊆₂ (map ρ xs ++ dom-ρ) ys) ys⊆zs
    }

⊢ʳ-splits-ρ' : ∀ {dom-ρ : List Id} {ρ ρ₁ : Ren} (Γᵢ Γ : Ctx)
                 (e₁ : Expr §) (e₂s : List (Expr §)) (eᵢs : List (Expr §))
                 (u₁ : UsageMap) extra  →
  let sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ in
  dom Γᵢ ⊆ dom Γ →
  varss eᵢs ⊆ vars e₁ ++ varss e₂s →
  (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  ((dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ) % map proj₁ sis ⊢ʳ ρ₁ →
  (dom Γᵢ ++ extra ++ varss eᵢs) % ((map proj₁ sis ++ dom-ρ) ∩ˡ dom Γᵢ) ⊢ʳ ((ρ ·ʳ ρ₁) ↓ʳ dom Γᵢ)
⊢ʳ-splits-ρ' {dom-ρ = dom-ρ} {ρ = ρ} {ρ₁ = ρ₁} Γᵢ Γ e₁ e₂s eᵢs u₁ extra Γᵢ⊆Γ eᵢ⊆e₁++e₂ ⊢ρ ⊢ρ₁ =
  let sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ in
  let eq =
        let open ≡-Reasoning in
        begin
          map proj₁ (((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ)
        ≡⟨ map-proj₁ ρ _ ⟩
          map ρ (map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁))
        ∎ in
  let sub : dom Γᵢ ++ extra ++ varss eᵢs ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
      sub =
        let open ⊆-Reasoning in
        begin
          dom Γᵢ ++ extra ++ varss eᵢs
        ⊆⟨ ⊆-++ Γᵢ⊆Γ (⊆-++ ⊆-refl eᵢ⊆e₁++e₂) ⟩
          dom Γ ++ extra ++ vars e₁ ++ varss e₂s
        ∎ in
  let xx = ⊢ʳ-· {dom-ρ> = (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)}
                {xs = map proj₁ ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁)}
                {ys = dom Γᵢ}
                {zs = (dom Γᵢ ++ extra ++ varss eᵢs)}
                ⊆-++₁' sub ⊢ρ
                (subst (_ %_⊢ʳ ρ₁) eq ⊢ρ₁) in
  subst (_ %_⊢ʳ ((ρ ·ʳ ρ₁) ↓ʳ dom Γᵢ)) (cong (λ ■ → (■ ++ dom-ρ) ∩ˡ dom Γᵢ) (sym eq)) xx

⊢ʳ-splits-ρ : ∀ {dom-ρ ρ} Γ₁ Γ₂ Γ (e₁ : Expr §) (e₂s : List (Expr §)) u₁ extra →
  dom Γ₁ ⊆ dom Γ →
  dom Γ₂ ⊆ dom Γ →
  let fvs₂  = List.foldl _++_ [] (map fvs e₂s) in
  let vars₂ = List.foldl _++_ [] (map vars e₂s) in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) fvs₂ u₁ (dom Γ ++ extra ++ vars e₁ ++ vars₂) dom-ρ ρ Γ₁ Γ₂ in
  (dom Γ ++ extra ++ vars e₁ ++ vars₂) % dom-ρ ⊢ʳ ρ →
  (dom Γ₁ ++ vars e₁) % dom-ρ₁ ⊢ʳ ρ₁ ×
  (dom Γ₂ ++ extra ++ vars₂) % dom-ρ₂ ⊢ʳ ρ₂
⊢ʳ-splits-ρ {dom-ρ = dom-ρ} {ρ = ρ} Γ₁ Γ₂ Γ e₁ e₂s u₁ extra Γ₁⊆Γ Γ₂⊆Γ ⊢ρ =
  let
    fvs₂  = List.foldl _++_ [] (map fvs e₂s)
    vars₂ = List.foldl _++_ [] (map vars e₂s)
    sis = ((fvs e₁ ∩ˡ fvs₂) ↓ᵘ u₁) ⋯ˢⁱ ρ
    ρ₁ , ρ₂ = split-rens (map proj₁ sis)
                         ((dom Γ ++ extra ++ vars e₁ ++ vars₂) ++ codʳ dom-ρ ρ)
    sub : map proj₁ sis ⊆ (dom Γ ++ extra ++ vars e₁ ++ vars₂) ++ codʳ dom-ρ ρ
    sub = sis⊆ρ-extra Γ e₁ e₂s u₁ extra ⊢ρ
    U-sis₁ = Unique-sis-extra Γ e₁ e₂s u₁ extra ⊢ρ
    (⊢ρ₁ , ⊢ρ₂ , d-ρ₁-ρ₂) = ⊢ʳ-split-rens
      (map proj₁ sis)
      ((dom Γ ++ extra ++ vars e₁ ++ vars₂) ++ codʳ dom-ρ ρ) sub U-sis₁
    extra-sub : dom Γ₁ ++ vars e₁ ⊆ dom Γ₁ ++ extra ++ vars e₁
    extra-sub = ⊆-++ (⊆-refl {xs = dom Γ₁}) (⊆-++₂' _)
    extra-sub₂ : (map proj₁ sis ++ dom-ρ) ∩ˡ dom Γ₁ ⊆ dom Γ₁ ++ vars e₁
    extra-sub₂ = ⊆-trans (∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom Γ₁)) ⊆-++₁'
  in
  ⊢ʳ-⊆-ys extra-sub extra-sub₂ (⊢ʳ-splits-ρ' Γ₁ Γ e₁ e₂s (e₁ ∷ []) u₁ extra Γ₁⊆Γ ⊆-++₁' ⊢ρ ⊢ρ₁) ,
  ⊢ʳ-splits-ρ' Γ₂ Γ e₁ e₂s e₂s u₁ extra Γ₂⊆Γ (⊆-++₂' _) ⊢ρ ⊢ρ₂

⊢ʳ-splits-ρ₁-extra : ∀ {dom-ρ ρ} Γ₁ Γ₂ Γ (e₁ : Expr §) (e₂s : List (Expr §)) u₁ extra →
  dom Γ₁ ⊆ dom Γ →
  dom Γ₂ ⊆ dom Γ →
  let fvs₂  = List.foldl _++_ [] (map fvs e₂s) in
  let vars₂ = List.foldl _++_ [] (map vars e₂s) in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) fvs₂ u₁ (dom Γ ++ extra ++ vars e₁ ++ vars₂) dom-ρ ρ Γ₁ Γ₂ in
  (dom Γ ++ extra ++ vars e₁ ++ vars₂) % dom-ρ ⊢ʳ ρ →
  (dom Γ₁ ++ extra ++ vars e₁) % dom-ρ₁ ⊢ʳ ρ₁
⊢ʳ-splits-ρ₁-extra {dom-ρ = dom-ρ} {ρ = ρ} Γ₁ Γ₂ Γ e₁ e₂s u₁ extra Γ₁⊆Γ Γ₂⊆Γ ⊢ρ =
  let
    fvs₂  = List.foldl _++_ [] (map fvs e₂s)
    vars₂ = List.foldl _++_ [] (map vars e₂s)
    sis = ((fvs e₁ ∩ˡ fvs₂) ↓ᵘ u₁) ⋯ˢⁱ ρ
    ρ₁ , ρ₂ = split-rens (map proj₁ sis)
                         ((dom Γ ++ extra ++ vars e₁ ++ vars₂) ++ codʳ dom-ρ ρ)
    sub : map proj₁ sis ⊆ (dom Γ ++ extra ++ vars e₁ ++ vars₂) ++ codʳ dom-ρ ρ
    sub = sis⊆ρ-extra Γ e₁ e₂s u₁ extra ⊢ρ
    U-sis₁ = Unique-sis-extra Γ e₁ e₂s u₁ extra ⊢ρ
    (⊢ρ₁ , ⊢ρ₂ , d-ρ₁-ρ₂) = ⊢ʳ-split-rens
      (map proj₁ sis)
      ((dom Γ ++ extra ++ vars e₁ ++ vars₂) ++ codʳ dom-ρ ρ) sub U-sis₁
  in
  ⊢ʳ-splits-ρ' Γ₁ Γ e₁ e₂s (e₁ ∷ []) u₁ extra Γ₁⊆Γ ⊆-++₁' ⊢ρ ⊢ρ₁
