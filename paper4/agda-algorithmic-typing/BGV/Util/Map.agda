module BGV.Util.Map where

import Data.List.Properties as ListP
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.List using (List; _++_; zip)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Maybe as Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl)
open import Function using (case_of_; _∘_; _$_; const)
open import Data.Empty using (⊥; ⊥-elim)
import Data.Maybe.Relation.Binary.Connected as Connected

open import Data.List using ([]; _∷_; map) public
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.Linked as Linked using (Linked; []; [-]; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Relation.Nullary using (¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import BGV.Util.Decidable
open import BGV.Util.List as L using (_∷?_; ∈-map; ∉-tail)

private variable
  ℓ ℓ₁ ℓ₂ ℓ₃ : Level
  A B C D K V : Set ℓ

Map : ∀ (K : Set ℓ₁) (V : Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
Map K V = List (K × V)

private variable
  m m' m₁ m₂ m₃ : Map K V

∅ : Map K V
∅ = []

dom : Map K V → List K
dom = map proj₁

cod : Map K V → List V
cod = map proj₂

lookup : ⦃ _ : DecEq K ⦄ → K → Map K V → Maybe V
lookup k [] = none
lookup k ((k' , v) ∷ m) with k ≟ k'
… | yes _ = some v
… | no _ = lookup k m

lookupDef : ⦃ _ : DecEq K ⦄ → K → V → Map K V → V
lookupDef k def m with lookup k m
… | none = def
… | some v = v

insert : K → V → Map K V → Map K V
insert k v m = (k , v) ∷ m

single : K → V → Map K V
single k v = insert k v ∅

insert-with : ⦃ _ : DecEq K ⦄ → K → (Maybe V → V) → Map K V → Map K V
insert-with k f m = insert k (f (lookup k m)) m

remove : ⦃ _ : DecEq K ⦄ → K → Map K V → Map K V
remove k [] = []
remove k ((k' , v) ∷ m) with k ≟ k'
… | yes _ = remove k m
… | no  _ = (k' , v) ∷ remove k m

modify : ⦃ _ : DecEq K ⦄ → K → (Maybe V → Maybe V) → Map K V → Map K V
modify k f [] = case f none of λ where
  none → []
  (some v') → (k , v') ∷ []
modify k f ((k' , v) ∷ m) with k ≟ k'
… | yes _ = Maybe.map (k ,_) (f (some v)) ∷? m
… | no _ = (k' , v) ∷ modify k f m

mod-insert-with : (Maybe V → V) → (Maybe V → Maybe V)
mod-insert-with f = some ∘ f

mod-insert : V → (Maybe V → Maybe V)
mod-insert v = mod-insert-with (const v)

mod-remove : Maybe V → Maybe V
mod-remove = const none

insert-with' : ⦃ _ : DecEq K ⦄ → K → (Maybe V → V) → Map K V → Map K V
insert-with' k f = modify k (mod-insert-with f)

insert' : ⦃ _ : DecEq K ⦄ → K → V → Map K V → Map K V
insert' k v = modify k (mod-insert v)

remove' : ⦃ _ : DecEq K ⦄ → K → Map K V → Map K V
remove' k = modify k (const none)

infixl 6 _-_
_-_ : ⦃ _ : DecEq K ⦄ → Map K V → K → Map K V
m - k = remove k m

infixl 6 _-*_
_-*_ : ⦃ _ : DecEq K ⦄ → Map K V → List K → Map K V
m -* [] = m
m -* (k ∷ ks) = m - k -* ks

merge : ⦃ _ : DecEq K ⦄ → (K → V → V → V) → Map K V → Map K V → Map K V
merge f []             m₂ = m₂
merge f ((k , v) ∷ m₁) m₂ = insert-with k (λ { none → v ; (some v') → f k v v' } ) (merge f m₁ m₂)

insertAll : ⦃ _ : DecEq K ⦄ → Map K V → Map K V → Map K V
insertAll m₁ m₂ = merge (λ _ v₁ _ → v₁) m₁ m₂

infix 3 _⊆_ _⊇_ _≈_ _⊆'_ _⊇'_ _≈'_

_⊆'_ : ⦃ _ : DecEq K ⦄ → Map K V → Map K V → Set _
m₁ ⊆' m₂ = ∀ k v → lookup k m₁ ≡ some v → lookup k m₂ ≡ some v

_⊇'_ : ⦃ _ : DecEq K ⦄ → Map K V → Map K V → Set _
m₁ ⊇' m₂ = m₂ ⊆' m₁

_≈'_ : ⦃ _ : DecEq K ⦄ → Map K V → Map K V → Set _
m₁ ≈' m₂ = ∀ k → lookup k m₁ ≡ lookup k m₂

record _⊆_ {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ (m₁ m₂ : Map K V) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mk-⊆ 
  field
    prf : m₁ ⊆' m₂

record _≈_ {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ (m₁ m₂ : Map K V) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor mk-≈
  field
    prf : m₁ ≈' m₂

_⊇_ : ⦃ _ : DecEq K ⦄ → Map K V → Map K V → Set _
m₁ ⊇ m₂ = m₂ ⊆ m₁

≈→⊆ : ∀ ⦃ _ : DecEq K ⦄ {m₁ m₂ : Map K V} → m₁ ≈ m₂ → m₁ ⊆ m₂ 
≈→⊆ (mk-≈ m₁≈m₂) = mk-⊆ λ k v p → trans (sym (m₁≈m₂ k)) p

⊆⊇→≈' : ∀ ⦃ _ : DecEq K ⦄ {m₁ m₂ : Map K V} → m₁ ⊆' m₂ → m₁ ⊇' m₂ → m₁ ≈' m₂
⊆⊇→≈' {m₁ = m₁} {m₂ = m₂} m₁⊆m₂ m₂⊆m₁ k with lookup k m₁ in eq₁ |  lookup k m₂ in eq₂
… | none    | none    = refl
… | _       | some v₂ rewrite sym eq₁ = m₂⊆m₁ k v₂ eq₂
… | some v₁ | _       rewrite sym eq₂ = sym (m₁⊆m₂ k v₁ eq₁)

⊆⊇→≈ : ∀ ⦃ _ : DecEq K ⦄ {m₁ m₂ : Map K V} → m₁ ⊆ m₂ → m₁ ⊇ m₂ → m₁ ≈ m₂
⊆⊇→≈ {m₁ = m₁} {m₂ = m₂} (mk-⊆ m₁⊆m₂) (mk-⊆ m₂⊆m₁) =
  mk-≈ (⊆⊇→≈' {m₁ = m₁} {m₂ = m₂} m₁⊆m₂ m₂⊆m₁)

∈dom→lookup-some : ∀ ⦃ _ : DecEq K ⦄ {k : K} (m : Map K V) →
  k ∈ dom m →
  ∃[ v ] lookup k m ≡ some v
∈dom→lookup-some ((k , v) ∷ m) (here refl) with k ≟ k
… | no ¬k≡k = ⊥-elim (¬k≡k refl)
… | yes k≡k = _ , refl
∈dom→lookup-some {k = k} ((k' , v) ∷ m) (there p) with k ≟ k'
… | no ¬k≡k' = ∈dom→lookup-some m p
… | yes refl = _ , refl

∉dom→lookup-none : ∀ ⦃ _ : DecEq K ⦄ {k : K} (m : Map K V) →
  k ∉ dom m →
  lookup k m ≡ none
∉dom→lookup-none {k = k} [] k∉m = refl
∉dom→lookup-none {k = k} ((k' , v) ∷ m) k∉m
  with k ≟ k'
… | yes refl = ⊥-elim (k∉m (here refl))
… | no ¬k≡k' = ∉dom→lookup-none m (∉-tail k∉m)

lookup-none→∉dom : ∀ ⦃ _ : DecEq K ⦄ {k : K} (m : Map K V) →
  lookup k m ≡ none →
  k ∉ dom m
lookup-none→∉dom {k = k} [] eq = λ ()
lookup-none→∉dom {k = k} ((k' , v) ∷ m) eq
  with k ≟ k'
… | yes refl with () ← eq
… | no ¬k≡k' = λ where
  (here refl) → ¬k≡k' refl
  (there p) → lookup-none→∉dom m eq p

lookup-some→∈ : ∀ ⦃ _ : DecEq K ⦄ {k : K} {v : V} (m : Map K V) →
  lookup k m ≡ some v →
  (k , v) ∈ m
lookup-some→∈ {k = k} ((k' , v') ∷ m) eq   with k ≟ k'
lookup-some→∈ {k = k} ((k' , v') ∷ m) eq   | no ¬k≡k' = there (lookup-some→∈ m eq)
lookup-some→∈ {k = k} ((k' , v') ∷ m) refl | yes refl = here refl

∈dom→∈ : ∀ ⦃ _ : DecEq K ⦄ {k : K} (m : Map K V) →
  k ∈ dom m →
  ∃[ v ] (k , v) ∈ m
∈dom→∈ m k∈ = _ , lookup-some→∈ m (proj₂ (∈dom→lookup-some m k∈))

∈→∈dom : ∀ {k : K} {v : V} {m : Map K V} →
  (k , v) ∈ m →
  k ∈ dom m
∈→∈dom p = ∈-map proj₁ p

-- lookup-cod : ∀ ⦃ _ : DecEq K ⦄ {k : K} {m : Map K V} {v : V} →
--   lookup k m ≡ some v →
--   v ∈ cod m
-- lookup-cod = {!!}

-- lookup-remove-≢ : ∀ ⦃ _ : DecEq K ⦄ (k k' : K) (m : Map K V) →
--   k ≢ k' →
--   lookup k (remove k' m) ≡ lookup k m
-- lookup-remove-≢ = {!!}

data LookupMerge {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄
                 (f : K → V → V → V) (k : K) (v : V) (m₁ m₂ : Map K V) : Set (ℓ₁ ⊔ ℓ₂) where
  lm-left :
    lookup k m₁ ≡ some v →
    lookup k m₂ ≡ none →
    LookupMerge f k v m₁ m₂
  lm-right :
    lookup k m₁ ≡ none →
    lookup k m₂ ≡ some v →
    LookupMerge f k v m₁ m₂
  lm-both : ∀ v₁ v₂ →
    lookup k m₁ ≡ some v₁ →
    lookup k m₂ ≡ some v₂ →
    v ≡ f k v₁ v₂ →
    LookupMerge f k v m₁ m₂

-- lookup-merge : ∀ ⦃ _ : DecEq K ⦄ (f : K → V → V → V) (k : K) (v : V) (m₁ m₂ : Map K V) →
--   lookup k (merge f m₁ m₂) ≡ some v →
--   LookupMerge f k v m₁ m₂
-- lookup-merge = {!!}

lookupDef-lookup : ∀ ⦃ _ : DecEq K ⦄ (k₁ k₂ : K) (v : V) (m₁ m₂ : Map K V) →
  lookup k₁ m₁ ≡ lookup k₂ m₂ →
  lookupDef k₁ v m₁ ≡ lookupDef k₂ v m₂
lookupDef-lookup k₁ k₂ v m₁ m₂ eq with lookup k₁ m₁
… | none rewrite (sym eq) = refl
… | some v rewrite (sym eq) = refl

lookup-∷-some : ∀ ⦃ _ : DecEq K ⦄ (k : K) (v : V) (m : Map K V) →
  lookup k ((k , v) ∷ m) ≡ some v
lookup-∷-some k v m with k ≟ k
… | no p with () ← p refl
… | yes _ = refl

lookupDef-some : ∀ ⦃ _ : DecEq K ⦄ (k : K) (v : V) (m : Map K V) →
  lookup k m ≡ some v →
  lookupDef k v m ≡ v
lookupDef-some k v m eq rewrite eq = refl

lookupDef-none : ∀ ⦃ _ : DecEq K ⦄ (k : K) (v : V) (m : Map K V) →
  lookup k m ≡ none →
  lookupDef k v m ≡ v
lookupDef-none k v m eq rewrite eq = refl

lookup-++₁ :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ (x : K) xs ys (y : V) →
  lookup x xs ≡ some y →
  lookup x (xs ++ ys) ≡ some y
lookup-++₁ x ((x' , y') ∷ xs) ys y eq with x ≟ x'
… | yes refl = eq
… | no ¬x≡x' = lookup-++₁ x xs ys y eq

lookup-++₂ :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ (x : K) (xs ys : List (K × V)) →
  lookup x xs ≡ none →
  lookup x (xs ++ ys) ≡ lookup x ys
lookup-++₂ x [] ys eq = refl
lookup-++₂ x ((x' , y') ∷ xs) ys eq with x ≟ x'
… | no ¬x≡x' = lookup-++₂ x xs ys eq 

lookup-++-disjoint :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ x (xs ys : List (K × V)) y →
  L.Disjoint (map proj₁ xs) (map proj₁ ys) →
  lookup x xs ≡ some y →
  lookup x ys ≡ none
lookup-++-disjoint x xs ys y d eq
  with lookup x ys in eq'
… | none = refl
… | some y' =
  let xy∈xs = lookup-some→∈ xs eq in
  let xy'∈ys = lookup-some→∈ ys eq' in
  let x∈xs₁ = ∈-map proj₁ xy∈xs in
  let x∈ys₁ = ∈-map proj₁ xy'∈ys in
  ⊥-elim (d x x∈xs₁ x∈ys₁)

lookup-++⁻-some-disjoint :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ x (xs ys : List (K × V)) y →
  L.Disjoint (map proj₁ xs) (map proj₁ ys) →
  lookup x (xs ++ ys) ≡ some y →
  lookup x xs ≡ some y × lookup x ys ≡ none ⊎
  lookup x xs ≡ none × lookup x ys ≡ some y
lookup-++⁻-some-disjoint x [] ys y d eq = inj₂ (refl , eq)
lookup-++⁻-some-disjoint x ((z , v) ∷ xs) ys y d eq
  with z ≟ x
… | yes refl rewrite ≟-yes x =
    inj₁ (eq , ∉dom→lookup-none ys (d x (here refl)))
… | no ¬z≡x rewrite ≟-no x z (λ p → ¬z≡x (sym p)) =
    lookup-++⁻-some-disjoint x xs ys y (L.Disjoint-⊆₁ L.⊆-∷ d) eq

lookup-++⁻-none :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ x (xs ys : List (K × V)) →
  lookup x (xs ++ ys) ≡ none →
  lookup x xs ≡ none × lookup x ys ≡ none
lookup-++⁻-none x xs ys eq =
  let x∉xs++ys = subst (x ∉_) (ListP.map-++ proj₁ xs ys) $
                 lookup-none→∉dom (xs ++ ys) eq in
  let x∉xs , x∉ys = L.∉-++⁻ (dom xs) (dom ys) x∉xs++ys in
  ∉dom→lookup-none xs x∉xs , ∉dom→lookup-none ys x∉ys

lookup-∉ :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ {k} (m : List (K × V)) →
  k ∉ map proj₁ m →
  lookup k m ≡ none
lookup-∉ {k = k} [] k∉dom = refl
lookup-∉ {k = k} ((k' , v) ∷ m) k∉dom with k ≟ k'
… | yes k≡k' = ⊥-elim (k∉dom (here k≡k'))
… | no ¬k≡k' = lookup-∉ m (∉-tail k∉dom)

lookup-∈-unique :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ {k} {v} {m : List (K × V)} →
  L.Unique (map proj₁ m) →
  (k , v) ∈ m →
  lookup k m ≡ some v
lookup-∈-unique {k = k} {v} {_ ∷ m} U-dom (here refl) rewrite ≟-yes k = refl
lookup-∈-unique {k = k} {v} {(k' , v') ∷ m} U-dom (there kv∈m) with k ≟ k'
… | yes refl = ⊥-elim (L.Unique-∈-∷ k (map proj₁ m) U-dom (∈-map proj₁ kv∈m))
… | no ¬k≡k' = lookup-∈-unique (L.Unique-tail U-dom) kv∈m

-- ∈-unique :
--   ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ {k} {v₁ v₂} {m : List (K × V)} →
--   L.Unique (map proj₁ m) →
--   (k , v₁) ∈ m →
--   (k , v₂) ∈ m →
--   v₁ ≡ v₂
-- ∈-unique = {!!}


-- TODO
-- this isn't correct: since f is only locally injective, it could make
-- a lookup that returns none to one that returns some
-- probably we need to say f is injective for a superset of the domain
-- and the identity otherwise
-- lookup-map-dom :
--   ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ {k}
--     (f : K → K) (m : List (K × V)) →
--   (f-inj : ∀ x y → x ∈ map proj₁ m → y ∈ map proj₁ m → f x ≡ f y → x ≡ y) →
--   lookup (f k) (map (L.map₁ f) m) ≡ lookup k m
-- lookup-map-dom {k = k} f []              f-inj = refl
-- lookup-map-dom {k = k} f ((k' , v') ∷ m) f-inj
--   with k ≟ k'
-- … | yes refl rewrite ≟-yes (f k) = refl
-- … | no ¬k≡k'
--   with f k ≟ f k'
-- … | no ¬fk≡fk' = lookup-map-dom {k = k} f m
--                    (λ x y x∈ y∈ eq → f-inj x y (there x∈) (there y∈) eq)
-- … | yes fk≡fk'
--   with k ∈? (k' ∷ map proj₁ m)
-- … | yes k∈dom = ⊥-elim (¬k≡k' (f-inj k k' k∈dom (here refl) fk≡fk'))
-- … | no ¬k∈dom = {!!}

lookup-map-dom :
  ∀ {ℓ₁ ℓ₂} {K : Set ℓ₁} {V : Set ℓ₂} ⦃ _ : DecEq K ⦄ {k}
    (f : K → K) (m : List (K × V)) →
  (f-inj : ∀ x y → x ∈ (k ∷ map proj₁ m) → y ∈ (k ∷ map proj₁ m) → f x ≡ f y → x ≡ y) →
  lookup (f k) (map (L.map₁ f) m) ≡ lookup k m
lookup-map-dom {k = k} f []              f-inj = refl
lookup-map-dom {k = k} f ((k' , v') ∷ m) f-inj
  with k ≟ k'
… | yes refl rewrite ≟-yes (f k) = refl
… | no ¬k≡k'
  with f k ≟ f k'
… | yes fk≡fk' = ⊥-elim (¬k≡k' (f-inj k k' (here refl) (there (here refl)) fk≡fk'))
… | no ¬fk≡fk' =
  lookup-map-dom {k = k} f m (λ x y x∈ y∈ eq → f-inj x y (sub x∈) (sub y∈) eq)
  where
    sub : k ∷ map proj₁ m L.⊆ k ∷ k' ∷ map proj₁ m
    sub (here refl) = here refl
    sub (there x∈) = there (there x∈)


