module BGV.Ren where

import Data.List.Properties as ListP
import Data.List.Relation.Unary.Any.Properties as AnyP
import Data.List.Relation.Unary.All.Properties as AllP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (_$_; _∘_; id; case_of_) renaming (_∋_ to _by_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import BGV.Context.SyntacticSplit using (LeftCtx; cct-⸴₁; cct-⸴₂; cct-[])
open import BGV.Id
open import BGV.Types
open import BGV.Multiplicities
open import BGV.Expressions
open import BGV.Context
open import BGV.Util.List
open import BGV.Util.Decidable
open import BGV.Util.FunMap public

-- Definitions -----------------------------------------------------------------

Ren : Set
Ren = Id → Id

variable
  ρ ρ₁ ρ₂ ρ₃ : Ren

infixl 7 _·ʳ_
infixl 6 _⋯ʳ_ _⋯ʳᶜ_ _⋯ˡ_

codʳ : List Id → Ren → List Id
codʳ dom ρ = List.map ρ dom

app-ren : Ren → (Id → Type → Ctx)
app-ren ρ x t = ρ x ∶ t

idʳ : Ren
idʳ = id

_⋯ʳ_ : Ctx → Ren → Ctx
Γ ⋯ʳ ρ = Γ >>=ᶜ app-ren ρ

_⋯ˡ_ : List Id → Ren → List Id
xs ⋯ˡ ρ = List.map ρ xs

_⋯ʳᶜ_ : CtxPat → Ren → CtxPat
C ⋯ʳᶜ ρ = C >>=ᶜᶜ app-ren ρ 

_·ʳ_ : Ren → Ren → Ren
(ρ₁ ·ʳ ρ₂) x = ρ₂ (ρ₁ x)

-- Properties ------------------------------------------------------------------

∈dom→∈cod : ∀ {x dom} ρ →
  x ∈ dom →
  ρ x ∈ codʳ dom ρ 
∈dom→∈cod {x} {dom} ρ x∈dom = ∈-map ρ x∈dom

⋯ʳ-id : ∀ Γ → Γ ⋯ʳ idʳ ≡ Γ
⋯ʳ-id · = refl
⋯ʳ-id (x ∶ t) = refl
⋯ʳ-id (Γ₁ ⸴[ o ] Γ₂) = cong₂ (_⸴[ o ]_) (⋯ʳ-id Γ₁) (⋯ʳ-id Γ₂)

⋯ʳ-·ʳ : ∀ Γ ρ₁ ρ₂ → Γ ⋯ʳ (ρ₁ ·ʳ ρ₂) ≡ Γ ⋯ʳ ρ₁ ⋯ʳ ρ₂
⋯ʳ-·ʳ · ρ₁ ρ₂ = refl
⋯ʳ-·ʳ (x ∶ t) ρ₁ ρ₂ = refl
⋯ʳ-·ʳ (Γ₁ ⸴[ o ] Γ₂) ρ₁ ρ₂ = cong₂ (_⸴[ o ]_) (⋯ʳ-·ʳ Γ₁ ρ₁ ρ₂) (⋯ʳ-·ʳ Γ₂ ρ₁ ρ₂)

⋯ʳᶜ-·ʳ : ∀ C ρ₁ ρ₂ → C ⋯ʳᶜ (ρ₁ ·ʳ ρ₂) ≡ C ⋯ʳᶜ ρ₁ ⋯ʳᶜ ρ₂
⋯ʳᶜ-·ʳ []            ρ₁ ρ₂ = refl
⋯ʳᶜ-·ʳ (C ⸴[ o ]₁ Γ) ρ₁ ρ₂ = cong₂ _⸴[ o ]₁_ (⋯ʳᶜ-·ʳ C ρ₁ ρ₂) (⋯ʳ-·ʳ Γ ρ₁ ρ₂)
⋯ʳᶜ-·ʳ (Γ ⸴[ o ]₂ C) ρ₁ ρ₂ = cong₂ _⸴[ o ]₂_ (⋯ʳ-·ʳ Γ ρ₁ ρ₂) (⋯ʳᶜ-·ʳ C ρ₁ ρ₂)
  

-- Local injectivity. This is necessary, because we usually don't have
-- general injectivity, because as soon as we extend the identity renaming,
-- with a non-identity mapping, general injectivity is lost.
Injectiveʳ : List Id → Ren → Set
Injectiveʳ xs ρ = ∀ x y → x ∈ xs → y ∈ xs → ρ x ≡ ρ y → x ≡ y

Injectiveʳ-tail : ∀ {x xs ρ} →
  Injectiveʳ (x ∷ xs) ρ →
  Injectiveʳ xs ρ
Injectiveʳ-tail inj x y x∈ y∈ ρx≡ρy = inj x y (there x∈) (there y∈) ρx≡ρy

Injectiveʳ-id : ∀ {xs} →
  Injectiveʳ xs idʳ
Injectiveʳ-id x y x∈ y∈ eq = eq

LocallyEq : List Id → Ren → Ren → Set
LocallyEq xs ρ₁ ρ₂ = ∀ x → x ∈ xs → ρ₁ x ≡ ρ₂ x

LocallyId : List Id → Ren → Set
LocallyId xs ρ = LocallyEq xs ρ idʳ

LocallyId-⊆ : ∀ {xs ys ρ} → xs ⊆ ys → LocallyId ys ρ → LocallyId xs ρ
LocallyId-⊆ xs⊆ys id-ρ x x∈xs = id-ρ x (xs⊆ys x∈xs)

LocallyEq-⊆ : ∀ {xs ys ρ₁ ρ₂} → xs ⊆ ys → LocallyEq ys ρ₁ ρ₂ → LocallyEq xs ρ₁ ρ₂
LocallyEq-⊆ xs⊆ys eq x x∈xs = eq x (xs⊆ys x∈xs)

Injecitveʳ-∈ : ∀ {ρ xs ys z} →
  xs ⊆ ys →
  Injectiveʳ ys ρ →
  z ∈ ys →
  ρ z ∈ map ρ xs →
  z ∈ xs
Injecitveʳ-∈ {xs = x ∷ xs} {z = z} xs⊆ys inj-ys-ρ z∈ys (here ρz≡ρx) =
  here (inj-ys-ρ z x z∈ys (xs⊆ys (here refl)) ρz≡ρx)
Injecitveʳ-∈ {xs = x ∷ xs} {z = z} xs⊆ys inj-ys-ρ z∈ys (there ρz∈ρxs) =
  there (Injecitveʳ-∈ (⊆-trans ⊆-∷ xs⊆ys) inj-ys-ρ z∈ys ρz∈ρxs)

Injecitveʳ-∉ : ∀ {ρ xs ys z} →
  xs ⊆ ys →
  Injectiveʳ ys ρ →
  z ∈ ys →
  z ∉ xs →
  ρ z ∉ map ρ xs
Injecitveʳ-∉ xs⊆ys inj-ys-ρ z∈ys z∉xs ρz∈ρxs =
  z∉xs (Injecitveʳ-∈ xs⊆ys inj-ys-ρ z∈ys ρz∈ρxs)

⋯ʳ-binds-eq : ∀ Γ ρ →
  binds (Γ ⋯ʳ ρ) ≡ map (map₁ ρ) (binds Γ)
⋯ʳ-binds-eq · ρ = refl
⋯ʳ-binds-eq (x ∶ t) ρ = refl
⋯ʳ-binds-eq (Γ₁ ⸴[ o ] Γ₂) ρ =
  let open ≡-Reasoning in
  begin
    binds (Γ₁ ⋯ʳ ρ) ++ binds (Γ₂ ⋯ʳ ρ)
  ≡⟨ cong₂ _++_ (⋯ʳ-binds-eq Γ₁ ρ) (⋯ʳ-binds-eq Γ₂ ρ) ⟩
    map (map₁ ρ) (binds Γ₁) ++ map (map₁ ρ) (binds Γ₂)
  ≡⟨ sym (ListP.map-++ (map₁ ρ) (binds Γ₁) (binds Γ₂)) ⟩
    map (map₁ ρ) (binds Γ₁ ++ binds Γ₂)
  ∎

⋯ʳ-binds : ∀ Γ ρ →
  (x , t) ∈ binds Γ →
  (ρ x , t) ∈ binds (Γ ⋯ʳ ρ)
⋯ʳ-binds (x ∶ t) ρ (here refl) = here refl
⋯ʳ-binds (Γ₁ ⸴[ o ] Γ₂) ρ xt∈Γ
  with AnyP.++⁻ (binds Γ₁) xt∈Γ
… | inj₁ xt∈Γ₁ = AnyP.++⁺ˡ $ ⋯ʳ-binds Γ₁ ρ xt∈Γ₁
… | inj₂ xt∈Γ₂ = AnyP.++⁺ʳ _ $ ⋯ʳ-binds Γ₂ ρ xt∈Γ₂

⋯ʳ-dom : ∀ Γ ρ →
  dom (Γ ⋯ʳ ρ) ≡ dom Γ ⋯ˡ ρ
⋯ʳ-dom · ρ = refl
⋯ʳ-dom (x ∶ t) ρ = refl
⋯ʳ-dom (Γ₁ ⸴[ o ] Γ₂) ρ =
  let open ≡-Reasoning in
  begin
    map proj₁ (binds (Γ₁ ⋯ʳ ρ) ++ binds (Γ₂ ⋯ʳ ρ))
  ≡⟨ ListP.map-++ proj₁ (binds (Γ₁ ⋯ʳ ρ)) (binds (Γ₂ ⋯ʳ ρ)) ⟩
    dom (Γ₁ ⋯ʳ ρ) ++ dom (Γ₂ ⋯ʳ ρ)
  ≡⟨ cong₂ _++_ (⋯ʳ-dom Γ₁ ρ) (⋯ʳ-dom Γ₂ ρ) ⟩
    (dom Γ₁ ⋯ˡ ρ) ++ (dom Γ₂ ⋯ˡ ρ)
  ≡⟨ sym (ListP.map-++ ρ (dom Γ₁) (dom Γ₂)) ⟩
    map ρ (dom Γ₁ ++ dom Γ₂)
  ≡⟨ cong (map ρ) (sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))) ⟩
    map ρ (map proj₁ (binds Γ₁ ++ binds Γ₂))
  ∎

⋯ˡ-unique : ∀ xs ρ →
  Injectiveʳ xs ρ →
  Unique xs →
  Unique (xs ⋯ˡ ρ)
⋯ˡ-unique (y ∷ xs) ρ inj-ρ U-xs x (here refl) (here refl) = refl
⋯ˡ-unique (y ∷ xs) ρ inj-ρ U-xs x (here refl) (there x∈₂) =
  let y∉xs = Unique-∈-∷ y xs U-xs in
  let ρy∉ρxs = Injecitveʳ-∉ ⊆-∷ inj-ρ (here refl) y∉xs in
  ⊥-elim (ρy∉ρxs x∈₂)
⋯ˡ-unique (y ∷ xs) ρ inj-ρ U-xs x (there x∈₁) (here refl) =
  let y∉xs = Unique-∈-∷ y xs U-xs in
  let ρy∉ρxs = Injecitveʳ-∉ ⊆-∷ inj-ρ (here refl) y∉xs in
  ⊥-elim (ρy∉ρxs x∈₁)
⋯ˡ-unique (y ∷ xs) ρ inj-ρ U-xs x (there x∈₁) (there x∈₂) =
  cong there (⋯ˡ-unique xs ρ (Injectiveʳ-tail inj-ρ) (Unique-tail U-xs) x x∈₁ x∈₂)

⋯ʳ-unique-dom : ∀ Γ ρ →
  Injectiveʳ (dom Γ) ρ →
  Unique (dom Γ) →
  Unique (dom (Γ ⋯ʳ ρ))
⋯ʳ-unique-dom Γ ρ inj-ρ U-Γ =
  subst Unique (sym (⋯ʳ-dom Γ ρ)) $
  ⋯ˡ-unique (dom Γ) ρ inj-ρ U-Γ

⋯ʳ-pres-Unrᶜ : ∀ Γ ρ → Unrᶜ Γ → Unrᶜ (Γ ⋯ʳ ρ)
⋯ʳ-pres-Unrᶜ · ρ unr-Γ = λ ()
⋯ʳ-pres-Unrᶜ (x ∶ t) ρ unr-Γ (here refl) = unr-Γ (here refl)
⋯ʳ-pres-Unrᶜ (Γ₁ ⸴[ o ] Γ₂) ρ unr-Γ =
  Unrᶜ-⸴ (Γ₁ ⋯ʳ ρ) o (Γ₂ ⋯ʳ ρ)
         (⋯ʳ-pres-Unrᶜ Γ₁ ρ (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ))
         (⋯ʳ-pres-Unrᶜ Γ₂ ρ (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ))

⋯ʳᶜ-pres-LeftCtx : ∀ C ρ → LeftCtx C → LeftCtx (C ⋯ʳᶜ ρ)
⋯ʳᶜ-pres-LeftCtx [] ρ cct-[] = cct-[]
⋯ʳᶜ-pres-LeftCtx (C ⸴[ o ]₁ Γ) ρ (cct-⸴₁ q C-left) =
  cct-⸴₁ (λ ()) (⋯ʳᶜ-pres-LeftCtx C ρ C-left)
⋯ʳᶜ-pres-LeftCtx (Γ ⸴[ o ]₂ C) ρ (cct-⸴₂ q C-left)
  with q refl
… | inj₁ o≡unordered = cct-⸴₂ (λ _ → inj₁ o≡unordered)
                              (⋯ʳᶜ-pres-LeftCtx C ρ C-left)
… | inj₂ unr-Γ       = cct-⸴₂ (λ _ → inj₂ (⋯ʳ-pres-Unrᶜ Γ ρ unr-Γ))
                              (⋯ʳᶜ-pres-LeftCtx C ρ C-left)

-- A renaming ρ that is locally injective for variables xs, can be
-- locally inverted, i.e. (invertʳ xs ρ) behaves like the identity
-- for all x ∈ xs.
invertʳ : List Id → Ren → Ren
invertʳ []       ρ = idʳ
invertʳ (x ∷ xs) ρ = (ρ x , x) ∷ᶠ invertʳ xs ρ

invertʳ-inverts : ∀ xs ρ →
  Injectiveʳ xs ρ →
  LocallyId xs (ρ ·ʳ invertʳ xs ρ)
invertʳ-inverts (x ∷ xs) ρ inj-ρ y y∈x∷xs with ρ x ≟ ρ y | y∈x∷xs
… | no ¬ρx≡ρy | here refl = ⊥-elim (¬ρx≡ρy refl)
… | no ¬ρx≡ρy | there y∈xs = invertʳ-inverts xs ρ (Injectiveʳ-tail inj-ρ) y y∈xs
… | yes ρx≡ρy | y∈x∷xs = inj-ρ x y (here refl) y∈x∷xs ρx≡ρy

Injectiveʳ-⊆ :
  xs ⊆ ys →
  Injectiveʳ ys ρ →
  Injectiveʳ xs ρ
Injectiveʳ-⊆ xs⊆ys inj x y x∈ y∈ = inj x y (xs⊆ys x∈) (xs⊆ys y∈)

invertʳ-∉-id : ∀ {xs x} ρ →
  x ∉ map ρ xs →
  invertʳ xs ρ x ≡ x
invertʳ-∉-id {[]} {x} ρ x∉xs = refl
invertʳ-∉-id {x' ∷ xs} {x} ρ x∉xs with ρ x' ≟ x
… | yes ρx'≡x = ⊥-elim (x∉xs (here (sym ρx'≡x)))
… | no ¬ρx'≡x = invertʳ-∉-id ρ (∉-tail x∉xs)

∈cod→∈dom : ∀ xs ρ →
  y ∈ codʳ xs ρ →
  ∃[ x ] x ∈ xs × ρ x ≡ y
∈cod→∈dom (x ∷ xs) ρ (here refl) = _ , here refl , refl
∈cod→∈dom (x ∷ xs) ρ (there y∈cod) =
  let (x , x∈xs , eq) = ∈cod→∈dom xs ρ y∈cod in
  x , there x∈xs , eq

record _%_⊢ʳ_ (ys xs : List Id) (ρ : Ren) : Set where
  field
    ⊢ʳ-∉xs-id   : ∀ {x} → x ∉ xs → ρ x ≡ x
    ⊢ʳ-ρxs⊎ys   : Disjoint (map ρ xs) ys
    ⊢ʳ-inj-ys-ρ : Injectiveʳ ys ρ
    ⊢ʳ-xs⊆ys    : xs ⊆ ys

  ⊢ʳ-inj-xs-ρ : Injectiveʳ xs ρ
  ⊢ʳ-inj-xs-ρ = Injectiveʳ-⊆ ⊢ʳ-xs⊆ys ⊢ʳ-inj-ys-ρ

  ⊢ʳ-xs⊎ρys : Disjoint xs (map ρ ys)
  ⊢ʳ-xs⊎ρys x x∈xs x∈ρys =
    let (x' , x'∈ys , ρx'≡x) = ∈cod→∈dom ys ρ x∈ρys in
    case x' ∈? xs of λ where
      (yes x'∈xs) →
        let ρx'∈ρxs = ∈dom→∈cod ρ x'∈xs in
        ⊢ʳ-ρxs⊎ys (ρ x') ρx'∈ρxs (⊢ʳ-xs⊆ys (subst (_∈ xs) (sym ρx'≡x) x∈xs))
      (no  x'∉xs) →
        let ρx'≡x' = ⊢ʳ-∉xs-id x'∉xs in
        let x≡x' = trans (sym ρx'≡x) ρx'≡x' in
        let x≡ρx = trans (sym ρx'≡x) (cong ρ (sym x≡x')) in
        ⊢ʳ-ρxs⊎ys (ρ x) (∈dom→∈cod ρ x∈xs) (⊢ʳ-xs⊆ys (subst (_∈ xs) x≡ρx x∈xs))

  ⊢ʳ-y∉ρxs : y ∈ ys → y ∉ xs → y ∉ map ρ xs
  ⊢ʳ-y∉ρxs {y = y} y∈ys y∉xs y∈ρxs =
    ⊢ʳ-ρxs⊎ys y y∈ρxs y∈ys
    -- let (x , x∈xs , ρx≡y) = ∈cod→∈dom xs ρ y∈ρxs in
    -- let ρy≡y = ⊢ʳ-∉xs-id y∉xs in
    -- let x≡y = ⊢ʳ-inj-ys-ρ x y (⊢ʳ-xs⊆ys x∈xs) y∈ys (trans ρx≡y (sym ρy≡y)) in
    -- ⊥-elim (⊢ʳ-xs⊎ρys x x∈xs (subst (_∈ map ρ ys) (sym x≡y) (⊆-map ρ ⊢ʳ-xs⊆ys y∈ρxs)))

  ⊢ʳ-ρys⊆ys++ρxs : map ρ ys ⊆ ys ++ map ρ xs
  ⊢ʳ-ρys⊆ys++ρxs {y} y∈ρ-ys =
    let (x , x∈ys , ρx≡y) = map-∈-inv ρ ys y∈ρ-ys in 
    case x ∈? xs of λ where
      (yes x∈xs) →
        let ρx∈ρ-xs = ∈-map ρ x∈xs in
        let y∈ρ-xs = subst (_∈ map ρ xs) ρx≡y ρx∈ρ-xs in
        AnyP.++⁺ʳ _ y∈ρ-xs 
      (no ¬x∈xs) →
        let ρx≡x = ⊢ʳ-∉xs-id ¬x∈xs in
        let x≡y = trans (sym ρx≡x) ρx≡y in
        let y∈ys = subst (_∈ _) x≡y x∈ys in
        AnyP.++⁺ˡ y∈ys

  ⊢ʳ-ρρ⊆ρ : ∀ zs → map ρ (map ρ zs) ⊆ map ρ zs
  ⊢ʳ-ρρ⊆ρ zs {x} x∈ρρxs =
    let (y , y∈ρxs , ρy≡x) = map-∈-inv ρ (map ρ zs) x∈ρρxs in
    let (z , z∈xs , ρz≡y) = map-∈-inv ρ zs y∈ρxs in
    case z ∈? xs of λ where
      (yes z∈dom-ρ) →
        let ρz∈ρ-dom-ρ = ∈-map ρ z∈dom-ρ in
        let ρz∉dom-ρ> = ⊢ʳ-ρxs⊎ys (ρ z) ρz∈ρ-dom-ρ in
        let y∉dom-ρ> = subst (_∉ _) ρz≡y ρz∉dom-ρ> in
        let ρy≡y = ⊢ʳ-∉xs-id (⊆-∉ ⊢ʳ-xs⊆ys y∉dom-ρ>) in
        let x∈ρxs = subst (_∈ _) (trans (sym ρy≡y) ρy≡x) y∈ρxs in
        x∈ρxs
      (no ¬z∈dom-ρ) →
        let ρz≡z = ⊢ʳ-∉xs-id ¬z∈dom-ρ in
        let y≡z = trans (sym ρz≡y) ρz≡z in
        let y≡x = trans (trans (sym ρz≡y) (cong ρ (sym y≡z))) ρy≡x in
        let x∈ρxs = subst (_∈ _) y≡x y∈ρxs in
        x∈ρxs

open _%_⊢ʳ_ public

⊢ʳ-id : ∀ {ys} →
  ys % [] ⊢ʳ idʳ
⊢ʳ-id = record
  { ⊢ʳ-∉xs-id   = λ _ → refl
  ; ⊢ʳ-ρxs⊎ys   = Disjoint-[]₁
  ; ⊢ʳ-inj-ys-ρ = Injectiveʳ-id
  ; ⊢ʳ-xs⊆ys    = []⊆ _
  }

⊢ʳ-∷₂ : ∀ {x xs ys ρ} →
  ρ x ∉ ys →
  x ∈ ys →
  ys % xs ⊢ʳ ρ →
  ys % (x ∷ xs) ⊢ʳ ρ
⊢ʳ-∷₂ {x} {xs} {ys} {ρ} ρx∉ys x∈ys ⊢ρ = record
  { ⊢ʳ-∉xs-id   = λ z∉x∷xs → ⊢ʳ-∉xs-id ⊢ρ (∉-tail z∉x∷xs) 
  ; ⊢ʳ-ρxs⊎ys   = Disjoint-∷₁ ρx∉ys (⊢ʳ-ρxs⊎ys ⊢ρ)
  ; ⊢ʳ-inj-ys-ρ = ⊢ʳ-inj-ys-ρ ⊢ρ
  ; ⊢ʳ-xs⊆ys    = λ where
      (here refl)  → x∈ys
      (there z∈ys) → ⊢ʳ-xs⊆ys ⊢ρ z∈ys
  }
  -- ; ⊢ʳ-∈doms→∉cod = λ where
  --     z (here refl)  ρz∈ys → ρx∉ys ρz∈ys
  --     z (there z∈xs) ρz∈ys → ⊢ʳ-xs⊎ρys ⊢ρ z z∈xs ρz∈ys

⊢ʳ-⊆-ys : ∀ {xs ys₁ ys₂ ρ} →
  ys₁ ⊆ ys₂ →
  xs ⊆ ys₁ →
  ys₂ % xs ⊢ʳ ρ →
  ys₁ % xs ⊢ʳ ρ
⊢ʳ-⊆-ys ys₁⊆ys₂ xs⊆ys₁ ⊢ρ = record
  { ⊢ʳ-∉xs-id   = ⊢ʳ-∉xs-id ⊢ρ
  ; ⊢ʳ-ρxs⊎ys   = Disjoint-⊆₂ ys₁⊆ys₂ (⊢ʳ-ρxs⊎ys ⊢ρ)
  ; ⊢ʳ-inj-ys-ρ = Injectiveʳ-⊆ ys₁⊆ys₂ (⊢ʳ-inj-ys-ρ ⊢ρ)
  ; ⊢ʳ-xs⊆ys    = xs⊆ys₁
  }

Unique-cod→Injectiveʳ : ∀ xs ρ →
  Unique (codʳ xs ρ) →
  Injectiveʳ xs ρ
Unique-cod→Injectiveʳ (x' ∷ xs) ρ U-cod x y (here refl) (here refl) ρx≡ρy =
  refl
Unique-cod→Injectiveʳ (_  ∷ xs) ρ U-cod x y (here refl) (there y∈xs) ρx≡ρy =
  ⊥-elim (Unique-∈-∷ (ρ y) _ (subst (λ ■ → Unique (■ ∷ map ρ xs)) ρx≡ρy U-cod) (∈dom→∈cod ρ y∈xs))
Unique-cod→Injectiveʳ (_ ∷ xs) ρ U-cod x y (there x∈xs) (here refl) ρx≡ρy =
  ⊥-elim (Unique-∈-∷ (ρ x) _ (subst (λ ■ → Unique (■ ∷ map ρ xs)) (sym ρx≡ρy) U-cod) (∈dom→∈cod ρ x∈xs))
Unique-cod→Injectiveʳ (x' ∷ xs) ρ U-cod x y (there x∈xs) (there y∈xs) ρx≡ρy =
  Unique-cod→Injectiveʳ xs ρ (Unique-tail U-cod) x y x∈xs y∈xs ρx≡ρy

⊢ʳ-⊇-ys : ∀ {xs ys₁ ys₂ ρ} →
  ys₁ ⊆ ys₂ →
  Disjoint (map ρ xs) ys₂ →
  Unique (map ρ ys₂) →
  ys₁ % xs ⊢ʳ ρ →
  ys₂ % xs ⊢ʳ ρ
⊢ʳ-⊇-ys ys₁⊆ys₂ d u ⊢ρ = record
  { ⊢ʳ-∉xs-id   = ⊢ʳ-∉xs-id ⊢ρ
  ; ⊢ʳ-ρxs⊎ys   = d
  ; ⊢ʳ-inj-ys-ρ = Unique-cod→Injectiveʳ _ _ u
  ; ⊢ʳ-xs⊆ys    = ⊆-trans (⊢ʳ-xs⊆ys ⊢ρ) ys₁⊆ys₂
  }

⊢ʳ-≈-ys : ∀ {xs ys₁ ys₂ ρ} →
  ys₁ ≈ˡ ys₂ →
  ys₂ % xs ⊢ʳ ρ →
  ys₁ % xs ⊢ʳ ρ
⊢ʳ-≈-ys ys₁≈ys₂ ⊢ρ =
  ⊢ʳ-⊆-ys (≈ˡ→⊆ ys₁≈ys₂) (⊆-trans (⊢ʳ-xs⊆ys ⊢ρ) (≈ˡ→⊆ (≈ˡ-sym ys₁≈ys₂))) ⊢ρ

⊢ʳ-≈-xs : ∀ {xs₁ xs₂ ys ρ} →
  xs₁ ≈ˡ xs₂ →
  ys % xs₁ ⊢ʳ ρ →
  ys % xs₂ ⊢ʳ ρ
⊢ʳ-≈-xs {ρ = ρ} xs₁≈xs₂ ⊢ρ = record
  { ⊢ʳ-∉xs-id   = λ x∉xs₁ → ⊢ʳ-∉xs-id ⊢ρ (⊆-∉ (≈ˡ→⊆ xs₁≈xs₂) x∉xs₁)
  ; ⊢ʳ-ρxs⊎ys   = Disjoint-≈₁ (≈ˡ-sym (≈ˡ-map ρ xs₁≈xs₂)) (⊢ʳ-ρxs⊎ys ⊢ρ)
  ; ⊢ʳ-inj-ys-ρ = ⊢ʳ-inj-ys-ρ ⊢ρ
  ; ⊢ʳ-xs⊆ys    = ⊆-trans (≈ˡ→⊆ (≈ˡ-sym xs₁≈xs₂)) (⊢ʳ-xs⊆ys ⊢ρ)
  }

-- ⋯ʳ-∉ : ∀ {ρ} Γ →
--   -- ys % xs ⊢ʳ ρ →
--   x ∉ map ρ (dom Γ) →
--   x ∉ dom Γ →
--   x ∉ dom (Γ ⋯ʳ ρ)
-- ⋯ʳ-∉ Γ ⊢ρ x∉Γ x∈ρΓ = {!!}

-- ⋯ʳ-∉ : ∀ Γ ρ →
--   x ∉ Map.cod ρ →
--   x ∉ dom Γ →
--   x ∉ dom (Γ ⋯ʳ ρ)
-- ⋯ʳ-∉ ·             ρ x∉ρ x∉Γ = x∉Γ
-- ⋯ʳ-∉ (x ∶ t)       ρ x∉ρ x∉Γ with Map.lookup x ρ in eq
-- … | none = x∉Γ
-- … | some ρx = λ { (here refl) → ⊥-elim (x∉ρ (Map.lookup-cod eq)) }
-- ⋯ʳ-∉ (Γ₁ ⸴[ o ] Γ₂) ρ x∉ρ x∉Γ y∈Γ
--   rewrite ListP.map-++ proj₁ (binds (Γ₁ ⋯ʳ ρ)) (binds (Γ₂ ⋯ʳ ρ))
--  with AnyP.++⁻ (dom (Γ₁ ⋯ʳ ρ)) y∈Γ
-- … | inj₁ y∈Γ₁ = let x∉Γ₁ = x∉Γ ∘ subst (_ ∈_) (sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))) ∘ AnyP.++⁺ˡ in
--                 ⋯ʳ-∉ Γ₁ ρ x∉ρ x∉Γ₁ y∈Γ₁
-- … | inj₂ y∈Γ₂ = let x∉Γ₂ = x∉Γ ∘ subst (_ ∈_) (sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))) ∘ AnyP.++⁺ʳ (dom Γ₁) in
--                 ⋯ʳ-∉ Γ₂ ρ x∉ρ x∉Γ₂ y∈Γ₂


-- Same as _%_⊢ʳ_ but without xs⊆ys
record _%_⊢ʳ⁻_ (ys xs : List Id) (ρ : Ren) : Set where
  field
    ⊢ʳ⁻-∉xs-id   : ∀ {x} → x ∉ xs → ρ x ≡ x
    ⊢ʳ⁻-ρxs⊎ys   : Disjoint (map ρ xs) ys
    ⊢ʳ⁻-inj-ys-ρ : Injectiveʳ ys ρ

open _%_⊢ʳ⁻_ public

⊢ʳ⁻-⊆-ys : ∀ {xs ys₁ ys₂ ρ} →
  ys₁ ⊆ ys₂ →
  ys₂ % xs ⊢ʳ⁻ ρ →
  ys₁ % xs ⊢ʳ⁻ ρ
⊢ʳ⁻-⊆-ys ys₁⊆ys₂ ⊢ρ = record
  { ⊢ʳ⁻-∉xs-id   = ⊢ʳ⁻-∉xs-id ⊢ρ
  ; ⊢ʳ⁻-ρxs⊎ys   = Disjoint-⊆₂ ys₁⊆ys₂ (⊢ʳ⁻-ρxs⊎ys ⊢ρ)
  ; ⊢ʳ⁻-inj-ys-ρ = Injectiveʳ-⊆ ys₁⊆ys₂ (⊢ʳ⁻-inj-ys-ρ ⊢ρ)
  }

invertʳ-inverts' : ∀ {xs ys ρ} →
  ys % xs ⊢ʳ ρ →
  LocallyId ys (ρ ·ʳ invertʳ xs ρ)
invertʳ-inverts' {xs} {ys} {ρ} ⊢ρ y y∈ys
  with y ∈? xs
… | yes y∈xs = invertʳ-inverts xs ρ (⊢ʳ-inj-xs-ρ ⊢ρ) y y∈xs
… | no ¬y∈xs
  with y ∈? map ρ xs
… | no ¬y∈ρxs = trans (cong (invertʳ xs ρ) (⊢ʳ-∉xs-id ⊢ρ ¬y∈xs))
                      (invertʳ-∉-id ρ ¬y∈ρxs)
… | yes y∈ρxs = ⊥-elim (⊢ʳ-y∉ρxs ⊢ρ y∈ys ¬y∈xs y∈ρxs)

LocallyEq-split : ∀ Γ₁ o Γ₂ ρ₁ ρ₂ →
  LocallyEq (dom (Γ₁ ⸴[ o ] Γ₂)) ρ₁ ρ₂ →
  LocallyEq (dom Γ₁) ρ₁ ρ₂ × LocallyEq (dom Γ₂) ρ₁ ρ₂
LocallyEq-split Γ₁ o Γ₂ ρ₁ ρ₂ eq =
  let eq' : LocallyEq (dom Γ₁ ++ dom Γ₂) ρ₁ ρ₂
      eq' = subst (λ ■ → LocallyEq ■ ρ₁ ρ₂)
                  (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))
                  eq in
  (λ x x∈Γ₁ → eq' x (AnyP.++⁺ˡ x∈Γ₁)) , λ x x∈Γ₂ → eq' x (AnyP.++⁺ʳ _ x∈Γ₂)

⋯ʳ-locally-eq : ∀ Γ ρ₁ ρ₂ → LocallyEq (dom Γ) ρ₁ ρ₂ → Γ ⋯ʳ ρ₁ ≡ Γ ⋯ʳ ρ₂
⋯ʳ-locally-eq · ρ₁ ρ₂ eq = refl
⋯ʳ-locally-eq (x ∶ t) ρ₁ ρ₂ eq = cong (_∶ t) (eq x (here refl))
⋯ʳ-locally-eq (Γ₁ ⸴[ o ] Γ₂) ρ₁ ρ₂ eq =
  let eq₁ , eq₂ = LocallyEq-split Γ₁ o Γ₂ ρ₁ ρ₂ eq in
  cong₂ (_⸴[ o ]_) (⋯ʳ-locally-eq Γ₁ ρ₁ ρ₂ eq₁)
                   (⋯ʳ-locally-eq Γ₂ ρ₁ ρ₂ eq₂)

⋯ʳᶜ-locally-eq : ∀ C ρ₁ ρ₂ → LocallyEq (dom (C [ · ])) ρ₁ ρ₂ → C ⋯ʳᶜ ρ₁ ≡ C ⋯ʳᶜ ρ₂
⋯ʳᶜ-locally-eq [] ρ₁ ρ₂ eq = refl
⋯ʳᶜ-locally-eq (C ⸴[ o ]₁ Γ) ρ₁ ρ₂ eq =
  let eq₁ , eq₂ = LocallyEq-split (C [ · ]) o Γ ρ₁ ρ₂ eq in
  cong₂ _⸴[ o ]₁_
        (⋯ʳᶜ-locally-eq C ρ₁ ρ₂ eq₁)
        (⋯ʳ-locally-eq Γ ρ₁ ρ₂ eq₂)
⋯ʳᶜ-locally-eq (Γ ⸴[ o ]₂ C) ρ₁ ρ₂ eq =
  let eq₁ , eq₂ = LocallyEq-split Γ o (C [ · ]) ρ₁ ρ₂ eq in
  cong₂ _⸴[ o ]₂_
        (⋯ʳ-locally-eq Γ ρ₁ ρ₂ eq₁)
        (⋯ʳᶜ-locally-eq C ρ₁ ρ₂ eq₂)

⋯ʳ-local-id : ∀ Γ ρ → LocallyId (dom Γ) ρ → Γ ⋯ʳ ρ ≡ Γ
⋯ʳ-local-id · ρ id-ρ = refl
⋯ʳ-local-id (x ∶ t) ρ id-ρ = cong (_∶ t) (id-ρ x (here refl))
⋯ʳ-local-id (Γ₁ ⸴[ o ] Γ₂) ρ id-ρ =
  let id-ρ' : LocallyId (dom Γ₁ ++ dom Γ₂) ρ
      id-ρ' = subst (λ ■ → LocallyId ■ ρ)
                    (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))
                    id-ρ in
  cong₂ (_⸴[ o ]_) (⋯ʳ-local-id Γ₁ ρ (LocallyId-⊆ ⊆-++₁' id-ρ'))
                   (⋯ʳ-local-id Γ₂ ρ (LocallyId-⊆ (⊆-++₂' _) id-ρ'))

⋯ʳ-ext : ∀ m Γ₁ Γ₂ ρ →
  ext m Γ₁ Γ₂ ⋯ʳ ρ ≡ ext m (Γ₁ ⋯ʳ ρ) (Γ₂ ⋯ʳ ρ)
⋯ʳ-ext ∞ Γ₁ Γ₂ ρ = refl
⋯ʳ-ext 𝟙 Γ₁ Γ₂ ρ = refl
⋯ʳ-ext ≻ Γ₁ Γ₂ ρ = refl
⋯ʳ-ext ≺ Γ₁ Γ₂ ρ = refl

Unrᶜ-⋯ʳ : ∀ Γ ρ →
  Unrᶜ Γ →
  Unrᶜ (Γ ⋯ʳ ρ)
Unrᶜ-⋯ʳ (x ∶ t) ρ unr-Γ (here refl) = unr-Γ (here refl)
Unrᶜ-⋯ʳ (Γ₁ ⸴[ o ] Γ₂) ρ unr-Γ y∈Γ with AnyP.++⁻ (binds (Γ₁ ⋯ʳ ρ)) y∈Γ
… | inj₁ y∈Γ₁ = Unrᶜ-⋯ʳ Γ₁ ρ (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ) y∈Γ₁
… | inj₂ y∈Γ₂ = Unrᶜ-⋯ʳ Γ₂ ρ (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ) y∈Γ₂

⋯ʳ-dist-[] : ∀ C Γ ρ →
  (C [ Γ ]) ⋯ʳ ρ ≡ (C ⋯ʳᶜ ρ) [ Γ ⋯ʳ ρ ]
⋯ʳ-dist-[] C Γ ρ = >>=ᶜ-dist-[] C Γ (app-ren ρ)

_↓ʳ_ : Ren → List Id → Ren
(ρ ↓ʳ xs) x with x ∈? xs
… | yes x∈xs = ρ x
… | no ¬x∈xs = x

↓ʳ-inv : ∀ ρ xs x →
  (ρ ↓ʳ xs) x ≡ x × x ∉ xs ⊎
  (ρ ↓ʳ xs) x ≡ ρ x × x ∈ xs
↓ʳ-inv ρ xs x with x ∈? xs
… | yes x∈xs = inj₂ (refl , x∈xs)
… | no ¬x∈xs = inj₁ (refl , ¬x∈xs)

↓ʳ-∈ : ∀ ρ {xs x} →
  x ∈ xs →
  (ρ ↓ʳ xs) x ≡ ρ x
↓ʳ-∈ ρ {xs} {x} x∈xs with x ∈? xs
… | yes _ = refl
… | no ¬x∈xs = ⊥-elim (¬x∈xs x∈xs)

↓ʳ-∉ : ∀ ρ {xs x} →
  x ∉ xs →
  (ρ ↓ʳ xs) x ≡ x
↓ʳ-∉ ρ {xs} {x} ¬x∈xs with x ∈? xs
… | yes x∈xs = ⊥-elim (¬x∈xs x∈xs)
… | no _ = refl 

↓ʳ-eq' : ∀ {xs} {ys} ρ →
  xs ⊆ ys →
  LocallyEq xs ρ (ρ ↓ʳ ys)
↓ʳ-eq' {x' ∷ xs} {ys} ρ xs⊆ys x (here refl)
  with x' ∈? ys
… | yes x'∈ys = refl
… | no ¬x'∈ys = ⊥-elim (¬x'∈ys (xs⊆ys (here refl)))
↓ʳ-eq' {x' ∷ xs} {ys} ρ xs⊆ys x (there x∈xs) = ↓ʳ-eq' ρ (⊆-trans ⊆-∷ xs⊆ys) x x∈xs

↓ʳ-eq : ∀ ρ xs →
  LocallyEq xs ρ (ρ ↓ʳ xs)
↓ʳ-eq ρ xs = ↓ʳ-eq' ρ ⊆-refl

↓ʳ-map : ∀ ρ xs →
  map (ρ ↓ʳ xs) xs ≡ map ρ xs
↓ʳ-map ρ xs = ListP.map-cong-local (All.tabulate (↓ʳ-∈ ρ))

↓ʳ-map' : ∀ ρ xs ys →
  ys ⊆ xs →
  map (ρ ↓ʳ xs) ys ≡ map ρ ys
↓ʳ-map' ρ xs ys ys⊆xs = ListP.map-cong-local (All.tabulate λ x∈ys → ↓ʳ-∈ ρ (ys⊆xs x∈ys))

⊢ʳ-↓ʳ : ∀ {xs ys ρ} zs →
  zs ⊆ xs →
  ys % xs ⊢ʳ ρ →
  ys % zs ⊢ʳ (ρ ↓ʳ zs)
⊢ʳ-↓ʳ {xs} {ys} {ρ} zs zs⊆xs ⊢ρ .⊢ʳ-∉xs-id {x} x∉zs with x ∈? zs
… | yes x∈zs  = ⊥-elim (x∉zs x∈zs)
… | no ¬x∈zs  = refl
⊢ʳ-↓ʳ {xs} {ys} {ρ} zs zs⊆xs ⊢ρ .⊢ʳ-ρxs⊎ys =
  subst (λ ■ → Disjoint ■ ys)
        (sym (↓ʳ-map ρ zs))
        (Disjoint-⊆₁ (⊆-map ρ zs⊆xs) (⊢ʳ-ρxs⊎ys ⊢ρ))
⊢ʳ-↓ʳ {xs} {ys} {ρ} zs zs⊆xs ⊢ρ .⊢ʳ-inj-ys-ρ x y x∈ys y∈ys ρ↓x≡ρ↓y
  with x ∈? zs | y ∈? zs
… | yes x∈zs | yes y∈zs = ⊢ʳ-inj-ys-ρ ⊢ρ x y x∈ys y∈ys ρ↓x≡ρ↓y
… | yes x∈zs | no ¬y∈zs =
  ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ (ρ x) (∈dom→∈cod ρ (zs⊆xs x∈zs)) (subst (_∈ ys) (sym ρ↓x≡ρ↓y) y∈ys))
… | no ¬x∈zs | yes y∈zs =
  ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ (ρ y) (∈dom→∈cod ρ (zs⊆xs y∈zs)) (subst (_∈ ys) ρ↓x≡ρ↓y x∈ys))
… | no ¬x∈zs | no ¬y∈zs = ρ↓x≡ρ↓y
⊢ʳ-↓ʳ {xs} {ys} {ρ} zs zs⊆xs ⊢ρ .⊢ʳ-xs⊆ys = ⊆-trans zs⊆xs (⊢ʳ-xs⊆ys ⊢ρ)

⊢ʳ⁻-↓ʳ' : ∀ {xs ys ρ} zs →
  ys % xs ⊢ʳ⁻ ρ →
  ys % (xs ∩ˡ zs) ⊢ʳ⁻ (ρ ↓ʳ zs)
⊢ʳ⁻-↓ʳ' {xs = xs} {ys = ys} {ρ = ρ} zs ⊢ρ = record
  { ⊢ʳ⁻-∉xs-id = λ {x} x∉xs∩zs →
      case ↓ʳ-inv ρ zs x of λ where
        (inj₁ (eq , x∉zs)) → eq
        (inj₂ (eq , x∈zs)) →
          case ∩ˡ-∉⁻ xs zs x∉xs∩zs of λ where
          (inj₁ x∉xs) →
            let open ≡-Reasoning in
            begin
              (ρ ↓ʳ zs) x
            ≡⟨ eq ⟩
              ρ x
            ≡⟨ ⊢ʳ⁻-∉xs-id ⊢ρ x∉xs ⟩
              x
            ∎
          (inj₂ x∉zs) → ⊥-elim (x∉zs x∈zs)
  ; ⊢ʳ⁻-ρxs⊎ys =
    Disjoint (map (ρ ↓ʳ zs) (xs ∩ˡ zs)) ys
      by (subst (λ ■ → Disjoint ■ ys) (sym (↓ʳ-map' ρ zs (xs ∩ˡ zs) (∩ˡ-⊆₂ xs zs))) $
    Disjoint (map ρ (xs ∩ˡ zs)) ys
      by (Disjoint-⊆₁ (⊆-map ρ (∩ˡ-⊆₁ xs zs)) $
    Disjoint (map ρ xs) ys
      by ⊢ʳ⁻-ρxs⊎ys ⊢ρ))
  ; ⊢ʳ⁻-inj-ys-ρ = λ x y x∈ys y∈ys eq →
      case ↓ʳ-inv ρ zs x of λ where
        (inj₁ (eqx , x∉zs)) →
          case ↓ʳ-inv ρ zs y of λ where
            (inj₁ (eqy , y∉zs)) →
              let open ≡-Reasoning in
              begin
                x
              ≡⟨ sym eqx ⟩
                (ρ ↓ʳ zs) x
              ≡⟨ eq ⟩
                (ρ ↓ʳ zs) y
              ≡⟨ eqy ⟩
                y
              ∎
            (inj₂ (eqy , y∈zs)) →
              let ρy≡x = trans (sym eqy) (trans (sym eq) eqx) in
              case y ∈? xs of λ where
                (yes y∈xs) →
                  let x∈ρxs = subst (_∈ _) ρy≡x (∈-map ρ y∈xs) in
                  ⊥-elim (⊢ʳ⁻-ρxs⊎ys ⊢ρ x x∈ρxs x∈ys)
                (no ¬y∈xs) →
                  let ρy≡y = ⊢ʳ⁻-∉xs-id ⊢ρ ¬y∈xs in
                  trans (sym ρy≡x) ρy≡y
        (inj₂ (eqx , x∈zs)) →
          case ↓ʳ-inv ρ zs y of λ where
            (inj₁ (eqy , y∉zs)) →
              let ρx≡y = trans (sym eqx) (trans eq eqy) in
              case x ∈? xs of λ where
                (yes x∈xs) →
                  let y∈ρys = subst (_∈ _) ρx≡y (∈-map ρ x∈xs) in
                  ⊥-elim (⊢ʳ⁻-ρxs⊎ys ⊢ρ y y∈ρys y∈ys)
                (no ¬x∈xs) →
                  let ρx≡x = ⊢ʳ⁻-∉xs-id ⊢ρ ¬x∈xs in
                  trans (sym ρx≡x) ρx≡y
            (inj₂ (eqy , y∈zs)) →
              ⊢ʳ⁻-inj-ys-ρ ⊢ρ x y x∈ys y∈ys $
                let open ≡-Reasoning in
                begin
                  ρ x
                ≡⟨ sym eqx ⟩
                  (ρ ↓ʳ zs) x
                ≡⟨ eq ⟩
                  (ρ ↓ʳ zs) y
                ≡⟨ eqy ⟩
                  ρ y
                ∎
  }

-- Renaming preserves ≲ --------------------------------------------------------

import BGV.Util.Graph as G

map-graph : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} → (A → B) → G.Graph A → G.Graph B
map-graph f (G.graph Node Edge label) = G.graph Node Edge (f ∘ label)

map-∅ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) →
  map-graph f G.∅ G.≃ G.∅
map-∅ f = record
  { iso = G.Type.≃-refl
  ; edges₁ = λ x y e → e
  ; edges₂ = λ x y e → e
  ; labels = λ ()
  }

map-pres-≲ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {g₁ g₂ : G.Graph A} →
  g₁ G.≲ g₂ →
  map-graph f g₁ G.≲ map-graph f g₂
map-pres-≲ f g₁≲g₂ = record
  { iso    = G.≲.iso g₁≲g₂
  ; edges  = G.≲.edges g₁≲g₂
  ; labels = λ x → cong f (G.≲.labels g₁≲g₂ x)
  }

map-pres-≃ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {g₁ g₂ : G.Graph A} →
  g₁ G.≃ g₂ →
  map-graph f g₁ G.≃ map-graph f g₂
map-pres-≃ f g₁≃g₂ = record 
  { iso    = G.≃.iso g₁≃g₂
  ; edges₁ = G.≃.edges₁ g₁≃g₂
  ; edges₂ = G.≃.edges₂ g₁≃g₂
  ; labels = λ x → cong f (G.≃.labels g₁≃g₂ x)
  }

map-pres-≲ᵍ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {g₁ g₂ : G.Graph A} →
  g₁ ≲ᵍ g₂ →
  map-graph f g₁ ≲ᵍ map-graph f g₂
map-pres-≲ᵍ f (g₁' , g₂' , g₁≃g₁' , g₁'≲g₂' , g₂'≃g₂) =
  map-graph f g₁' , map-graph f g₂' ,
  map-pres-≃ f g₁≃g₁' , map-pres-≲ f g₁'≲g₂' , map-pres-≃ f g₂'≃g₂

map-graph-∪ᵍ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g₁ g₂ : G.Graph A) →
  map-graph f g₁ G.∪ map-graph f g₂ G.≃ map-graph f (g₁ G.∪ g₂)
map-graph-∪ᵍ f g₁ g₂ = record
  { iso    = G.Type.≃-refl
  ; edges₁ = λ x y e → e
  ; edges₂ = λ x y e → e
  ; labels = λ where
      (inj₁ n₁) → refl
      (inj₂ n₂) → refl
  }

map-graph-+ᵍ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g₁ g₂ : G.Graph A) →
  map-graph f g₁ G.+ map-graph f g₂ G.≃ map-graph f (g₁ G.+ g₂)
map-graph-+ᵍ f g₁ g₂ = record
  { iso    = G.Type.≃-refl
  ; edges₁ = λ x y e → e
  ; edges₂ = λ x y e → e
  ; labels = λ where
      (inj₁ n₁) → refl
      (inj₂ n₂) → refl
  }

map-graph-⸴ᵍ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (g₁ g₂ : G.Graph A) →
  map-graph f g₁ ⸴ᵍ[ o ] map-graph f g₂ G.≃ map-graph f (g₁ ⸴ᵍ[ o ] g₂)
map-graph-⸴ᵍ {o = ordered}   f g₁ g₂ = map-graph-+ᵍ f g₁ g₂
map-graph-⸴ᵍ {o = unordered} f g₁ g₂ = map-graph-∪ᵍ f g₁ g₂

_⋯ʳˢ_ : SemCtx → Ren → SemCtx
(O , U) ⋯ʳˢ ρ = map-graph (map₁ ρ) O , map (map₁ ρ) U

⋯ʳ-⟦⟧ : ∀ Γ ρ → ⟦ Γ ⋯ʳ ρ ⟧ ≈ˢ ⟦ Γ ⟧ ⋯ʳˢ ρ
⋯ʳ-⟦⟧ · ρ = G.≃-sym (map-∅ (map₁ ρ)) , ≈ˡ-refl
⋯ʳ-⟦⟧ (x ∶ t) ρ with Unr? t
… | yes unr-t = G.≃-sym (map-∅ (map₁ ρ)) , ≈ˡ-refl
… | no ¬unr-t = G.≃-refl , ≈ˡ-refl
⋯ʳ-⟦⟧ (Γ₁ ⸴[ o ] Γ₂) ρ =
  ≈ˢ-trans (≈ˢ-⸴ (⋯ʳ-⟦⟧ Γ₁ ρ) (⋯ʳ-⟦⟧ Γ₂ ρ))
           (eq-g , eq-l)
  where
    eq-g =
      let open G.≃-Reasoning in
      begin
        map-graph (map₁ ρ) (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⸴ᵍ[ o ] map-graph (map₁ ρ) (SemCtx.ord-graph ⟦ Γ₂ ⟧)
      ≃⟨ map-graph-⸴ᵍ (map₁ ρ) _ _ ⟩
        map-graph (map₁ ρ) (SemCtx.ord-graph ⟦ Γ₁ ⟧ ⸴ᵍ[ o ] SemCtx.ord-graph ⟦ Γ₂ ⟧)
      ∎
    eq-l =
      let open ≈ˡ-Reasoning in
      begin
        map (map₁ ρ) (SemCtx.unr-set ⟦ Γ₁ ⟧ ++ SemCtx.unr-set ⟦ Γ₂ ⟧)
      ≡⟨ ListP.map-++ (map₁ ρ) (SemCtx.unr-set ⟦ Γ₁ ⟧) (SemCtx.unr-set ⟦ Γ₂ ⟧) ⟩
        map (map₁ ρ) (SemCtx.unr-set ⟦ Γ₁ ⟧) ++ map (map₁ ρ) (SemCtx.unr-set ⟦ Γ₂ ⟧)
      ∎

≲ˢ-⋯ʳ' : ∀ {γ₁ γ₂} ρ →
  γ₁ ≲ˢ γ₂ →
  (γ₁ ⋯ʳˢ ρ) ≲ˢ (γ₂ ⋯ʳˢ ρ)
≲ˢ-⋯ʳ' ρ (g₁≲g₂ , l₁⊆l₂) = map-pres-≲ᵍ (map₁ ρ) g₁≲g₂ , ⊆-map (map₁ ρ) l₁⊆l₂

≲ˢ-⋯ʳ : ∀ Γ₁ Γ₂ ρ →
  ⟦ Γ₁ ⟧ ≲ˢ ⟦ Γ₂ ⟧ →
  ⟦ Γ₁ ⋯ʳ ρ ⟧ ≲ˢ ⟦ Γ₂ ⋯ʳ ρ ⟧
≲ˢ-⋯ʳ Γ₁ Γ₂ ρ γ₁≲γ₂ =
  ≲ˢ-trans (≈ˢ→≲ˢ (⋯ʳ-⟦⟧ Γ₁ ρ))
           (≲ˢ-trans (≲ˢ-⋯ʳ' ρ γ₁≲γ₂)
                     (≈ˢ→≲ˢ (≈ˢ-sym (⋯ʳ-⟦⟧ Γ₂ ρ))))

≲-⋯ʳ : ∀ ρ →
  Γ₁ ≲ Γ₂ →
  (Γ₁ ⋯ʳ ρ) ≲ (Γ₂ ⋯ʳ ρ)
≲-⋯ʳ {Γ₁ = Γ₁} {Γ₂ = Γ₂} ρ (mk-≲ Γ₁≲Γ₂) = mk-≲ (≲ˢ-⋯ʳ Γ₁ Γ₂ ρ Γ₁≲Γ₂)

≲-single-⋯ʳ : ∀ {ρ : Ren} →
  Γ ≲ x ∶ t →
  (Γ ⋯ʳ ρ) ≲ ρ x ∶ t
≲-single-⋯ʳ {ρ = ρ} = ≲-⋯ʳ ρ

-- split-replace ---------------------------------------------------------------

split-replaceʳ : List Id → List Id → Ren → Ren → Ren → Ren → Ren → Ren
split-replaceʳ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' x
  with x ∈? codʳ dom₁ ρ₁
… | yes x∈cod₁ = (invertʳ dom₁ ρ₁ ·ʳ ρ' ·ʳ ρ₁') x
… | no ¬x∈cod₁
  with x ∈? codʳ dom₂ ρ₂
… | yes x∈cod₂ = (invertʳ dom₂ ρ₂ ·ʳ ρ' ·ʳ ρ₂') x
… | no ¬x∈cod₂ = ρ' x

split-replaceʳ-lem₁ : ∀ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' →
  Injectiveʳ dom₁ ρ₁ →
  LocallyEq dom₁ (ρ₁ ·ʳ split-replaceʳ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ') (ρ' ·ʳ ρ₁')
split-replaceʳ-lem₁ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' inj x x∈dom₁
  with ρ₁ x ∈? codʳ dom₁ ρ₁
… | yes ρx∈cod₁ = cong (ρ' ·ʳ ρ₁') (invertʳ-inverts dom₁ ρ₁ inj x x∈dom₁)
… | no ¬ρx∈cod₁ = ⊥-elim (¬ρx∈cod₁ (∈dom→∈cod ρ₁ x∈dom₁))

ext-loc-eq : ∀ {xs ys} ρ₁ ρ₂ →
  xs ⊆ ys →
  (∀ y → y ∈ ys → y ∉ xs → ρ₁ y ≡ ρ₂ y) →
  LocallyEq xs ρ₁ ρ₂ →
  LocallyEq ys ρ₁ ρ₂
ext-loc-eq {xs = xs} {ys = ys} ρ₁ ρ₂ xs⊆ys p eq y y∈ys
  with y ∈? xs
… | yes y∈xs = eq y y∈xs
… | no ¬y∈xs = p y y∈ys ¬y∈xs

split-replaceʳ-lem₂ : ∀ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' →
  Disjoint (codʳ dom₁ ρ₁) (codʳ dom₂ ρ₂) →
  Injectiveʳ dom₂ ρ₂ →
  LocallyEq dom₂ (ρ₂ ·ʳ split-replaceʳ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ')  (ρ' ·ʳ ρ₂')
split-replaceʳ-lem₂ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' D-cod inj x x∈dom₂
  with ρ₂ x ∈? codʳ dom₁ ρ₁
… | yes ρx∈cod₁ = ⊥-elim (D-cod (ρ₂ x) ρx∈cod₁ (∈dom→∈cod ρ₂ x∈dom₂))
… | no ¬ρx∈cod₁
  with ρ₂ x ∈? codʳ dom₂ ρ₂
… | yes ρx∈cod₂ = cong (ρ' ·ʳ ρ₂') (invertʳ-inverts dom₂ ρ₂ inj x x∈dom₂) -- 
… | no ¬ρx∈cod₂ = ⊥-elim (¬ρx∈cod₂ (∈dom→∈cod ρ₂ x∈dom₂))

split-replaceʳ-∉cod : ∀ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' x →
  x ∉ codʳ dom₁ ρ₁ →
  x ∉ codʳ dom₂ ρ₂ →
  split-replaceʳ dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' x ≡ ρ' x
split-replaceʳ-∉cod dom₁ dom₂ ρ₁ ρ₂ ρ₁' ρ₂' ρ' x x∉cod₁ x∉cod₂
  with x ∈? codʳ dom₁ ρ₁
… | yes x∈cod₁ = ⊥-elim (x∉cod₁ x∈cod₁)
… | no ¬x∈cod₁
  with x ∈? codʳ dom₂ ρ₂
… | yes x∈cod₂ = ⊥-elim (x∉cod₂ x∈cod₂)
… | no ¬x∈cod₂ = refl

-- invertʳ-inverts' : ∀ xs ys ρ →
--   xs ⊆ ys →
--   Injectiveʳ ys ρ →
--   Disjoint xs (codʳ ys ρ) →
--   LocallyId (ys \\ xs) ρ →
--   LocallyId ys (ρ ·ʳ invertʳ xs ρ)

split-replaceʳ-lem₁x : ∀ xs ys dom-ρ ρ₁' ρ₂' ρ₁ ρ₂ ρ →
  ys % xs ⊢ʳ ρ₁' →
  ys % xs ⊢ʳ ρ₂' →
  ys % dom-ρ ⊢ʳ ρ →
  (ys ++ codʳ dom-ρ ρ) % map ρ xs ⊢ʳ ρ₁ →
  LocallyEq ys (ρ₁' ·ʳ split-replaceʳ xs xs ρ₁' ρ₂' ρ₁ ρ₂ ρ) (ρ ·ʳ ρ₁)
split-replaceʳ-lem₁x xs ys dom-ρ ρ₁' ρ₂' ρ₁ ρ₂ ρ ⊢ρ₁' ⊢ρ₂' ⊢ρ ⊢ρ₁ y y∈ys
  with ρ₁' y ∈? codʳ xs ρ₁'
… | yes ρ₁'y∈ρ₁'xs = cong (ρ ·ʳ ρ₁) (invertʳ-inverts' ⊢ρ₁' y y∈ys)
… | no ¬ρ₁'y∈ρ₁'xs
  with y ∈? xs
… | yes y∈xs = ⊥-elim (¬ρ₁'y∈ρ₁'xs (∈-map ρ₁' y∈xs))
… | no ¬y∈xs
  with ρ₁' y ∈? codʳ xs ρ₂'
… | yes ρ₁'y∈ρ₂'xs =
  let ρ₁'y≡y = ⊢ʳ-∉xs-id ⊢ρ₁' ¬y∈xs in
  ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ₂' y (subst (_∈ _) ρ₁'y≡y ρ₁'y∈ρ₂'xs) y∈ys)
… | no ¬ρ₁'y∈ρ₂'xs
  rewrite ⊢ʳ-∉xs-id ⊢ρ₁' ¬y∈xs
  rewrite ⊢ʳ-∉xs-id ⊢ρ₁ {x = ρ y} (Injecitveʳ-∉ (⊢ʳ-xs⊆ys ⊢ρ₁') (⊢ʳ-inj-ys-ρ ⊢ρ) y∈ys ¬y∈xs)
  = refl

split-replaceʳ-lem₂x : ∀ xs ys dom-ρ ρ₁' ρ₂' ρ₁ ρ₂ ρ →
  ys % xs ⊢ʳ ρ₁' →
  ys % xs ⊢ʳ ρ₂' →
  ys % dom-ρ ⊢ʳ ρ →
  (ys ++ codʳ dom-ρ ρ) % map ρ xs ⊢ʳ ρ₂ →
  Disjoint (codʳ xs ρ₁') (codʳ xs ρ₂') →
  LocallyEq ys (ρ₂' ·ʳ split-replaceʳ xs xs ρ₁' ρ₂' ρ₁ ρ₂ ρ) (ρ ·ʳ ρ₂)
split-replaceʳ-lem₂x xs ys dom-ρ ρ₁' ρ₂' ρ₁ ρ₂ ρ ⊢ρ₁' ⊢ρ₂' ⊢ρ ⊢ρ₂ d-cod₁-cod₂ y y∈ys
  with ρ₂' y ∈? codʳ xs ρ₁' | y ∈? xs
… | yes ρ₂'y∈ρ₁'xs | yes y∈xs =
  ⊥-elim (d-cod₁-cod₂ (ρ₂' y) ρ₂'y∈ρ₁'xs (∈-map ρ₂' y∈xs))
… | yes ρ₂'y∈ρ₁'xs | no ¬y∈xs =
  let ρ₂'y≡y = ⊢ʳ-∉xs-id ⊢ρ₂' ¬y∈xs in
  ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ₁' y (subst (_∈ _) ρ₂'y≡y ρ₂'y∈ρ₁'xs) y∈ys)
split-replaceʳ-lem₂x xs ys dom-ρ ρ₁' ρ₂' ρ₁ ρ₂ ρ ⊢ρ₁' ⊢ρ₂' ⊢ρ ⊢ρ₂ d-cod₁-cod₂ y y∈ys | no ¬ρ₂'y∈ρ₁'xs | yes y∈xs
  with ρ₂' y ∈? codʳ xs ρ₂'
… | yes ρ₂'y∈ρ₂'xs = cong (ρ ·ʳ ρ₂) (invertʳ-inverts' ⊢ρ₂' y y∈ys)
… | no ¬ρ₂'y∈ρ₂'xs = ⊥-elim (¬ρ₂'y∈ρ₂'xs (∈-map ρ₂' y∈xs))
split-replaceʳ-lem₂x xs ys dom-ρ ρ₁' ρ₂' ρ₁ ρ₂ ρ ⊢ρ₁' ⊢ρ₂' ⊢ρ ⊢ρ₂ d-cod₁-cod₂ y y∈ys | no ¬ρ₂'y∈ρ₁'xs | no ¬y∈xs
  with ρ₂' y ∈? codʳ xs ρ₂'
… | yes ρ₂'y∈ρ₂'xs =
  cong (ρ ·ʳ ρ₂) (invertʳ-inverts' ⊢ρ₂' y y∈ys)
… | no ¬ρ₂'y∈ρ₂'xs
  rewrite ⊢ʳ-∉xs-id ⊢ρ₂' ¬y∈xs
  rewrite ⊢ʳ-∉xs-id ⊢ρ₂ {x = ρ y} (Injecitveʳ-∉ (⊢ʳ-xs⊆ys ⊢ρ₁') (⊢ʳ-inj-ys-ρ ⊢ρ) y∈ys ¬y∈xs)
  = refl


