open import PrefixStripping.Prelude
open Relation.Binary

module PrefixStripping.Decide {𝕋 END : Set} (_≟ᵀ_ : DecidableEquality 𝕋) (_≟E_ : DecidableEquality END) where

open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.Maybe using (just; nothing; Is-just; Is-nothing)
open import Data.Maybe.Relation.Unary.All as All? using (just; nothing) renaming (All to All?)
open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected)
open import Data.Maybe.Relation.Binary.Pointwise as PW using (Pointwise)
open import Data.Unit using (⊤)

open import PrefixStripping.Syntax

open import PrefixStripping.Sessions.Equivalence 𝕋 as In hiding (refl; trans; sym)
open import PrefixStripping.Decide.Universe _≟ᵀ_ _≟E_
import PrefixStripping.Decide.Soundness _≟ᵀ_ _≟E_ as Soundness
import PrefixStripping.Decide.Coinduction _≟ᵀ_ _≟E_ as Seen

open Nat using () renaming (suc-injective to suc⁻¹)


infix 4 _⊢_≰ₚ_

_⊢_≰ₚ_ : List ⊢𝒰 → ◇-Rel _
A ⊢ ⊢p ≰ₚ ⊢s = ∀ r → ¬ A ⊢ ⊢p % ⊢s ＝ r

module Core (𝒰⁰ : 𝒰) where
  open Seen 𝒰⁰ public
  open Counter using (_⊕_; lookupOrInsert)
  open Hyp

  open import Data.List.Membership.Setoid hypSetoid renaming (_∈_ to _⟨∈⟩_; _∉_ to _⟨∉⟩_)
  open import Data.List.Membership.Propositional as In
  open Connected
  open Pointwise

  import Data.List.Membership.Setoid.Properties as ⟨∈⟩

  ⟨∈⟩⇒∈ : (x : Hyp) {A : List Hyp} → x ⟨∈⟩ A → ⊢⟨ x ⟩ ∈ ⊢⟨ A ⟩*
  ⟨∈⟩⇒∈ x x∈ = ⟨∈⟩.∈-map⁺
    (DecSetoid.setoid hypDecSetoid)
    (Eq.setoid ⊢𝒰)
    (λ{ {mkHyp a _} {mkHyp b _} refl → cong₂ _%_ (⊢-irr (⊢𝒰.p a) (⊢𝒰.p b)) (⊢-irr (⊢𝒰.s a) (⊢𝒰.s b)) })
    {v = x}
    x∈

  ⟨∈⟩⇐∈ : (x : Hyp) {A : List Hyp} → ⊢⟨ x ⟩ ∈ ⊢⟨ A ⟩* → x ⟨∈⟩ A
  ⟨∈⟩⇐∈ x x∈ with ⟨∈⟩.∈-map⁻ (DecSetoid.setoid hypDecSetoid) (Eq.setoid ⊢𝒰) x∈
  ... | x′ , x′∈ , eq with ux ← u x rewrite eq = x′∈

  data Θ-Storable : Pred 𝒰 0ℓ where
    Θ-♯ : ∀ {T₁ T₂ : 𝕋} → Θ-Storable (⁉₁ ♯ T₁ ▸ p % ⁉₂ ♯ T₂ ▸ s)
    Θ-⋆ : Θ-Storable (⁉₁ ⟨ p₁ ⨟ p₂ ⟩ % ⁉₂ ⟨ s₁ ⨟ s₂ ⟩)

  Θ-Stored* : Pred (List ⊢𝒰) _
  Θ-Stored* = All (Θ-Storable ∘ 𝒰⌊_⌋)

  Θ-Stored⟨_⟩* : Pred (List Hyp) _
  Θ-Stored⟨ A ⟩* = Θ-Stored* ⊢⟨ A ⟩*

  Unique : List ⊢𝒰 → ⊢ p → ⊢ s → ⊢ℝ → Set _
  Unique A ⊢p ⊢s r = ∀ r′ → A ⊢ ⊢p % ⊢s ＝ r′ → r ≃ᴿ r′

  Success : List ⊢𝒰 → ◇-Rel _
  Success A ⊢p ⊢s = ∃ λ r → A ⊢ ⊢p % ⊢s ＝ r × All? (λ _ → ∃□ ⊢p) r × Unique A ⊢p ⊢s r

  infix 4 _⊢_≤?_

  _⊢_≤?_ : List ⊢𝒰 → ◇-Rel _
  A ⊢ ⊢p ≤? ⊢s = Success A ⊢p ⊢s ⊎ Fail′ ⊢p ⊢s × ¬ (∃ λ r → A ⊢ ⊢p % ⊢s ＝ r)

  %⁻¹-μˡ : ∀ {p r} (⊢p : ⊢ p) (pᶜ : ⊢ᶜ p) →
    Θ-Stored* A →
    A ⊢ ⊢μ ⊢p pᶜ % ⊢s ＝ r →
    A ⊢ ⊢-unfold ⊢p pᶜ % ⊢s ＝ r
  %⁻¹-μˡ ⊢p pᶜ Θ-st (%-μˡ x) = x
  %⁻¹-μˡ ⊢p pᶜ Θ-st (%-μʳ x) = %-μʳ (%⁻¹-μˡ ⊢p pᶜ Θ-st x)
  %⁻¹-μˡ ⊢p pᶜ Θ-st (hyp x)  = case All.lookup Θ-st x of λ()

  %⁻¹-μʳ : ∀ {s r} (⊢s : ⊢ s) (sᶜ : ⊢ᶜ s) →
    Θ-Stored* A →
    A ⊢ ⊢p % ⊢μ ⊢s sᶜ ＝ r →
    A ⊢ ⊢p % ⊢-unfold ⊢s sᶜ ＝ r
  %⁻¹-μʳ ⊢s sᶜ Θ-st (%-□  eq) = %-□ (In.trans (In.sym (In.≃-μ ⊢s sᶜ)) eq)
  %⁻¹-μʳ ⊢s sᶜ Θ-st (%-μˡ x)  = %-μˡ (%⁻¹-μʳ ⊢s sᶜ Θ-st x)
  %⁻¹-μʳ ⊢s sᶜ Θ-st (%-μʳ x)  = x
  %⁻¹-μʳ ⊢s sᶜ Θ-st (hyp x)   = case All.lookup Θ-st x of λ()

  buildHyp : ∀ {A} (H : Hyp) → Θ-Storable 𝒰⌊ u H ⌋ → H ⟨∈⟩ A → Success ⊢⟨ A ⟩* (⊢𝒰.p (u H)) (⊢𝒰.s (u H))
  buildHyp H x H∈ = -, hyp (⟨∈⟩⇒∈ H H∈) , nothing , λ where
    _ (%-♯ ∉Θ _)     → contradiction (⟨∈⟩⇒∈ H H∈) ∉Θ
    _ (%-⋆ ∉Θ _ _ _) → contradiction (⟨∈⟩⇒∈ H H∈) ∉Θ
    _ (hyp x)        → nothing

  %-⋆-uniq-⊥ˡ :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    ∀ {r} →
    H ∉ A →
    Unique (H ∷ A) ⊢p₁ ⊢s₁ nothing →
    Unique (H ∷ A) ⊢p₂ ⊢s₂ r →
    Unique A (⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩) (⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩) r
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ eq)) = ≃ᴿ-trans (u₂ _ %₂) eq
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ (just eq))) = case u₁ _ %₁ of λ()
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ nothing)) = u₂ _ %₂
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) = case u₁ _ %₁ of λ()
  %-⋆-uniq-⊥ˡ H∉ u₁ u₂ _ (hyp H∈) = contradiction H∈ H∉

  %-⋆-uniq-⊥ʳ :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    ∀ {r} →
    H ∉ A →
    Unique (H ∷ A) ⊢p₁ ⊢s₁ r →
    Unique (H ∷ A) ⊢p₂ ⊢s₂ nothing →
    Unique A (⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩) (⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩) r
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ (just x))) = case u₂ _ %₂ of λ()
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ nothing)) = u₁ _ %₁
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ eq)) = ≃ᴿ-trans (u₁ _ %₁) eq
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ _ (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) = case u₂ _ %₂ of λ()
  %-⋆-uniq-⊥ʳ H∉ u₁ u₂ _ (hyp H∈) = contradiction H∈ H∉

  %-⋆-uniq-just :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    ∀ {r₁ r₂} →
    H ∉ A →
    Unique (H ∷ A) ⊢p₁ ⊢s₁ (just r₁) →
    Unique (H ∷ A) ⊢p₂ ⊢s₂ (just r₂) →
    Unique A (⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩) (⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩) (just r₁)
  %-⋆-uniq-just H∉ u₁ u₂ _ (%-⋆ _ p%s₁ p%s₂ (⊔-⊥ˡ eq)) = case u₁ _ p%s₁ of λ()
  %-⋆-uniq-just H∉ u₁ u₂ _ (%-⋆ _ p%s₁ p%s₂ (⊔-⊥ʳ eq)) = case u₂ _ p%s₂ of λ()
  %-⋆-uniq-just H∉ u₁ u₂ _ (%-⋆ _ p%s₁ p%s₂ (⊔-≃ eq₁ eq₂)) = just (In.trans (PW.drop-just (u₁ _ p%s₁)) eq₁)
  %-⋆-uniq-just H∉ u₁ u₂ _ (hyp H∈) = contradiction H∈ H∉

  %-⋆-r≃ :
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    ∀ {r} →
    H ∉ A →
    Unique (H ∷ A) ⊢p₁ ⊢s₁ (just (-, ⊢r₁)) →
    Unique (H ∷ A) ⊢p₂ ⊢s₂ (just (-, ⊢r₂)) →
    A ⊢ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ＝ r →
    ⊢r₁ ≃ ⊢r₂
  %-⋆-r≃ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ˡ x)) = case u₁ _ %₁ of λ()
  %-⋆-r≃ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-⊥ʳ x)) = case u₂ _ %₂ of λ()
  %-⋆-r≃ H∉ u₁ u₂ (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) =
    In.trans (PW.drop-just (u₁ _ %₁)) $
    In.trans eq₁ $
    In.trans eq₂ $
    In.sym (PW.drop-just (u₂ _ %₂))
  %-⋆-r≃ H∉ u₁ u₂ (hyp H∈) = contradiction H∈ H∉

  run : ∀ {A ℓ} (c : A ⊕ ℓ) (Θ-st : Θ-Stored⟨ A ⟩*) (⊢p : ⊢ p) (⊢s : ⊢ s)
    → p % s ⊑ᵤ 𝒰⁰
    → ⊢⟨ A ⟩* ⊢ ⊢p ≤? ⊢s

  run-unfold : ∀ {A ℓ} (Θ : A ⊕ ℓ) (ℓᵖ ℓˢ : ℕ)
    → .(μLeaders p ≡ ℓᵖ)
    → .(μLeaders s ≡ ℓˢ)
    → Θ-Stored⟨ A ⟩*
    → (⊢p : ⊢ p) (⊢s : ⊢ s)
    → p % s ⊑ᵤ 𝒰⁰
    → ⊢⟨ A ⟩* ⊢ ⊢p ≤? ⊢s

  run-hnf : ∀ {A ℓ} (Θ : A ⊕ ℓ)
    → .(μLeaders p ≡ 0)
    → .(μLeaders s ≡ 0)
    → Θ-Stored⟨ A ⟩*
    → (⊢p : ⊢ p) (⊢s : ⊢ s)
    → p % s ⊑ᵤ 𝒰⁰
    → ⊢⟨ A ⟩* ⊢ ⊢p ≤? ⊢s

  run Θ = run-unfold Θ _ _ refl refl

  run-unfold Θ 0 0 eqᵖ eqˢ Θ-st ⊢p ⊢s ps⊑ =
    run-hnf Θ eqᵖ eqˢ Θ-st ⊢p ⊢s ps⊑
  run-unfold Θ 0 (suc ℓˢ) eqᵖ eqˢ Θ-st ⊢p (⊢μ s sᶜ) ps⊑ =
    Sum.map
      (Π.map₂ (Π.map %-μʳ (Π.map₂ λ r≃ _ p%s → r≃ _ (%⁻¹-μʳ s sᶜ Θ-st p%s))))
      (Π.map
        (λ fail eq → fail (In.trans eq (In.≃-μ s sᶜ)))
        (λ fail → fail ∘ Π.map₂ (%⁻¹-μʳ s sᶜ Θ-st)))
      (run-unfold Θ 0 ℓˢ eqᵖ (trans (μLeaders-⋯ₛ-0↦ s sᶜ) (suc⁻¹ eqˢ)) Θ-st ⊢p (⊢-unfold s sᶜ) (⊑ᵤ⁻¹-μˢ ps⊑))
  run-unfold Θ (suc ℓᵖ) ℓˢ eqᵖ eqˢ Θ-st (⊢μ p pᶜ) ⊢s ps⊑ =
    Sum.map
      (Π.map₂ (Π.map %-μˡ (Π.map
        (All?.map (cong-∃□ (In.sym (≃-μ p pᶜ))))
        (λ r≃ _ p%s → r≃ _ (%⁻¹-μˡ p pᶜ Θ-st p%s)))))
      (Π.map
        (λ fail eq → fail (In.trans (In.sym (In.≃-μ◇ p pᶜ)) eq))
        (λ fail → fail ∘ Π.map₂ (%⁻¹-μˡ p pᶜ Θ-st)))
      (run-unfold Θ ℓᵖ ℓˢ (trans (μLeaders-⋯ₛ-0↦ p pᶜ) (suc⁻¹ eqᵖ)) eqˢ Θ-st (⊢-unfold p pᶜ) ⊢s (⊑ᵤ⁻¹-μᵖ ps⊑))

  run-hnf Θ ¬μᵖ ¬μˢ Θ-st ⊢□ s ps⊑ = inj₁ $ -, %-□ In.refl , just ∃□-□ , λ where
    _ (%-□ x) → just x
    _ (hyp x) → case All.lookup Θ-st x of λ()

  run-hnf Θ ¬μᵖ ¬μˢ Θ-st p⁰@(⊢♯ ⁉₁ · T₁ ▸ p) s⁰@(⊢♯ ⁉₂ · T₂ ▸ s) ps⊑
    using H ← mkHyp (p⁰ % s⁰) ps⊑
    with Counter.lookupOrInsert Θ H
  ... | inj₁ H∈ = inj₁ (buildHyp H Θ-♯ H∈)
  ... | inj₂ (-, refl , Θ′ , H∉)
    with ⁉₁ ≟⁉ ⁉₂
  ... | no ⁉≠ = inj₂ ((λ eq → case eq 1 of λ{ refl → ⁉≠ refl }) , λ where
    (-, %-♯ H∉ p%s) → ⁉≠ refl
    (-, hyp x)      → H∉ (⟨∈⟩⇐∈ H x))
  ... | yes refl
    with T₁ ≟ᵀ T₂
  ... | no T≠ = inj₂ ((λ eq → case eq 1 of λ{ refl → T≠ refl }) , λ where
    (-, %-♯ H∉ p%s) → T≠ refl
    (-, hyp x)      → H∉ (⟨∈⟩⇐∈ H x))
  ... | yes refl
    with run Θ′ (Θ-♯ ∷ Θ-st) p s (⊑ᵤ⁻¹-♯ ps⊑)
  ... | inj₁ (-, p%s , fin? , uniq) = inj₁ $ -, %-♯ (H∉ ∘ ⟨∈⟩⇐∈ H) p%s , All?.map (∃□-step⁻¹ step-♯) fin? , λ where
    _ (%-♯ H∉ p%s′) → uniq _ p%s′
    _ (hyp H∈)      → contradiction (⟨∈⟩⇐∈ H H∈) H∉
  ... | inj₂ ¬p%s = inj₂ (proj₁ ¬p%s ∘ ≃⁻¹-♯ , λ where
    (-, %-♯ H∉ p%s) → proj₂ ¬p%s (-, p%s)
    (-, hyp H∈)     → H∉ (⟨∈⟩⇐∈ H H∈))

  run-hnf Θ ¬μᵖ ¬μˢ Θ-st p⁰@(⊢ ⁉₁ ⋆⟨ p₁ ⨟ p₂ ⟩) s⁰@(⊢ ⁉₂ ⋆⟨ s₁ ⨟ s₂ ⟩) ps⊑
    using H ← mkHyp (p⁰ % s⁰) ps⊑
    with Counter.lookupOrInsert Θ H
  ... | inj₁ H∈ = inj₁ (buildHyp H Θ-⋆ H∈)
  ... | inj₂ (-, refl , Θ′ , H∉)
    with ⁉₁ ≟⁉ ⁉₂
  ... | no ⁉≠ = inj₂ ((λ eq → case eq 1 of λ{ refl → ⁉≠ refl }) , λ where
    (-, %-⋆ _ _ _ _) → ⁉≠ refl
    (-, hyp H∈)      → H∉ (⟨∈⟩⇐∈ H H∈))
  ... | yes refl
    using Θ′-st ← Θ-⋆ ∷ Θ-st
    with run Θ′ Θ′-st p₁ s₁ $ ⊑ᵤ⁻¹-⋆ ps⊑ .proj₁
  ... | inj₂ ¬p%s = inj₂ (proj₁ ¬p%s ∘ proj₁ ∘ ≃⁻¹-⋆ , λ where
    (-, %-⋆ _ p%s _ _) → proj₂ ¬p%s (-, p%s)
    (-, hyp H∈)        → H∉ (⟨∈⟩⇐∈ H H∈))
  ... | inj₁ (r₁ , p%s₁ , fin₁ , u₁)
    with run Θ′ Θ′-st p₂ s₂ $ ⊑ᵤ⁻¹-⋆ ps⊑ .proj₂
  ... | inj₂ ¬p%s = inj₂ (proj₁ ¬p%s ∘ proj₂ ∘ ≃⁻¹-⋆ , λ where
    (-, %-⋆ _ _ p%s _) → proj₂ ¬p%s (-, p%s)
    (-, hyp H∈)        → H∉ (⟨∈⟩⇐∈ H H∈))
  ... | inj₁ (r₂ , p%s₂ , fin₂ , u₂)
    with r₁ | r₂
  ... | nothing | nothing = inj₁ $ nothing
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) p%s₁ p%s₂ (⊔-⊥ˡ nothing)
    , nothing
    , %-⋆-uniq-⊥ˡ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂
  ... | nothing | just r  = inj₁ $ just r
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) p%s₁ p%s₂ (⊔-⊥ˡ (just In.refl))
    , All?.map (∃□-step⁻¹ step-⋆₂) fin₂
    , %-⋆-uniq-⊥ˡ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂
  ... | just r  | nothing = inj₁ $ just r
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) p%s₁ p%s₂ (⊔-⊥ʳ (just In.refl))
    , All?.map (∃□-step⁻¹ step-⋆₁) fin₁
    , %-⋆-uniq-⊥ʳ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂
  ... | just (-, ⊢r₁) | just (-, ⊢r₂)
    with ⊢r₁ ≃? ⊢r₂
  ... | yes r≃ = inj₁ $ just (-, ⊢r₁)
    , %-⋆ (H∉ ∘ ⟨∈⟩⇐∈ H) p%s₁ p%s₂ (⊔-≃ In.refl r≃)
    , All?.map (∃□-step⁻¹ step-⋆₁) fin₁
    , %-⋆-uniq-just (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂
  ... | no r≄ = inj₂
    let module R₁ = RemPaths (remPaths p%s₁) in
    let module R₂ = RemPaths (remPaths p%s₂) in
    ( (λ {r} {⊢r} → targets*≄-⇒-≄
        (step-⋆₁ , path◇ R₁.returnPath∈p r)
        (step-⋆₂ , path◇ R₂.returnPath∈p r)
        (step-⋆₁ , R₁.returnPath∈s)
        (step-⋆₂ , R₂.returnPath∈s)
        (In.trans
          (◇s–[π→□]→s _ R₁.returnPath∈p R₁.–[returnPath]→□)
          (In.sym (◇s–[π→□]→s _ R₂.returnPath∈p R₂.–[returnPath]→□)))
        λ eq → r≄ (In.trans (In.sym R₁.–[returnPath]→r) (In.trans eq R₂.–[returnPath]→r))
      )
    , λ p%s → r≄ (%-⋆-r≃ (H∉ ∘ ⟨∈⟩⇐∈ H) u₁ u₂ (p%s .proj₂))
    )

  run-hnf Θ ¬μᵖ ¬μˢ Θ-st (⊢♯ p) ⊢□ ps⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (-, hyp x) → case All.lookup Θ-st x of λ() }
    )
  run-hnf Θ ¬μᵖ ¬μˢ Θ-st (⊢♯ p) ⊢⋆⟨ _ ⨟ _ ⟩ ps⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (-, hyp x) → case All.lookup Θ-st x of λ() }
    )
  run-hnf Θ ¬μᵖ ¬μˢ Θ-st ⊢⋆⟨ _ ⨟ _ ⟩ ⊢□ ps⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (-, hyp x) → case All.lookup Θ-st x of λ() }
    )
  run-hnf Θ ¬μᵖ ¬μˢ Θ-st ⊢⋆⟨ _ ⨟ _ ⟩ (⊢♯ _) ps⊑ = inj₂
    ( (λ eq → case eq 1 of λ())
    , λ{ (-, hyp x) → case All.lookup Θ-st x of λ() }
    )

module _ (⊢p : ⊢ p) (⊢s : ⊢ s) where
  open import Data.Unit using (⊤)
  open import Data.Maybe using (Maybe; just; nothing; maybe)
  open import Data.Maybe.Relation.Unary.All using (just; nothing)
  open import Data.Maybe.Relation.Unary.Any using (just)
  open Core (p % s)

  strip : Dec (∃ λ r → [] ⊢ ⊢p % ⊢s ＝ r)
  strip with run Counter.begin [] ⊢p ⊢s ⊑ᵤ-refl
  ... | inj₁ (-, p%s , _) = yes (-, p%s)
  ... | inj₂ ¬p%s         = no (proj₂ ¬p%s)

  finite-⊥⇒¬∃□ : [] ⊢ ⊢p % ⊢s ＝ nothing → ¬ ∃□ ⊢p
  finite-⊥⇒¬∃□ p%s = Soundness.Unknown.¬∃□ p%s

  finite-¬⊥⇒∃□ : [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → ∃□ ⊢p
  finite-¬⊥⇒∃□ p%s with run Counter.begin [] ⊢p ⊢s ⊑ᵤ-refl
  ... | inj₁ (just _  , _    , fin , _)    = All?.drop-just fin
  ... | inj₁ (nothing , p%s′ , _   , uniq) = case uniq _ p%s of λ()
  ... | inj₂ (_ , ¬p%s)                    = contradiction (-, p%s) ¬p%s

  finite-∃□⇒¬⊥ : ∀ {r} → [] ⊢ ⊢p % ⊢s ＝ r → ∃□ ⊢p → Is-just r
  finite-∃□⇒¬⊥ p%s fin with run Counter.begin [] ⊢p ⊢s ⊑ᵤ-refl
  ... | inj₁ (just _ , _ , _ , u) rewrite PW.just-inv (u _ p%s) .proj₂ .proj₁ = just _
  ... | inj₁ (nothing , p%s′ , _) = contradiction fin (finite-⊥⇒¬∃□ p%s′)
  ... | inj₂ (_ , ¬p%s)           = contradiction (-, p%s) ¬p%s

  finite-¬∃□⇒⊥ : ∀ {r} → [] ⊢ ⊢p % ⊢s ＝ r → ¬ ∃□ ⊢p → Is-nothing r
  finite-¬∃□⇒⊥ p%s ¬fin with run Counter.begin [] ⊢p ⊢s ⊑ᵤ-refl
  ... | inj₁ (just _  , _ , fin , _) = contradiction (All?.drop-just fin) ¬fin
  ... | inj₁ (nothing , _ , _   , u) rewrite PW.nothing-inv (u _ p%s) = nothing
  ... | inj₂ (_ , ¬p%s)             = contradiction (-, p%s) ¬p%s

  complete : ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s → ∃ λ r′ → [] ⊢ ⊢p % ⊢s ＝ r′
  complete eq with run Counter.begin [] ⊢p ⊢s ⊑ᵤ-refl
  ... | inj₁ (-, p%s , _) = -, p%s
  ... | inj₂ (¬p%s , _) = contradiction eq ¬p%s

  complete-∃□ : ∃□ ⊢p → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s → [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r)
  complete-∃□ fin-p eq with complete eq
  ... | just (-, ⊢r′) , p%s =
    ⊢%-subst
      (In.sym $ ◇≃◇-injective fin-p $ In.trans eq $ In.sym $ Soundness.Remainder.sound p%s)
      p%s
  ... | nothing , p%s = contradiction fin-p (finite-⊥⇒¬∃□ p%s)

  complete-¬∃□ : ¬ ∃□ ⊢p → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s → [] ⊢ ⊢p % ⊢s ＝ nothing
  complete-¬∃□ inf-p eq with complete eq
  ... | just (-, ⊢r′) , p%s = contradiction (finite-¬⊥⇒∃□ p%s) inf-p
  ... | nothing       , p%s = p%s

  sound-S : [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound-S p%s = Soundness.Remainder.sound p%s

  sound-⊥ : [] ⊢ ⊢p % ⊢s ＝ nothing → ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s
  sound-⊥ p%s = Soundness.Unknown.sound p%s
