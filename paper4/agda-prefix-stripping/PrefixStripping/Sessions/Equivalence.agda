----------------------------------------------------------------------------------------------------
-- This module defines the equivalence of session types.

module PrefixStripping.Sessions.Equivalence (𝕋 : Set) where

open import PrefixStripping.Prelude hiding (refl; sym; trans)
open import Data.List using (List; []; _∷_)
open Nat.Variables

import PrefixStripping.Sessions 𝕋 as Sessions
open Sessions using (SREL; SRel)
open Sessions.Functions hiding (idₛ; _∷ₛ_; 0↦)

open import PrefixStripping.Syntax

----------------------------------------------------------------------------------------------------
-- Trees represent a completely unfolded session type up to a maximum depth d where they are cut
-- off.

module Tree (END : Set) where
  private variable d : ℕ
  data 𝓣_≤_ (n : ℕ) : ℕ → Set where
    𝓣⊥     : 𝓣 n ≤ 0
    `_     : (z : 𝔽 n) → 𝓣 n ≤ suc d
    □      : (E : END) → 𝓣 n ≤ suc d
    _♯_▸_  : (⁉ : Dir) (T : 𝕋) (t : 𝓣 n ≤ d) → 𝓣 n ≤ suc d
    _⟨_⨟_⟩ : (⁉ : Dir) (t₁ t₂ : 𝓣 n ≤ d) → 𝓣 n ≤ suc d

module _ {END : Set} where
  open Sessions.Core END
  open Tree END

  private variable
    T T₁ T₂ : 𝕋
    E E₁ E₂ : END
    s s₁ s₂ : 𝕊 n
    x y z x′ y′ z′ x₁ x₂ y₁ y₂ : ⊢ s

    d d₁ d₂ d₃ d′ : ℕ
    t u t₁ t₂ t₃ u₁ u₂ u₃ : 𝓣 n ≤ d

  ♯-injective : {t₁ t₂ : 𝓣 n ≤ d} → ⁉₁ ♯ T₁ ▸ t₁ ≡ ⁉₂ ♯ T₂ ▸ t₂ → ⁉₁ ≡ ⁉₂ × T₁ ≡ T₂ × t₁ ≡ t₂
  ♯-injective Eq.refl = Eq.refl , Eq.refl , Eq.refl

  ⋆-injective : {t₁ t₂ u₁ u₂ : 𝓣 n ≤ d} → ⁉₁ ⟨ t₁ ⨟ t₂ ⟩ ≡ ⁉₂ ⟨ u₁ ⨟ u₂ ⟩ → ⁉₁ ≡ ⁉₂ × t₁ ≡ u₁ × t₂ ≡ u₂
  ⋆-injective Eq.refl = Eq.refl , Eq.refl , Eq.refl

----------------------------------------------------------------------------------------------------
-- We can “grow” trees from session types.

  ⟦_⟧ : {s : 𝕊 n} → ⊢ s → (d : ℕ) → 𝓣 n ≤ d
  grow : {s : 𝕊 n} (d ℓ : ℕ) (x : ⊢ s) → .(μLeaders s ≡ ℓ) → 𝓣 n ≤ d

  ⟦ s ⟧ d = grow d _ s Eq.refl

  grow zero ℓ s ℓ-eq = 𝓣⊥
  grow (suc d) 0 (⊢□′ E)          ℓ-eq = □ E
  grow (suc d) 0 (⊢` z)           ℓ-eq = ` z
  grow (suc d) 0 (⊢♯ ⁉ · T ▸ x)   ℓ-eq = ⁉ ♯ T ▸ ⟦ x ⟧ d
  grow (suc d) 0 (⊢ ⁉ ⋆⟨ x ⨟ y ⟩) ℓ-eq = ⁉ ⟨ ⟦ x ⟧ d ⨟ ⟦ y ⟧ d ⟩
  grow (suc d) (suc ℓ) (⊢μ x xᶜ) ℓ-eq =
    grow (suc d) ℓ (⊢-unfold x xᶜ) (Eq.trans (μLeaders-⋯ₛ-0↦ x xᶜ) (Nat.suc-injective ℓ-eq))

  cong-grow-depth : (⊢s : ⊢ s) {d ℓ₁ ℓ₂ : ℕ}
    .(eq₁ : μLeaders s ≡ ℓ₁) .(eq₂ : μLeaders s ≡ ℓ₂) →
    .(ℓ₁ ≡ ℓ₂) →
    grow d ℓ₁ ⊢s eq₁ ≡ grow d ℓ₂ ⊢s eq₂
  cong-grow-depth s {0} eq₁ eq₂ eq = Eq.refl
  cong-grow-depth s {suc _} {0} {0} eq₁ eq₂ eq = Eq.refl
  cong-grow-depth (⊢μ s sᶜ) {suc _} {suc ℓ₁} {suc ℓ₂} eq₁ eq₂ eq =
    cong-grow-depth (⊢-unfold s sᶜ)
      (Eq.trans (μLeaders-⋯ₛ-0↦ s sᶜ) (Nat.suc-injective eq₁))
      (Eq.trans (μLeaders-⋯ₛ-0↦ s sᶜ) (Nat.suc-injective eq₂))
      (Nat.suc-injective eq)

  cong-grow : ∀ {ℓ₁ ℓ₂} {x : ⊢ s₁} (y : ⊢ s₂) .(eq₁ : μLeaders s₁ ≡ ℓ₁) .(eq₂ : μLeaders s₂ ≡ ℓ₂) {p : s₁ ≡ s₂} →
    x ≡ subst ⊢_ (Eq.sym p) y →
    grow d ℓ₁ x eq₁ ≡ grow d ℓ₂ y eq₂
  cong-grow y eq₁ eq₂ {p = Eq.refl} Eq.refl = cong-grow-depth _ eq₁ eq₂ (Eq.trans (Eq.sym eq₁) eq₂)

----------------------------------------------------------------------------------------------------
-- We can cut trees (removing one level)

  cut : 𝓣 n ≤ suc d → 𝓣 n ≤ d
  cut {d = zero}  t             = 𝓣⊥
  cut {d = suc d} (` z)         = ` z
  cut {d = suc d} (□ E)         = □ E
  cut {d = suc d} (⁉ ♯ T ▸ t)   = ⁉ ♯ T ▸ cut t
  cut {d = suc d} (⁉ ⟨ t ⨟ u ⟩) = ⁉ ⟨ cut t ⨟ cut u ⟩

  cut-grow-suc : (x : ⊢ s) {d ℓ : ℕ} .(eq : μLeaders s ≡ ℓ) → cut (grow (suc d) ℓ x eq) ≡ grow d ℓ x eq
  cut-grow-suc x           {0}         eq = Eq.refl
  cut-grow-suc (⊢` x)      {suc d} {0} eq = Eq.refl
  cut-grow-suc ⊢□          {suc d} {0} eq = Eq.refl
  cut-grow-suc (⊢♯ x)      {suc d} {0} eq = cong (_ ♯ _ ▸_) (cut-grow-suc x Eq.refl)
  cut-grow-suc ⊢⋆⟨ x ⨟ y ⟩ {suc d} {0} eq = cong₂ (_ ⟨_⨟_⟩) (cut-grow-suc x Eq.refl) (cut-grow-suc y Eq.refl)
  cut-grow-suc (⊢μ x xᶜ)   {suc d} {suc d-μ} eq =
    cut-grow-suc (⊢-unfold x xᶜ) $· Eq.trans (μLeaders-⋯ₛ-0↦ x xᶜ) (Nat.suc-injective eq)

  ⟦_⟧·suc-cut : (x : ⊢ s) {d : ℕ} → cut (⟦ x ⟧ (suc d)) ≡ ⟦ x ⟧ d
  ⟦ x ⟧·suc-cut = cut-grow-suc x Eq.refl

----------------------------------------------------------------------------------------------------
-- Substitutions on trees

  𝓣≤_Sub : (d m n : ℕ) → Set _
  𝓣≤ d Sub m n = (z : 𝔽 m) → 𝓣 n ≤ d

  idₛ : 𝓣≤ d Sub n n
  idₛ {d = zero}  z = 𝓣⊥
  idₛ {d = suc d} z = ` z

  _∷ₛ_ : 𝓣 n ≤ d → 𝓣≤ d Sub m n → 𝓣≤ d Sub (suc m) n
  (t ∷ₛ σ) zero    = t
  (t ∷ₛ σ) (suc z) = σ z

  0↦ : 𝓣 n ≤ d → 𝓣≤ d Sub (suc n) n
  0↦ t = t ∷ₛ idₛ

  ⟦_⟧ₛ : {σ : Sub m n} → ⊢Sub σ → ∀ d → 𝓣≤ d Sub m n
  ⟦ τ ⟧ₛ d z = ⟦ τ z ⟧ d

  cutₛ : 𝓣≤ suc d Sub m n → 𝓣≤ d Sub m n
  cutₛ σ z = cut (σ z)

  ⟦_⟧ₛ·suc-cutₛ : {σ : Sub m n} (τ : ⊢Sub σ) {d : ℕ} → cutₛ (⟦ τ ⟧ₛ (suc d)) ≗ ⟦ τ ⟧ₛ d
  ⟦ τ ⟧ₛ·suc-cutₛ z = ⟦ τ z ⟧·suc-cut

  _𝓣⋯_ : 𝓣 m ≤ d → 𝓣≤ d Sub m n → 𝓣 n ≤ d
  𝓣⊥            𝓣⋯ σ = 𝓣⊥
  (` z)         𝓣⋯ σ = σ z
  □ E           𝓣⋯ σ = □ E
  (⁉ ♯ T ▸ t)   𝓣⋯ σ = ⁉ ♯ T ▸ t 𝓣⋯ cutₛ σ
  (⁉ ⟨ t ⨟ u ⟩) 𝓣⋯ σ = ⁉ ⟨ t 𝓣⋯ cutₛ σ ⨟ u 𝓣⋯ cutₛ σ ⟩

  _𝓣·_ : 𝓣≤ d Sub m n → 𝓣≤ d Sub n o → 𝓣≤ d Sub m o
  (σ₁ 𝓣· σ₂) z = σ₁ z 𝓣⋯ σ₂

----------------------------------------------------------------------------------------------------
-- Growing a tree from a substituted session is the same as growing the tree from the original
-- session and applying the substitution then.

  𝓣⋯-cong : (t : 𝓣 m ≤ d) {σ₁ σ₂ : 𝓣≤ d Sub m n} → σ₁ ≗ σ₂ → t 𝓣⋯ σ₁ ≡ t 𝓣⋯ σ₂
  𝓣⋯-cong 𝓣⊥              σ= = Eq.refl
  𝓣⋯-cong (` z)           σ= = σ= z
  𝓣⋯-cong (□ E)           σ= = Eq.refl
  𝓣⋯-cong (⁉ ♯ T ▸ t)     σ= = cong (⁉ ♯ T ▸_) (𝓣⋯-cong t (cong cut ∘ σ=))
  𝓣⋯-cong (⁉ ⟨ t₁ ⨟ t₂ ⟩) σ= = cong₂ (⁉ ⟨_⨟_⟩) (𝓣⋯-cong t₁ (cong cut ∘ σ=)) (𝓣⋯-cong t₂ (cong cut ∘ σ=))

  ⟦_⟧-comm-⋯ₛ : {s : 𝕊 m} {σ : Sub m n} (x : ⊢ s) (τ : ⊢Sub σ) → ∀ d → ⟦ ⊢-⋯ₛ x τ ⟧ d ≡ ⟦ x ⟧ d 𝓣⋯ ⟦ τ ⟧ₛ d
  grow-comm-⋯ₛ : ∀ d {s : 𝕊 m} {σ : Sub m n} (x : ⊢ s) (τ : ⊢Sub σ) {ℓˢ ℓˣ : ℕ}
    .(eqˢ : μLeaders (s ⋯ₛ σ) ≡ ℓˢ) .(eqˣ : μLeaders s ≡ ℓˣ) →
    grow d ℓˢ (⊢-⋯ₛ x τ) eqˢ ≡ grow d ℓˣ x eqˣ 𝓣⋯ ⟦ τ ⟧ₛ d

  ⟦ x ⟧-comm-⋯ₛ τ d = grow-comm-⋯ₛ d x τ Eq.refl Eq.refl

  grow-comm-⋯ₛ 0 x τ eqˢ eqˣ = Eq.refl
  grow-comm-⋯ₛ (suc d) x τ {0} {suc ℓˣ} eqˢ eqˣ =
    let open Nat.≤-Reasoning in
    ⊥-elim-irr $· begin-contradiction
      zero                   <⟨ Nat.z<s ⟩
      suc ℓˣ                 ≡⟨ eqˣ ⟨
      μLeaders ⌊ x ⌋         ≤⟨ μLeaders-⋯ₛ-≤ ⌊ x ⌋ ⟩
      μLeaders ⌊ ⊢-⋯ₛ x τ ⌋  ≡⟨ eqˢ ⟩
      zero ∎
  grow-comm-⋯ₛ (suc d) ⊢□ τ {0} {0} eqˢ eqˣ = Eq.refl
  grow-comm-⋯ₛ (suc d) (⊢♯ x) τ {0} {0} eqˢ eqˣ
    rewrite ⟦ x ⟧-comm-⋯ₛ τ d | 𝓣⋯-cong (⟦ x ⟧ d) ⟦ τ ⟧ₛ·suc-cutₛ
    = Eq.refl
  grow-comm-⋯ₛ (suc d) ⊢⋆⟨ x ⨟ y ⟩ τ {0} {0} eqˢ eqˣ
    rewrite ⟦ x ⟧-comm-⋯ₛ τ d | 𝓣⋯-cong (⟦ x ⟧ d) ⟦ τ ⟧ₛ·suc-cutₛ
          | ⟦ y ⟧-comm-⋯ₛ τ d | 𝓣⋯-cong (⟦ y ⟧ d) ⟦ τ ⟧ₛ·suc-cutₛ
    = Eq.refl
  grow-comm-⋯ₛ (suc d) (⊢` z) τ {0} {0} eqˢ eqˣ =
    cong-grow-depth (τ z) eqˢ Eq.refl (Eq.sym eqˢ)
  grow-comm-⋯ₛ (suc d) (⊢` z) τ {suc d-μˢ} {0} eqˢ eqˣ =
    cong-grow-depth (τ z) eqˢ Eq.refl (Eq.sym eqˢ)
  grow-comm-⋯ₛ (suc d) {σ = σ} (⊢μ x xᶜ) τ {suc ℓˢ} {suc ℓˣ} eqˢ eqˣ =
    let open ≡-Reasoning in
    let suc⁻¹ = Nat.suc-injective in
    let x⋯ₛ   = (⊢-⋯ₛ x (⊢↑ τ)) in
    let xᶜ⋯ₛ  = ⊢ᶜ-⋯ₛ-↑ _ xᶜ in
    let μLeaders-unfold = Eq.trans (μLeaders-⋯ₛ-0↦ x⋯ₛ xᶜ⋯ₛ) ∘ suc⁻¹ in
    begin
      grow _ (suc ℓˢ) (⊢-⋯ₛ (⊢μ x xᶜ) τ) eqˢ
    ≡⟨⟩
      grow _ (suc ℓˢ) (⊢μ x⋯ₛ xᶜ⋯ₛ) eqˢ
    ≡⟨⟩
      grow _ ℓˢ (⊢-unfold x⋯ₛ xᶜ⋯ₛ) (μLeaders-unfold eqˢ)
    ≡⟨ cong-grow (⊢-⋯ₛ (⊢-unfold x xᶜ) τ) (μLeaders-unfold eqˢ)
         (Eq.trans (cong μLeaders (Eq.sym (⋯-exchangeₛₛ ⌊ x ⌋ (μ ⌊ x ⌋) σ))) (μLeaders-unfold eqˢ))
         (dcong-⊢ (⊢-⋯ₛ (⊢-unfold x xᶜ) τ) (⋯-exchangeₛₛ ⌊ x ⌋ (μ ⌊ x ⌋) σ))
    ⟩
      grow _ ℓˢ (⊢-⋯ₛ (⊢-unfold x xᶜ) τ) _
    ≡⟨ grow-comm-⋯ₛ _ (⊢-unfold x xᶜ) τ
         (Eq.trans (cong μLeaders (Eq.sym (⋯-exchangeₛₛ ⌊ x ⌋ (μ ⌊ x ⌋) σ))) (μLeaders-unfold eqˢ))
         (Eq.trans (μLeaders-⋯ₛ-0↦ x xᶜ) (suc⁻¹ eqˣ))
    ⟩
      grow _ ℓˣ (⊢-unfold x xᶜ) _ 𝓣⋯ ⟦ τ ⟧ₛ (suc d)
    ≡⟨⟩
      grow _ (suc ℓˣ) (⊢μ x xᶜ) eqˣ 𝓣⋯ ⟦ τ ⟧ₛ (suc d)
    ∎

----------------------------------------------------------------------------------------------------
-- Two session are equivalent if for all maximum depths the trees are equal.

  infix 4 _≃_

  _≃_ : SRel END n _
  x ≃ y = ∀ d → ⟦ x ⟧ d ≡ ⟦ y ⟧ d

  _≄_ : SRel END n _
  x ≄ y = ¬ (x ≃ y)

  refl : x ≃ x
  refl d = Eq.refl

  reflexive : {x : ⊢ s₁} {y : ⊢ s₂} → s₁ ≡ s₂ → x ≃ y
  reflexive {x = x} {y = y} Eq.refl rewrite ⊢-irr y x = refl {x = x}

  sym : x ≃ y → y ≃ x
  sym eq d = Eq.sym (eq d)

  trans : x ≃ y → y ≃ z → x ≃ z
  trans xy yz d = Eq.trans (xy d) (yz d)

  ≃-♯ : ∀ {⁉ T} → x ≃ y → ⊢♯ ⁉ · T ▸ x ≃ ⊢♯ ⁉ · T ▸ y
  ≃-♯ eq zero = Eq.refl
  ≃-♯ eq (suc d) = cong (_ ♯ _ ▸_) (eq d)

  ≃⁻¹-♯ : ⊢♯ ⁉₁ · T₁ ▸ x ≃ ⊢♯ ⁉₂ · T₂ ▸ y → x ≃ y
  ≃⁻¹-♯ eq d = ♯-injective (eq (suc d)) .proj₂ .proj₂

  ≃-⋆ : ∀ {⁉} → x₁ ≃ y₁ → x₂ ≃ y₂ → ⊢ ⁉ ⋆⟨ x₁ ⨟ x₂ ⟩ ≃ ⊢ ⁉ ⋆⟨ y₁ ⨟ y₂ ⟩
  ≃-⋆ eq₁ eq₂ zero = Eq.refl
  ≃-⋆ eq₁ eq₂ (suc d) = cong₂ (_ ⟨_⨟_⟩) (eq₁ d) (eq₂ d)

  ≃⁻¹-⋆ : ⊢ ⁉₁ ⋆⟨ x₁ ⨟ x₂ ⟩ ≃ ⊢ ⁉₂ ⋆⟨ y₁ ⨟ y₂ ⟩ → x₁ ≃ y₁ × x₂ ≃ y₂
  ≃⁻¹-⋆ eq = (λ d → ⋆-injective (eq (suc d)) .proj₂ .proj₁) , (λ d → ⋆-injective (eq (suc d)) .proj₂ .proj₂)

  ≃-μ : (x : ⊢ s) (xᶜ : ⊢ᶜ s) → ⊢μ x xᶜ ≃ ⊢-unfold x xᶜ
  ≃-μ x xᶜ zero = Eq.refl
  ≃-μ x xᶜ (suc d) = cong-grow-depth (⊢-unfold x xᶜ) (μLeaders-⋯ₛ-0↦ x xᶜ) Eq.refl (Eq.sym (μLeaders-⋯ₛ-0↦ x xᶜ))

----------------------------------------------------------------------------------------------------
-- Assertion that accessing a path in a session type gives a specific result.

  infix 4 _–[_]→_

  _–[_]→_ : ∀ {s₁ s₂ : 𝕊 n} {π} → ⊢ s₁ → Path π s₁ → ⊢ s₂ → Set _
  src –[ π ]→ tgt = ⊢-target* src π ≃ tgt

  ≃-step′ : ∀ ℓ {x : ⊢ s₁} {y : ⊢ s₂} {s} → .(μLeaders s₂ ≡ ℓ) → x ≃ y → Step s s₁ → Step s s₂
  ≃-step′ 0 ℓ-eq ∀eq s with ∀eq 1
  ≃-step′ 0 {⊢♯ x}          {⊢♯ y}          ℓ-eq ∀eq step-♯     | eq = step-♯
  ≃-step′ 0 {⊢⋆⟨ x₁ ⨟ x₂ ⟩} {⊢⋆⟨ y₁ ⨟ y₂ ⟩} ℓ-eq ∀eq step-⋆₁    | eq = step-⋆₁
  ≃-step′ 0 {⊢⋆⟨ x₁ ⨟ x₂ ⟩} {⊢⋆⟨ y₁ ⨟ y₂ ⟩} ℓ-eq ∀eq step-⋆₂    | eq = step-⋆₂
  ≃-step′ 0 {⊢μ x xᶜ}       {y}             ℓ-eq ∀eq (step-μ s) | eq = ≃-step′ _ Eq.refl (trans (sym (≃-μ x xᶜ)) ∀eq) s
  ≃-step′ (suc ℓ) {y = ⊢μ y yᶜ} ℓ-eq ∀eq step =
    step-μ (≃-step′ ℓ (Eq.trans (μLeaders-⋯ₛ-0↦ y yᶜ) (Nat.suc-injective ℓ-eq)) (trans ∀eq (≃-μ y yᶜ)) step)

  ≃-step : ∀ {x : ⊢ s₁} {y : ⊢ s₂} {rs} → x ≃ y → Step rs s₁ → Step rs s₂
  ≃-step = ≃-step′ _ Eq.refl

  ≃-target′ : ∀ ℓ {x : ⊢ s₁} {y : ⊢ s₂} .(ℓ-eq : μLeaders s₂ ≡ ℓ) (eq : x ≃ y) {rstep} (s : Step rstep s₁) →
    ⊢-target x s ≃ ⊢-target y (≃-step eq s)
  ≃-target′ 0 ℓ-eq x≃y s with x≃y 1
  ≃-target′ 0 {⊢♯ x}          {⊢♯ y}          ℓ-eq x≃y step-♯  | eq = ≃⁻¹-♯ x≃y
  ≃-target′ 0 {⊢⋆⟨ x₁ ⨟ x₂ ⟩} {⊢⋆⟨ y₁ ⨟ y₂ ⟩} ℓ-eq x≃y step-⋆₁ | eq = ≃⁻¹-⋆ x≃y .proj₁
  ≃-target′ 0 {⊢⋆⟨ x₁ ⨟ x₂ ⟩} {⊢⋆⟨ y₁ ⨟ y₂ ⟩} ℓ-eq x≃y step-⋆₂ | eq = ≃⁻¹-⋆ x≃y .proj₂
  ≃-target′ 0 {⊢μ x xᶜ} ℓ-eq x≃y (step-μ s) | eq =
    let x≃y′ = trans (sym (≃-μ x xᶜ)) x≃y in
    trans (≃-target′ _ Eq.refl x≃y′ s) $ reflexive $ cong target $
      step-irr (≃-step x≃y′ s) (≃-step x≃y (step-μ s))
  ≃-target′ (suc ℓ) {x} {y = ⊢μ y yᶜ} ℓ-eq x≃y s =
    let x≃y′ = trans x≃y (≃-μ y yᶜ) in
    let IH = ≃-target′ ℓ (Eq.trans (μLeaders-⋯ₛ-0↦ y yᶜ) (Nat.suc-injective ℓ-eq)) x≃y′ s in
    trans IH $ reflexive $ cong target $
      step-irr (≃-step x≃y′ s) (≃-step′ _ (μLeaders-⋯ₛ-0↦ y yᶜ) x≃y′ s)

  ≃-target : ∀ {x : ⊢ s₁} {y : ⊢ s₂} (eq : x ≃ y) {rstep} (s : Step rstep s₁) → ⊢-target x s ≃ ⊢-target y (≃-step eq s)
  ≃-target = ≃-target′ _ Eq.refl

  ≃-path : ∀ {x : ⊢ s₁} {y : ⊢ s₂} {π} → x ≃ y → Path π s₁ → Path π s₂
  ≃-path {π = []}    eq π       = _
  ≃-path {π = _ ∷ _} eq (x , π) = ≃-step eq x , ≃-path (≃-target eq x) π

  ≃-target* : ∀ {x : ⊢ s₁} {y : ⊢ s₂} (eq : x ≃ y) {rπ} (π : Path rπ s₁) → ⊢-target* x π ≃ ⊢-target* y (≃-path eq π)
  ≃-target* eq {[]}    π       = eq
  ≃-target* eq {_ ∷ _} (x , π) = ≃-target* (≃-target eq x) π

  targets*≄-⇒-≄ :
    ∀ {π₁ π₂} {x : ⊢ s₁} {y : ⊢ s₂} →
    (π₁∈x : Path π₁ s₁) (π₂∈x : Path π₂ s₁) →
    (π₁∈y : Path π₁ s₂) (π₂∈y : Path π₂ s₂) →
    ⊢-target* x π₁∈x ≃ ⊢-target* x π₂∈x →
    ⊢-target* y π₁∈y ≄ ⊢-target* y π₂∈y →
    x ≄ y
  targets*≄-⇒-≄ {x = x} {y} π₁∈x π₂∈x π₁∈y π₂∈y eqˣ ¬eqʸ eq
    rewrite path-irr π₁∈x (≃-path (sym eq) π₁∈y) | path-irr π₂∈x (≃-path (sym eq) π₂∈y)
    = ¬eqʸ $
    trans (≃-target* (sym eq) π₁∈y)
      $ trans eqˣ
      $ sym (≃-target* (sym eq) π₂∈y)

----------------------------------------------------------------------------------------------------
-- A predicate for session types that contain an end value.

  data ∃□ {s : 𝕊 n} (x : ⊢ s) : Set where
    □ : ∀ {s*} (π : Path s* s) → x –[ π ]→ ⊢□′ E → ∃□ x

  ∃□-step⁻¹ : ∀ {rstep} {x : ⊢ s} (step : Step rstep s) → ∃□ (⊢-target x step) → ∃□ x
  ∃□-step⁻¹ step (□ π eq) = □ (step , π) eq

  ∃□-□ : ∃□ {n = n} (⊢□′ E)
  ∃□-□ = □ {s* = []} _ refl

  ∃□-♯ : ∃□ x → ∃□ (⊢♯ ⁉ · T ▸ x)
  ∃□-♯ = ∃□-step⁻¹ step-♯

  ∃□-♯⁻¹ : ∃□ (⊢♯ ⁉ · T ▸ x) → ∃□ x
  ∃□-♯⁻¹ (□ {s* = []}    π            eq) = case eq 1 of λ()
  ∃□-♯⁻¹ (□ {s* = _ ∷ _} (step-♯ , π) eq) = □ π eq

  ∃□-⋆₁ : ∃□ x → ∃□ (⊢ ⁉ ⋆⟨ x ⨟ y ⟩)
  ∃□-⋆₁ = ∃□-step⁻¹ step-⋆₁

  ∃□-⋆₂ : ∃□ y → ∃□ (⊢ ⁉ ⋆⟨ x ⨟ y ⟩)
  ∃□-⋆₂ = ∃□-step⁻¹ step-⋆₂

  ∃□-⋆⁻¹ : ∃□ (⊢ ⁉ ⋆⟨ x ⨟ y ⟩) → ∃□ x ⊎ ∃□ y
  ∃□-⋆⁻¹ (□ {s* = []}    π             eq) = case eq 1 of λ()
  ∃□-⋆⁻¹ (□ {s* = _ ∷ _} (step-⋆₁ , π) eq) = inj₁ (□ π eq)
  ∃□-⋆⁻¹ (□ {s* = _ ∷ _} (step-⋆₂ , π) eq) = inj₂ (□ π eq)

  ¬∃□-` : {z : 𝔽 n} → ¬ ∃□ (⊢` z)
  ¬∃□-` (□ {s* = []} π eq) = case eq 1 of λ()

  cong-∃□ : x ≃ y → ∃□ x → ∃□ y
  cong-∃□ eq (□ π x) = □ (≃-path eq π) (trans (sym (≃-target* eq π)) x)

----------------------------------------------------------------------------------------------------
-- We postulate decidable equivalence for session types.

  open Relation.Binary using (DecidableEquality)
  module Decide (_ : DecidableEquality 𝕋) (_ : DecidableEquality END) where
    postulate _≃?_ : (x : ⊢ s₁) (y : ⊢ s₂) → Dec (x ≃ y)

module _ {END : Set} where
  open Sessions hiding (𝕊)
  open Sessions.Core END using (𝕊)

  module P = Tree End-ℙ
  module S = Tree END
  open Tree.𝓣_≤_

  private variable
    p p₁ p₂ : ℙ n
    s s₁ s₂ : 𝕊 n
    ⊢p ⊢p₁ ⊢p₂ : ⊢ p
    ⊢s ⊢s₁ ⊢s₂ : ⊢ s

----------------------------------------------------------------------------------------------------
-- We lift session type composition to trees and prove that growing a tree distributes over
-- compositing.

  _𝓣◇_ : ∀ {n d} → P.𝓣 n ≤ d → S.𝓣 n ≤ d → S.𝓣 n ≤ d
  𝓣⊥              𝓣◇ u = S.𝓣⊥
  (` z)           𝓣◇ u = S.` z
  □ E             𝓣◇ u = u
  (⁉ ♯ T ▸ t)     𝓣◇ u = ⁉ ♯ T ▸ t 𝓣◇ cut u
  (⁉ ⟨ t₁ ⨟ t₂ ⟩) 𝓣◇ u = ⁉ ⟨ t₁ 𝓣◇ cut u ⨟ t₂ 𝓣◇ cut u ⟩

  ⟦_◇_⟧-dist : ∀ (⊢p : ⊢ p) (⊢s : ⊢ s) d → ⟦ ⊢[ ⊢p ◇ ⊢s ] ⟧ d ≡ ⟦ ⊢p ⟧ d 𝓣◇ ⟦ ⊢s ⟧ d
  grow-dist-◇ : ∀ (⊢p : ⊢ p) (⊢s : ⊢ s) d ℓᶜ ℓᵖ ℓˢ
    .(eqᶜ : μLeaders (p ◇ s) ≡ ℓᶜ)
    .(eqᵖ : μLeaders p ≡ ℓᵖ)
    .(eqˢ : μLeaders s ≡ ℓˢ) →
    grow d ℓᶜ ⊢[ ⊢p ◇ ⊢s ] eqᶜ ≡ grow d ℓᵖ ⊢p eqᵖ 𝓣◇ grow d ℓˢ ⊢s eqˢ

  ⟦ ⊢p ◇ ⊢s ⟧-dist d = grow-dist-◇ ⊢p ⊢s d _ _ _ Eq.refl Eq.refl Eq.refl

  grow-dist-◇ p s 0 d-μᶜ d-μᵖ d-μˢ eqᶜ eqᵖ eqˢ = Eq.refl
  grow-dist-◇ (⊢` z) s (suc d) 0 0 d-μˢ eqᶜ eqᵖ eqˢ = Eq.refl
  grow-dist-◇ ⊢□ s (suc d) d-μᶜ 0 d-μˢ eqᶜ eqᵖ eqˢ =
    cong-grow-depth s eqᶜ eqˢ (Eq.trans (Eq.sym eqᶜ) eqˢ)
  grow-dist-◇ (⊢♯ p) s (suc d) 0 0 d-μˢ eqᶜ eqᵖ eqˢ =
    cong (_ ♯ _ ▸_)
      $ Eq.trans (⟦ p ◇ s ⟧-dist d)
      $ cong (grow d _ p Eq.refl 𝓣◇_)
      $ Eq.trans (Eq.sym (cut-grow-suc s Eq.refl))
      $ cong cut
      $ cong-grow-depth s Eq.refl eqˢ eqˢ
  grow-dist-◇ ⊢⋆⟨ p₁ ⨟ p₂ ⟩ s (suc d) 0 0 d-μˢ eqᶜ eqᵖ eqˢ =
    let eq = Eq.trans (Eq.sym (cut-grow-suc s Eq.refl))
               $ cong cut
               $ cong-grow-depth s Eq.refl eqˢ eqˢ
    in
    cong₂ (_ ⟨_⨟_⟩)
      (Eq.trans (⟦ p₁ ◇ s ⟧-dist d) (cong (grow d _ p₁ Eq.refl 𝓣◇_) eq))
      (Eq.trans (⟦ p₂ ◇ s ⟧-dist d) (cong (grow d _ p₂ Eq.refl 𝓣◇_) eq))
  grow-dist-◇ (⊢μ p pᶜ) s (suc d) (suc d-μᶜ) (suc d-μᵖ) d-μˢ eqᶜ eqᵖ eqˢ =
    let open ≡-Reasoning in
    let p◇s⋯ = ⊢[ p ◇ ⊢-⋯ s wk-injective ] in
    let suc⁻¹ = Nat.suc-injective in
    begin
      grow _ (suc d-μᶜ) ⊢[ ⊢μ p pᶜ ◇ s ] eqᶜ
    ≡⟨⟩
      grow _ (suc d-μᶜ) (⊢μ p◇s⋯ _) eqᶜ
    ≡⟨⟩
      grow _ d-μᶜ (⊢-unfold p◇s⋯ _) _
    ≡⟨ cong-grow ⊢[ ⊢-unfold p pᶜ ◇ s ]
         (Eq.trans (μLeaders-⋯ₛ-0↦ p◇s⋯ ⊢ᶜ[ pᶜ ◇ _ ]) (suc⁻¹ eqᶜ))
         (Eq.trans μLeaders-unfold[ pᶜ ◇ ⌊ s ⌋ ] (suc⁻¹ eqᶜ))
         (dcong-⊢ ⊢[ ⊢-unfold p pᶜ ◇ s ] unfold[ ⌊ p ⌋ ◇ ⌊ s ⌋ ])
    ⟩
      grow _ d-μᶜ ⊢[ ⊢-unfold p pᶜ ◇ s ] _
    ≡⟨ grow-dist-◇ (⊢-unfold p pᶜ) s (suc d) d-μᶜ d-μᵖ d-μˢ
         (Eq.trans (μLeaders-unfold[ pᶜ ◇ ⌊ s ⌋ ]) (suc⁻¹ eqᶜ))
         (Eq.trans (μLeaders-⋯ₛ-0↦ p pᶜ) (suc⁻¹ eqᵖ))
         eqˢ
    ⟩
      grow (suc d) d-μᵖ (⊢-unfold p pᶜ) (Eq.trans (μLeaders-⋯ₛ-0↦ p pᶜ) (suc⁻¹ eqᵖ))
        𝓣◇ grow (suc d) d-μˢ s eqˢ
    ≡⟨⟩
      grow (suc d) (suc d-μᵖ) (⊢μ p pᶜ) eqᵖ 𝓣◇ grow (suc d) d-μˢ s eqˢ
    ∎

----------------------------------------------------------------------------------------------------
-- _≃_ is a congruence relation with respect to _◇_

  cong₂-◇ : ⊢p₁ ≃ ⊢p₂ → ⊢s₁ ≃ ⊢s₂ → ⊢[ ⊢p₁ ◇ ⊢s₁ ] ≃ ⊢[ ⊢p₂ ◇ ⊢s₂ ]
  cong₂-◇ {⊢p₁ = p₁} {⊢p₂ = p₂} {⊢s₁ = s₁} {⊢s₂ = s₂} p≃ s≃ d =
    let open ≡-Reasoning in
    ⟦ ⊢[ p₁ ◇ s₁ ] ⟧ d    ≡⟨ ⟦ p₁ ◇ s₁ ⟧-dist d ⟩
    ⟦ p₁ ⟧ d 𝓣◇ ⟦ s₁ ⟧ d  ≡⟨ cong₂ _𝓣◇_ (p≃ d) (s≃ d) ⟩
    ⟦ p₂ ⟧ d 𝓣◇ ⟦ s₂ ⟧ d  ≡⟨ ⟦ p₂ ◇ s₂ ⟧-dist d ⟨
    ⟦ ⊢[ p₂ ◇ s₂ ] ⟧ d    ∎

  ≃-μ◇ : (⊢p : ⊢ p) (pᶜ : ⊢ᶜ p) {⊢s : ⊢ s} → ⊢[ ⊢μ ⊢p pᶜ ◇ ⊢s ] ≃ ⊢[ ⊢-unfold ⊢p pᶜ ◇ ⊢s ]
  ≃-μ◇ p pᶜ = cong₂-◇ (≃-μ p pᶜ) refl

  ◇s–[π→□]→s : ∀ (⊢p : ⊢ p) {⊢s : ⊢ s} {s*} (π : Path s* p) → ⊢p –[ π ]→ ⊢□ → ⊢[ ⊢p ◇ ⊢s ] –[ path◇ π s ]→ ⊢s
  ◇s–[π→□]→s ⊢p {s* = []} π π→□ = cong₂-◇ π→□ refl
  ◇s–[π→□]→s ⊢p {⊢s} {s* = _ ∷ _} (s , π) π→□ =
    trans
      (reflexive $ Eq.dcong₂ {B = Path _} (λ s′ π′ → target* {s = s′} π′)
        {target (step◇ s ⌊ ⊢s ⌋)}
        {target s ◇ ⌊ ⊢s ⌋}
        {proj₂ (path◇ (s , π) ⌊ ⊢s ⌋)}
        {path◇ π ⌊ ⊢s ⌋}
        (target-step◇ s ⌊ ⊢s ⌋)
        (Eq.subst-subst-sym (target-step◇ s ⌊ ⊢s ⌋)))
      (◇s–[π→□]→s (⊢-target ⊢p s) π π→□)

----------------------------------------------------------------------------------------------------
-- If the prefix contains `Return` then  p ◇ s₁ ≃ p ◇ s₂  implies  s₁ ≃ s₂

  ◇≃◇-injective′-here : ∀ {x : ⊢ s₁} {y : ⊢ s₂} ℓ → .(μLeaders p ≡ ℓ) → {⊢p : ⊢ p} →
    ⊢p ≃ ⊢□ → ⊢[ ⊢p ◇ x ] ≃ ⊢[ ⊢p ◇ y ] → x ≃ y
  ◇≃◇-injective′-here d ℓ-eq eq-□ eq-◇ with eq-□ 1
  ◇≃◇-injective′-here d ℓ-eq {⊢p = ⊢□}      eq-□ eq-◇ | zz = eq-◇
  ◇≃◇-injective′-here (suc d) ℓ-eq {⊢p = ⊢μ p pᶜ} eq-□ eq-◇ | zz =
    ◇≃◇-injective′-here d
      (Eq.trans (μLeaders-⋯ₛ-0↦ p pᶜ) (Nat.suc-injective ℓ-eq))
      (trans (sym (≃-μ p pᶜ)) eq-□)
      (trans (sym (≃-μ◇ p pᶜ)) (trans eq-◇ (≃-μ◇ p pᶜ)))

  ◇≃◇-injective′ : ∀ {s*} {⊢p : ⊢ p} {x : ⊢ s₁} {y : ⊢ s₂} (π : Path s* p) →
    ⊢p –[ π ]→ ⊢□ → ⊢[ ⊢p ◇ x ] ≃ ⊢[ ⊢p ◇ y ] → x ≃ y
  ◇≃◇-injective′ {s* = []}    π π→□ eq = ◇≃◇-injective′-here  _ Eq.refl π→□ eq
  ◇≃◇-injective′ {s* = _ ∷ _} {⊢♯ p}        (step-♯   , π) π→□ eq = ◇≃◇-injective′ π π→□ (≃⁻¹-♯ eq)
  ◇≃◇-injective′ {s* = _ ∷ _} {⊢⋆⟨ p ⨟ _ ⟩} (step-⋆₁  , π) π→□ eq = ◇≃◇-injective′ π π→□ (≃⁻¹-⋆ eq .proj₁)
  ◇≃◇-injective′ {s* = _ ∷ _} {⊢⋆⟨ _ ⨟ p ⟩} (step-⋆₂  , π) π→□ eq = ◇≃◇-injective′ π π→□ (≃⁻¹-⋆ eq .proj₂)
  ◇≃◇-injective′ {s* = _ ∷ _} {⊢μ p pᶜ}     (step-μ x , π) π→□ eq =
    ◇≃◇-injective′ (x , π) π→□
      (trans (sym (≃-μ◇ p pᶜ)) (trans eq (≃-μ◇ p pᶜ)))

  ◇≃◇-injective : {x : ⊢ s₁} {y : ⊢ s₂} → ∃□ ⊢p → ⊢[ ⊢p ◇ x ] ≃ ⊢[ ⊢p ◇ y ] → x ≃ y
  ◇≃◇-injective (□ π eq) = ◇≃◇-injective′ π eq
