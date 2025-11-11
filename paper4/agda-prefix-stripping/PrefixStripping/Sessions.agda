----------------------------------------------------------------------------------------------------
-- This module defines sessions types parameterized over some set of base types 𝕋.

module PrefixStripping.Sessions (𝕋 : Set) where

open import PrefixStripping.Prelude hiding (subst₂)
open import Data.Unit as Unit using (⊤)
open import Data.List using (List; []; _∷_)

open Nat.Variables
open Relation.Binary hiding (Irrelevant; _⇒_)

open import PrefixStripping.Syntax

module Core (END : Set) where
  infix 8 `_ _⟨_⨟_⟩
  infixr 5 _♯_▸_

  private variable T T₁ T₂ : 𝕋

  -- Sessions are intrinsically scoped and use de-Bruijn indices.
  data 𝕊 (n : ℕ) : Set where
    -- a completed session (Wait/Term when END is instantiated with Dir, Return when instantiated with ⊤)
    □ : END → 𝕊 n
    -- send/recieve: ?/! T.S
    _♯_▸_ : (⁉ : Dir) (T : 𝕋) (S : 𝕊 n) → 𝕊 n
    -- binary choice: &/⊕ { l₁: S₁; l₂: S₂ }
    _⟨_⨟_⟩ : (⁉ : Dir) (S₁ S₂ : 𝕊 n) → 𝕊 n
    -- recursion: μ S
    μ : (S : 𝕊 (suc n)) → 𝕊 n
    -- recursion variables X
    `_ : 𝔽 n → 𝕊 n

module Variables (END : Set) where
  variable
    T T₁ T₂ : 𝕋
    E E₁ E₂ : END
    s s₁ s₂ s₃ s′ s₁′ s₂′ : Core.𝕊 END n

module Functions {END : Set} where
  open Core (END)
  open Variables (END)

  open Nat using (_≤_; z≤n; s≤s)

  infix  4 ⊢ᶜ_·_ ⊢ᶜ_ ⊢_
  infixr 5 ⊢♯_·_▸_

  `-injective : ∀ {x y : 𝔽 n} → ` x ≡ ` y → x ≡ y
  `-injective refl = refl

  μX-injective : μ s₁ ≡ μ s₂ → s₁ ≡ s₂
  μX-injective refl = refl

  data ⊢ᶜ_·_ {n} (x : 𝔽 n) : 𝕊 n → Set where
    ⊢c-□ : ⊢ᶜ x · □ E
    ⊢c-♯ : ⊢ᶜ x · ⁉ ♯ T ▸ s
    ⊢c-⋆ : ⊢ᶜ x · ⁉ ⟨ s₁ ⨟ s₂ ⟩
    ⊢c-μ : ⊢ᶜ suc x · s → ⊢ᶜ x · μ s
    ⊢c-` : ∀ {y} → x ≢· y → ⊢ᶜ x · ` y

  ⊢ᶜ_ : 𝕊 (suc n) → Set _
  ⊢ᶜ_ = ⊢ᶜ zero ·_

  ¬-⊢c-`x : {x : 𝔽 n} → ¬ ⊢ᶜ x · ` x
  ¬-⊢c-`x (⊢c-` x≠x) = x≠x refl

  ⊢c-μ⁻¹ : {x : 𝔽 n} → ⊢ᶜ x · μ s → ⊢ᶜ suc x · s
  ⊢c-μ⁻¹ (⊢c-μ x) = x

  -- Well formed sessions ensure that every new variable introduced appears guarded.
  data ⊢_ {n} : 𝕊 n → Set where
    ⊢□′      : ∀ E → ⊢ □ E
    ⊢♯_·_▸_  : ∀ ⁉ T → ⊢ s → ⊢ ⁉ ♯ T ▸ s
    ⊢_⋆⟨_⨟_⟩ : ∀ ⁉ → ⊢ s₁ → ⊢ s₂ → ⊢ ⁉ ⟨ s₁ ⨟ s₂ ⟩
    ⊢μ       : ⊢ s → ⊢ᶜ s → ⊢ μ s
    ⊢`       : ∀ x → ⊢ ` x

  -- Some abbreviations for when the direction/payload is not of interest or can be inferred.
  pattern ⊢□ = ⊢□′ _
  pattern ⊢♯ s = ⊢♯ _ · _ ▸ s
  pattern ⊢⋆⟨_⨟_⟩ s₁ s₂ = ⊢ _ ⋆⟨ s₁ ⨟ s₂ ⟩

  -- Easy extraction of the underlying session from a well-formedness proof.
  ⌊_⌋ : {s : 𝕊 n} → ⊢ s → 𝕊 n
  ⌊_⌋ {s = s} _ = s

  ⊢ᶜ-irr : ∀ {x} {s : 𝕊 n} → Irrelevant (⊢ᶜ x · s)
  ⊢ᶜ-irr ⊢c-□     ⊢c-□     = refl
  ⊢ᶜ-irr ⊢c-♯     ⊢c-♯     = refl
  ⊢ᶜ-irr ⊢c-⋆     ⊢c-⋆     = refl
  ⊢ᶜ-irr (⊢c-` _) (⊢c-` _) = refl
  ⊢ᶜ-irr (⊢c-μ x) (⊢c-μ y) = cong ⊢c-μ (⊢ᶜ-irr x y)

  -- Two well-formedness proofs are equivalent.
  ⊢-irr : {s : 𝕊 n} (x : ⊢ s) (y : ⊢ s) → x ≡ y
  ⊢-irr ⊢□      ⊢□     = refl
  ⊢-irr (⊢` _)  (⊢` _) = refl
  ⊢-irr (⊢♯ x)  (⊢♯ y)
    rewrite ⊢-irr x y
    = refl
  ⊢-irr ⊢⋆⟨ x₁ ⨟ x₂ ⟩ ⊢⋆⟨ y₁ ⨟ y₂ ⟩
    rewrite ⊢-irr x₁ y₁ | ⊢-irr x₂ y₂
    = refl
  ⊢-irr (⊢μ x xᶜ) (⊢μ y yᶜ)
    rewrite ⊢-irr x y | ⊢ᶜ-irr xᶜ yᶜ
    = refl

  dcong-⊢ : {x : ⊢ s₁} (y : ⊢ s₂) (eq : s₁ ≡ s₂) → x ≡ subst ⊢_ (sym eq) y
  dcong-⊢ y refl = ⊢-irr _ y


----------------------------------------------------------------------------------------------------
-- Renaming and substitution of sessions.
--
-- These are standard results applied to our setting.

  infixl 7 _⋯_

  _⋯_ : 𝕊 m → Ren m n → 𝕊 n
  □ e           ⋯ ρ = □ e
  (⁉ ♯ T ▸ s)   ⋯ ρ = ⁉ ♯ T ▸ (s ⋯ ρ)
  ⁉ ⟨ s₁ ⨟ s₂ ⟩ ⋯ ρ = ⁉ ⟨ s₁ ⋯ ρ ⨟ s₂ ⋯ ρ ⟩
  μ s           ⋯ ρ = μ (s ⋯ ↑ ρ)
  ` x           ⋯ ρ = ` ρ x

  ⋯-cong : (s : 𝕊 n) → ρ₁ ≗ ρ₂ → s ⋯ ρ₁ ≡ s ⋯ ρ₂
  ⋯-cong (□ x)           eq = refl
  ⋯-cong (⁉ ♯ T ▸ s)     eq = cong (⁉ ♯ T ▸_) (⋯-cong s eq)
  ⋯-cong (⁉ ⟨ s₁ ⨟ s₂ ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯-cong s₁ eq) (⋯-cong s₂ eq)
  ⋯-cong (μ s)           eq = cong μ (⋯-cong s (↑-pres-≗ eq))
  ⋯-cong (` x)           eq = cong `_ (eq x)

  ⋯-composes : (s : 𝕊 n₁) (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) → s ⋯ ρ₁ ⋯ ρ₂ ≡ s ⋯ (ρ₂ ∘ ρ₁)
  ⋯-composes (□ x)           ρ₁ ρ₂ = refl
  ⋯-composes (⁉ ♯ T ▸ s)     ρ₁ ρ₂ = cong (⁉ ♯ T ▸_) (⋯-composes s ρ₁ ρ₂)
  ⋯-composes (⁉ ⟨ s₁ ⨟ s₂ ⟩) ρ₁ ρ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯-composes s₁ ρ₁ ρ₂) (⋯-composes s₂ ρ₁ ρ₂)
  ⋯-composes (μ s)           ρ₁ ρ₂ = cong μ (trans (⋯-composes s (↑ ρ₁) (↑ ρ₂)) (⋯-cong s (↑-dist-∘ ρ₁ ρ₂)))
  ⋯-composes (` x)           ρ₁ ρ₂ = refl

  ⋯-id : (s : 𝕊 n) → ρ ≗ id → s ⋯ ρ ≡ s
  ⋯-id (□ x)           eq = refl
  ⋯-id (⁉ ♯ T ▸ s)     eq = cong (⁉ ♯ T ▸_) (⋯-id s eq)
  ⋯-id (⁉ ⟨ s₁ ⨟ s₂ ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯-id s₁ eq) (⋯-id s₂ eq)
  ⋯-id (μ s)           eq = cong μ (⋯-id s (λ{ zero → refl; (suc x) → cong suc (eq x) }))
  ⋯-id (` x)           eq = cong `_ (eq x)

  □⋯-injective : (ρ : Ren m n) → s ⋯ ρ ≡ □ E → s ≡ □ E
  □⋯-injective {s = □ E} ρ refl = refl

  ⋯⁻¹-` : ∀ {x} → s ⋯ ρ ≡ ` x → ∃ λ y → s ≡ ` y × ρ y ≡ x
  ⋯⁻¹-` {s = ` x} refl = -, refl , refl

  Sub : ℕ → ℕ → Set _
  Sub m n = (x : 𝔽 m) → 𝕊 n

  infixl 7 _⋯ₛ_
  infixr 7.5 _∷ₛ_
  infixr 11 ↑ₛ_ _↑ₛ⋆_

  idₛ : Sub n n
  idₛ = `_

  _∷ₛ_ : 𝕊 n → Sub m n → Sub (suc m) n
  (s ∷ₛ σ) zero = s
  (s ∷ₛ σ) (suc x) = σ x

  liftₛ : Sub m n → Sub m (suc n)
  liftₛ σ x = σ x ⋯ suc

  ↑ₛ_ : Sub m n → Sub (suc m) (suc n)
  ↑ₛ σ = ` zero ∷ₛ liftₛ σ

  _↑ₛ⋆_ : ∀ m → Sub n n′ → Sub (m + n) (m + n′)
  zero  ↑ₛ⋆ σ = σ
  suc m ↑ₛ⋆ σ = ↑ₛ m ↑ₛ⋆ σ

  0↦ : 𝕊 n → Sub (suc n) n
  0↦ x = x ∷ₛ idₛ

  _⋯ₛ_ : 𝕊 m → Sub m n → 𝕊 n
  □ x         ⋯ₛ σ = □ x
  (⁉ ♯ T ▸ s) ⋯ₛ σ = ⁉ ♯ T ▸ (s ⋯ₛ σ)
  ⁉ ⟨ x ⨟ y ⟩ ⋯ₛ σ = ⁉ ⟨ x ⋯ₛ σ ⨟ y ⋯ₛ σ ⟩
  μ s         ⋯ₛ σ = μ (s ⋯ₛ ↑ₛ σ)
  ` x         ⋯ₛ σ = σ x

  ↑ₛ-id : {σ : Sub n n} → σ ≗ idₛ → ↑ₛ σ ≗ idₛ
  ↑ₛ-id eq zero = refl
  ↑ₛ-id eq (suc x) rewrite eq x = refl

  ↑ₛ-pres-≗ : {σ₁ σ₂ : Sub m n} → σ₁ ≗ σ₂ → ↑ₛ σ₁ ≗ ↑ₛ σ₂
  ↑ₛ-pres-≗ eq zero    = refl
  ↑ₛ-pres-≗ eq (suc x) = cong (_⋯ wk) (eq x)

  ⋯ₛ-id : (s : 𝕊 n) {σ : Sub n n} → σ ≗ idₛ → s ⋯ₛ σ ≡ s
  ⋯ₛ-id (□ x)         eq = refl
  ⋯ₛ-id (⁉ ♯ T ▸ s)   eq = cong (⁉ ♯ T ▸_) (⋯ₛ-id s eq)
  ⋯ₛ-id (⁉ ⟨ x ⨟ y ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛ-id x eq) (⋯ₛ-id y eq)
  ⋯ₛ-id (μ s)         eq = cong μ (⋯ₛ-id s (↑ₛ-id eq))
  ⋯ₛ-id (` x)         eq = eq x

  ⋯ₛ-cong : (s : 𝕊 m) {σ₁ σ₂ : Sub m n} → σ₁ ≗ σ₂ → s ⋯ₛ σ₁ ≡ s ⋯ₛ σ₂
  ⋯ₛ-cong (□ x)         eq = refl
  ⋯ₛ-cong (⁉ ♯ T ▸ s)   eq = cong (⁉ ♯ T ▸_) (⋯ₛ-cong s eq)
  ⋯ₛ-cong (⁉ ⟨ x ⨟ y ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛ-cong x eq) (⋯ₛ-cong y eq)
  ⋯ₛ-cong (μ s)         eq = cong μ (⋯ₛ-cong s (↑ₛ-pres-≗ eq))
  ⋯ₛ-cong (` x)         eq = eq x

  infix 7.5 _·ᵣᵣ_ _·ᵣₛ_ _·ₛᵣ_ _·ₛₛ_

  _·ᵣᵣ_ : ∀ {m n o} → Ren m n → Ren n o → Ren m o
  (ρ₁ ·ᵣᵣ ρ₂) x  = ρ₂ (ρ₁ x)

  _·ᵣₛ_ : ∀ {m n o} → Ren m n → Sub n o → Sub m o
  (ρ₁ ·ᵣₛ σ₂) x  = σ₂ (ρ₁ x)

  _·ₛᵣ_ : ∀ {m n o} → Sub m n → Ren n o → Sub m o
  (σ₁ ·ₛᵣ ρ₂) x  = σ₁ x ⋯ ρ₂

  _·ₛₛ_ : ∀ {m n o} → Sub m n → Sub n o → Sub m o
  (σ₁ ·ₛₛ σ₂) x  = σ₁ x ⋯ₛ σ₂

  private variable
    σ σ₁ σ₂ : Sub m n

  ↑-dist-·ᵣᵣ : ∀ (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    ↑ (ρ₁ ·ᵣᵣ ρ₂) ≗ ↑ ρ₁ ·ᵣᵣ ↑ ρ₂
  ↑-dist-·ᵣᵣ ρ₁ ρ₂ = sym ∘ ↑-dist-∘ ρ₁ ρ₂

  ⋯ᵣᵣ-fusion : ∀ (s : 𝕊 n₁) (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    s ⋯ ρ₁ ⋯ ρ₂ ≡ s ⋯ (ρ₁ ·ᵣᵣ ρ₂)
  ⋯ᵣᵣ-fusion (` x)           ρ₁ ρ₂ = refl
  ⋯ᵣᵣ-fusion (□ x)           ρ₁ ρ₂ = refl
  ⋯ᵣᵣ-fusion (⁉ ♯ T ▸ s)     ρ₁ ρ₂ = cong (⁉ ♯ T ▸_) (⋯ᵣᵣ-fusion s ρ₁ ρ₂)
  ⋯ᵣᵣ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) ρ₁ ρ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ᵣᵣ-fusion s₁ ρ₁ ρ₂) (⋯ᵣᵣ-fusion s₂ ρ₁ ρ₂)
  ⋯ᵣᵣ-fusion (μ s)           ρ₁ ρ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ ↑ ρ₁ ⋯ ↑ ρ₂      ≡⟨ ⋯ᵣᵣ-fusion s (↑ ρ₁) (↑ ρ₂) ⟩
    s ⋯ (↑ ρ₁ ·ᵣᵣ ↑ ρ₂)  ≡⟨ ⋯-cong s (↑-dist-·ᵣᵣ ρ₁ ρ₂) ⟨
    s ⋯ ↑ (ρ₁ ·ᵣᵣ ρ₂)    ∎

  ↑-dist-·ᵣₛ : ∀ (ρ₁ : Ren n₁ n₂) (σ₂ : Sub n₂ n₃) →
    ↑ₛ (ρ₁ ·ᵣₛ σ₂) ≗ ↑ ρ₁ ·ᵣₛ ↑ₛ σ₂
  ↑-dist-·ᵣₛ ρ₁ σ₂ zero = refl
  ↑-dist-·ᵣₛ ρ₁ σ₂ (suc x) = refl

  ⋯ᵣₛ-fusion : ∀ (s : 𝕊 n₁) (ρ₁ : Ren n₁ n₂) (σ₂ : Sub n₂ n₃) →
    s ⋯ ρ₁ ⋯ₛ σ₂ ≡ s ⋯ₛ (ρ₁ ·ᵣₛ σ₂)
  ⋯ᵣₛ-fusion (` x) ρ₁ σ₂ = refl
  ⋯ᵣₛ-fusion (□ x) ρ₁ σ₂ = refl
  ⋯ᵣₛ-fusion (⁉ ♯ T ▸ s) ρ₁ σ₂ = cong (⁉ ♯ T ▸_) (⋯ᵣₛ-fusion s ρ₁ σ₂)
  ⋯ᵣₛ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) ρ₁ σ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ᵣₛ-fusion s₁ ρ₁ σ₂) (⋯ᵣₛ-fusion s₂ ρ₁ σ₂)
  ⋯ᵣₛ-fusion (μ s) ρ₁ σ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ ↑ ρ₁ ⋯ₛ ↑ₛ σ₂      ≡⟨ ⋯ᵣₛ-fusion s (↑ ρ₁) (↑ₛ σ₂) ⟩
    s ⋯ₛ (↑ ρ₁ ·ᵣₛ ↑ₛ σ₂)  ≡⟨ ⋯ₛ-cong s (↑-dist-·ᵣₛ ρ₁ σ₂) ⟨
    s ⋯ₛ ↑ₛ (ρ₁ ·ᵣₛ σ₂)    ∎

  ·-↑ᵣ-wk : ∀ (ρ : Ren n₁ n₂) → ρ ·ᵣᵣ wk ≡ wk ·ᵣᵣ ↑ ρ
  ·-↑ᵣ-wk ρ = refl

  ↑-dist-·ₛᵣ : ∀ (σ₁ : Sub n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    ↑ₛ (σ₁ ·ₛᵣ ρ₂) ≗ ↑ₛ σ₁ ·ₛᵣ ↑ ρ₂
  ↑-dist-·ₛᵣ σ₁ ρ₂ zero = refl
  ↑-dist-·ₛᵣ σ₁ ρ₂ (suc x) =
    let open ≡-Reasoning in
    σ₁ x ⋯ ρ₂ ⋯ wk        ≡⟨ ⋯ᵣᵣ-fusion (σ₁ x) ρ₂ wk ⟩
    σ₁ x ⋯ (ρ₂ ·ᵣᵣ wk)    ≡⟨ cong (σ₁ x ⋯_) (·-↑ᵣ-wk ρ₂) ⟩
    σ₁ x ⋯ (wk ·ᵣᵣ ↑ ρ₂)  ≡⟨ ⋯ᵣᵣ-fusion (σ₁ x) wk (↑ ρ₂) ⟨
    σ₁ x ⋯ wk ⋯ ↑ ρ₂     ∎

  ⋯ₛᵣ-fusion : ∀ (s : 𝕊 n₁) (σ₁ : Sub n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    s ⋯ₛ σ₁ ⋯ ρ₂ ≡ s ⋯ₛ (σ₁ ·ₛᵣ ρ₂)
  ⋯ₛᵣ-fusion (` x) σ₁ ρ₂ = refl
  ⋯ₛᵣ-fusion (□ x) σ₁ ρ₂ = refl
  ⋯ₛᵣ-fusion (⁉ ♯ T ▸ s) σ₁ ρ₂ = cong (⁉ ♯ T ▸_) (⋯ₛᵣ-fusion s σ₁ ρ₂)
  ⋯ₛᵣ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) σ₁ ρ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛᵣ-fusion s₁ σ₁ ρ₂) (⋯ₛᵣ-fusion s₂ σ₁ ρ₂)
  ⋯ₛᵣ-fusion (μ s) σ₁ ρ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ₛ ↑ₛ σ₁ ⋯ ↑ ρ₂      ≡⟨ ⋯ₛᵣ-fusion s (↑ₛ σ₁) (↑ ρ₂) ⟩
    s ⋯ₛ (↑ₛ σ₁ ·ₛᵣ ↑ ρ₂)  ≡⟨ ⋯ₛ-cong s (↑-dist-·ₛᵣ σ₁ ρ₂) ⟨
    s ⋯ₛ ↑ₛ (σ₁ ·ₛᵣ ρ₂)    ∎

  ·-↑ₛ-wk : ∀ (σ : Sub n₁ n₂) → σ ·ₛᵣ wk ≡ wk ·ᵣₛ ↑ₛ σ
  ·-↑ₛ-wk σ = refl

  ↑-dist-·ₛₛ : ∀ (σ₁ : Sub n₁ n₂) (σ₂ : Sub n₂ n₃) →
    ↑ₛ (σ₁ ·ₛₛ σ₂) ≗ ↑ₛ σ₁ ·ₛₛ ↑ₛ σ₂
  ↑-dist-·ₛₛ σ₁ σ₂ zero    = refl
  ↑-dist-·ₛₛ σ₁ σ₂ (suc x) =
    let open ≡-Reasoning in
    σ₁ x ⋯ₛ σ₂ ⋯ wk         ≡⟨ ⋯ₛᵣ-fusion (σ₁ x) σ₂ wk ⟩
    σ₁ x ⋯ₛ (σ₂ ·ₛᵣ wk)     ≡⟨ cong (σ₁ x ⋯ₛ_) (·-↑ₛ-wk σ₂) ⟩
    σ₁ x ⋯ₛ (wk ·ᵣₛ ↑ₛ σ₂)  ≡⟨ ⋯ᵣₛ-fusion (σ₁ x) wk (↑ₛ σ₂) ⟨
    σ₁ x ⋯ wk ⋯ₛ ↑ₛ σ₂      ∎

  ⋯ₛₛ-fusion : ∀ (s : 𝕊 n₁) (σ₁ : Sub n₁ n₂) (σ₂ : Sub n₂ n₃) →
    s ⋯ₛ σ₁ ⋯ₛ σ₂ ≡ s ⋯ₛ (σ₁ ·ₛₛ σ₂)
  ⋯ₛₛ-fusion (` x) σ₁ σ₂ = refl
  ⋯ₛₛ-fusion (□ x) σ₁ σ₂ = refl
  ⋯ₛₛ-fusion (⁉ ♯ T ▸ s) σ₁ σ₂ = cong (⁉ ♯ T ▸_) (⋯ₛₛ-fusion s σ₁ σ₂)
  ⋯ₛₛ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) σ₁ σ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛₛ-fusion s₁ σ₁ σ₂) (⋯ₛₛ-fusion s₂ σ₁ σ₂)
  ⋯ₛₛ-fusion (μ s) σ₁ σ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ₛ ↑ₛ σ₁ ⋯ₛ ↑ₛ σ₂     ≡⟨ ⋯ₛₛ-fusion s (↑ₛ σ₁) (↑ₛ σ₂) ⟩
    s ⋯ₛ (↑ₛ σ₁ ·ₛₛ ↑ₛ σ₂)  ≡⟨ ⋯ₛ-cong s (↑-dist-·ₛₛ σ₁ σ₂) ⟨
    s ⋯ₛ ↑ₛ (σ₁ ·ₛₛ σ₂)     ∎

  exchangeᵣₛ : (s : 𝕊 m) (ρ : Ren m n) → (x : 𝔽 (suc m)) → (↑ ρ ·ᵣₛ 0↦ (s ⋯ ρ)) x ≡ (0↦ s ·ₛᵣ ρ) x
  exchangeᵣₛ s ρ zero    = refl
  exchangeᵣₛ s ρ (suc x) = refl

  exchangeₛₛ : (s : 𝕊 m) (σ : Sub m n) → (x : 𝔽 (suc m)) → (↑ₛ σ ·ₛₛ 0↦ (s ⋯ₛ σ)) x ≡ (0↦ s ·ₛₛ σ) x
  exchangeₛₛ s σ zero = refl
  exchangeₛₛ s σ (suc x) =
    let open ≡-Reasoning in
    σ x ⋯ wk ⋯ₛ (s ⋯ₛ σ) ∷ₛ idₛ      ≡⟨ ⋯ᵣₛ-fusion (σ x) suc _ ⟩
    σ x ⋯ₛ wk ·ᵣₛ ((s ⋯ₛ σ) ∷ₛ idₛ)  ≡⟨⟩
    σ x ⋯ₛ idₛ                       ≡⟨ ⋯ₛ-id (σ x) (λ _ → refl) ⟩
    σ x                              ∎

  ⋯-exchangeᵣₛ : (s : 𝕊 (suc m)) (s′ : 𝕊 m) (ρ : Ren m n) → s ⋯ ↑ ρ ⋯ₛ 0↦ (s′ ⋯ ρ) ≡ s ⋯ₛ 0↦ s′ ⋯ ρ
  ⋯-exchangeᵣₛ s s′ ρ =
    let open ≡-Reasoning in
    s ⋯ ↑ ρ ⋯ₛ 0↦ (s′ ⋯ ρ)    ≡⟨ ⋯ᵣₛ-fusion s (↑ ρ) (0↦ (s′ ⋯ ρ)) ⟩
    s ⋯ₛ ↑ ρ ·ᵣₛ 0↦ (s′ ⋯ ρ)  ≡⟨ ⋯ₛ-cong s (exchangeᵣₛ s′ ρ) ⟩
    s ⋯ₛ 0↦ s′ ·ₛᵣ ρ          ≡⟨ ⋯ₛᵣ-fusion s (0↦ s′) ρ ⟨
    s ⋯ₛ 0↦ s′ ⋯ ρ            ∎

  ⋯-exchangeₛₛ : (s : 𝕊 (suc m)) (s′ : 𝕊 m) (σ : Sub m n) → s ⋯ₛ ↑ₛ σ ⋯ₛ 0↦ (s′ ⋯ₛ σ) ≡ s ⋯ₛ 0↦ s′ ⋯ₛ σ
  ⋯-exchangeₛₛ s s′ σ =
    let open ≡-Reasoning in
    s ⋯ₛ ↑ₛ σ ⋯ₛ 0↦ (s′ ⋯ₛ σ)   ≡⟨ ⋯ₛₛ-fusion s (↑ₛ σ) (0↦ (s′ ⋯ₛ σ)) ⟩
    s ⋯ₛ ↑ₛ σ ·ₛₛ 0↦ (s′ ⋯ₛ σ)  ≡⟨ ⋯ₛ-cong s (exchangeₛₛ s′ σ) ⟩
    s ⋯ₛ 0↦ s′ ·ₛₛ σ            ≡⟨ ⋯ₛₛ-fusion s (0↦ s′) σ ⟨
    s ⋯ₛ 0↦ s′ ⋯ₛ σ             ∎

  ·-wk-cancels-ext : (s : 𝕊 n) (σ : Sub m n) → wk ·ᵣₛ (s ∷ₛ σ) ≡ σ
  ·-wk-cancels-ext s σ = refl

  ·-wk⋆-cancels-0↦ : ∀ m (s : 𝕊 n) → m ↑⋆ wk ·ᵣₛ m ↑ₛ⋆ 0↦ s ≗ idₛ
  ·-wk⋆-cancels-0↦ zero s _ = refl
  ·-wk⋆-cancels-0↦ (suc m) s zero = refl
  ·-wk⋆-cancels-0↦ (suc m) s (suc x) rewrite ·-wk⋆-cancels-0↦ m s x = refl

  ·-wk-cancels-0↦ : ∀ (s : 𝕊 n) → wk ·ᵣₛ 0↦ s ≗ idₛ
  ·-wk-cancels-0↦ s = ·-wk⋆-cancels-0↦ 0 s

  ⋯-wk⋆-cancels-0↦ : ∀ m {s : 𝕊 (m + n)} (s′ : 𝕊 n) →
    s ⋯ m ↑⋆ wk ⋯ₛ m ↑ₛ⋆ 0↦ s′ ≡ s
  ⋯-wk⋆-cancels-0↦ m {s} s′ = let open ≡-Reasoning in
    s ⋯ m ↑⋆ wk ⋯ₛ m ↑ₛ⋆ 0↦ s′    ≡⟨ ⋯ᵣₛ-fusion s (m ↑⋆ wk) (m ↑ₛ⋆ 0↦ s′) ⟩
    s ⋯ₛ m ↑⋆ wk ·ᵣₛ m ↑ₛ⋆ 0↦ s′  ≡⟨ ⋯ₛ-id s (·-wk⋆-cancels-0↦ m s′) ⟩
    s ∎

  ⋯-wk-cancels-0↦ : ∀ (s′ : 𝕊 n) → s ⋯ wk ⋯ₛ 0↦ s′ ≡ s
  ⋯-wk-cancels-0↦ s′ = ⋯-wk⋆-cancels-0↦ 0 s′

  ·-wk-↑ᵣ : (ρ : Ren m n) → ρ ·ᵣᵣ wk ≗ wk ·ᵣᵣ ↑ ρ
  ·-wk-↑ᵣ ρ zero = refl
  ·-wk-↑ᵣ ρ (suc x) = refl

  ⋯-wk-↑ᵣ : ∀ (s : 𝕊 m) (ρ : Ren m n) →
    s ⋯ ρ ⋯ wk ≡ s ⋯ wk ⋯ ↑ ρ
  ⋯-wk-↑ᵣ s ρ = let open ≡-Reasoning in
    s ⋯ ρ ⋯ wk       ≡⟨ ⋯ᵣᵣ-fusion s ρ wk ⟩
    s ⋯ ρ ·ᵣᵣ wk     ≡⟨ ⋯-cong s (·-wk-↑ᵣ ρ) ⟩
    s ⋯ wk ·ᵣᵣ ↑ ρ   ≡⟨ ⋯ᵣᵣ-fusion s wk (↑ ρ) ⟨
    s ⋯ wk ⋯ ↑ ρ     ∎

  ·-wk-↑ₛ : ∀ (σ : Sub n₁ n₂) → σ ·ₛᵣ wk ≗ wk ·ᵣₛ ↑ₛ σ
  ·-wk-↑ₛ σ zero    = refl
  ·-wk-↑ₛ σ (suc x) = refl

  ⋯-wk-↑ₛ : ∀ (s : 𝕊 n₁) (σ : Sub n₁ n₂) →
    s ⋯ₛ σ ⋯ wk ≡ s ⋯ wk ⋯ₛ ↑ₛ σ
  ⋯-wk-↑ₛ s σ =
    let open ≡-Reasoning in
    s ⋯ₛ σ ⋯ wk         ≡⟨ ⋯ₛᵣ-fusion s σ wk ⟩
    s ⋯ₛ (σ ·ₛᵣ wk)     ≡⟨ ⋯ₛ-cong s (·-wk-↑ₛ σ) ⟩
    s ⋯ₛ (wk ·ᵣₛ ↑ₛ σ)  ≡⟨ ⋯ᵣₛ-fusion s wk (↑ₛ σ) ⟨
    s ⋯ wk ⋯ₛ ↑ₛ σ      ∎

  ·-wk-↑ₛ⋆ : (m : ℕ) (σ : Sub n₁ n₂) →
    σ ·ₛᵣ wk⋆ m ≗ wk⋆ m ·ᵣₛ m ↑ₛ⋆ σ
  ·-wk-↑ₛ⋆ zero σ x = ⋯-id (σ x) (λ _ → refl)
  ·-wk-↑ₛ⋆ (suc m) σ x =
    let open ≡-Reasoning in
    σ x ⋯ wk⋆ (suc m)                ≡⟨⟩
    σ x ⋯ wk⋆ m ·ᵣᵣ wk               ≡⟨ ⋯ᵣᵣ-fusion (σ x) (wk⋆ m) wk ⟨
    σ x ⋯ wk⋆ m ⋯ wk                 ≡⟨ cong (_⋯ suc) (·-wk-↑ₛ⋆ m σ x) ⟩
    (m ↑ₛ⋆ σ) (m ↑ʳ x) ⋯ wk          ≡⟨⟩
    (wk⋆ (suc m) ·ᵣₛ suc m ↑ₛ⋆ σ) x  ∎

  ⋯-wk-↑ₛ⋆ : ∀ (s : 𝕊 n₁) (m : ℕ) (σ : Sub n₁ n₂) →
    s ⋯ₛ σ ⋯ wk⋆ m ≡ s ⋯ wk⋆ m ⋯ₛ m ↑ₛ⋆ σ
  ⋯-wk-↑ₛ⋆ s m σ =
    let open ≡-Reasoning in
    s ⋯ₛ σ ⋯ wk⋆ m          ≡⟨ ⋯ₛᵣ-fusion s σ (wk⋆ m) ⟩
    s ⋯ₛ σ ·ₛᵣ wk⋆ m        ≡⟨ ⋯ₛ-cong s (·-wk-↑ₛ⋆ m σ) ⟩
    s ⋯ₛ wk⋆ m ·ᵣₛ m ↑ₛ⋆ σ  ≡⟨ ⋯ᵣₛ-fusion s (wk⋆ m) (m ↑ₛ⋆ σ) ⟨
    s ⋯ wk⋆ m ⋯ₛ m ↑ₛ⋆ σ    ∎

----------------------------------------------------------------------------------------------------
-- Renaming and substitution preserve well-formedness

  module _ where
    open Relation.Unary

    RenOn : Sub m n → Pred (𝔽 m) _
    RenOn σ x = ∃ λ y → σ x ≡ ` y

    renOrC : 𝕊 m → Pred (Sub m n) _
    renOrC s σ = Π[ ∁ (RenOn σ) ⇒ (⊢ᶜ_· s)  ]

  ⊢ᶜ-⋯ : ∀ {x} → ⊢ᶜ x · s → Inj m n ρ → ⊢ᶜ ρ x · s ⋯ ρ
  ⊢ᶜ-⋯ ⊢c-□      ρ = ⊢c-□
  ⊢ᶜ-⋯ ⊢c-♯      ρ = ⊢c-♯
  ⊢ᶜ-⋯ ⊢c-⋆      ρ = ⊢c-⋆
  ⊢ᶜ-⋯ (⊢c-μ s)  ρ = ⊢c-μ (⊢ᶜ-⋯ s (↑-injective ρ))
  ⊢ᶜ-⋯ (⊢c-` ≠x) ρ = ⊢c-` (≠x ∘· ρ)

  ⊢ᶜ-wk′ : ∀ n (x : 𝔽 m) (s : 𝕊 (n + n′)) → ⊢ᶜ n ↑ʳ (x ↑ˡ n′) · s ⋯ n ↑⋆ wk⋆ m
  ⊢ᶜ-wk′ n x (□ e)           = ⊢c-□
  ⊢ᶜ-wk′ n x (⁉ ♯ T ▸ s)     = ⊢c-♯
  ⊢ᶜ-wk′ n x (⁉ ⟨ s₁ ⨟ s₂ ⟩) = ⊢c-⋆
  ⊢ᶜ-wk′ n x (μ s)           = ⊢c-μ (⊢ᶜ-wk′ (suc n) x s)
  ⊢ᶜ-wk′ zero    x (` y)     = ⊢c-` Fin.↑ˡ≢↑ʳ
  ⊢ᶜ-wk′ (suc n) x (` zero)  = ⊢c-` (⊥-elim-irr ∘· ≢-sym Fin.0≢1+n)
  ⊢ᶜ-wk′ (suc n) x (` suc y) = ⊢ᶜ-⋯ (⊢ᶜ-wk′ n x (` y)) Fin.suc-injective

  ⊢ᶜ-wk : (x : 𝔽 m) (s : 𝕊 n) → ⊢ᶜ x ↑ˡ n · s ⋯ wk⋆ m
  ⊢ᶜ-wk = ⊢ᶜ-wk′ 0

  ⊢-⋯ : ⊢ s → Inj m n ρ → ⊢ s ⋯ ρ
  ⊢-⋯ ⊢□              ρ = ⊢□
  ⊢-⋯ (⊢♯ s)          ρ = ⊢♯ (⊢-⋯ s ρ)
  ⊢-⋯ (⊢⋆⟨ s₁ ⨟ s₂ ⟩) ρ = ⊢⋆⟨ ⊢-⋯ s₁ ρ ⨟ ⊢-⋯ s₂ ρ ⟩
  ⊢-⋯ (⊢μ s sᶜ)       ρ = ⊢μ (⊢-⋯ s (↑-injective ρ)) (⊢ᶜ-⋯ sᶜ (↑-injective ρ))
  ⊢-⋯ (⊢` x)          ρ = ⊢` _

  ⊢Sub : Pred (Sub m n) _
  ⊢Sub σ = ∀ x → ⊢ σ x

  ⊢lift : ⊢Sub σ → ⊢Sub (liftₛ σ)
  ⊢lift ⊢σ x = ⊢-⋯ (⊢σ x) Fin.suc-injective

  ⊢ext : ⊢ s → ⊢Sub σ → ⊢Sub (s ∷ₛ σ)
  ⊢ext s ⊢σ zero = s
  ⊢ext s ⊢σ (suc x) = ⊢σ x

  ⊢↑ : ⊢Sub σ → ⊢Sub (↑ₛ σ)
  ⊢↑ ⊢σ = ⊢ext (⊢` zero) (⊢lift ⊢σ)

  ⊢idₛ : ∀ n → ⊢Sub (idₛ {n})
  ⊢idₛ _ x = ⊢` x

  ⊢0↦ : ⊢ s → ⊢Sub (0↦ s)
  ⊢0↦ s = ⊢ext s (⊢idₛ _)

  ⊢ᶜ-⋯ₛ-∀c : {x : 𝔽 m} {y : 𝔽 n} (σ : Sub m n) → ⊢ᶜ x · s → σ x ≡ ` y → (∀ z → x ≢· z → ⊢ᶜ y · σ z) → ⊢ᶜ y · s ⋯ₛ σ
  ⊢ᶜ-⋯ₛ-∀c σ ⊢c-□ σx=y ∀c-y = ⊢c-□
  ⊢ᶜ-⋯ₛ-∀c σ ⊢c-♯ σx=y ∀c-y = ⊢c-♯
  ⊢ᶜ-⋯ₛ-∀c σ ⊢c-⋆ σx=y ∀c-y = ⊢c-⋆
  ⊢ᶜ-⋯ₛ-∀c σ (⊢c-` x≠) σx=y ∀c-y = ∀c-y _ x≠
  ⊢ᶜ-⋯ₛ-∀c σ (⊢c-μ xᶜ) σx=y ∀c-y = ⊢c-μ $ ⊢ᶜ-⋯ₛ-∀c (↑ₛ σ) xᶜ (cong (_⋯ suc) σx=y) λ where
    zero x≠0 → ⊢c-` λ()
    (suc z) x≠z → ⊢ᶜ-⋯ (∀c-y z (x≠z ∘· cong suc)) Fin.suc-injective

  ⊢ᶜ-⋯ₛ-↑ : (σ : Sub m n) → ⊢ᶜ s → ⊢ᶜ s ⋯ₛ ↑ₛ σ
  ⊢ᶜ-⋯ₛ-↑ σ sᶜ = ⊢ᶜ-⋯ₛ-∀c (↑ₛ σ) sᶜ refl λ where
    zero    0≠0   → ⊥-elim (0≠0 refl)
    (suc x) 0≠1+x → ⊢ᶜ-wk zero (σ x)

  ⊢-⋯ₛ : ⊢ s → ⊢Sub σ → ⊢ s ⋯ₛ σ
  ⊢-⋯ₛ ⊢□          ⊢σ = ⊢□
  ⊢-⋯ₛ (⊢♯ s)      ⊢σ = ⊢♯ (⊢-⋯ₛ s ⊢σ)
  ⊢-⋯ₛ ⊢⋆⟨ x ⨟ y ⟩ ⊢σ = ⊢⋆⟨ ⊢-⋯ₛ x ⊢σ ⨟ ⊢-⋯ₛ y ⊢σ ⟩
  ⊢-⋯ₛ (⊢μ s sᶜ)   ⊢σ = ⊢μ (⊢-⋯ₛ s (⊢↑ ⊢σ)) (⊢ᶜ-⋯ₛ-↑ _ sᶜ)
  ⊢-⋯ₛ (⊢` x)      ⊢σ = ⊢σ x

  ⊢·ᵣₛ : (ρ : Ren m n) → ⊢Sub σ → ⊢Sub (ρ ·ᵣₛ σ)
  ⊢·ᵣₛ ρ ⊢σ x = ⊢σ (ρ x)

  ⊢·ₛᵣ : ⊢Sub σ → Inj′ ρ → ⊢Sub (σ ·ₛᵣ ρ)
  ⊢·ₛᵣ ⊢σ ρ x = ⊢-⋯ (⊢σ x) ρ

  ⊢·ₛₛ : ⊢Sub σ₁ → ⊢Sub σ₂ → ⊢Sub (σ₁ ·ₛₛ σ₂)
  ⊢·ₛₛ ⊢σ₁ ⊢σ₂ x = ⊢-⋯ₛ (⊢σ₁ x) ⊢σ₂

  ⊢fusionₛₛ : (⊢s : ⊢ s) (⊢σ₁ : ⊢Sub σ₁) (⊢σ₂ : ⊢Sub σ₂) →
    ⊢-⋯ₛ (⊢-⋯ₛ ⊢s ⊢σ₁) ⊢σ₂ ≡ subst ⊢_ (sym (⋯ₛₛ-fusion s σ₁ σ₂)) (⊢-⋯ₛ ⊢s (⊢·ₛₛ ⊢σ₁ ⊢σ₂))
  ⊢fusionₛₛ ⊢s ⊢σ₁ ⊢σ₂ = dcong-⊢ (⊢-⋯ₛ ⊢s (⊢·ₛₛ ⊢σ₁ ⊢σ₂)) (⋯ₛₛ-fusion ⌊ ⊢s ⌋ _ _)

  ⊢fusionₛᵣ : (⊢s : ⊢ s) (τ : ⊢Sub σ) (π : Inj′ ρ) →
    ⊢-⋯ (⊢-⋯ₛ ⊢s τ) π ≡ subst ⊢_ (sym (⋯ₛᵣ-fusion s σ ρ)) (⊢-⋯ₛ ⊢s (⊢·ₛᵣ τ π))
  ⊢fusionₛᵣ ⊢s τ π = dcong-⊢ (⊢-⋯ₛ ⊢s (⊢·ₛᵣ τ π)) (⋯ₛᵣ-fusion ⌊ ⊢s ⌋ _ _)

  ⊢fusionᵣₛ : (⊢s : ⊢ s) (π : Inj′ ρ) (τ : ⊢Sub σ) →
    ⊢-⋯ₛ (⊢-⋯ ⊢s π) τ ≡ subst ⊢_ (sym (⋯ᵣₛ-fusion s ρ σ)) (⊢-⋯ₛ ⊢s (⊢·ᵣₛ ρ τ))
  ⊢fusionᵣₛ ⊢s π τ = dcong-⊢ (⊢-⋯ₛ ⊢s (⊢·ᵣₛ _ τ)) (⋯ᵣₛ-fusion ⌊ ⊢s ⌋ _ _)

  unfold : 𝕊 (suc n) → 𝕊 n
  unfold s = s ⋯ₛ 0↦ (μ s)

  ⊢-unfold : ⊢ s → ⊢ᶜ s → ⊢ unfold s
  ⊢-unfold ⊢s sᶜ = ⊢-⋯ₛ ⊢s (⊢0↦ (⊢μ ⊢s sᶜ))

----------------------------------------------------------------------------------------------------
-- `Step`/`Path` restricts the raw steps/raw paths to the set fitting a specific session type.
--
-- We also define functions accessing the targets of steps/paths.

  data Step {n} : RawStep → 𝕊 n → Set where
    step-♯  : Step step-♯  (⁉ ♯ T ▸ s)
    step-⋆₁ : Step step-⋆₁ (⁉ ⟨ s₁ ⨟ s₂ ⟩)
    step-⋆₂ : Step step-⋆₂ (⁉ ⟨ s₁ ⨟ s₂ ⟩)
    step-μ  : ∀ {step} → Step step (unfold s) → Step step (μ s)

  step-irr : Relation.Binary.Irrelevant (Step {n})
  step-irr step-♯      step-♯      = refl
  step-irr step-⋆₁     step-⋆₁     = refl
  step-irr step-⋆₂     step-⋆₂     = refl
  step-irr (step-μ s₁) (step-μ s₂) = cong step-μ (step-irr s₁ s₂)

  step-⋯ₛ : ∀ {rstep} → Step rstep s → Step rstep (s ⋯ₛ σ)
  step-⋯ₛ {s = ⁉ ♯ T ▸ s} step-♯ = step-♯
  step-⋯ₛ {s = ⁉ ⟨ s₁ ⨟ s₂ ⟩} step-⋆₁ = step-⋆₁
  step-⋯ₛ {s = ⁉ ⟨ s₁ ⨟ s₂ ⟩} step-⋆₂ = step-⋆₂
  step-⋯ₛ {s = μ s} (step-μ x) = step-μ (subst (Step _) (sym (⋯-exchangeₛₛ s (μ s) _)) (step-⋯ₛ x))

  target : ∀ {rstep} {s : 𝕊 n} → Step rstep s → 𝕊 n
  target {s = ⁉ ♯ T ▸ s}   step-♯  = s
  target {s = ⁉ ⟨ s ⨟ _ ⟩} step-⋆₁ = s
  target {s = ⁉ ⟨ _ ⨟ s ⟩} step-⋆₂ = s
  target {s = μ s} (step-μ x) = target x

  ⊢-target : ∀ {rstep} (⊢s : ⊢ s) (step : Step rstep s) → ⊢ target step
  ⊢-target (⊢♯ x)      step-♯     = x
  ⊢-target ⊢⋆⟨ x ⨟ _ ⟩ step-⋆₁    = x
  ⊢-target ⊢⋆⟨ _ ⨟ x ⟩ step-⋆₂    = x
  ⊢-target (⊢μ x xᶜ)   (step-μ s) = ⊢-target (⊢-unfold x xᶜ) s

  Path : REL RawPath (𝕊 n) _
  Path []      s = ⊤
  Path (x ∷ π) s = Σ[ step ∈ Step x s ] Path π (target step)

  path-irr : Relation.Binary.Irrelevant (Path {n})
  path-irr {x = []}    π₁        π₂        = refl
  path-irr {x = _ ∷ _} (s₁ , π₁) (s₂ , π₂)
    rewrite step-irr s₁ s₂ | path-irr π₁ π₂
    = refl

  target* : ∀ {s : 𝕊 n} {π : RawPath} → Path π s → 𝕊 n
  target* {s = s} {[]}    _       = s
  target* {s = s} {_ ∷ _} (x , π) = target* π

  ⊢-target* : ∀ (⊢s : ⊢ s) {rπ} (π : Path rπ s) → ⊢ target* π
  ⊢-target* ⊢s {[]}    _       = ⊢s
  ⊢-target* ⊢s {_ ∷ _} (x , π) = ⊢-target* (⊢-target ⊢s x) π

------------------------------------------------------------------------------------------------------------------------
-- We define an induction measure `μLeaders`.

  μLeaders : 𝕊 n → ℕ
  μLeaders (□ x)           = 0
  μLeaders (⁉ ♯ T ▸ s)     = 0
  μLeaders (⁉ ⟨ s₁ ⨟ s₂ ⟩) = 0
  μLeaders (` x)           = 0
  μLeaders (μ s)           = suc (μLeaders s)

  μLeaders-⋯ : (s : 𝕊 m) (ρ : Ren m n) → μLeaders (s ⋯ ρ) ≡ μLeaders s
  μLeaders-⋯ (□ E)           _ = refl
  μLeaders-⋯ (⁉ ♯ T ▸ s)     _ = refl
  μLeaders-⋯ (⁉ ⟨ s₁ ⨟ s₂ ⟩) _ = refl
  μLeaders-⋯ (μ s)           _ = cong suc (μLeaders-⋯ s _)
  μLeaders-⋯ (` x)           _ = refl

  μLeaders-⋯ₛ : {s : 𝕊 m} → ⊢ s → renOrC s σ → μLeaders (s ⋯ₛ σ) ≡ μLeaders s
  μLeaders-⋯ₛ ⊢□          ρ⊎sᶜ = refl
  μLeaders-⋯ₛ (⊢♯ s)      ρ⊎sᶜ = refl
  μLeaders-⋯ₛ ⊢⋆⟨ _ ⨟ _ ⟩ ρ⊎sᶜ = refl
  μLeaders-⋯ₛ (⊢μ s sᶜ)   ρ⊎sᶜ = cong suc $ μLeaders-⋯ₛ s λ where
    zero    ¬ρ → sᶜ
    (suc x) ¬ρ → ⊢c-μ⁻¹ $ ρ⊎sᶜ x λ{ (z , eq) → ¬ρ $ -, cong (_⋯ suc) eq }
  μLeaders-⋯ₛ {σ = σ} (⊢` x) ρ⊎sᶜ with σ x in eq
  ... | ` x′        = refl
  ... | □ x         = refl
  ... | ⁉ ♯ T ▸ _   = refl
  ... | ⁉ ⟨ _ ⨟ _ ⟩ = refl
  ... | μ s = ⊥-elim $ ¬-⊢c-`x $ ρ⊎sᶜ x λ{ (y , eq′) → case (trans (sym eq) eq′) of λ() }

  -- The induction measure's main property: if s has at least one free variable then
  --
  --   μLeaders (unfold s) ≡ μLeaders s
  --
  -- (The type signature is slightly more general than that.)
  μLeaders-⋯ₛ-0↦ : {s⁰ : 𝕊 n} → ⊢ s → ⊢ᶜ s → μLeaders (s ⋯ₛ 0↦ s⁰) ≡ μLeaders s
  μLeaders-⋯ₛ-0↦ s sᶜ = μLeaders-⋯ₛ s λ where
    zero    ¬ρ → sᶜ
    (suc x) ¬ρ → ⊥-elim (¬ρ (-, refl))

  μLeaders-⋯ₛ-≤ : (s : 𝕊 m) → μLeaders s ≤ μLeaders (s ⋯ₛ σ)
  μLeaders-⋯ₛ-≤ (□ x)           = z≤n
  μLeaders-⋯ₛ-≤ (⁉ ♯ T ▸ s)     = z≤n
  μLeaders-⋯ₛ-≤ (⁉ ⟨ s₁ ⨟ s₂ ⟩) = z≤n
  μLeaders-⋯ₛ-≤ (μ s)           = s≤s (μLeaders-⋯ₛ-≤ s)
  μLeaders-⋯ₛ-≤ (` x)           = z≤n


module _ where
  open Functions

  SREL : ∀ (E₁ E₂ : Set) (n : ℕ) (ℓ : Level) → Set _
  SREL E₁ E₂ n ℓ = {s₁ : Core.𝕊 E₁ n} {s₂ : Core.𝕊 E₂ n} → REL (⊢ s₁) (⊢ s₂) ℓ

  SRel : ∀ (E : Set) (n : ℕ) (ℓ : Level) → Set _
  SRel E = SREL E E


------------------------------------------------------------------------------------------------------------------------
-- Prefixes (borrowed sessions) only have one way to end (END = ⊤). Owned session types must differentiate between
-- Wait and Term which is done by instantiating END = Dir.
End-ℙ = ⊤
End-𝕊 = Dir

module _ {END : Set} where
  open Core End-ℙ using () renaming (𝕊 to ℙ)
  open Core END   using (𝕊)
  open Core.𝕊
  open Functions

  private variable
    p : ℙ n
    s : 𝕊 n

----------------------------------------------------------------------------------------------------
-- Session type composition (written in the paper as  R ⨟ S).

  infixr 6 _◇_

  _◇_ : ℙ n → 𝕊 n → 𝕊 n
  □ x           ◇ s = s
  (⁉ ♯ T ▸ p)   ◇ s = ⁉ ♯ T ▸ p ◇ s
  ⁉ ⟨ p₁ ⨟ p₂ ⟩ ◇ s = ⁉ ⟨ p₁ ◇ s ⨟ p₂ ◇ s ⟩
  μ p           ◇ s = μ (p ◇ s ⋯ suc)
  ` x           ◇ s = ` x

  ⊢ᶜ_·[_◇_] : ∀ x → ⊢ᶜ x · p → ⊢ᶜ x · s → ⊢ᶜ x · p ◇ s
  ⊢ᶜ x ·[ ⊢c-□    ◇ sᶜ ] = sᶜ
  ⊢ᶜ x ·[ ⊢c-♯    ◇ sᶜ ] = ⊢c-♯
  ⊢ᶜ x ·[ ⊢c-⋆    ◇ sᶜ ] = ⊢c-⋆
  ⊢ᶜ x ·[ ⊢c-μ pᶜ ◇ sᶜ ] = ⊢c-μ ⊢ᶜ suc x ·[ pᶜ ◇ ⊢ᶜ-⋯ sᶜ wk-injective ]
  ⊢ᶜ x ·[ ⊢c-` x≠ ◇ sᶜ ] = ⊢c-` x≠

  ⊢ᶜ[_◇_] : ⊢ᶜ p → (s : 𝕊 n) → ⊢ᶜ p ◇ (s ⋯ wk)
  ⊢ᶜ[ pᶜ ◇ s ] = ⊢ᶜ zero ·[ pᶜ ◇ ⊢ᶜ-wk zero s ]

  ⊢[_◇_] : ⊢ p → ⊢ s → ⊢ p ◇ s
  ⊢[ ⊢□            ◇ s ] = s
  ⊢[ ⊢♯ p          ◇ s ] = ⊢♯ ⊢[ p ◇ s ]
  ⊢[ ⊢⋆⟨ p₁ ⨟ p₂ ⟩ ◇ s ] = ⊢⋆⟨ ⊢[ p₁ ◇ s ] ⨟ ⊢[ p₂ ◇ s ] ⟩
  ⊢[ ⊢μ p pᶜ       ◇ s ] = ⊢μ ⊢[ p ◇ ⊢-⋯ s wk-injective ] ⊢ᶜ[ pᶜ ◇ _ ]
  ⊢[ ⊢` x          ◇ s ] = ⊢` x

  [_◇_]⋯-dist : (p : ℙ m) (s : 𝕊 m) (ρ : Ren m n) → (p ◇ s) ⋯ ρ ≡ p ⋯ ρ ◇ s ⋯ ρ
  [ ` x           ◇ s ]⋯-dist ρ = refl
  [ □ x           ◇ s ]⋯-dist ρ = refl
  [ ⁉ ♯ T ▸ p     ◇ s ]⋯-dist ρ = cong (⁉ ♯ T ▸_) ([ p ◇ s ]⋯-dist ρ)
  [ ⁉ ⟨ p₁ ⨟ p₂ ⟩ ◇ s ]⋯-dist ρ = cong₂ (⁉ ⟨_⨟_⟩) ([ p₁ ◇ s ]⋯-dist ρ) ([ p₂ ◇ s ]⋯-dist ρ)
  [ μ p           ◇ s ]⋯-dist ρ =
    cong μ
      $ trans ([ p ◇ s ⋯ wk ]⋯-dist (↑ ρ))
      $ cong (p ⋯ ↑ ρ ◇_) (sym (⋯-wk-↑ᵣ s ρ))

  ◇-⋯0↦⋆-dist : (m : ℕ) (p : ℙ (m + suc n)) (s : 𝕊 n) (p′ : ℙ n) →
    (p ◇ (s ⋯ wk ⋯ wk⋆ m)) ⋯ₛ m ↑ₛ⋆ 0↦ (p′ ◇ s) ≡ p ⋯ₛ m ↑ₛ⋆ 0↦ p′ ◇ s ⋯ wk⋆ m
  ◇-⋯0↦⋆-dist m (□ x) s p′ =
    trans (sym (⋯-wk-↑ₛ⋆ (s ⋯ wk) m (0↦ (p′ ◇ s))))
      $ cong (_⋯ wk⋆ m) (⋯-wk-cancels-0↦ (p′ ◇ s))
  ◇-⋯0↦⋆-dist m (⁉ ♯ T ▸ p) s p′ = cong (⁉ ♯ T ▸_) (◇-⋯0↦⋆-dist m p s p′)
  ◇-⋯0↦⋆-dist m (⁉ ⟨ p₁ ⨟ p₂ ⟩) s p′ = cong₂ (⁉ ⟨_⨟_⟩) (◇-⋯0↦⋆-dist m p₁ s p′) (◇-⋯0↦⋆-dist m p₂ s p′)
  ◇-⋯0↦⋆-dist m (μ p) s p′
    rewrite ⋯ᵣᵣ-fusion s (wk⋆ m) wk
    rewrite ⋯ᵣᵣ-fusion (s ⋯ wk) (wk⋆ m) wk
    = cong μ (◇-⋯0↦⋆-dist (suc m) p s p′)
  ◇-⋯0↦⋆-dist zero    (` zero)  s p′ rewrite ⋯-id s (λ z → refl) = refl
  ◇-⋯0↦⋆-dist zero    (` suc z) s p′ = refl
  ◇-⋯0↦⋆-dist (suc m) (` zero)  s p′ = refl
  ◇-⋯0↦⋆-dist (suc m) (` suc z) s p′ =
    trans (cong (_⋯ suc) (◇-⋯0↦⋆-dist m (` z) s p′))
      $ trans ([ (m ↑ₛ⋆ 0↦ p′) z ◇ s ⋯ wk⋆ m ]⋯-dist wk)
      $ cong ((m ↑ₛ⋆ 0↦ p′) z ⋯ wk ◇_) (⋯ᵣᵣ-fusion s (wk⋆ m) wk)

  unfold[_◇_] : (p : ℙ (suc n)) (s : 𝕊 n) → unfold (p ◇ s ⋯ wk) ≡ unfold p ◇ s
  unfold[ p ◇ s ] =
    trans (cong (λ s′ → (p ◇ s′) ⋯ₛ 0↦ (μ p ◇ s)) (sym (⋯-id (s ⋯ wk) (λ _ → refl))))
      $ trans (◇-⋯0↦⋆-dist 0 p s (μ p))
      $ cong (unfold p ◇_) (⋯-id s λ _ → refl)

  μLeaders-◇-⋯0↦⋆ : ∀ m (p : ℙ (m + suc n)) (pᶜ : ⊢ᶜ m ↑ʳ zero · p) (p′ : ℙ n) (s : 𝕊 n) →
    μLeaders (p ⋯ₛ m ↑ₛ⋆ 0↦ p′ ◇ s ⋯ wk⋆ m) ≡ μLeaders (p ◇ s ⋯ wk ⋯ wk⋆ m)
  μLeaders-◇-⋯0↦⋆ m (□ x) pᶜ p′ s =
    let open ≡-Reasoning in
    μLeaders (s ⋯ wk⋆ m)       ≡⟨ μLeaders-⋯ s (wk⋆ m) ⟩
    μLeaders s                 ≡⟨ μLeaders-⋯ s wk ⟨
    μLeaders (s ⋯ wk)          ≡⟨ μLeaders-⋯ (s ⋯ wk) (wk⋆ m) ⟨
    μLeaders (s ⋯ wk ⋯ wk⋆ m)  ∎
  μLeaders-◇-⋯0↦⋆ m (⁉ ♯ T ▸ p)   pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ m (⁉ ⟨ _ ⨟ _ ⟩) pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ m (μ p) (⊢c-μ pᶜ) p′ s
    rewrite ⋯ᵣᵣ-fusion s (wk⋆ m) wk
    rewrite ⋯ᵣᵣ-fusion (s ⋯ wk) (wk⋆ m) wk
    = cong suc $ μLeaders-◇-⋯0↦⋆ (suc m) p pᶜ p′ s
  μLeaders-◇-⋯0↦⋆ zero (` zero) pᶜ p′ s = ⊥-elim (¬-⊢c-`x pᶜ)
  μLeaders-◇-⋯0↦⋆ zero (` suc x) pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ (suc m) (` zero) pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ (suc m) (` suc z) (⊢c-` 0≠) p′ s =
    let open ≡-Reasoning in
    let z⋯ₛ = ` z ⋯ₛ m ↑ₛ⋆ 0↦ p′ in
    let IH = μLeaders-◇-⋯0↦⋆ m (` z) (⊢c-` (0≠ ∘· cong suc)) p′ s in
    μLeaders (z⋯ₛ ⋯ wk ◇ s ⋯ wk⋆ (suc m))       ≡⟨ cong (μLeaders ∘ (z⋯ₛ ⋯ wk ◇_)) (⋯ᵣᵣ-fusion s (wk⋆ m) wk) ⟨
    μLeaders (z⋯ₛ ⋯ wk ◇ s ⋯ wk⋆ m ⋯ wk)        ≡⟨ cong μLeaders ([ z⋯ₛ ◇ s ⋯ wk⋆ m ]⋯-dist wk) ⟨
    μLeaders ((z⋯ₛ     ◇ s ⋯ wk⋆ m) ⋯ wk)       ≡⟨ μLeaders-⋯ (z⋯ₛ ◇ s ⋯ wk⋆ m) wk ⟩
    μLeaders (z⋯ₛ      ◇ s ⋯ wk⋆ m)             ≡⟨ IH ⟩
    μLeaders (` suc z  ◇ s ⋯ wk ⋯ wk⋆ (suc m))  ∎

  μLeaders-unfold[_◇_] : (pᶜ : ⊢ᶜ p) (s : 𝕊 n) → μLeaders (unfold p ◇ s) ≡ μLeaders (p ◇ s ⋯ wk)
  μLeaders-unfold[_◇_] {p = p} pᶜ s =
    trans (cong (μLeaders ∘ (unfold p ◇_)) (sym (⋯-id s λ _ → refl)))
      $ trans (μLeaders-◇-⋯0↦⋆ 0 p pᶜ (μ p) s)
      $ cong (μLeaders ∘ (p ◇_))
      $ ⋯-id (s ⋯ wk) (λ _ → refl)

  step◇ : ∀ {rstep} → Step rstep p → (s : 𝕊 n) → Step rstep (p ◇ s)
  step◇ step-♯  s = step-♯
  step◇ step-⋆₁ s = step-⋆₁
  step◇ step-⋆₂ s = step-⋆₂
  step◇ (step-μ {p} x) s = step-μ (subst (Step _) (sym unfold[ p ◇ s ]) (step◇ x s))

  target-step◇ : ∀ {rstep} (step : Step rstep p) s → target (step◇ step s) ≡ target step ◇ s
  target-step◇ step-♯  s = refl
  target-step◇ step-⋆₁ s = refl
  target-step◇ step-⋆₂ s = refl
  target-step◇ (step-μ {p} step) s rewrite unfold[ p ◇ s ] = target-step◇ step s

  path◇ : ∀ {rπ} → Path rπ p → (s : 𝕊 n) → Path rπ (p ◇ s)
  path◇ {rπ = []}    _       s = _
  path◇ {rπ = _ ∷ _} (x , π) s = step◇ x s , subst (Path _) (sym (target-step◇ x s)) (path◇ π s)


------------------------------------------------------------------------------------------------------------------------
-- Given a decidable equality for the base types 𝕋 and END values the syntactic equality of sessions is decidable.
--
module EqualityCore (_≟T_ : DecidableEquality 𝕋) {END : Set} (_≟E_ : DecidableEquality END) where
  open Core (END)

  infix 4 _≟_

  _≟_ : DecidableEquality (𝕊 n)
  □ x ≟ □ y = map′ (λ{ refl → refl }) (λ{ refl → refl }) (x ≟E y)
  ⁉₁ ♯ T ▸ x ≟ ⁉₂ ♯ U ▸ y = map′ (λ{ (refl , refl , refl) → refl })
                                 (λ{ refl → refl , refl , refl })
                                 (⁉₁ ≟⁉ ⁉₂ ×-dec T ≟T U ×-dec x ≟ y)
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩ = map′ (λ{ (refl , refl , refl) → refl })
                                         (λ{ refl → refl , refl , refl })
                                         (⁉₁ ≟⁉ ⁉₂ ×-dec x₁ ≟ y₁ ×-dec x₂ ≟ y₂)
  μ x ≟ μ y = map′ (λ{ refl → refl }) (λ{ refl → refl }) (x ≟ y)
  ` x ≟ ` y = map′ (λ{ refl → refl }) (λ{ refl → refl }) (x Fin.≟ y)

  □ x ≟ ⁉ ♯ T ▸ y             = no λ()
  □ x ≟ ⁉ ⟨ y₁ ⨟ y₂ ⟩         = no λ()
  □ x ≟ μ y                   = no λ()
  □ x ≟ ` y                   = no λ()

  ⁉₁ ♯ T ▸ x ≟ □ y            = no λ()
  ⁉₁ ♯ T ▸ x ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩ = no λ()
  ⁉₁ ♯ T ▸ x ≟ μ y            = no λ()
  ⁉₁ ♯ T ▸ x ≟ ` y            = no λ()

  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ □ y        = no λ()
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ ⁉₂ ♯ U ▸ y = no λ()
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ μ y        = no λ()
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ ` y        = no λ()

  μ x ≟ □ y                   = no λ()
  μ x ≟ ⁉₂ ♯ U ▸ y            = no λ()
  μ x ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩        = no λ()
  μ x ≟ ` y                   = no λ()

  ` x ≟ □ y                   = no λ()
  ` x ≟ ⁉₂ ♯ U ▸ y            = no λ()
  ` x ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩        = no λ()
  ` x ≟ μ y                   = no λ()

  decSetoid : ℕ → DecSetoid _ _
  decSetoid n = Eq.decSetoid (_≟_ {n})

  decSetoid₀ : DecSetoid _ _
  decSetoid₀ = decSetoid 0

open Core End-ℙ using () renaming (𝕊 to ℙ) public
open Core End-𝕊 using (𝕊) public
open Core.𝕊 public

module Equality (eq : DecidableEquality 𝕋) where
  open EqualityCore eq Unit._≟_ renaming
    ( _≟_ to infix 4 _≟ℙ_
    ; decSetoid  to decSetoid-ℙ
    ; decSetoid₀ to decSetoid-ℙ₀
    ) public
  open EqualityCore eq _≟⁉_ public
