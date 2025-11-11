----------------------------------------------------------------------------------------------------
-- Lemmas about the number of syntactic subterms of a session type.
--
-- Based on the proofs by Gapeyev et al. (2002).

module PrefixStripping.Sessions.Subterm (𝕋 : Set) {END : Set} where

open import Function using (_⇔_)

open import PrefixStripping.Prelude hiding (trans)
open import PrefixStripping.Syntax

import PrefixStripping.Sessions 𝕋 as Sessions
open Sessions.Core END
open Sessions.Variables END
open Sessions.Functions

open import Data.Vec.Functional as V using (Vector)
import Data.Vec.Functional.Properties as V

open Nat.Variables

----------------------------------------------------------------------------------------------------
-- We can count the number of subterms

count : 𝕊 n → ℕ
childCount : 𝕊 n → ℕ

count = suc ∘ childCount

childCount (` x)           = 0
childCount (□ x)           = 0
childCount (⁉ ♯ T ▸ s)     = count s
childCount (⁉ ⟨ s₁ ⨟ s₂ ⟩) = count s₁ + count s₂
childCount (μ s)           = count s

----------------------------------------------------------------------------------------------------
-- Top down subterms

infix 4 _⊑_

data _⊑_ (s : 𝕊 n) : Pred (𝕊 n) 0ℓ where
  refl  : s ⊑ s
  ⊑-♯   : s ⊑ s′ → s ⊑ ⁉ ♯ T ▸ s′
  ⊑-⋆₁  : s ⊑ s₁ → s ⊑ ⁉ ⟨ s₁ ⨟ s₂ ⟩
  ⊑-⋆₂  : s ⊑ s₂ → s ⊑ ⁉ ⟨ s₁ ⨟ s₂ ⟩
  ⊑-μ   : s ⊑ unfold s′ → s ⊑ μ s′

trans : s₁ ⊑ s₂ → s₂ ⊑ s₃ → s₁ ⊑ s₃
trans xy refl      = xy
trans xy (⊑-♯  yz) = ⊑-♯  (trans xy yz)
trans xy (⊑-⋆₁ yz) = ⊑-⋆₁ (trans xy yz)
trans xy (⊑-⋆₂ yz) = ⊑-⋆₂ (trans xy yz)
trans xy (⊑-μ  yz) = ⊑-μ  (trans xy yz)


----------------------------------------------------------------------------------------------------
-- Bottom up subterms

infix 4 _≼_

data _≼_ {n} : Rel (𝕊 n) 0ℓ where
  refl   : s ≼ s
  ≼-♯    : s ≼ s′ → s ≼ ⁉ ♯ T ▸ s′
  ≼-⋆₁   : s ≼ s₁ → s ≼ ⁉ ⟨ s₁ ⨟ s₂ ⟩
  ≼-⋆₂   : s ≼ s₂ → s ≼ ⁉ ⟨ s₁ ⨟ s₂ ⟩
  ≼-μ    : s ≼ s′ → s ⋯ₛ 0↦ (μ s′) ≼ μ s′

≼-reflexive : s₁ ≡ s₂ → s₁ ≼ s₂
≼-reflexive refl = refl

----------------------------------------------------------------------------------------------------
-- The set of top-down subterms is a subset of the set of bottom-up subterms.

infixl 7 _≼⋯_

_≼⋯_ : s₁ ≼ s₂ → (ρ : Ren m n) → s₁ ⋯ ρ ≼ s₂ ⋯ ρ
refl   ≼⋯ ρ = refl
≼-♯  x ≼⋯ ρ = ≼-♯ (x ≼⋯ ρ)
≼-⋆₁ x ≼⋯ ρ = ≼-⋆₁ (x ≼⋯ ρ)
≼-⋆₂ x ≼⋯ ρ = ≼-⋆₂ (x ≼⋯ ρ)
≼-μ {s} {s′} x ≼⋯ ρ = subst (_≼ _) (⋯-exchangeᵣₛ s (μ s′) ρ) (≼-μ (x ≼⋯ ↑ ρ))

≼-⋯wk : ∀ m {s₁ : 𝕊 (m + suc n)} {s₂ : 𝕊 (m + n)} → s₁ ≼ s₂ ⋯ m ↑⋆ wk → ∃ λ s₁′ → s₁′ ⋯ m ↑⋆ wk ≡ s₁ × s₁′ ≼ s₂
≼-⋯wk m {s₂ = ⁉ ♯ T ▸ _}   (≼-♯ x)  = Π.map₂ (Π.map₂ ≼-♯)  (≼-⋯wk m x)
≼-⋯wk m {s₂ = ⁉ ⟨ _ ⨟ _ ⟩} (≼-⋆₁ x) = Π.map₂ (Π.map₂ ≼-⋆₁) (≼-⋯wk m x)
≼-⋯wk m {s₂ = ⁉ ⟨ _ ⨟ _ ⟩} (≼-⋆₂ x) = Π.map₂ (Π.map₂ ≼-⋆₂) (≼-⋯wk m x)
≼-⋯wk m {s₂ = μ s₂} (≼-μ x)
  with s₁′ , refl , x′ ← ≼-⋯wk (suc m) x
  = -, sym (⋯-exchangeᵣₛ s₁′ (μ s₂) (m ↑⋆ wk)) , ≼-μ x′
≼-⋯wk m refl = -, refl , refl

≼-⋯/⋯ₛ-≼ : {s′ : 𝕊 n} {s : 𝕊 (suc n)} {s⁰ : 𝕊 n} → s ≼ s′ ⋯ wk → s ⋯ₛ 0↦ s⁰ ≼ s′
≼-⋯/⋯ₛ-≼ {s⁰ = s⁰} x with ≼-⋯wk 0 x
... | s′ , refl , x′ rewrite ⋯-wk-cancels-0↦ {s = s′} s⁰ = x′

lemma10-9-` : ∀ (m : ℕ) {s : 𝕊 (m + n)} {q : 𝕊 n} (y : 𝔽 (m + suc n)) →
  s ≼ (m ↑ₛ⋆ 0↦ q) y →
  s ≼ q ⋯ wk⋆ m ⊎ ∃ λ s′ → s ≡ s′ ⋯ₛ m ↑ₛ⋆ 0↦ q × s′ ≼ (` y)
lemma10-9-` zero    zero    x    = inj₁ (subst (_ ≼_) (sym (⋯-id _ λ z → refl)) x)
lemma10-9-` zero    (suc y) refl = inj₂ (-, refl , refl)
lemma10-9-` (suc m) zero    refl = inj₂ (-, refl , refl)
lemma10-9-` (suc m) {s} {q} (suc y) x
  with s′ , s-eq , x′ ← ≼-⋯wk 0 x
  with lemma10-9-` m y x′
... | inj₁ s′≼ = inj₁ (subst₂ _≼_ s-eq (⋯ᵣᵣ-fusion q (wk⋆ m) wk) (s′≼ ≼⋯ wk))
... | inj₂ (-, refl , refl) = inj₂ (-, sym s-eq , refl)

lemma10-9 : ∀ (m : ℕ) {s : 𝕊 (m + n)} {q : 𝕊 n} (t : 𝕊 (m + suc n)) →
  s ≼ t ⋯ₛ m ↑ₛ⋆ 0↦ q →
  s ≼ q ⋯ wk⋆ m ⊎ ∃ λ s′ → s ≡ s′ ⋯ₛ m ↑ₛ⋆ 0↦ q × s′ ≼ t
lemma10-9 m (⁉ ♯ T ▸ t) (≼-♯ x) with lemma10-9 m t x
... | inj₁ s≼q = inj₁ s≼q
... | inj₂ (-, eq , s′≼t) = inj₂ (-, eq , ≼-♯ s′≼t)
lemma10-9 m (⁉ ⟨ t₁ ⨟ t₂ ⟩) (≼-⋆₁ x) with lemma10-9 m t₁ x
... | inj₁ s≼q = inj₁ s≼q
... | inj₂ (-, eq , s′≼t) = inj₂ (-, eq , ≼-⋆₁ s′≼t)
lemma10-9 m (⁉ ⟨ t₁ ⨟ t₂ ⟩) (≼-⋆₂ x) with lemma10-9 m t₂ x
... | inj₁ s≼q = inj₁ s≼q
... | inj₂ (-, eq , s′≼t) = inj₂ (-, eq , ≼-⋆₂ s′≼t)
lemma10-9 m {q = q} (μ t) (≼-μ {s} x) with lemma10-9 (suc m) t x
... | inj₁ s≼q = inj₁ $ ≼-⋯/⋯ₛ-≼ $ subst (s ≼_) (sym (⋯ᵣᵣ-fusion q (wk⋆ m) wk)) s≼q
... | inj₂ (s′ , refl , s′≼t) = inj₂ (s′ ⋯ₛ 0↦ (μ t) , ⋯-exchangeₛₛ s′ (μ t) (m ↑ₛ⋆ 0↦ q) , ≼-μ s′≼t)
lemma10-9 m (` z) x = lemma10-9-` m z x
lemma10-9 m t refl = inj₂ (-, refl , refl)

⊑⇒≼ : s′ ⊑ s → s′ ≼ s
⊑⇒≼ refl     = refl
⊑⇒≼ (⊑-♯  x) = ≼-♯  (⊑⇒≼ x)
⊑⇒≼ (⊑-⋆₁ x) = ≼-⋆₁ (⊑⇒≼ x)
⊑⇒≼ (⊑-⋆₂ x) = ≼-⋆₂ (⊑⇒≼ x)
⊑⇒≼ {s′ = s′} (⊑-μ {s″} x) with lemma10-9 0 s″ (⊑⇒≼ x)
... | inj₁ x′ = subst (s′ ≼_) (cong μ (⋯-id _ (↑-id (λ _ → refl)))) x′
... | inj₂ (-, refl , x′) = ≼-μ x′

----------------------------------------------------------------------------------------------------
-- There are a finite amount of bottom-up subterms.

≼-tabulate  : (s : 𝕊 n) → Vector (Σ[ s′ ∈ 𝕊 n ] s′ ≼ s) (count s)
≼-tabulate′ : (s : 𝕊 n) → Vector (Σ[ s′ ∈ 𝕊 n ] s′ ≼ s) (childCount s)

≼-tabulate-⋆₁ : ∀ ⁉ s₁ → Vector (Σ[ s ∈ 𝕊 n ] s ≼ ⁉ ⟨ s₁ ⨟ s₂ ⟩) (count s₁)
≼-tabulate-⋆₁ _ = V.map (λ x → -, ≼-⋆₁ (x .proj₂)) ∘ ≼-tabulate

≼-tabulate-⋆₂ : ∀ ⁉ s₂ → Vector (Σ[ s ∈ 𝕊 n ] s ≼ ⁉ ⟨ s₁ ⨟ s₂ ⟩) (count s₂)
≼-tabulate-⋆₂ _ = V.map (λ x → -, ≼-⋆₂ (x .proj₂)) ∘ ≼-tabulate

≼-tabulate s = (-, refl) V.∷ ≼-tabulate′ s

≼-tabulate′ (` x)           = V.[]
≼-tabulate′ (□ x)           = V.[]
≼-tabulate′ (⁉ ♯ T ▸ s)     = V.map (λ x → -, ≼-♯ (x .proj₂)) (≼-tabulate s)
≼-tabulate′ (μ s)           = V.map (λ x → -, ≼-μ (x .proj₂)) (≼-tabulate s)
≼-tabulate′ (⁉ ⟨ s₁ ⨟ s₂ ⟩) = ≼-tabulate-⋆₁ ⁉ s₁ V.++ ≼-tabulate-⋆₂ ⁉ s₂

≼-tabulate-complete : (s′≤s : s′ ≼ s) →
  Σ[ i ∈ 𝔽 (count s) ]
  (s′ , s′≤s) ≡ ≼-tabulate s i
≼-tabulate-complete refl = zero , refl
≼-tabulate-complete (≼-♯ ≤s) with ≼-tabulate-complete ≤s
... | i , refl = suc i , refl
≼-tabulate-complete {s = ⁉ ⟨ s₁ ⨟ s₂ ⟩} (≼-⋆₁ ≤s) with ≼-tabulate-complete ≤s
... | i , refl =
  suc (Fin.join (count s₁) (count s₂) (inj₁ i)) ,
    sym (V.lookup-++ˡ (≼-tabulate-⋆₁ ⁉ s₁) (≼-tabulate-⋆₂ ⁉ s₂) i)
≼-tabulate-complete {s = ⁉ ⟨ s₁ ⨟ s₂ ⟩} (≼-⋆₂ ≤s) with ≼-tabulate-complete ≤s
... | i , refl =
  suc (Fin.join (count s₁) (count s₂) (inj₂ i)) ,
    sym (V.lookup-++ʳ (≼-tabulate-⋆₁ ⁉ s₁) (≼-tabulate-⋆₂ ⁉ s₂) i)
≼-tabulate-complete (≼-μ ≤s) with ≼-tabulate-complete ≤s
... | i , refl = suc i , refl

≼-index : s ≼ s′ → 𝔽 (count s′)
≼-index refl     = zero
≼-index (≼-♯  x) = suc (≼-index x)
≼-index (≼-⋆₁ x) = suc (≼-index x ↑ˡ _)
≼-index (≼-⋆₂ x) = suc (suc _ ↑ʳ ≼-index x)
≼-index (≼-μ  x) = suc (≼-index x)

≼-index-injective : (a : s₁ ≼ s) (b : s₂ ≼ s) → .(≼-index a ≡ ≼-index b) → s₁ ≡ s₂
≼-index-injective refl     refl     eq = refl
≼-index-injective (≼-♯  a) (≼-♯  b) eq = ≼-index-injective a b (Fin.suc-injective eq)
≼-index-injective (≼-⋆₁ a) (≼-⋆₂ b) eq = ⊥-elim-irr (Fin.↑ˡ≢↑ʳ (Fin.suc-injective eq))
≼-index-injective (≼-⋆₂ a) (≼-⋆₁ b) eq = ⊥-elim-irr (Fin.↑ˡ≢↑ʳ (sym (Fin.suc-injective eq)))
≼-index-injective (≼-μ  a) (≼-μ  b) eq = cong (_⋯ₛ 0↦ _) (≼-index-injective a b (Fin.suc-injective eq))
≼-index-injective (≼-⋆₁ a) (≼-⋆₁ b) eq = ≼-index-injective a b $·
    Fin.↑ˡ-injective (suc _) (≼-index a) (≼-index b) (Fin.suc-injective eq)
≼-index-injective (≼-⋆₂ a) (≼-⋆₂ b) eq = ≼-index-injective a b $·
  Fin.↑ʳ-injective (suc _) (≼-index a) (≼-index b) (Fin.suc-injective eq)

lookup-≼-index : (s₁≼s₂ : s₁ ≼ s₂) → ≼-tabulate-complete s₁≼s₂ .proj₁ ≡ ≼-index s₁≼s₂
lookup-≼-index refl = refl
lookup-≼-index {s₂ = ⁉ ♯ T ▸ s₂} (≼-♯ s₁≼s₂)
  with (i , refl) ← ≼-tabulate-complete s₁≼s₂ in eq
  = cong suc (Eq.trans (Π.Σ-≡,≡←≡ (sym eq) .proj₁) (lookup-≼-index s₁≼s₂))
lookup-≼-index {s₂ = ⁉ ⟨ _ ⨟ _ ⟩} (≼-⋆₁ s₁≼s₂)
  with (i , refl) ← ≼-tabulate-complete s₁≼s₂ in eq
  = cong (λ i′ → suc (i′ ↑ˡ suc _)) (Eq.trans (Π.Σ-≡,≡←≡ (sym eq) .proj₁) (lookup-≼-index s₁≼s₂))
lookup-≼-index {s₂ = ⁉ ⟨ _ ⨟ _ ⟩} (≼-⋆₂ s₁≼s₂)
  with (i , refl) ← ≼-tabulate-complete s₁≼s₂ in eq
  = cong (λ i′ → suc (suc _ ↑ʳ i′)) (Eq.trans (Π.Σ-≡,≡←≡ (sym eq) .proj₁) (lookup-≼-index s₁≼s₂))
lookup-≼-index {s₂ = μ s₂} (≼-μ s₁≼s₂)
  with (i , refl) ← ≼-tabulate-complete s₁≼s₂ in eq
  = cong suc (Eq.trans (Π.Σ-≡,≡←≡ (sym eq) .proj₁) (lookup-≼-index s₁≼s₂))

≼-`-injective : {x y : 𝔽 n} → ` x ≼ ` y → x ≡ y
≼-`-injective refl = refl

index : s ≼ s′ → 𝔽 (count s′)
index x = ≼-tabulate-complete x .proj₁

index-⊑ : s ⊑ s′ → 𝔽 (count s′)
index-⊑ = index ∘ ⊑⇒≼
