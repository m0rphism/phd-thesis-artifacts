open import PrefixStripping.Prelude hiding (_⟨_⟩_)
open Relation.Binary

module PrefixStripping.Decide.Soundness
    {𝕋 END : Set}
    (_≟ᵀ_ : DecidableEquality 𝕋)
    (_≟E_ : DecidableEquality END)
  where

open import Data.Unit using (⊤; tt)
open import Data.Maybe using (just; nothing; Is-nothing)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any as Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties

open import PrefixStripping.Syntax
open import PrefixStripping.Decide.Universe _≟ᵀ_ _≟E_

open import PrefixStripping.Sessions.Equivalence 𝕋 as In hiding (refl; sym; trans)
open In.Tree
open In.Decide _≟ᵀ_ _≟E_


Valid : ◇-Rel ℓ → Pred ⊢𝒰 _
Valid _~_ (⊢p % ⊢s) = ⊢p ~ ⊢s

data AllI (P : List ⊢𝒰 → ⊢𝒰 → Set ℓ) : List ⊢𝒰 → Set ℓ where
  [] : AllI P []
  _∷_ : ∀ {x} → P A x → AllI P A → AllI P (x ∷ A)

allI-lookup : ∀ {P : List ⊢𝒰 → ⊢𝒰 → Set ℓ} {x} → AllI P A → x ∈ A → ∃ λ A′ → P A′ x × AllI P (x ∷ A′)
allI-lookup (px ∷ all) (here refl) = -, px , px ∷ all
allI-lookup (px ∷ all) (there x∈)  = allI-lookup all x∈

infix 3 _⊢[_]_%⁺_＝_

data _⊢[_]_%⁺_＝_ (A : List ⊢𝒰) (P : Pred ⊢ℝ ℓ) : ⊢ p → ⊢ s → ⊢ℝ → Set ℓ where
  %-♯ : ∀ {T ⊢r} →
    let H = ⊢♯ ⁉ · T ▸ ⊢p % ⊢♯ ⁉ · T ▸ ⊢s in
    (p%s : H ∷ A ⊢ ⊢p % ⊢s ＝ ⊢r) →
    P ⊢r →
    A ⊢[ P ] ⊢♯ ⁉ · T ▸ ⊢p %⁺ ⊢♯ ⁉ · T ▸ ⊢s ＝ ⊢r
  %-⋆ : ∀ {⊢r₁ ⊢r₂ ⊢r} →
    let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
    (p%s₁ : H ∷ A ⊢ ⊢p₁ % ⊢s₁ ＝ ⊢r₁) →
    (p%s₂ : H ∷ A ⊢ ⊢p₂ % ⊢s₂ ＝ ⊢r₂) →
    P ⊢r₁ →
    P ⊢r₂ →
    ⊢r₁ ⊔ᴿ ⊢r₂ ＝ ⊢r →
    A ⊢[ P ] ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ %⁺ ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ＝ ⊢r

module Unknown where
  _⟿⊥ : List ⊢𝒰 → ◇-Rel _
  A ⟿⊥ = A ⊢[ const ⊤ ]_%⁺_＝ nothing

  sound′ : AllI (λ A → Valid (A ⟿⊥)) A → A ⊢ ⊢p % ⊢s ＝ nothing → Cyclic′ ⊢p ⊢s
  sound′ A p%s zero = refl
  sound′ A (%-♯ ∉A p%s) (suc d) = cong (_ ♯ _ ▸_) (sound′ (%-♯ p%s _ ∷ A) p%s d)
  sound′ A (%-⋆ ∉A p%s₁ p%s₂ R⊔) (suc d) =
    let A′ = %-⋆ p%s₁ p%s₂ _ _ R⊔ ∷ A in
    cong₂ (_ ⟨_⨟_⟩)
      (sound′ A′ (⊢%-subst′ (⊔ᴿ-nothing⁻¹ R⊔ .proj₁) p%s₁) d)
      (sound′ A′ (⊢%-subst′ (⊔ᴿ-nothing⁻¹ R⊔ .proj₂) p%s₂) d)
  sound′ A (%-μˡ {⊢p = p} {pᶜ} p%s) (suc d) = trans (≃-μ◇ p pᶜ _) (sound′ A p%s (suc d))
  sound′ A (%-μʳ {⊢s = s} {sᶜ} p%s) (suc d) = trans (sound′ A p%s (suc d)) (sym (≃-μ s sᶜ _))
  sound′ A (hyp x) (suc d) with allI-lookup A x
  ... | -, %-♯ p%s eq , A′ = cong (_ ♯ _ ▸_) (sound′ A′ p%s d)
  ... | -, %-⋆ p%s₁ p%s₂ _ _ R⊔ , A′ = cong₂ (_ ⟨_⨟_⟩)
    (sound′ A′ (⊢%-subst′ (⊔ᴿ-nothing⁻¹ R⊔ .proj₁) p%s₁) d)
    (sound′ A′ (⊢%-subst′ (⊔ᴿ-nothing⁻¹ R⊔ .proj₂) p%s₂) d)

  sound : [] ⊢ ⊢p % ⊢s ＝ nothing → Cyclic′ ⊢p ⊢s
  sound = sound′ []

  ¬∃□-here : AllI (λ A → Valid (A ⟿⊥)) A → A ⊢ ⊢p % ⊢s ＝ nothing → ⊢p ≄ ⊢□
  ¬∃□-here A p%s eq with eq 1
  ¬∃□-here A (%-μˡ {⊢p = p} {pᶜ} p%s) eq | ≡□ =
    ¬∃□-here A p%s (In.trans (In.sym (≃-μ p pᶜ)) eq)
  ¬∃□-here A (%-μʳ {⊢s = s} {sᶜ} p%s) eq | ≡□ =
    ¬∃□-here A p%s eq
  ¬∃□-here A (hyp x) eq | ≡□ with allI-lookup A x
  ¬∃□-here A (hyp x) eq | () | -, %-♯ p%s x′ , _
  ¬∃□-here A (hyp x) eq | () | -, %-⋆ %₁ %₂ _ _ x′ , _

  ¬∃□′ : ∀ {⊢p : ⊢ p} →
    AllI (λ A → Valid (A ⟿⊥)) A →
    A ⊢ ⊢p % ⊢s ＝ nothing →
    ∀ {s*} (π : Path s* p) → ⊢p –[ π ]→ ⊢□ → ⊥
  ¬∃□′ A p%s {[]} π π→□ = ¬∃□-here A p%s π→□
  ¬∃□′ A (%-♯ _ p%s) {_ ∷ _} (step-♯ , π) π→□ =
    ¬∃□′ (%-♯ p%s _ ∷ A) p%s π π→□
  ¬∃□′ A (%-⋆ {⁉ = ⁉} _ %₁ %₂ x) {_ ∷ _} (step-⋆₁ , π) π→□ =
    ¬∃□′ (%-⋆ %₁ %₂ _ _ x ∷ A) (⊢%-subst′ (⊔ᴿ-nothing⁻¹ x .proj₁) %₁) π π→□
  ¬∃□′ A (%-⋆ {⁉ = ⁉} _ %₁ %₂ x) {_ ∷ _} (step-⋆₂ , π) π→□ =
    ¬∃□′ (%-⋆ %₁ %₂ _ _ x ∷ A) (⊢%-subst′ (⊔ᴿ-nothing⁻¹ x .proj₂) %₂) π π→□
  ¬∃□′ A (%-μˡ {⊢p = p} {pᶜ} p%s) {_ ∷ _} π@(_ , _) π→□ =
    ¬∃□′ A p%s (≃-path (≃-μ p pᶜ) π)
      (In.trans (In.sym (≃-target* (≃-μ p pᶜ) π)) π→□)
  ¬∃□′ A (%-μʳ p%s) {_ ∷ _} π@(_ , _) π→□ =
    ¬∃□′ A p%s π π→□
  ¬∃□′ A (hyp ∈A) {_ ∷ _} (x , π) π→□ with allI-lookup A ∈A
  ¬∃□′ A (hyp ∈A) {_ ∷ _} (step-♯  , π) π→□ | -, %-♯ p%s x , A′ = ¬∃□′ A′ p%s π π→□
  ¬∃□′ A (hyp ∈A) {_ ∷ _} (step-⋆₁ , π) π→□ | -, %-⋆ %₁ %₂ _ _ x , A′ =
    ¬∃□′ A′ (⊢%-subst′ (⊔ᴿ-nothing⁻¹ x .proj₁) %₁) π π→□
  ¬∃□′ A (hyp ∈A) {_ ∷ _} (step-⋆₂ , π) π→□ | -, %-⋆ %₁ %₂ _ _ x , A′ =
    ¬∃□′ A′ (⊢%-subst′ (⊔ᴿ-nothing⁻¹ x .proj₂) %₂) π π→□

  ¬∃□ : [] ⊢ ⊢p % ⊢s ＝ nothing → ¬ ∃□ ⊢p
  ¬∃□ p%s (□ π π→□) = ¬∃□′ [] p%s π π→□

module Remainder where
  open import Data.List.Relation.Binary.Subset.Propositional
  open import Data.List.Relation.Binary.Subset.Propositional.Properties
  open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected)
  open Connected

  infix 4 _⟿_

  _⟿_ : List ⊢𝒰 → ⊢ r → ◇-Rel _
  (A ⟿ r) p s = ∃ λ r′ → A ⊢[ MayRemain r ] p %⁺ s ＝ r′

  sound′ : ∀ {⊢r′} → AllI (λ A → Valid (A ⟿ ⊢r)) A → A ⊢ ⊢p % ⊢s ＝ ⊢r′ → MayRemain ⊢r ⊢r′ → IsRem ⊢r ⊢p ⊢s

  sound′-⋆ : ∀ {⊢r₁ ⊢r₂ d} →
    AllI (λ A → Valid (A ⟿ ⊢r)) A →
    A ⊢ ⊢p₁ % ⊢s₁ ＝ ⊢r₁ →
    A ⊢ ⊢p₂ % ⊢s₂ ＝ ⊢r₂ →
    MayRemain ⊢r ⊢r₁ →
    MayRemain ⊢r ⊢r₂ →
    ⟦ ⊢[ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ ◇ ⊢r ] ⟧ (suc d) ≡ ⟦ ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ⟧ (suc d)

  sound′ A p%s r-eq zero = refl
  sound′ A (%-□ eq) r-eq = In.trans (Conn.drop-just r-eq) (In.sym eq)
  sound′ A (%-♯ ∉A p%s) r-eq (suc d) =
    cong (_ ♯ _ ▸_) (sound′ ((-, %-♯ p%s r-eq) ∷ A) p%s r-eq d)
  sound′ A (%-⋆ ∉A p%s₁ p%s₂ x) r-eq (suc d) =
    let eq₁ = (MayRemain-trans r-eq x) in
    let eq₂ = (MayRemain-trans r-eq (⊔ᴿ-sym x)) in
    let H = -, %-⋆ p%s₁ p%s₂ eq₁ eq₂ x in
    sound′-⋆ (H ∷ A) p%s₁ p%s₂ eq₁ eq₂
  sound′ A (%-μˡ {⊢p = p} {pᶜ} p%s) r-eq (suc d) = trans (In.≃-μ◇ p pᶜ _) (sound′ A p%s r-eq (suc d))
  sound′ A (%-μʳ {⊢s = s} {sᶜ} p%s) r-eq (suc d) = trans (sound′ A p%s r-eq (suc d)) (sym (≃-μ s sᶜ (suc d)))
  sound′ A (hyp H) r-eq (suc d) with allI-lookup A H
  ... | -, (r′ , %-♯ p%s eq) , A′ = cong (_ ♯ _ ▸_) (sound′ A′ p%s eq d)
  ... | -, (r′ , %-⋆ p%s₁ p%s₂ eq₁ eq₂ x) , A′ = sound′-⋆ A′ p%s₁ p%s₂ eq₁ eq₂

  sound′-⋆ A p%s₁ p%s₂ eq₁ eq₂ = cong₂ (_ ⟨_⨟_⟩) (sound′ A p%s₁ eq₁ _) (sound′ A p%s₂ eq₂ _)

  sound : [] ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → IsRem ⊢r ⊢p ⊢s
  sound p%s = sound′ [] p%s (just In.refl)
