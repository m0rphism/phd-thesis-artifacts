open import PrefixStripping.Prelude
open Relation.Binary

module PrefixStripping.Decide.Universe {𝕋 END : Set} (_≟ᵀ_ : DecidableEquality 𝕋) (_≟E_ : DecidableEquality END) where

open import Data.List as List using (List; []; _∷_)
open import Data.List.Membership.Propositional
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties using (∈-∷⁺ʳ)
open import Data.List.Relation.Unary.Any using (Any; here; there)

open import PrefixStripping.Syntax

open import PrefixStripping.Sessions 𝕋 as Sessions hiding (𝕊; module Core) public
open Sessions.Core END using (𝕊) public
open Sessions.Functions public
open Sessions.Equality _≟ᵀ_ using (_≟ℙ_; decSetoid-ℙ₀) public
open Sessions.EqualityCore _≟ᵀ_ _≟E_ using () renaming (_≟_ to _≟𝕊_; decSetoid₀ to decSetoid-𝕊₀) public

open import PrefixStripping.Sessions.Equivalence 𝕋 as In hiding (refl; sym; trans)
open In.Decide _≟ᵀ_ _≟E_ public

open import PrefixStripping.Sessions.Subterm 𝕋 as ST using (_⊑_)
open _⊑_

infix 4 _%_

record 𝒰 : Set where
  constructor _%_
  field
    p  : ℙ 0
    s  : 𝕊 0

record ⊢𝒰 : Set where
  constructor _%_
  field
    {𝒰⌊_⌋} : 𝒰
    p : ⊢ 𝒰.p 𝒰⌊_⌋
    s : ⊢ 𝒰.s 𝒰⌊_⌋

open ⊢𝒰 public using (𝒰⌊_⌋)

variable
  p p₁ p₂ p′ : ℙ 0
  s s₁ s₂ s′ : 𝕊 0
  r r₁ r₂ r′ : 𝕊 0
  ⊢p ⊢p₁ ⊢p₂ ⊢p′ : ⊢ p
  ⊢s ⊢s₁ ⊢s₂ ⊢s′ : ⊢ s
  ⊢r ⊢r₁ ⊢r₂ ⊢r′ : ⊢ r
  A A₁ A₂ A′ : List ⊢𝒰

𝒰⌊_⌋* : List ⊢𝒰 → List 𝒰
𝒰⌊_⌋* = List.map 𝒰⌊_⌋

infix 4 _⊑ᵤ_ _%_⊑ᵤ_

_%_⊑ᵤ_ : ℙ 0 → 𝕊 0 → 𝒰 → Set
p % s ⊑ᵤ u = p ⊑ 𝒰.p u × s ⊑ 𝒰.s u

_⊑ᵤ_ : Rel 𝒰 _
x ⊑ᵤ y = 𝒰.p x % 𝒰.s x ⊑ᵤ y

⊑ᵤ-refl : Reflexive _⊑ᵤ_
⊑ᵤ-refl = refl , refl

⊑ᵤ⁻¹-♯ : ∀ {T u} → ⁉ ♯ T ▸ p % ⁉ ♯ T ▸ s ⊑ᵤ u → p % s ⊑ᵤ u
⊑ᵤ⁻¹-♯ (♯p⊑ , ♯s⊑) = ST.trans (⊑-♯ refl) ♯p⊑ , ST.trans (⊑-♯ refl) ♯s⊑

⊑ᵤ⁻¹-⋆ : ∀ {u} →
  ⁉ ⟨ p₁ ⨟ p₂ ⟩ % ⁉ ⟨ s₁ ⨟ s₂ ⟩ ⊑ᵤ u →
  (p₁ % s₁ ⊑ᵤ u) × (p₂ % s₂ ⊑ᵤ u)
⊑ᵤ⁻¹-⋆ (⋆p⊑ , ⋆s⊑) =
  (ST.trans (⊑-⋆₁ refl) ⋆p⊑ , ST.trans (⊑-⋆₁ refl) ⋆s⊑) ,
  (ST.trans (⊑-⋆₂ refl) ⋆p⊑ , ST.trans (⊑-⋆₂ refl) ⋆s⊑)

⊑ᵤ⁻¹-μᵖ : ∀ {p u} → μ p % s ⊑ᵤ u → unfold p % s ⊑ᵤ u
⊑ᵤ⁻¹-μᵖ (μp⊑ , s⊑) = ST.trans (⊑-μ refl) μp⊑ , s⊑

⊑ᵤ⁻¹-μˢ : ∀ {s u} → p % μ s ⊑ᵤ u → p % unfold s ⊑ᵤ u
⊑ᵤ⁻¹-μˢ (p⊑ , μs⊑) = p⊑ , ST.trans (⊑-μ refl) μs⊑

-- We have decidable equality on universe elements.
_≟_ : DecidableEquality 𝒰
x ≟ y = map′
  (λ{ (refl , refl) → refl })
  (λ{ refl → refl , refl })
  (𝒰.p x ≟ℙ 𝒰.p y ×-dec 𝒰.s x ≟𝕊 𝒰.s y)

decSetoid : DecSetoid _ _
decSetoid = Eq.decSetoid _≟_

setoid : Setoid _ _
setoid = DecSetoid.setoid decSetoid

◇-Rel = SREL End-ℙ END 0

IsRem : ⊢ r → ◇-Rel _
IsRem ⊢r ⊢p ⊢s = ⊢[ ⊢p ◇ ⊢r ] ≃ ⊢s

Cyclic′ : ◇-Rel _
Cyclic′ ⊢p ⊢s = ∀ {r} {⊢r : ⊢ r} → IsRem ⊢r ⊢p ⊢s

Fail′ : ◇-Rel _
Fail′ ⊢p ⊢s = ∀ {r} {⊢r : ⊢ r} → ¬ IsRem ⊢r ⊢p ⊢s

open import Data.Maybe
open import Data.Maybe.Relation.Binary.Connected as Conn using (Connected)
open import Data.Maybe.Relation.Binary.Pointwise as PW using (Pointwise)
open Connected
open Pointwise

open import Data.Unit using (⊤; tt)

⊢ℝ = Maybe (Σ[ r ∈ 𝕊 0 ] ⊢ r)

infix 3.5 _wk≃ᴿ_ _≃ᴿ_

_wk≃ᴿ_ : Rel ⊢ℝ _
_wk≃ᴿ_ = Connected λ{ (-, x) (-, y) → x ≃ y }

_≃ᴿ_ : Rel ⊢ℝ _
_≃ᴿ_ = Pointwise λ{ (-, x) (-, y) → x ≃ y }

≃ᴿ-trans : ∀ {x y z} → x ≃ᴿ y → y ≃ᴿ z → x ≃ᴿ z
≃ᴿ-trans = PW.trans In.trans

infix 3.5 _⊔ᴿ_＝_

data _⊔ᴿ_＝_ : ⊢ℝ → ⊢ℝ → ⊢ℝ → Set where
  ⊔-⊥ˡ : ∀ {r r′} → r ≃ᴿ r′ → nothing ⊔ᴿ r ＝ r′
  ⊔-⊥ʳ : ∀ {r r′} → r ≃ᴿ r′ → r ⊔ᴿ nothing ＝ r′
  ⊔-≃  : ⊢s₁ ≃ ⊢r → ⊢r ≃ ⊢s₂ → just (-, ⊢s₁) ⊔ᴿ just (-, ⊢s₂) ＝ just (-, ⊢r)

⊔ᴿ-nothing⁻¹ : ∀ {x y} → x ⊔ᴿ y ＝ nothing → x ≃ᴿ nothing × y ≃ᴿ nothing
⊔ᴿ-nothing⁻¹ (⊔-⊥ˡ x) = nothing , x
⊔ᴿ-nothing⁻¹ (⊔-⊥ʳ x) = x , nothing

⊔ᴿ-sym : ∀ {x y z} → x ⊔ᴿ y ＝ z → y ⊔ᴿ x ＝ z
⊔ᴿ-sym (⊔-⊥ˡ eq) = ⊔-⊥ʳ eq
⊔ᴿ-sym (⊔-⊥ʳ eq) = ⊔-⊥ˡ eq
⊔ᴿ-sym (⊔-≃ eq₁ eq₂) = ⊔-≃ (In.sym eq₂) (In.sym eq₁)

infix 3.5 _⊢_%_＝_

data _⊢_%_＝_ (A : List ⊢𝒰) : ⊢ p → ⊢ s → ⊢ℝ → Set where
  -- Strip-Return
  %-□ : {⊢s : ⊢ s} {⊢r : ⊢ s′} → ⊢s ≃ ⊢r → A ⊢ ⊢□ % ⊢s ＝ just (-, ⊢r)

  -- Strip-Message
  %-♯ : ∀ {⁉ T} {⊢p : ⊢ p} {⊢s : ⊢ s} {⊢r} →
        let H = ⊢♯ ⁉ · T ▸ ⊢p % ⊢♯ ⁉ · T ▸ ⊢s in
        H ∉ A →
        H ∷ A ⊢ ⊢p % ⊢s ＝ ⊢r →
        A ⊢ ⊢♯ ⁉ · T ▸ ⊢p % ⊢♯ ⁉ · T ▸ ⊢s ＝ ⊢r

  -- Strip-Branching
  %-⋆ : ∀ {⊢p₁ : ⊢ p₁} {⊢p₂ : ⊢ p₂} {⊢s₁ : ⊢ s₁} {⊢s₂ : ⊢ s₂} {⊢r₁ ⊢r₂ ⊢r} →
        let H = ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ in
        H ∉ A →
        H ∷ A ⊢ ⊢p₁ % ⊢s₁ ＝ ⊢r₁ →
        H ∷ A ⊢ ⊢p₂ % ⊢s₂ ＝ ⊢r₂ →
        ⊢r₁ ⊔ᴿ ⊢r₂ ＝ ⊢r →
        A ⊢ ⊢ ⁉ ⋆⟨ ⊢p₁ ⨟ ⊢p₂ ⟩ % ⊢ ⁉ ⋆⟨ ⊢s₁ ⨟ ⊢s₂ ⟩ ＝ ⊢r

  -- Strip-UnrollR
  %-μˡ : ∀ {p} {⊢p : ⊢ p} {pᶜ : ⊢ᶜ p} {⊢s : ⊢ s} {⊢r} →
    A ⊢ ⊢-unfold ⊢p pᶜ % ⊢s ＝ ⊢r →
    A ⊢ ⊢μ ⊢p pᶜ % ⊢s ＝ ⊢r

  -- Strip-UnrollS
  %-μʳ : ∀ {⊢p : ⊢ p} {s} {⊢s : ⊢ s} {sᶜ : ⊢ᶜ s} {⊢r} →
    A ⊢ ⊢p % ⊢-unfold ⊢s sᶜ ＝ ⊢r →
    A ⊢ ⊢p % ⊢μ ⊢s sᶜ ＝ ⊢r

  -- Strip-Fix
  hyp : ∀ {H} → H ∈ A → A ⊢ ⊢𝒰.p H % ⊢𝒰.s H ＝ nothing

MayRemain : ⊢ r → ⊢ℝ → Set _
MayRemain r r′ = just (-, r) wk≃ᴿ r′

MayRemain-trans : ∀ {x y z} → MayRemain ⊢r z → x ⊔ᴿ y ＝ z → MayRemain ⊢r x
MayRemain-trans eq           (⊔-⊥ˡ eq′)        = just-nothing
MayRemain-trans eq           (⊔-⊥ʳ (just eq′)) = just (In.trans (Conn.drop-just eq) (In.sym eq′))
MayRemain-trans just-nothing (⊔-⊥ʳ nothing)    = just-nothing
MayRemain-trans eq           (⊔-≃ eq₁ eq₂)     = just (In.trans (Conn.drop-just eq) (In.sym eq₁))

⊔ᴿ-subst : ∀ {x y} → ⊢r₁ ≃ ⊢r₂ → x ⊔ᴿ y ＝ just (-, ⊢r₁) → x ⊔ᴿ y ＝ just (-, ⊢r₂)
⊔ᴿ-subst eq (⊔-⊥ˡ (just x)) = ⊔-⊥ˡ (just (In.trans x eq))
⊔ᴿ-subst eq (⊔-⊥ʳ (just x)) = ⊔-⊥ʳ (just (In.trans x eq))
⊔ᴿ-subst eq (⊔-≃ eq₁ eq₂)   = ⊔-≃ (In.trans eq₁ eq) (In.trans (In.sym eq) eq₂)

⊢%-subst : ⊢r₁ ≃ ⊢r₂ → A ⊢ ⊢p % ⊢s ＝ just (-, ⊢r₁) → A ⊢ ⊢p % ⊢s ＝ just (-, ⊢r₂)
⊢%-subst eq (%-□ eq′) = %-□ (In.trans eq′ eq)
⊢%-subst eq (%-♯ ∉A p%s) = %-♯ ∉A (⊢%-subst eq p%s)
⊢%-subst eq (%-⋆ ∉A p%s₁ p%s₂ x) = %-⋆ ∉A p%s₁ p%s₂ (⊔ᴿ-subst eq x)
⊢%-subst eq (%-μˡ p%s) = %-μˡ (⊢%-subst eq p%s)
⊢%-subst eq (%-μʳ p%s) = %-μʳ (⊢%-subst eq p%s)

⊢%-subst′ : ∀ {x y} → x ≃ᴿ y → A ⊢ ⊢p % ⊢s ＝ x → A ⊢ ⊢p % ⊢s ＝ y
⊢%-subst′ (just eq) x = ⊢%-subst eq x
⊢%-subst′ nothing   x = x

record RemPaths (⊢p : ⊢ p) (⊢s : ⊢ s) (⊢r : ⊢ r) : Set where
  field
    {returnPath} : RawPath
    returnPath∈p : Path returnPath p
    returnPath∈s : Path returnPath s
    –[returnPath]→□ : ⊢p –[ returnPath∈p ]→ ⊢□
    –[returnPath]→r : ⊢s –[ returnPath∈s ]→ ⊢r

remPaths-□ : ⊢s₁ ≃ ⊢s₂ → RemPaths ⊢□ ⊢s₁ ⊢s₂
remPaths-□ eq = record
  { returnPath      = []
  ; returnPath∈p    = _
  ; returnPath∈s    = _
  ; –[returnPath]→□ = In.refl
  ; –[returnPath]→r = eq
  }

liftRemPaths : {⊢p : ⊢ p} {⊢s : ⊢ s} {rstep : RawStep} (sᵖ : Step rstep p) (sˢ : Step rstep s)
  → RemPaths (⊢-target ⊢p sᵖ) (⊢-target ⊢s sˢ) ⊢r
  → RemPaths ⊢p ⊢s ⊢r
liftRemPaths sᵖ sˢ rp =
  let open RemPaths rp in
  record
   { returnPath∈p    = sᵖ , returnPath∈p
   ; returnPath∈s    = sˢ , returnPath∈s
   ; –[returnPath]→□ = –[returnPath]→□
   ; –[returnPath]→r = –[returnPath]→r
   }

substRemPaths : ⊢p₁ ≃ ⊢p₂ → ⊢s₁ ≃ ⊢s₂ → ⊢r₁ ≃ ⊢r₂ → RemPaths ⊢p₁ ⊢s₁ ⊢r₁ → RemPaths ⊢p₂ ⊢s₂ ⊢r₂
substRemPaths eqᵖ eqˢ eqʳ rp =
  let open RemPaths rp in
  record
   { returnPath∈p    = In.≃-path eqᵖ returnPath∈p
   ; returnPath∈s    = In.≃-path eqˢ returnPath∈s
   ; –[returnPath]→□ = In.trans (In.sym (In.≃-target* eqᵖ returnPath∈p)) –[returnPath]→□
   ; –[returnPath]→r = In.trans (In.sym (In.≃-target* eqˢ returnPath∈s)) (In.trans –[returnPath]→r eqʳ)
   }

remPaths : A ⊢ ⊢p % ⊢s ＝ just (-, ⊢r) → RemPaths ⊢p ⊢s ⊢r
remPaths (%-□ eq) = remPaths-□ eq
remPaths (%-♯ _ p%s) = liftRemPaths step-♯ step-♯ (remPaths p%s)
remPaths (%-⋆ _ %₁ %₂ (⊔-⊥ˡ (just eq))) =
  liftRemPaths step-⋆₂ step-⋆₂
    (substRemPaths In.refl In.refl eq (remPaths %₂))
remPaths (%-⋆ _ %₁ %₂ (⊔-⊥ʳ (just eq))) =
  liftRemPaths step-⋆₁ step-⋆₁
    (substRemPaths In.refl In.refl eq (remPaths %₁))
remPaths (%-⋆ _ %₁ %₂ (⊔-≃ eq₁ eq₂)) =
  liftRemPaths step-⋆₁ step-⋆₁
    (substRemPaths In.refl In.refl eq₁ (remPaths %₁))
remPaths (%-μˡ {⊢p = p} {pᶜ} p%s) =
  substRemPaths (In.sym (In.≃-μ p pᶜ)) In.refl In.refl (remPaths p%s)
remPaths (%-μʳ {⊢s = s} {sᶜ} p%s) =
  substRemPaths In.refl (In.sym (In.≃-μ s sᶜ)) In.refl (remPaths p%s)
