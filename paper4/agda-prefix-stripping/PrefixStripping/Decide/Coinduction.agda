open import PrefixStripping.Prelude hiding (_⟨_⟩_)
open Relation.Binary

import PrefixStripping.Decide.Universe

module PrefixStripping.Decide.Coinduction
    {𝕋 : Set} {END : Set}
    (_≟ᵀ_ : DecidableEquality 𝕋)
    (_≟E_ : DecidableEquality END)
    (𝒰⁰ : PrefixStripping.Decide.Universe.𝒰 _≟ᵀ_ _≟E_)
  where

import Relation.Binary.Construct.On as On

open import PrefixStripping.Syntax

module Universe = PrefixStripping.Decide.Universe _≟ᵀ_ _≟E_
open Universe

open import PrefixStripping.Sessions.Subterm 𝕋 as ST hiding (trans)

open Nat using (_+_; _*_)
open import Data.List as List using (List; []; _∷_)

record Hyp : Set where
  constructor mkHyp
  field
    u  : ⊢𝒰
    u⊑ : 𝒰⌊ u ⌋ ⊑ᵤ 𝒰⁰

⟨_⟩ : Hyp → 𝒰
⟨ h ⟩ = 𝒰⌊ Hyp.u h ⌋

⊢⟨_⟩ : Hyp → ⊢𝒰
⊢⟨ h ⟩ = Hyp.u h

⊢⟨_⟩* : List Hyp → List ⊢𝒰
⊢⟨_⟩* = List.map ⊢⟨_⟩

hypDecSetoid : DecSetoid _ _
hypDecSetoid = On.decSetoid Universe.decSetoid ⟨_⟩

hypSetoid : Setoid _ _
hypSetoid = DecSetoid.setoid hypDecSetoid

module Counter where
  open import Data.List.Countdown hypDecSetoid as Countdown hiding (empty; lookupOrInsert) public
  open DecSetoid hypDecSetoid using (_≈_)

  MAX : ℕ
  MAX = ST.count (𝒰.p 𝒰⁰) * ST.count (𝒰.s 𝒰⁰)

  indexOfᵖ : Hyp → 𝔽 (ST.count (𝒰.p 𝒰⁰))
  indexOfᵖ h = ≼-tabulate-complete (⊑⇒≼ (Hyp.u⊑ h .proj₁)) .proj₁

  indexOfˢ : Hyp → 𝔽 (ST.count (𝒰.s 𝒰⁰))
  indexOfˢ h = ≼-tabulate-complete (⊑⇒≼ (Hyp.u⊑ h .proj₂)) .proj₁

  indexOf : Hyp → 𝔽 MAX
  indexOf h = Fin.combine (indexOfᵖ h) (indexOfˢ h)

  indexOf-injective : {x y : Hyp} {i : 𝔽 MAX} →
    indexOf x ≡ i → indexOf y ≡ i → x ≈ y
  indexOf-injective {x} {y} eqˡ eqʳ
    using eq₁ , eq₂ ← Fin.combine-injective (indexOfᵖ x) (indexOfˢ x)
                                            (indexOfᵖ y) (indexOfˢ y)
                                            (trans eqˡ (sym eqʳ))
    with refl ← ≼-index-injective (⊑⇒≼ (Hyp.u⊑ x .proj₁)) (⊑⇒≼ (Hyp.u⊑ y .proj₁))
                                  (trans (sym (lookup-≼-index _)) (trans eq₁ (lookup-≼-index _)))
    with refl ← ≼-index-injective (⊑⇒≼ (Hyp.u⊑ x .proj₂)) (⊑⇒≼ (Hyp.u⊑ y .proj₂))
                                  (trans (sym (lookup-≼-index _)) (trans eq₂ (lookup-≼-index _)))
    = refl

  begin : [] ⊕ MAX
  begin = record
    { kind = inj₂ ∘ indexOf
    ; injective = λ {x} {y} eqˡ eqʳ → indexOf-injective {x} {y} (inj₂-injective eqˡ) (inj₂-injective eqʳ)
    }

  open import Data.List.Membership.Setoid hypSetoid

  lookupOrInsert : ∀ {counted : List Hyp} {m} → counted ⊕ m →
    ∀ x → x ∈ counted ⊎
          ∃ λ n → m ≡ suc n × x ∷ counted ⊕ n × x ∉ counted
  lookupOrInsert c x with Countdown.lookup c x
  ... | yes x∈ = inj₁ x∈
  lookupOrInsert {m = zero}  c x | no x∉ = contradiction (Countdown.lookup! c x) x∉
  lookupOrInsert {m = suc m} c x | no x∉ = inj₂ (-, refl , insert c x x∉ , x∉)
