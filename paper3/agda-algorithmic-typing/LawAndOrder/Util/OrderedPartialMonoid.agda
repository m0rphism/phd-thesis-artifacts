module LawAndOrder.Util.OrderedPartialMonoid where

open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)

record OPM : Set₁ where
  infix 3 _≤_ _≤'_
  infixr 6 _*_
  field
    Carrier : Set

    ϵ : Carrier

    _*_ : Carrier → Carrier → Maybe Carrier
    *-assoc : ∀ x y z xy yz →
      x * y ≡ some xy →
      y * z ≡ some yz →
      xy * z ≡ x * yz
    *-neutralʳ : ∀ x →
      x * ϵ ≡ some x
    *-neutralˡ : ∀ x →
      ϵ * x ≡ some x

    _≤_ : Carrier → Carrier → Set
    ≤-refl : ∀ {x} →
      x ≤ x
    ≤-trans : ∀ {x y z} →
      x ≤ y →
      y ≤ z →
      x ≤ z
    ≤-mono-+ : ∀ {x y x' y' xy xy'} →
      x ≤ x' →
      y ≤ y' →
      x * y ≡ some xy →
      x' * y' ≡ some xy' →
      xy ≤ xy'

  _≤'_ : Maybe Carrier → Carrier → Set
  some x ≤' y = x ≤ y
  none   ≤' y = ⊥

record DecidableOPM (M : OPM) : Set₁ where
  open OPM M public
  field
    _≟_   : ∀ (x y : Carrier) → Dec (x ≡ y)
    _≤?_  : ∀ (x y : Carrier) → Dec (x ≤ y)
    _∃≤?_ : ∀ (x y : Carrier) → Dec (∃[ z ] x * z ≤' y)
