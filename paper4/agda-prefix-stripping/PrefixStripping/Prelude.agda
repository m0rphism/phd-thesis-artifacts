module PrefixStripping.Prelude where

open import Level using (Level; 0ℓ; Setω) renaming (suc to ℓsuc; _⊔_ to _ℓ⊔_) public
variable
  ℓ ℓ₁ ℓ₂ : Level

open import Function.Base public

module Eq where
  open import Relation.Unary using (Pred)
  open import Relation.Binary.PropositionalEquality public

open Eq using
  ( _≡_
  ; _≢_
  ; refl
  ; _≗_
  ; subst
  ; subst₂
  ; trans
  ; cong
  ; cong₂
  ; sym
  ; ≢-sym
  ; module ≡-Reasoning
  ) public

open import Data.Empty using (⊥; ⊥-elim; ⊥-elim-irr) public

infix 3 ¬·_

¬·_ : Set ℓ → Set ℓ
¬· A = .A → ⊥

infix 4 _≢·_

_≢·_ : {A : Set ℓ} → A → A → Set ℓ
x ≢· y = ¬· x ≡ y

module Bool where
  open import Data.Bool public
  open import Data.Bool.Properties public

open Bool using (true; false; if_then_else_) renaming (Bool to 𝔹) public

module Nat where
  open import Data.Nat public
  open import Data.Nat.Properties public

  module Variables where
    variable m n o m₁ m₂ n₁ n₂ n₃ m′ n′ : ℕ

open Nat using (ℕ; zero; suc; _+_; +-suc; +-assoc; +-comm; +-identityʳ; NonZero) public

module Sum where
  open import Data.Sum public
  open import Data.Sum.Properties public

open Sum using (_⊎_; inj₁; inj₂; inj₁-injective; inj₂-injective; fromInj₁; fromInj₂) public

module Π where
  open import Data.Product hiding (-,_) public
  open import Data.Product.Properties public

  infixr 4 -,_
  pattern -,_ x = _ , x

open Π using (Σ; Σ-syntax; ∃; ∃₂; ∄; _×_; proj₁; proj₂; _,_; -,_; curry; uncurry) public

module Fin where
  open import Data.Fin public
  open import Data.Fin.Properties public

  ↑ˡ≢↑ʳ : ∀ {m n} {x : Fin m} {y : Fin n} → x ↑ˡ n ≢· m ↑ʳ y
  ↑ˡ≢↑ʳ {m = suc m} {x = suc x} eq = ↑ˡ≢↑ʳ (suc-injective eq)

open Fin using (zero; suc; fromℕ; toℕ; ¬Fin0) renaming (Fin to 𝔽) public

infixr 0 _$·_
infixr 9 _∘·_

_$·_ : ∀ {a b} {A : Set a} {B : Set b} → (.A → B) → .A → B
f $· x = f x

_∘·_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} → (.B → C) → (A → B) → (.A → C)
(f ∘· g) x = f (g x)


import Relation.Nullary as Stdlib-Nullary
import Relation.Unary   as Stdlib-Unary
import Relation.Binary  as Stdlib-Binary

module Relation where
  module Nullary = Stdlib-Nullary
  module Unary   = Stdlib-Unary
  module Binary  = Stdlib-Binary

open Relation.Nullary hiding (⌊_⌋; stable; proof) public
open Relation.Unary   using  (Pred) public
open Relation.Binary  using  (REL; Rel) public
