open import Data.List using (List; []; _∷_; _++_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.String as String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)
open import Level using (Level; 0ℓ) renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)

module LawAndOrder.Util.Closures where

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} (R : A → A → Set ℓ₂) where
  data Sym : A → A → Set (ℓ₁ ⊔ₗ ℓ₂) where
    fwd : ∀ {x y} → R x y → Sym x y
    bwd : ∀ {x y} → R y x → Sym x y

  data ReflTrans : A → A → Set (ℓ₁ ⊔ₗ ℓ₂) where
    refl : ∀ {x} → ReflTrans x x
    step : ∀ {x y z} → R x y → ReflTrans y z → ReflTrans x z

  sym' : ∀ {x y} → Sym x y → Sym y x
  sym' (fwd x) = bwd x
  sym' (bwd x) = fwd x

  trans' : ∀ {x y z} → ReflTrans x y → ReflTrans y z → ReflTrans x z
  trans' refl q = q
  trans' (step x p) q = step x (trans' p q)

  module _ (R-sym : ∀ {x y} → R x y → R y x) where
    sym-trans' : ∀ {x y} → ReflTrans x y → ReflTrans y x
    sym-trans' refl       = refl
    sym-trans' (step p q) = trans' (sym-trans' q) (step (R-sym p) refl)


single : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {R : A → A → Set ℓ₂} {x y} → R x y → ReflTrans R x y
single p = step p refl
