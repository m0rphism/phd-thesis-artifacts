module BGV.Util.FunMap where

open import Function using (_$_) renaming (_∋_ to _by_)
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (Extensionality)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.Empty using (⊥; ⊥-elim)

open import BGV.Util.Decidable
open import BGV.Util.List

private variable
  ℓ ℓ₁ ℓ₂ : Level
  K V : Set ℓ
  f g : K → V

infixr 6 _∷ᶠ_

_∷ᶠ_ : ⦃ _ : DecEq K ⦄ → K × V → (K → V) → (K → V)
((k  , v) ∷ᶠ f) k' with k ≟ k'
… | yes k≡k' = v 
… | no ¬k≡k' = f k' 

infix 4 _~_

_~_ : ∀ (f g : K → V) → Set _
f ~ g = ∀ x → f x ≡ g x 

map-∷ᶠ-∉ : ∀ ⦃ _ : DecEq K ⦄ (k : K) (v : V) f ks →
  k ∉ ks →
  map ((k , v) ∷ᶠ f) ks ≡ map f ks 
map-∷ᶠ-∉ x y ρ [] x∉zs = refl
map-∷ᶠ-∉ x y ρ (z ∷ zs) x∉zs with x ≟ z
… | yes x≡z = ⊥-elim (x∉zs (here x≡z))
… | no ¬x≡z = cong (ρ z ∷_) (map-∷ᶠ-∉ x y ρ zs (∉-tail x∉zs))
