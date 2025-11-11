open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕP
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinP
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; module ≅-Reasoning)
open import Function using (_$_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.List using (List; []; _∷_)

open import LawAndOrder.Util.Graph

-- Lemma A.29
