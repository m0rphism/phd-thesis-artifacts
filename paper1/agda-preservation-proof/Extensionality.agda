module Extensionality where

open import Relation.Binary.PropositionalEquality

postulate fun-ext : ∀ {A B : Set} → (f g : A → B) → (∀ x → f x ≡ g x) → f ≡ g 

