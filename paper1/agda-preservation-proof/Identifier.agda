module Identifier where

open import Data.String

open import Function using (_∘_)

open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality

Id : Set
Id = String

data Polarity : Set where
  `+ `- : Polarity

data Alpha : Set where
  `var : (x : Id) → Alpha
  `cid : (γ : Id) → (p : Polarity) → Alpha

-- decidable equality for Polarity

_p=?_ : (p q : Polarity) → Dec (p ≡ q)
`+ p=? `+ = yes refl
`+ p=? `- = no λ()
`- p=? `+ = no λ()
`- p=? `- = yes refl

-- decidable equality for Alpha

_α=?_ : (α β : Alpha) → Dec (α ≡ β)
`var x α=? `var x₁ with x ≟ x₁
... | no ¬p = no λ { refl → ¬p refl }
... | yes p = yes (cong `var p)
`var x α=? `cid γ p = no λ()
`cid γ p α=? `var x = no λ()
`cid γ p α=? `cid γ₁ p₁ with γ ≟ γ₁ | p p=? p₁
... | no ¬p  | _      = no λ { refl → ¬p refl }
... | _      | no ¬p  = no λ { refl → ¬p refl }
... | yes p₂ | yes p₃ = yes (cong₂ `cid p₂ p₃)

--

dualPolarity : Polarity → Polarity
dualPolarity `+ = `-
dualPolarity `- = `+
