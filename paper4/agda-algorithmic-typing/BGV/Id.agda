module BGV.Id where

import Data.Nat.Properties as NatP
open import Data.List as List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
open import Function using (case_of_)
open import Relation.Binary.Definitions using (Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; module ≡-Reasoning)

open import BGV.Util.Decidable

abstract
  Id : Set
  Id = ℕ

  instance
    DecEq-Id : DecEq Id
    DecEq-Id = DecEq-ℕ

  _<_ : Id → Id → Set
  _<_ = Nat._<_

  sum : List ℕ → ℕ
  sum []       = 0
  sum (x ∷ xs) = x + sum xs

  fresh : List Id → Id
  fresh xs = suc (sum xs)

  fresh-< : ∀ {x} {xs} → x ∈ xs → x < fresh xs
  fresh-< {x} {x' ∷ xs} (here refl) =
    Nat.s≤s (NatP.m≤n⇒m≤n+o {m = x} (sum xs) NatP.≤-refl)
  fresh-< {x} {x' ∷ xs} (there x∈xs)
    with fresh-< x∈xs
  … | Nat.s≤s x≤sumxs = Nat.s≤s (NatP.m≤n⇒m≤o+n x' x≤sumxs)

  fresh-∉ : ∀ xs → fresh xs ∉ xs
  fresh-∉ (x ∷ xs) p = NatP.<-irrefl refl (fresh-< p)

variable
  x y z x' y' z' : Id
  x₁ x₂ x₃ y₁ y₂ y₃ : Id
  xs ys zs xs' ys' zs' : List Id
