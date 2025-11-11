open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Context.Context {M : OPM} (DM : DecidableOPM M) where

open import Data.List as L using (List; []; _∷_; _++_)
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
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import LawAndOrder.Util.Decidable
open import LawAndOrder.Multiplicities
open import LawAndOrder.Effect
open import LawAndOrder.Type DM
open import LawAndOrder.Util.List
open import LawAndOrder.Id
open import LawAndOrder.Util.Graph as G using (Graph)
open import LawAndOrder.Context.Semantic DM
open import LawAndOrder.Context.Syntactic DM

-- Specification

infix 5 _⸴[_]₁_ _⸴[_]₂_ _⸴₁_ _⸴₂_ _∥₁_ _∥₂_

data CtxCtx : Set where
  [] : CtxCtx
  _⸴[_]₁_ : CtxCtx → IsOrd → Ctx → CtxCtx
  _⸴[_]₂_ : Ctx → IsOrd → CtxCtx → CtxCtx

pattern _∥₁_ Γ₁ Γ₂ = _⸴[_]₁_ Γ₁ unordered Γ₂
pattern _∥₂_ Γ₁ Γ₂ = _⸴[_]₂_ Γ₁ unordered Γ₂
pattern _⸴₁_ Γ₁ Γ₂ = _⸴[_]₁_ Γ₁ ordered Γ₂
pattern _⸴₂_ Γ₁ Γ₂ = _⸴[_]₂_ Γ₁ ordered Γ₂

infix 6 _[_]
_[_] : CtxCtx → Ctx → Ctx
[]            [ Γ' ] = Γ'
(C ⸴[ o ]₁ Γ) [ Γ' ] = C [ Γ' ] ⸴[ o ] Γ
(Γ ⸴[ o ]₂ C) [ Γ' ] = Γ ⸴[ o ] C [ Γ' ]

variable
  C C₁ C₂ C₃ C' C₁' C₂' C₃' : CtxCtx
  𝒢 𝒢₁ 𝒢₂ 𝒢₃ 𝒢' 𝒢₁' 𝒢₂' 𝒢₃' : CtxCtx

-- Properties
