module VGR.Syntax where

open import Data.Bool hiding (_≟_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.String hiding (_++_; _≈_)
open import Data.Product
open import Data.Sum

open import Function

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning -- using (begin_; _≡⟨⟩_; _∎)

open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Identifier
open import Extensionality

private
  variable
    α β α′ α₁ α₂ : Alpha

mutual
  data Type : Set where
    `data : (D : Data) → Type
    `chan : (α : Alpha) → Type

  data Data : Set where
    `ap : (S : Session) → Data
    `fun : (σ₁ : Store) → (T₁ : Type) → (T₂ : Type) → (σ₂ : Store) → Data
    `unit : Data

  data Session : Set where
    `send `recv : (D : Data) → (S : Session) → Session
    `sendc `recvc : (S₁ : Session) → (S₂ : Session) → Session
    `end : Session

  data Store : Set where
    `emp : Store
    _,_⦂_[_] : (σ : Store) (α : Alpha) (S : Session) (α#σ : α # σ) →
            Store

  data _#_ : Alpha → Store → Set where
    #emp  : α # `emp
    #cons : ∀ {σ : Store}{S : Session}{α′#σ} → α # σ → α ≢ α′ → α # (σ , α′ ⦂ S [ α′#σ ])

----------------------------------------------------------------------

private
  variable
    σ σ′ σ₁ σ₂ σ₃ σ₁′ : Store
    S S′ S₁ S₂ : Session
    α#σ : α # σ
    α₁#σ : α₁ # σ
    α#σ₁ : α # σ₁
    α#σ₂ : α # σ₂
    α′#σ′ : α′ # σ′
    α₂#σ₂ : α₂ # σ₂

data _⦂_`in_ : Alpha → Session → Store → Set where
  `Z : 
      α ⦂ S `in (σ , α ⦂ S [ α#σ ])
  `S : 
      (α≢β : α ≢ β) →
      (α∈σ : α ⦂ S `in σ) →
      α ⦂ S `in (σ , β ⦂ S′ [ α#σ ])

mutual

  data Value : Set where
    `val : (α : Alpha) → Value
    `lam : (σ : Store) → (x : Id) → (T : Type) → (e : Expr) → Value
    `rec : (x : Id) (T : Type) (v : Value) → Value
    `unit : Value

  data Expr : Set where
    `val : (v : Value) → Expr
    `thread : (t : Thread) → Expr
    `app : (v₁ : Value) → (v₂ : Value) → Expr
    `new : (S : Session) → Expr
    `accept : (v : Value) → Expr
    `request : (v : Value) → Expr
    `send_`on_ : (v₁ : Value) → (v₂ : Value) → Expr
    `receive : (v : Value) → Expr
    `close : (v : Value) → Expr

  data Thread : Set where
    `ret : (v : Value) → Thread
    `let : (x : String) → (e : Expr) → (t : Thread) → Thread
    `letv : (x : String) → (v : Value) → (t : Thread) → Thread
    `fork : (t₁ : Thread) → (t₂ : Thread) → Thread

data Config : Set where
  ⟨_⟩ : (t : Thread) → Config
  _∥_ : (C₁ C₂ : Config) → Config
  ν_⦂[_]_ : (x : Id) (S : Session) (C : Config) → Config
  ν_∘_ : (γ : Id) (C : Config) → Config

data TEnv : Set where
  `emp : TEnv
  _,_⦂_ : (Γ : TEnv) (x : Id) (T : Type) → TEnv

_,,_ : TEnv → TEnv → TEnv
Γ ,, `emp = Γ
Γ ,, (Δ , x ⦂ T) = (Γ ,, Δ) , x ⦂ T

dualSession : Session → Session
dualSession (`send D S) = `recv D (dualSession S)
dualSession (`recv D S) = `send D (dualSession S)
dualSession (`sendc S S₁) = `recvc S (dualSession S₁)
dualSession (`recvc S S₁) = `sendc S (dualSession S₁)
dualSession `end = `end

_∈′_ : (α : Alpha) → (σ : Store) → Dec (Σ Session λ S → α ⦂ S `in σ)
α ∈′ `emp = no (λ ())
α ∈′ (σ , β ⦂ S [ _ ]) with α α=? β
... | yes refl = yes (_ , `Z)
... | no ¬p with α ∈′ σ
... | no ¬p₁ = no λ{ (S₁ , `S eq path) → ¬p₁ (S₁ , path);
                     (S₁ , `Z) → ¬p refl }
... | yes (S₁ , path) = yes (S₁ , (`S ¬p path))

all# : Store → Store → Set
all# σ₁ `emp = ⊤
all# σ₁ (σ₂ , α ⦂ S [ α#σ ]) = all# σ₁ σ₂ × α # σ₁

all#-emp : ∀ σ → all# `emp σ
all#-emp `emp = tt
all#-emp (σ , α ⦂ S [ α#σ ]) = all#-emp σ , #emp

#-weak : ∀ {α α₁}{α₁#σ₁} → α # (σ₁ , α₁ ⦂ S [ α₁#σ₁ ]) → α # σ₁
#-weak (#cons α#σ₁α₁ x) = α#σ₁α₁

#-≢ : ∀ {α α₁}{α₁#σ₁} → α # (σ₁ , α₁ ⦂ S [ α₁#σ₁ ]) → α ≢ α₁
#-≢ (#cons x x₁) = x₁

all#-weak : all# (σ₁ , α ⦂ S [ α#σ ]) σ₂ → all# σ₁ σ₂
all#-weak {σ₂ = `emp} σ₁α#σ₂ = tt
all#-weak {σ₂ = σ₂ , α ⦂ S [ α#σ ]} (fst , snd) = all#-weak fst , #-weak snd

all#-head : all# (σ₁ , α ⦂ S [ α#σ ]) σ₂ → α # σ₂
all#-head {σ₂ = `emp} σ₁α#σ₂ = #emp
all#-head {σ₂ = σ₂ , β ⦂ S [ β#σ ]} (fst , #cons snd α≢β) =
  #cons (all#-head {σ₂ = σ₂} fst) λ x → α≢β (sym x)

-- disjoint concatenation of stores

mutual
  _++_[_] : (σ₁ σ₂ : Store) → all# σ₁ σ₂ → Store
  σ₁ ++ `emp [ σ₁#σ₂ ] = σ₁
  σ₁ ++ σ₂ , α ⦂ S [ α#σ₂ ] [ σ₁#σ₂ , α#σ₁ ] = (σ₁ ++ σ₂ [ σ₁#σ₂ ]) , α ⦂ S [ #-++ α#σ₁ α#σ₂ ]

  #-++ : ∀ {σ₁#σ₂ : all# σ₁ σ₂} → α # σ₁ → α # σ₂ → α # (σ₁ ++ σ₂ [ σ₁#σ₂ ])
  #-++ {σ₁} {`emp} α#σ₁ α#σ₂ = α#σ₁
  #-++ {σ₁} {σ₂ , α ⦂ S [ α#σ ]} α#σ₁ (#cons α₁#σ₂ α₁≢α) = #cons (#-++ α#σ₁ α₁#σ₂) α₁≢α

mutual
  _∩_ : Store → Store → Store
  σ₁ ∩ `emp = `emp
  σ₁ ∩ (σ₂ , α ⦂ S [ α#σ₂ ]) with α ∈′ σ₁
  ... | no ¬p = σ₁ ∩ σ₂
  ... | yes p = (σ₁ ∩ σ₂) , α ⦂ S [ #-∩ σ₁ σ₂ α#σ₂ ]

  #-∩ : ∀ σ₁ σ₂ → α # σ₂ → α # (σ₁ ∩ σ₂)
  #-∩ σ₁ `emp α#σ₂ = #emp
  #-∩ σ₁ (σ₂ , α ⦂ S [ α#σ₂ ]) α₁#σ₂+ with α ∈′ σ₁
  #-∩ σ₁ (σ₂ , α ⦂ S [ α#σ₂ ]) (#cons α₁#σ₂+ x) | no ¬p = #-∩ σ₁ σ₂ α₁#σ₂+
  #-∩ σ₁ (σ₂ , α ⦂ S [ α#σ₂ ]) (#cons α₁#σ₂+ α₁≢α) | yes p = #cons (#-∩ σ₁ σ₂ α₁#σ₂+) α₁≢α

data _⊆_ : Store → Store → Set where
  ⊆-emp : `emp ⊆ σ′
  ⊆-elem : (α∈ : α ⦂ S `in σ′) → (σ⊆σ′ : σ ⊆ σ′) → (σ , α ⦂ S [ α#σ ]) ⊆ σ′

infix 15 _⊆_

_⊆⊇_ : Store → Store → Set
σ₁ ⊆⊇ σ₂ = σ₁ ⊆ σ₂ × σ₂ ⊆ σ₁

infix 15 _⊆⊇_
