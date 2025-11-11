module VGR.Typing where

open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Identifier
open import VGR.Syntax
open import VGR.Free using (InTEnv; InStore)

private
  variable
    Γ : TEnv
    x y γ n : Id
    p : Polarity
    T T′ T₁ T₂ U : Type
    σ σ₁ σ₂ σ′ σ₁′ σ₂′ σ″ : Store
    t t₁ t₂ : Thread
    e : Expr
    v v′ : Value
    α β : Alpha
    D : Data
    S S′ : Session
    C C₁ C₂ : Config
    α#σ : α # σ
    α#σ′ : α # σ′
    β#σ : β # σ
    β#σ′ : β # σ′
    β#σ″ : β # σ″ 
    σ₁#σ : all# σ₁ σ
    σ₁#σ₁′ : all# σ₁ σ₁′
    σ₁#σ₂ : all# σ₁ σ₂

-- variable lookup (cf Wadler/Kokke)

infix  4  _∋_⦂_

data _∋_⦂_ : TEnv → Id → Type → Set where

  `Z : 
    ------------------
    Γ , x ⦂ T ∋ x ⦂ T

  `S : x ≢ y
    → Γ ∋ x ⦂ T
      ------------------
    → Γ , y ⦂ T′ ∋ x ⦂ T

-- environment lookup is a function

-- σ ~[ α ]~ σ′ holds iff α is in σ and σ′ is a reordering of σ,
-- where the session described by α is the head of σ′.
data _~[_]~_ : Store → Alpha → Store → Set where

  `Z : (σ , α ⦂ S [ α#σ ]) ~[ α ]~ (σ , α ⦂ S [ α#σ ])

  `S : (α≢β : α ≢ β) →
       σ ~[ α ]~ (σ′ , α ⦂ S [ α#σ′ ]) →
       (σ , β ⦂ S′ [ β#σ ]) ~[ α ]~ ((σ′ , β ⦂ S′ [ β#σ′ ]) , α ⦂ S [ #cons α#σ′ α≢β ])

-- expression typing

mutual
 data _፤_፤_↦_፤_፤_ : TEnv → Store → Expr → Store → Type → Store → Set where

  C-ReceiveD :
    (⊢v : Γ ፤ v ↦ `chan α) →
    (sp : σ ~[ α ]~ (σ′ , α ⦂ (`recv D S) [ α#σ′ ])) →
    Γ ፤ σ ፤ `receive v ↦ σ′ ፤ `data D ፤ (`emp , α ⦂ S [ #emp ])

  C-ReceiveS :
    (⊢v : Γ ፤ v ↦ `chan α) →
    -- β fresh, implies this
    (α≢β : α ≢ β) →
    (sp : σ ~[ α ]~ (σ′ , α ⦂ `recvc S′ S [ α#σ′ ])) →
    Γ ፤ σ ፤ `receive v ↦ σ′ ፤ `chan β ፤ ((`emp , β ⦂ S′ [ #emp ]) , α ⦂ S [ #cons #emp α≢β ])

  C-SendD :
    (⊢v : Γ ፤ v ↦ `data D) →
    (⊢v′ : Γ ፤ v′ ↦ `chan α) →
    (sp : σ ~[ α ]~ (σ′ , α ⦂ `send D S [ α#σ′ ])) →
    Γ ፤ σ ፤ `send v `on v′ ↦ σ′ ፤ `data `unit ፤ (`emp , α ⦂ S [ #emp ])
  
  C-SendDS :
    (⊢v : Γ ፤ v ↦ `chan β) →
    (⊢v′ : Γ ፤ v′ ↦ `chan α) →
    (sp : σ ~[ α ]~ (σ′ , α ⦂ `sendc S′ S [ α#σ′ ])) →
    (sp′ : σ′ ~[ β ]~ (σ″ , β ⦂ S′ [ β#σ″ ])) →
    Γ ፤ σ ፤ `send v `on v′ ↦ σ″ ፤ `data `unit ፤ (`emp , α ⦂ S [ #emp ])
  
  C-Close :
    (⊢v : Γ ፤ v ↦ `chan α) → 
    (sp : σ ~[ α ]~ (σ′ , α ⦂ `end [ α#σ′ ])) →
    Γ ፤ σ ፤ `close v ↦ σ′ ፤ `data `unit ፤ `emp

  C-Accept :                    -- β fresh
    (⊢v : Γ ፤ v ↦ `data (`ap S)) →
    Γ ፤ σ ፤ `accept v ↦ σ ፤ `chan β ፤ (`emp , β ⦂ S [ #emp ])
    
  C-Request :                   -- β fresh
    (⊢v : Γ ፤ v ↦ `data (`ap S)) →
    Γ ፤ σ ፤ `request v ↦ σ ፤ `chan β ፤ (`emp , β ⦂ dualSession S [ #emp ])

  C-Val :                      -- this is the correct rule
    (⊢v : Γ ፤ v ↦ T) →
    Γ ፤ σ ፤ `thread (`ret v) ↦ σ ፤ T ፤ `emp

  C-App :
    (⊢v : Γ ፤ v ↦ `data (`fun σ₁ T U σ₂)) →
    (⊢v′ : Γ ፤ v′ ↦ T) →
    Γ ፤ (σ₁ ++ σ [ σ₁#σ ]) ፤ `app v v′ ↦ σ ፤ U ፤ σ₂

  C-New :
    Γ ፤ σ ፤ `new S ↦ σ ፤ `data (`ap S) ፤ `emp

  C-Let : ∀ {σσ σσ'} {σ₁′∩σ₂#σ₂′} →
    (⊢e : Γ ፤ σ ፤ e ↦ σ₁ ፤ T₁ ፤ σ₁′) →
    (⊢e′ : (Γ , x ⦂ T₁) ፤ (σ₁ ++ σ₁′ [ σ₁#σ₁′ ]) ፤ `thread t ↦ σ₂ ፤ T₂ ፤ σ₂′) →
    σσ ≡ σ₁ ∩ σ₂ →
    σσ' ⊆⊇ ((σ₁′ ∩ σ₂) ++ σ₂′ [ σ₁′∩σ₂#σ₂′ ]) → 
    Γ ፤ σ ፤ `thread (`let x e t) ↦ σσ ፤ T₂ ፤ σσ'

  C-LetV :
    (⊢v : Γ ፤ v ↦ T₁) →
    (⊢e′ : (Γ , x ⦂ T₁) ፤ σ ፤ `thread t ↦ σ₂ ፤ T₂ ፤ σ₂′) →
    Γ ፤ σ ፤ `thread (`letv x v t) ↦ σ₂ ፤ T₂ ፤ σ₂′

  C-Fork :
    (⊢e₁ : Γ ፤ σ₁ ፤ `thread t₁ ↦ `emp ፤ T₁ ፤ `emp) →
    (⊢e₂ : Γ ፤ σ₂ ፤ `thread t₂ ↦ σ ፤ T₂ ፤ `emp) →
    Γ ፤ (σ₁ ++ σ₂ [ σ₁#σ₂ ]) ፤ `thread (`fork t₁ t₂) ↦ σ ፤ T₂ ፤ `emp

-- value typing

 data _፤_↦_ : TEnv → Value → Type → Set where

  C-Const :
    Γ ፤ `unit ↦ `data `unit

  C-Chan :
    Γ ፤ `val (`cid γ p) ↦ `chan (`cid γ p)

  C-Var :
    Γ ∋ x ⦂ T →
    ---------------------
    Γ ፤ `val (`var x) ↦ T

  C-Abs :
    (⊢e : (Γ , x ⦂ T) ፤ σ ፤ e ↦ σ₁ ፤ U ፤ σ₂) → 
    Γ ፤ `lam σ x T e ↦ `data (`fun σ T U (σ₁ ++ σ₂ [ σ₁#σ₂ ]))

  C-Rec :
    let U = `data (`fun σ₁ T T′ σ₂) in
    (⊢v : (Γ , x ⦂ U) ፤ v ↦ U) →
    Γ ፤ `rec x U v ↦ U

-- configuration typing

data _⁏_⁏_↦_ : TEnv → Store → Config → Store → Set where

  C-Thread :
    (⊢e : Γ ፤ σ ፤ `thread t ↦ σ′ ፤ T ፤ `emp) →
    Γ ⁏ σ ⁏ ⟨ t ⟩ ↦ σ′

  C-Par :
    (⊢C₁ : Γ ⁏ σ ⁏ C₁ ↦ σ₁) →
    (⊢C₂ : Γ ⁏ σ₁ ⁏ C₂ ↦ σ₂) →
    Γ ⁏ σ ⁏ (C₁ ∥ C₂) ↦ σ₂

  C-NewN :
    (⊢C : (Γ , n ⦂ `data (`ap S)) ⁏ σ ⁏ C ↦ σ′) →
    Γ ⁏ σ ⁏ (ν n ⦂[ S ] C) ↦ σ′
    
  C-NewB : ∀ {β≢α} →
    (⊢C : Γ ⁏ ((σ , α ⦂ S [ α#σ ]), β ⦂ dualSession S [ #cons β#σ β≢α ]) ⁏ C ↦ σ′) → 
    α ≡ `cid γ `+ →
    β ≡ `cid γ `- → 
    -- γ not in Γ, σ, σ′
    ¬ InTEnv γ Γ →
    ¬ InStore γ σ →
    ¬ InStore γ σ′ →
    Γ ⁏ σ ⁏ (ν γ ∘ C) ↦ σ′

  C-NewC :
    (⊢C : Γ ⁏ σ ⁏ C ↦ σ′) → 
    -- γ not in Γ, σ, σ′
    ¬ InTEnv γ Γ →
    ¬ InStore γ σ →
    ¬ InStore γ σ′ →
    Γ ⁏ σ ⁏ (ν γ ∘ C) ↦ σ′



