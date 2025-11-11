module GV.Typing where

open import Data.List hiding (_++_)
open import GV.Syntax
open import Identifier using (Id; Polarity; Alpha; `var; `cid; `+; `-)

private
  variable
    α : Alpha
    α* : List Alpha
    x y n γ δ : Id
    k : Constant
    T U V T₁ T₂ : Type
    Γ Γ′ Γ₁ Γ₂ : TEnv
    e e′ e₁ e₂ : Expr
    r r′ r₁ r₂ : Row
    S : Session
    C C₁ C₂ : Config

-- constant typing

data ⊢const_⦂_ : Constant → Type → Set where

  T-Fix : ⊢const `fix ⦂ `fun (`fun T T) T

  T-Receive : ⊢const `receive ⦂ `fun (`session (`inp T S)) (`pair T (`session S))

  T-Send : ⊢const `send ⦂ `fun T (`fun (`session (`outp T S)) (`session S))

  T-Accept : ⊢const `accept ⦂ `fun (`ap S) (`session S)

  T-Request : ⊢const `request ⦂ `fun (`ap S) (`session (dual S))

  T-New : ⊢const `new ⦂ `ap S

  T-Fork :
    Unr T →
    ⊢const `fork ⦂ `fun T `unit

-- expression typing

data _⊢_⦂_ : TEnv → Expr → Type → Set where

  T-Unit :
    UnrEnv Γ →
    Γ ⊢ `unit ⦂ `unit

  T-Const :
    UnrEnv Γ →
    ⊢const k ⦂ T →
    Γ ⊢ `const k ⦂ T

  T-Id :
    Γ ≡[ Γ′ , x ⦂ T ] → 
    UnrEnv Γ′ →
    Γ ⊢ `alpha (`var x) ⦂ T

  T-Pair :
    Split Γ Γ₁ Γ₂ → 
    Γ₁ ⊢ e₁ ⦂ T₁ →
    Γ₂ ⊢ e₂ ⦂ T₂ →
    Γ  ⊢ `pair e₁ e₂ ⦂ `pair T₁ T₂

  T-Split :
    Split Γ Γ₁ Γ₂ → 
    Γ₁ ⊢ e ⦂ `pair T U →
    ((Γ₂ , x ⦂ T) , y ⦂ U) ⊢ e′ ⦂ V →
    Γ ⊢ `letp x y e e′ ⦂ V

  T-Abs :
    (Γ , x ⦂ T) ⊢ e ⦂ U →
    Γ ⊢ `lam x e ⦂ `fun T U

  T-App :
    Split Γ Γ₁ Γ₂ → 
    Γ₁ ⊢ e₁ ⦂ `fun T U →
    Γ₂ ⊢ e₂ ⦂ T →
    Γ ⊢ `app e₁ e₂ ⦂ U

  -- extra

  T-Let :                       -- derived
    Split Γ Γ₁ Γ₂ → 
    Γ₁ ⊢ e₁ ⦂ T₁ →
    (Γ₂ , x ⦂ T₁) ⊢ e₂ ⦂ T₂ →
    Γ ⊢ `let x e₁ e₂ ⦂ T₂

  T-UnitElim :
    Split Γ Γ₁ Γ₂ → 
    Γ₁ ⊢ e ⦂ `unit →
    Γ₂ ⊢ e′ ⦂ V →
    Γ ⊢ `letu e e′ ⦂ V

  T-Emp :
    UnrEnv Γ →
    Γ ⊢ `emp ⦂ `record `emp

  T-Single :
    Γ ⊢ e ⦂ T →
    Γ ⊢ `single α e ⦂ `record (`emp , α ⦂ T)

  T-Concat :
    Split Γ Γ₁ Γ₂ → 
    Γ₁ ⊢ e₁ ⦂ `record r₁ →
    Γ₂ ⊢ e₂ ⦂ `record r₂ →
    Γ ⊢ `concat e₁ e₂ ⦂ `record (r₁ ++ r₂)

  T-SplitRecord :
    Γ ⊢ e ⦂ `record r →
    r ~[ α ]R~ (r′ , α ⦂ T) →
    Γ ⊢ `split e α ⦂ `pair T (`record r′)

  T-SplitRecordMany :
    Γ ⊢ e ⦂ `record r →
    r >> α* >> r₁ , r₂ →
    Γ ⊢ `splitmany e α* ⦂ `pair (`record r₁) (`record r₂)

-- configuration typing

data _⊢conf_ : TEnv → Config → Set where

  T-Thread :
    Unr T →
    Γ ⊢ e ⦂ T →
    Γ ⊢conf ⟨ e ⟩

  T-Par :
    Split Γ Γ₁ Γ₂ →
    Γ₁ ⊢conf C₁ →
    Γ₂ ⊢conf C₂ →
    Γ ⊢conf (C₁ ∥ C₂)

  T-New :
    ((Γ , γ ⦂ `session S) , δ ⦂ `session (dual S)) ⊢conf C →
    Γ ⊢conf (ν γ , δ ∘ C)

  T-NewAp :
    (Γ , n ⦂ `ap S) ⊢conf C →
    Γ ⊢conf (ν n ∙ C)
