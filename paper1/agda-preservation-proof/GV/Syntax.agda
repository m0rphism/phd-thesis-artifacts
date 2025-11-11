module GV.Syntax where

open import Data.List hiding (_++_)
open import Data.String hiding (_++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Identifier using (Id; Polarity; Alpha)

-- Gay and Vasconcelos, Functional Session Types, JFP 2010

Label : Set
Label = String

data Constant : Set where
  -- original
  `fix `fork `send `receive `accept `request : Constant

  -- extension
  `new : Constant

data Expr : Set where
  -- original
  `alpha : (α : Alpha) → Expr
  `const : (k : Constant) → Expr
  `lam : (x : Id) → (e : Expr) → Expr
  `pair : (e₁ : Expr) → (e₂ : Expr) → Expr
  `unit : Expr
  `app : (e₁ : Expr) → (e₂ : Expr) → Expr
  `letp : (x : Id) → (y : Id) → (e₁ : Expr) → (e₂ : Expr) → Expr

  -- extension
  `let : (x : Id) → (e₁ : Expr) → (e₂ : Expr) → Expr
  `letu : (e₁ : Expr) → (e₂ : Expr) → Expr
  `emp : Expr                           -- empty record
  `single : Alpha → Expr → Expr         -- singleton record
  `concat : Expr → Expr → Expr          -- disjoint record concatenation
  `split : Expr → Alpha → Expr          -- split off a single field
  `splitmany : Expr → List Alpha → Expr -- split into two records

private
  variable
    α β : Alpha
    x y : Id
    k : Constant
    e v₁ v₂ : Expr

data Value : Expr → Set where
  -- original
  `valpha : Value (`alpha α)
  `vconst : Value (`const k)
  `vlam : Value (`lam x e)
  `vpair : Value v₁ → Value v₂ → Value (`pair v₁ v₂)
  `vunit : Value `unit

  -- extension
  `vemp : Value `emp
  `vsingle : Value e → Value (`single α e)
  
data Config : Set where
  -- original
  ⟨_⟩ : (e : Expr) → Config
  _∥_ : (C₁ : Config) → (C₂ : Config) → Config -- parallel composition
  ν_,_∘_ : (γ δ : Id) → (C : Config) → Config  -- binder for channel pairs

  -- extension
  ν_∙_ : (n : Id) → (C : Config) → Config      -- binder for access points

mutual
  data Type : Set where
    -- original
    `session : Session → Type
    `unit : Type
    `pair : Type → Type → Type
    `fun  : Type → Type → Type  -- lin and unr
    `ap   : Session → Type      -- original syntax <S, S'>

    -- extension
    `record : Row → Type

  data Session : Set where
    `end : Session
    `inp : (T : Type) → (S : Session) → Session
    `outp : (T : Type) → (S : Session) → Session

  data Row : Set where
    `emp : Row
    _,_⦂_ : Row → Alpha → Type → Row

data TEnv : Set where
  `emp : TEnv
  _,_⦂_ : (Γ : TEnv) → (x : Id) (T : Type) → TEnv

_,,_ : TEnv → TEnv → TEnv
Γ ,, `emp = Γ
Γ ,, (Δ , x ⦂ T) = (Γ ,, Δ) , x ⦂ T

private
  variable
    α* : List Alpha
    Γ Γ′ Γ₁ Γ₂ : TEnv
    T T′ U : Type
    S : Session
    R R′ R₁ R₂ R₃ : Row

data _≡[_,_⦂_] : TEnv → TEnv → Id → Type → Set where

  `Z :
    (Γ , x ⦂ T) ≡[ Γ , x ⦂ T ]

  `S :
    x ≢ y →
    Γ ≡[ Γ′ , x ⦂ T ] →
    (Γ , y ⦂ U) ≡[ (Γ′ , y ⦂ U) , x ⦂ T ]

-- rows

_++_ : Row → Row → Row
r₁ ++ `emp = r₁
r₁ ++ (r₂ , α ⦂ T) = (r₁ ++ r₂) , α ⦂ T 

row-++-assoc : ∀ r₁ r₂ r₃ → (r₁ ++ (r₂ ++ r₃)) ≡ (r₁ ++ r₂) ++ r₃
row-++-assoc r₁ r₂ `emp = refl
row-++-assoc r₁ r₂ (r₃ , x ⦂ x₁) rewrite row-++-assoc r₁ r₂ r₃ = refl

-- reordering rows

-- R ~[ α ]R~ R′ holds iff α is in R and R′ is a reordering of R,
-- where the field described by α is the head of R′.
data _~[_]R~_ : Row → Alpha → Row → Set where

  `Z : (R , α ⦂ T) ~[ α ]R~ (R , α ⦂ T)

  `S : α ≢ β →
       R ~[ α ]R~ (R′ , α ⦂ T) →
       (R , β ⦂ T′) ~[ α ]R~ ((R′ , β ⦂ T′) , α ⦂ T)

-- R >> α* >> R₁ , R₂ holds iff α* are in R and R can be split
-- into R₁ and R₂, such that R₁ contains exactly the fields
-- described by α*.
data  _>>_>>_,_ : Row → List Alpha → Row → Row → Set where

  `remp : 
    R >> [] >> `emp , R

  `rlft : 
    R ~[ α ]R~ (R′ , α ⦂ T) →
    R′ >> α* >> R₁ , R₂ →
    R >> (α ∷ α*) >> (R₁ , α ⦂ T) , R₂

-- linearity

data Lin : Type → Set where
  `linsession : Lin (`session S)
  `linpairleft : Lin T → Lin (`pair T U)
  `linpairright : Lin U → Lin (`pair T U)
  `linfun : Lin (`fun T U)
  `linrecord : Lin (`record R)

data Unr : Type → Set where
  `unrunit : Unr `unit
  `unrpair : Unr T → Unr U → Unr (`pair T U)
  `unrfun : Unr (`fun T U)
  `unrap : Unr (`ap S)
  `unrend : Unr (`session `end)
  `unremp : Unr (`record `emp)

data UnrEnv : TEnv → Set where
  `unremp : UnrEnv `emp
  `unrvar : (unrG : UnrEnv Γ) → (unrT : Unr T) → UnrEnv (Γ , x ⦂ T)

data Split : TEnv → TEnv → TEnv → Set where
  `spemp : Split `emp `emp `emp
  `spunr : Unr T → Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ T) (Γ₁ , x ⦂ T) (Γ₂ , x ⦂ T)
  `splft : Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ T) (Γ₁ , x ⦂ T) Γ₂
  `sprgt : Split Γ Γ₁ Γ₂ → Split (Γ , x ⦂ T) (Γ₁) (Γ₂ , x ⦂ T)

allunr : ∀ Γ → UnrEnv Γ → Split Γ Γ Γ
allunr `emp unrG = `spemp
allunr (Γ , x ⦂ T) (`unrvar unrG unrT) = `spunr unrT (allunr Γ unrG)

-- duality

dual : Session → Session
dual `end = `end
dual (`inp T S) = `outp T (dual S)
dual (`outp T S) = `inp T (dual S)
