module VGR.Free where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Identifier
open import VGR.Syntax

private
  variable
    x y γ : Id
    t t₁ t₂ : Thread
    C C′ : Config
    S S₁ S₂ : Session
    T T₁ T₂ : Type
    v v₁ v₂ : Value
    e : Expr
    α : Alpha
    σ σ₁ σ₂ : Store
    α#σ : α # σ
    p : Polarity
    D : Data
    Γ : TEnv

mutual
  data FreeD : Id → Data → Set where
    `fap : FreeS x S → FreeD x (`ap S)
    `ffunleft : FreeTy x T₁ → FreeD x (`fun σ₁ T₁ T₂ σ₂)
    `ffunright : FreeTy x T₂ → FreeD x (`fun σ₁ T₁ T₂ σ₂)

  data FreeTy : Id → Type → Set where
    `fdata : FreeD x D → FreeTy x (`data D)
    `fchan : FreeA x α → FreeTy x (`chan α)

  data FreeS : Id → Session → Set where
    `fsenddata : FreeD x D → FreeS x (`send D S)
    `fsendcont : FreeS x S → FreeS x (`send D S)
    `frecvdata : FreeD x D → FreeS x (`recv D S)
    `frecvcont : FreeS x S → FreeS x (`recv D S)
    `fsendcleft : FreeS x S₁ → FreeS x (`sendc S₁ S₂)
    `fsendcright : FreeS x S₂ → FreeS x (`sendc S₁ S₂)
    `frecvcleft : FreeS x S₁ → FreeS x (`recvc S₁ S₂)
    `frecvcright : FreeS x S₂ → FreeS x (`recvc S₁ S₂)

  data FreeA : Id → Alpha → Set where
    `fvar : FreeA x (`var x)
    `fcid : FreeA x (`cid x p)

  data FreeE : Id → Expr → Set where
    `fval : FreeV x v → FreeE x (`val v)
    `fthread : FreeT x t → FreeE x (`thread t)
    `fappleft : FreeV x v₁ → FreeE x (`app v₁ v₂)
    `fappright : FreeV x v₂ → FreeE x (`app v₁ v₂)
    `faccept : FreeV x v → FreeE x (`accept v)
    `frequest : FreeV x v → FreeE x (`request v)
    `fsendleft : FreeV x v₁ → FreeE x (`send v₁ `on v₂)
    `fsendright : FreeV x v₂ → FreeE x (`send v₁ `on v₂)
    `freceive : FreeV x v → FreeE x (`receive v)
    `fclose : FreeV x v → FreeE x (`close v)

  data FreeV : Id → Value → Set where
    `fval : FreeA x α → FreeV x (`val α)
    `flam : x ≢ y → FreeE x e → FreeV x (`lam σ y T e)
    `frec : x ≢ y → FreeV x v → FreeV x (`rec y T v)

  data FreeT : Id → Thread → Set where
    `fret : FreeV x v → FreeT x (`ret v)
    `fletheader : FreeE x e → FreeT x (`let y e t)
    `fletbody : x ≢ y → FreeT x t → FreeT x (`let y e t)
    `fletvheader : FreeV x v → FreeT x (`letv y v t)
    `fletvbody : x ≢ y → FreeT x t → FreeT x (`letv y v t)
    `fforkleft : FreeT x t₁ → FreeT x (`fork t₁ t₂)
    `fforkright : FreeT x t₂ → FreeT x (`fork t₁ t₂)

data FreeC : Id → Config → Set where
  `fthread : FreeT x t → FreeC x ⟨ t ⟩
  `fparleft : FreeC x C → FreeC x (C ∥ C′)
  `fparright : FreeC x C′ → FreeC x (C ∥ C′)
  `fscopenty : FreeS x S → FreeC x (ν y ⦂[ S ] C)
  `fscopen : x ≢ y → FreeC x C → FreeC x (ν y ⦂[ S ] C)
  `fscopec : x ≢ γ → FreeC x C → FreeC x (ν γ ∘ C)

data InDom : Id → TEnv → Set where
  `here : InDom x (Γ , x ⦂ T)
  `there : InDom x Γ → x ≢ y → InDom x (Γ , y ⦂ T)

data InTEnv : Id → TEnv → Set where
  `here : FreeTy x T → InTEnv x (Γ , y ⦂ T)
  `there : InTEnv x Γ → InTEnv x (Γ , y ⦂ T)

data InStore : Id → Store → Set where
  `herevar : FreeA x α → InStore x (σ , α ⦂ S [ α#σ ])
  `heretype : FreeS x S → InStore x (σ , α ⦂ S [ α#σ ])
  `there : InStore x σ → InStore x (σ , α ⦂ S [ α#σ ])
