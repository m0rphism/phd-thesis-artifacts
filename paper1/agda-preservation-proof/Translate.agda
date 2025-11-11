module Translate where

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.List using (List)
open import Data.String renaming (_++_ to _+++_)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality using (_≢_; _≡_; refl; sym; cong)

open import Identifier

open import GV.Syntax
import GV.Typing as TRG

import VGR.Syntax as SRC
open SRC using (_,_⦂_[_])
open import VGR.Typing
open import VGR.Lemmas as SRC

private
  variable
    x x′ : Id
    α : Alpha
    Γ : SRC.TEnv
    v : SRC.Value
    e : SRC.Expr
    t : SRC.Thread
    D : SRC.Data
    C : SRC.Config
    T T′ U : SRC.Type
    σ σ′ σ₁ σ₂ : SRC.Store
    Δ : TEnv

-- fresh variable names introduced by translation

st-name : String
st-name = "**s**"

st : Expr
st = `alpha (`var st-name)

ch-name : String
ch-name = "ch"

ch : Expr
ch = `alpha (`var ch-name)

pl-name : String
pl-name = "chb"

pl : Expr
pl = `alpha (`var pl-name)

rv-name : String
rv-name = "rv"

rv : Expr
rv = `alpha (`var rv-name)

st≢rv : st-name ≢ rv-name
st≢rv with st-name ≟ rv-name
... | no ¬p = ¬p

rv≢_ : rv-name ≢ "_"
rv≢_ with rv-name ≟ "_"
... | no ¬p = ¬p

pos neg : Id → Id
pos x = x +++ "+"
neg x = x +++ "-"

cp->name : Id → Polarity → Id
cp->name x `+ = pos x
cp->name x `- = neg x

-- channel representation

repT : Alpha → Type
repT α = `unit        -- translation is fully type driven

repV : Alpha → Expr
repV α = `unit

-- translation of VGR value types and contexts to GV types and contexts

⟪_⟫ˢ : SRC.Session → Session
⟪_⟫ᵈ : SRC.Data → Type
⟪_⟫ⱽ : SRC.Type → Type
⟪_⟫ᴿ : SRC.Store → Row

⟪ SRC.`send D S ⟫ˢ = `outp ⟪ D ⟫ᵈ ⟪ S ⟫ˢ
⟪ SRC.`recv D S ⟫ˢ = `inp ⟪ D ⟫ᵈ ⟪ S ⟫ˢ
⟪ SRC.`sendc S S₁ ⟫ˢ = `outp (`session ⟪ S ⟫ˢ) ⟪ S₁ ⟫ˢ
⟪ SRC.`recvc S S₁ ⟫ˢ = `inp (`session ⟪ S ⟫ˢ) ⟪ S₁ ⟫ˢ
⟪ SRC.`end ⟫ˢ = `end

⟪ SRC.`ap S ⟫ᵈ =
  `ap ⟪ S ⟫ˢ
⟪ SRC.`fun σ₁ T₁ T₂ σ₂ ⟫ᵈ =
  `fun ⟪ T₁ ⟫ⱽ (`fun (`record ⟪ σ₁ ⟫ᴿ) (`pair ⟪ T₂ ⟫ⱽ (`record ⟪ σ₂ ⟫ᴿ)))
⟪ SRC.`unit ⟫ᵈ =
  `unit

⟪ SRC.`data D ⟫ⱽ = ⟪ D ⟫ᵈ
⟪ SRC.`chan α ⟫ⱽ = repT α

⟪ SRC.`emp ⟫ᴿ = `emp
⟪ σ , α ⦂ S [ _ ] ⟫ᴿ = ⟪ σ ⟫ᴿ , α ⦂ `session ⟪ S ⟫ˢ

⟪_⟫ : SRC.TEnv → TEnv
⟪ SRC.`emp ⟫ = `emp
⟪ SRC._,_⦂_ Γ x T ⟫ = ⟪ Γ ⟫ , x ⦂ ⟪ T ⟫ⱽ

-- translation of value types and contexts is unrestricted

Unr-⟪⟫ᵈ : Unr ⟪ D ⟫ᵈ
Unr-⟪⟫ᵈ {SRC.`ap S} = `unrap
Unr-⟪⟫ᵈ {SRC.`fun σ₁ T₁ T₂ σ₂} = `unrfun
Unr-⟪⟫ᵈ {SRC.`unit} = `unrunit

Unr-⟪⟫ⱽ : Unr ⟪ T ⟫ⱽ
Unr-⟪⟫ⱽ {SRC.`data D} = Unr-⟪⟫ᵈ
Unr-⟪⟫ⱽ {SRC.`chan α} = `unrunit

Unr-⟪⟫ : UnrEnv ⟪ Γ ⟫
Unr-⟪⟫ {SRC.`emp} = `unremp
Unr-⟪⟫ {SRC._,_⦂_ Γ x T} = `unrvar Unr-⟪⟫ (Unr-⟪⟫ⱽ {T})

-- translation of values and expression

⟦_⟧ⱽ : Γ ፤ v ↦ T → Expr
⟦_⟧ᵉ : (Γ ፤ σ ፤ e ↦ σ₁ ፤ U ፤ σ₂) → Expr

⟦ C-Const ⟧ⱽ = `unit
⟦ C-Chan {γ = γ} {p = p} ⟧ⱽ = repV (`cid γ p)             -- fully type driven
⟦ C-Var {x = x} x⦂T ⟧ⱽ = `alpha (`var x)
⟦ C-Abs {x = x} ⊢e ⟧ⱽ = `lam x (`lam st-name ⟦ ⊢e ⟧ᵉ)
⟦ C-Rec {x = x} ⊢v ⟧ⱽ = `app (`const `fix) (`lam x ⟦ ⊢v ⟧ⱽ)

⟦ C-ReceiveD {α = α} ⊢v sp ⟧ᵉ =
  `letp ch-name st-name (`split st α)
  (`letp rv-name ch-name (`app (`const `receive) ch)
  (`pair rv (`concat st (`single α ch))))
⟦ C-ReceiveS {α = α} {β = β} ⊢v α≢β sp ⟧ᵉ =
  `letp ch-name st-name (`split st α)
  (`letp rv-name ch-name (`app (`const `receive) ch)
  (`pair (repV β) (`concat st (`concat (`single β rv) (`single α ch)))))
⟦ C-SendD {α = α} ⊢v ⊢v′ sp ⟧ᵉ =
  `letp ch-name st-name (`split st α)
  (`let ch-name (`app (`app (`const `send) ⟦ ⊢v ⟧ⱽ) ch)
  (`pair `unit (`concat st (`single α ch))))
⟦ C-SendDS {β = β} {α = α} ⊢v ⊢v′ sp sp′ ⟧ᵉ =
  `letp ch-name st-name (`split st α)
  (`letp pl-name st-name (`split st β)
  (`let ch-name (`app (`app (`const `send) pl) ch)
  (`pair `unit (`concat st (`single α ch)))))
⟦ C-Close {α = α} ⊢v sp ⟧ᵉ =
  `letp ch-name st-name (`split st α)
  (`pair `unit st)
⟦ C-Accept {β = β} ⊢v ⟧ᵉ =
  `let rv-name (`app (`const `accept) ⟦ ⊢v ⟧ⱽ)
  (`pair (repV β) (`concat st (`single β rv)))
⟦ C-Request {β = β} ⊢v ⟧ᵉ =
  `let rv-name (`app (`const `request) ⟦ ⊢v ⟧ⱽ)
  (`pair (repV β) (`concat st (`single β rv)))
⟦ C-Val ⊢v ⟧ᵉ =
  `pair ⟦ ⊢v ⟧ⱽ st
⟦ C-App {σ₁ = σ₁} {σ₂ = σ₂} {σ = σ} ⊢v ⊢v′ ⟧ᵉ =
  `letp st-name pl-name (`splitmany st (SRC.store-dom σ₁))
  (`letp rv-name st-name (`app (`app ⟦ ⊢v ⟧ⱽ ⟦ ⊢v′ ⟧ⱽ) st)
  (`pair rv (`concat pl st)))
⟦ C-New ⟧ᵉ =
  `pair (`const `new) st
⟦ C-Let {x = x} ⊢e ⊢e₁ σσ σσ₁ ⟧ᵉ =
  `letp x st-name ⟦ ⊢e ⟧ᵉ ⟦ ⊢e₁ ⟧ᵉ
⟦ C-LetV {x = x} ⊢v ⊢e ⟧ᵉ =
  `let x ⟦ ⊢v ⟧ⱽ ⟦ ⊢e ⟧ᵉ
⟦ C-Fork {σ₁ = σ₁} {σ₂ = σ₂} {σ = σ} ⊢e ⊢e₁ ⟧ᵉ =
  `letp st-name rv-name (`splitmany st (SRC.store-dom σ₁))
  (`letu (`app (`const `fork) ⟦ ⊢e ⟧ᵉ)
  (`let st-name rv ⟦ ⊢e₁ ⟧ᵉ))

-- translation of stores and configurations

⟦_⟧ᴿ : SRC.Store → Expr
⟦ SRC.`emp ⟧ᴿ  = `emp
⟦ γ̃ , α ⦂ S [ α#σ ] ⟧ᴿ = `concat ⟦ γ̃ ⟧ᴿ (`single α (`alpha α))

⟦_⟧ᶜ : Γ ⁏ σ ⁏ C ↦ σ′ → Config
⟦ C-Thread {σ = σ} {t = t} {σ′ = σ′} ⊢e ⟧ᶜ =
  ⟨ (`let st-name ⟦ σ′ SRC.\\ σ ⟧ᴿ ⟦ ⊢e ⟧ᵉ) ⟩
⟦ C-Par ⊢C ⊢C₁ ⟧ᶜ = 
  ⟦ ⊢C ⟧ᶜ ∥ ⟦ ⊢C₁ ⟧ᶜ
⟦ C-NewN {n = n} ⊢C ⟧ᶜ = 
  ν n ∙ ⟦ ⊢C ⟧ᶜ
⟦ C-NewB {γ = γ} ⊢C α≡ β≡ x x₁ x₂ ⟧ᶜ = 
  ν γ , neg γ ∘ ⟦ ⊢C ⟧ᶜ
⟦ C-NewC {γ = γ} ⊢C x x₁ x₂ ⟧ᶜ =
  ν γ , neg γ ∘ ⟦ ⊢C ⟧ᶜ

-- postulates as described in `README.md`.

postulate

  post-swap-expr :
    ∀ {Γ T T′ U e} → 
    x ≢ x′ →
    (((Γ , x ⦂ T) , x′ ⦂ T′) TRG.⊢ e ⦂ U) → 
    (((Γ , x′ ⦂ T′) , x ⦂ T) TRG.⊢ e ⦂ U)

  post-st-unused :
    x ≢ st-name

-- environment preservation

env-access :
  Γ ∋ x ⦂ T →
  Σ _ λ Δ → ⟪ Γ ⟫ ≡[ Δ , x ⦂ ⟪ T ⟫ⱽ ]
env-access `Z = ⟨ _ , `Z ⟩
env-access (`S x≢y x⦂t) with env-access x⦂t
... | ⟨ Δ , x∈ ⟩ = ⟨ _ , (`S x≢y x∈) ⟩

unr-access : (x⦂t : Γ ∋ x ⦂ T) → UnrEnv (proj₁ (env-access x⦂t))
unr-access `Z = Unr-⟪⟫
unr-access {T = T} (`S {T′ = T′} x≢y x⦂t) = `unrvar (unr-access x⦂t) (Unr-⟪⟫ⱽ {T′})

-- store preservation

store-reordering :
  σ ~[ α ]~ σ′ →
  ⟪ σ ⟫ᴿ ~[ α ]R~ ⟪ σ′ ⟫ᴿ
store-reordering `Z = `Z
store-reordering (`S x σ~σ′) = `S x (store-reordering σ~σ′)

store-concat : ∀ σ₁ σ₂ (σ₁#σ₂ :  SRC.all# σ₁ σ₂) → 
  ⟪ σ₁ SRC.++ σ₂ [ σ₁#σ₂ ] ⟫ᴿ ≡ ⟪ σ₁ ⟫ᴿ ++ ⟪ σ₂ ⟫ᴿ
store-concat σ₁ SRC.`emp  _ = refl
store-concat σ₁ (σ₂ , α ⦂ S [ α#σ₂ ]) ⟨ σ₁#σ₂ , snd ⟩ = cong (λ p → p , α ⦂ `session ⟪ S ⟫ˢ) (store-concat σ₁ σ₂ σ₁#σ₂)

session-dual : ∀ S → dual ⟪ S ⟫ˢ ≡ ⟪ SRC.dualSession S ⟫ˢ
session-dual (SRC.`send D S) = cong (`inp ⟪ D ⟫ᵈ) (session-dual S)
session-dual (SRC.`recv D S) = cong (`outp ⟪ D ⟫ᵈ) (session-dual S)
session-dual (SRC.`sendc S S₁) = cong (`inp (`session ⟪ S ⟫ˢ)) (session-dual S₁)
session-dual (SRC.`recvc S S₁) = cong (`outp (`session ⟪ S ⟫ˢ)) (session-dual S₁)
session-dual SRC.`end = refl

row-emp-++ : (r : Row) → `emp ++ r ≡ r
row-emp-++ `emp = refl
row-emp-++ (r , x ⦂ x₁) rewrite row-emp-++ r = refl

store-permutation :
  {T : Type} →
  ∀ σ₁ α σ₂ (α#σ₂ : α SRC.# σ₂) →  
  ((⟪ σ₁ ⟫ᴿ , α ⦂ T) ++ ⟪ σ₂ ⟫ᴿ) ~[ α ]R~ ((⟪ σ₁ ⟫ᴿ ++ ⟪ σ₂ ⟫ᴿ) , α ⦂ T)
store-permutation σ₁ α SRC.`emp α#σ₂ = `Z
store-permutation σ₁ α (σ₂ , α₁ ⦂ S [ α₁#σ₁ ]) (SRC.#cons α#σ₂ α≢α₁) =
  `S α≢α₁ (store-permutation σ₁ α σ₂ α#σ₂)

store-splitting′ :
  ∀ σ₁ σ₂ (σ₁#σ₂ : SRC.all# σ₁ σ₂) →
  (⟪ σ₁ ⟫ᴿ ++ ⟪ σ₂ ⟫ᴿ) >> SRC.store-dom σ₁ >> ⟪ σ₁ ⟫ᴿ , ⟪ σ₂ ⟫ᴿ
store-splitting′ SRC.`emp σ₂ σ₁#σ₂ rewrite row-emp-++ ⟪ σ₂ ⟫ᴿ = `remp
store-splitting′ (σ₁ , α ⦂ S [ α#σ ]) σ₂ σ₁α#σ₂
  = `rlft (store-permutation σ₁ α σ₂ (SRC.all#-head σ₁α#σ₂)) (store-splitting′ σ₁ σ₂ (SRC.all#-weak σ₁α#σ₂))

store-splitting :
  ∀ σ₁ σ₂ (σ₁#σ₂ : SRC.all# σ₁ σ₂) →
  ⟪ σ₁ SRC.++ σ₂ [ σ₁#σ₂ ] ⟫ᴿ >> SRC.store-dom σ₁ >> ⟪ σ₁ ⟫ᴿ , ⟪ σ₂ ⟫ᴿ
store-splitting σ₁ σ₂ σ₁#σ₂ rewrite store-concat σ₁ σ₂ σ₁#σ₂ = store-splitting′ σ₁ σ₂ σ₁#σ₂


ty-let-rewrite1 : {Γ : TEnv}{e : Expr}{T : Type} →
  ∀ σ₁ σ₁′ σ₁#σ₁′ →
  ((Γ , st-name ⦂ `record ⟪ σ₁ SRC.++ σ₁′ [ σ₁#σ₁′ ] ⟫ᴿ) TRG.⊢ e ⦂ T) ≡
    ((Γ , st-name ⦂ `record (⟪ σ₁ ⟫ᴿ ++ ⟪ σ₁′ ⟫ᴿ)) TRG.⊢ e ⦂ T)
ty-let-rewrite1 σ₁ σ₁′ σ₁#σ₁′ rewrite store-concat σ₁ σ₁′ σ₁#σ₁′ = refl

ty-let-rewrite2 : {Γ : TEnv}{e : Expr}{T : Type} →
  ∀ σ₁ σ₁′ σ₁#σ₁′ →
  ((Γ , st-name ⦂ `record ⟪ σ₁ SRC.++ σ₁′ [ σ₁#σ₁′ ] ⟫ᴿ) TRG.⊢ e ⦂ T) →
  ((Γ , st-name ⦂ `record (⟪ σ₁ ⟫ᴿ ++ ⟪ σ₁′ ⟫ᴿ)) TRG.⊢ e ⦂ T)
ty-let-rewrite2 {Γ}{e}{T} σ₁ σ₁′ σ₁#σ₁′ x rewrite ty-let-rewrite1  {Γ}{e}{T} σ₁ σ₁′ σ₁#σ₁′ = x


-- typing preservation

postulate
  -- this is a shortcut / hack.
  -- In reality, σ₁ and σ₂ are isomorphic and a proper reordering isomorphism of the records
  -- has to be inserted. 
  ⊆⊇-≡ : {σ₁ σ₂ : SRC.Store} → σ₁ SRC.⊆⊇ σ₂ → σ₁ ≡ σ₂

  -- a final proof obligation
  σ₁#σ₁′⇒σ₁∩σ₂#σ₁′∩σ₂ : ∀ {σ₁′} → SRC.all# σ₁ σ₁′ → SRC.all# (σ₁ SRC.∩ σ₂) (σ₁′ SRC.∩ σ₂)

lemma-let-rewrite-intersection :
  ∀ σ₁ σ₂ σ₁′ (σ₁#σ₁′ : SRC.all# σ₁ σ₁′)
    (σ₁₂#σ₁′₂ : SRC.all# (σ₁ SRC.∩ σ₂) (σ₁′ SRC.∩ σ₂))
    (σ₂⊆σ₁++σ₂ : σ₂ SRC.⊆ (σ₁ SRC.++ σ₁′ [ σ₁#σ₁′ ])) → 
  (⟪ σ₁ SRC.∩ σ₂ ⟫ᴿ ++ ⟪ σ₁′ SRC.∩ σ₂ ⟫ᴿ) ≡ ⟪ σ₂ ⟫ᴿ
lemma-let-rewrite-intersection σ₁ σ₂ σ₁′ σ₁#σ₁′ σ₁₂#σ₁′₂ σ₂⊆σ₁++σ₂
  rewrite sym (store-concat (σ₁ SRC.∩ σ₂) (σ₁′ SRC.∩ σ₂) σ₁₂#σ₁′₂)
  = cong ⟪_⟫ᴿ (⊆⊇-≡ (SRC.store-sub σ₂⊆σ₁++σ₂))

lemma-let-rewrite-full :
  ∀ σ₁ σ₂ σ₁′ σ₂′ σ₁#σ₁′ σ₁′∩σ₂#σ₂′ σ₁⊆σ → 
  (⟪ σ₁ SRC.∩ σ₂ ⟫ᴿ ++ ⟪ (σ₁′ SRC.∩ σ₂) SRC.++ σ₂′ [ σ₁′∩σ₂#σ₂′ ] ⟫ᴿ) ≡ (⟪ σ₂ ⟫ᴿ ++ ⟪ σ₂′ ⟫ᴿ)
lemma-let-rewrite-full σ₁ σ₂ σ₁′ σ₂′ σ₁#σ₁′ σ₁′∩σ₂#σ₂′ σ₁⊆σ
  rewrite store-concat (σ₁′ SRC.∩ σ₂) σ₂′ σ₁′∩σ₂#σ₂′
        | row-++-assoc ⟪ σ₁ SRC.∩ σ₂ ⟫ᴿ ⟪ σ₁′ SRC.∩ σ₂ ⟫ᴿ ⟪ σ₂′ ⟫ᴿ
  = cong (λ r → r ++ ⟪ σ₂′ ⟫ᴿ)
         (lemma-let-rewrite-intersection σ₁ σ₂ σ₁′ σ₁#σ₁′ (σ₁#σ₁′⇒σ₁∩σ₂#σ₁′∩σ₂ {σ₂ = σ₂} σ₁#σ₁′) σ₁⊆σ)


ty-preserveV :
  (⊢v : Γ ፤ v ↦ T) →
  ⟪ Γ ⟫ TRG.⊢ ⟦ ⊢v ⟧ⱽ ⦂ ⟪ T ⟫ⱽ

ty-preserveE :
  (⊢e : Γ ፤ σ ፤ e ↦ σ₁ ፤ T ፤ σ₂) →
  (⟪ Γ ⟫ , st-name ⦂ `record ⟪ σ ⟫ᴿ) TRG.⊢ ⟦ ⊢e ⟧ᵉ ⦂ `pair ⟪ T ⟫ⱽ (`record (⟪ σ₁ ⟫ᴿ ++ ⟪ σ₂ ⟫ᴿ))

ty-preserveV C-Const = TRG.T-Unit Unr-⟪⟫
ty-preserveV C-Chan = TRG.T-Unit Unr-⟪⟫
ty-preserveV (C-Var x⦂T) with env-access x⦂T | unr-access x⦂T
... | ⟨ Δ , snd ⟩ | unra = TRG.T-Id snd unra
ty-preserveV (C-Abs {σ₁ = σ₁} {σ₂ = σ₂} {σ₁#σ₂ = σ₁#σ₂} ⊢e) with ty-preserveE ⊢e
... | ty-pe rewrite store-concat σ₁ σ₂ σ₁#σ₂ =
  TRG.T-Abs (TRG.T-Abs ty-pe)
ty-preserveV {Γ} (C-Rec ⊢v) = 
  TRG.T-App (allunr ⟪ Γ ⟫ Unr-⟪⟫) (TRG.T-Const Unr-⟪⟫ TRG.T-Fix) (TRG.T-Abs (ty-preserveV ⊢v))

ty-preserveE (C-ReceiveD ⊢v sp) = 
  TRG.T-Split (`splft (allunr _ Unr-⟪⟫)) 
    (TRG.T-SplitRecord (TRG.T-Id `Z Unr-⟪⟫) (store-reordering sp))
    (TRG.T-Split (`sprgt (`splft (allunr _ Unr-⟪⟫)))
      (TRG.T-App (`sprgt (allunr _ Unr-⟪⟫)) (TRG.T-Const Unr-⟪⟫ TRG.T-Receive) (TRG.T-Id `Z Unr-⟪⟫))
      (TRG.T-Pair
        (`sprgt (`splft (`sprgt (allunr _ Unr-⟪⟫))))
        (TRG.T-Id `Z Unr-⟪⟫)
        (TRG.T-Concat
          (`sprgt (`splft (allunr _ Unr-⟪⟫)))
          (TRG.T-Id `Z Unr-⟪⟫)
          (TRG.T-Single (TRG.T-Id `Z Unr-⟪⟫)))))

ty-preserveE (C-ReceiveS ⊢v α≢β sp) =
  TRG.T-Split
    (`splft (allunr _ Unr-⟪⟫))
    (TRG.T-SplitRecord (TRG.T-Id `Z Unr-⟪⟫) (store-reordering sp))
    (TRG.T-Split
      (`sprgt (`splft (allunr _ Unr-⟪⟫)))
      (TRG.T-App (`sprgt (allunr _ Unr-⟪⟫)) (TRG.T-Const Unr-⟪⟫ TRG.T-Receive) (TRG.T-Id `Z Unr-⟪⟫))
      (TRG.T-Pair
        (`sprgt (`sprgt (`sprgt (allunr _ Unr-⟪⟫))))
        (TRG.T-Unit Unr-⟪⟫)
        (TRG.T-Concat
          (`sprgt (`sprgt (`splft (allunr _ Unr-⟪⟫))))
          (TRG.T-Id `Z Unr-⟪⟫)
          (TRG.T-Concat (`sprgt (`splft (allunr _ Unr-⟪⟫)))
            (TRG.T-Single (TRG.T-Id `Z Unr-⟪⟫))
            (TRG.T-Single (TRG.T-Id `Z Unr-⟪⟫))))))

ty-preserveE (C-SendD ⊢v ⊢v′ sp) = 
  TRG.T-Split
    (`splft (allunr _ Unr-⟪⟫))
    (TRG.T-SplitRecord (TRG.T-Id `Z Unr-⟪⟫) (store-reordering sp))
    (TRG.T-Let
      (`sprgt (`splft (allunr _ Unr-⟪⟫)))
      (TRG.T-App
        (`sprgt (allunr _ Unr-⟪⟫))
        (TRG.T-App (allunr _ Unr-⟪⟫) (TRG.T-Const Unr-⟪⟫ TRG.T-Send) (ty-preserveV ⊢v))
        (TRG.T-Id `Z Unr-⟪⟫))
      (TRG.T-Pair
        (`sprgt (`sprgt (allunr _ Unr-⟪⟫))) (TRG.T-Unit Unr-⟪⟫)
        (TRG.T-Concat
          (`sprgt (`splft (allunr _ Unr-⟪⟫)))
          (TRG.T-Id `Z Unr-⟪⟫)
          (TRG.T-Single (TRG.T-Id `Z Unr-⟪⟫)))))

ty-preserveE (C-SendDS ⊢v ⊢v′ sp sp′) =
  TRG.T-Split
    (`splft (allunr _ Unr-⟪⟫))
    (TRG.T-SplitRecord (TRG.T-Id `Z Unr-⟪⟫) (store-reordering sp))
    (TRG.T-Split
      (`splft (`sprgt (allunr _ Unr-⟪⟫)))
      (TRG.T-SplitRecord (TRG.T-Id `Z Unr-⟪⟫) (store-reordering sp′))
      (TRG.T-Let
        (`sprgt (`splft (`splft (allunr _ Unr-⟪⟫)))) 
        (TRG.T-App
          (`splft (`sprgt (allunr _ Unr-⟪⟫)))
          (TRG.T-App
            (`sprgt (allunr _ Unr-⟪⟫))
            (TRG.T-Const Unr-⟪⟫ TRG.T-Send)
            (TRG.T-Id `Z Unr-⟪⟫))
          (TRG.T-Id `Z Unr-⟪⟫))
        (TRG.T-Pair
          (`sprgt (`sprgt (allunr _ Unr-⟪⟫)))
          (TRG.T-Unit Unr-⟪⟫)
          (TRG.T-Concat
            (`sprgt (`splft (allunr _ Unr-⟪⟫)))
            (TRG.T-Id `Z Unr-⟪⟫)
            (TRG.T-Single (TRG.T-Id `Z Unr-⟪⟫))))))

ty-preserveE (C-Close ⊢v sp) =
  TRG.T-Split
    (`splft (allunr _ Unr-⟪⟫))
    (TRG.T-SplitRecord (TRG.T-Id `Z Unr-⟪⟫) (store-reordering sp))
    (TRG.T-Pair
      (`sprgt (`sprgt (allunr _ Unr-⟪⟫)))
      (TRG.T-Unit Unr-⟪⟫)
      (TRG.T-Id `Z (`unrvar Unr-⟪⟫ `unrend)))
ty-preserveE (C-Accept ⊢v) =
  TRG.T-Let (`sprgt (allunr _ Unr-⟪⟫)) 
    (TRG.T-App (allunr _ Unr-⟪⟫) (TRG.T-Const Unr-⟪⟫ TRG.T-Accept) (ty-preserveV ⊢v))
    (TRG.T-Pair
      (`sprgt (`sprgt (allunr _ Unr-⟪⟫)))
      (TRG.T-Unit Unr-⟪⟫)
      (TRG.T-Concat
        (`sprgt (`splft (allunr _ Unr-⟪⟫)))
        (TRG.T-Id `Z Unr-⟪⟫)
        (TRG.T-Single (TRG.T-Id `Z Unr-⟪⟫))))
ty-preserveE (C-Request {S = S} ⊢v) =
  TRG.T-Let
    (`sprgt (allunr _ Unr-⟪⟫))
    (TRG.T-App (allunr _ Unr-⟪⟫) (TRG.T-Const Unr-⟪⟫ TRG.T-Request) (ty-preserveV ⊢v))
    (TRG.T-Pair
      (`sprgt (`sprgt (allunr _ Unr-⟪⟫)))
      (TRG.T-Unit Unr-⟪⟫)
      (TRG.T-Concat
        (`sprgt (`splft (allunr _ Unr-⟪⟫)))
        (TRG.T-Id `Z Unr-⟪⟫)
        (TRG.T-Single (TRG.T-Id getrv Unr-⟪⟫))))
  where
    getrv : (⟪ Γ ⟫ , rv-name ⦂ `session (dual ⟪ S ⟫ˢ)) ≡[ ⟪ Γ ⟫ , rv-name ⦂ `session ⟪ SRC.dualSession S ⟫ˢ ]
    getrv rewrite session-dual S = `Z
ty-preserveE (C-Val ⊢v) =
  TRG.T-Pair (`sprgt (allunr _ Unr-⟪⟫)) (ty-preserveV ⊢v) (TRG.T-Id `Z Unr-⟪⟫)
ty-preserveE (C-App {σ₁ = σ₁} {σ = σ₂} {σ₁#σ = σ₁#σ₂} ⊢v ⊢v′) =
  TRG.T-Split
    (`splft (allunr _ Unr-⟪⟫))
    (TRG.T-SplitRecordMany (TRG.T-Id `Z Unr-⟪⟫) (store-splitting σ₁ σ₂ σ₁#σ₂))
    (TRG.T-Split
      (`sprgt (`splft (allunr _ Unr-⟪⟫)))
      (TRG.T-App
        (`sprgt (allunr _ Unr-⟪⟫))
        (TRG.T-App (allunr _ Unr-⟪⟫) (ty-preserveV ⊢v) (ty-preserveV ⊢v′))
        (TRG.T-Id `Z Unr-⟪⟫))
      (TRG.T-Pair
        (`sprgt (`splft (`sprgt (allunr _ Unr-⟪⟫))))
        (TRG.T-Id `Z Unr-⟪⟫)
        (TRG.T-Concat
          (`sprgt (`splft (allunr _ Unr-⟪⟫)))
          (TRG.T-Id `Z Unr-⟪⟫)
          (TRG.T-Id `Z Unr-⟪⟫))))
ty-preserveE C-New = 
  TRG.T-Pair (`sprgt (allunr _ Unr-⟪⟫)) (TRG.T-Const Unr-⟪⟫ TRG.T-New) (TRG.T-Id `Z Unr-⟪⟫)

ty-preserveE {T = T} (C-Let {Γ = Γ} {σ₁ = σ₁} {T₁ = T₁} {σ₁′ = σ₁′} {x = x} {σ₁#σ₁′ = σ₁#σ₁′}
                            {σ₂ = σ₂} {σ₂′ = σ₂′} {σ₁′∩σ₂#σ₂′ = σ₁′∩σ₂#σ₂′} ⊢e ⊢e₁ σσ≡@refl σ⊆⊇σ)
  rewrite ⊆⊇-≡ σ⊆⊇σ
   with ty-let-rewrite2
          {Γ = ⟪ Γ ⟫ , x ⦂ ⟪ T₁ ⟫ⱽ }
          {e = ⟦ ⊢e₁ ⟧ᵉ}
          {T = `pair ⟪ T ⟫ⱽ (`record (⟪ σ₂ ⟫ᴿ ++ ⟪ σ₂′ ⟫ᴿ))}
          σ₁ σ₁′ σ₁#σ₁′ (ty-preserveE ⊢e₁)
... | tpe1
   with ⊢e⇒σ₁⊆σ ⊢e₁
... |  σ₁⊆σ
   rewrite lemma-let-rewrite-full σ₁ σ₂ σ₁′ σ₂′ σ₁#σ₁′ σ₁′∩σ₂#σ₂′ σ₁⊆σ
  = 
    TRG.T-Split (`splft (allunr _ Unr-⟪⟫)) (ty-preserveE ⊢e) tpe1

ty-preserveE (C-LetV ⊢v ⊢e) =
  TRG.T-Let
    (`sprgt (allunr _ Unr-⟪⟫))
    (ty-preserveV ⊢v)
    (post-swap-expr post-st-unused (ty-preserveE ⊢e))

ty-preserveE (C-Fork {σ₁ = σ₁} {T₁ = T₁} {σ₂ = σ₂} {σ = σ} {σ₁#σ₂ = σ₁#σ₂} ⊢e ⊢e₁) =
  TRG.T-Split
    (`splft (allunr _ Unr-⟪⟫))
    (TRG.T-SplitRecordMany (TRG.T-Id `Z Unr-⟪⟫) (store-splitting σ₁ σ₂ σ₁#σ₂))
    (TRG.T-UnitElim
      (`sprgt (`splft (allunr _ Unr-⟪⟫)))
      (TRG.T-App (`sprgt (allunr _ Unr-⟪⟫))
        (TRG.T-Const Unr-⟪⟫ (TRG.T-Fork {T = `pair ⟪ T₁ ⟫ⱽ (`record `emp)} (`unrpair (Unr-⟪⟫ⱽ {T = T₁}) `unremp)))
        (ty-preserveE ⊢e))
      (TRG.T-Let
        (`splft (allunr _ Unr-⟪⟫))
        (TRG.T-Id `Z Unr-⟪⟫)
        (ty-preserveE ⊢e₁)))


