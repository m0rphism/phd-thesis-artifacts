module BGV.Logical where

open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; module ≡-Reasoning)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)

open import BGV.Id
open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Types
open import BGV.Expressions
open import BGV.Context
open import BGV.Context.SyntacticSplit using (LeftCtx)
open import BGV.Util.Map as Map using (Map)
open import BGV.Util.Decidable

data EffRestr : Mult → Effect → Effect → Set where
  er-≺ : ϕ₁ ≡ 𝟎 → EffRestr ≺ ϕ₁ ϕ₂
  er-≻ : ϕ₂ ≡ 𝟎 → EffRestr ≻ ϕ₁ ϕ₂
  er-𝟙 : EffRestr 𝟙 ϕ₁ ϕ₂
  er-∞ : EffRestr ∞ ϕ₁ ϕ₂

data _⊢_∶_⍮_ : Ctx → Expr log → Type → Effect → Set₁ where
  ⊢` :
    Γ ≲ (x ∶ t) →
    Γ ⊢ (` x) ∶ t ⍮ 𝟎
  ⊢λ :
    x ∉ dom Γ →
    ext m Γ (x ∶ t₁) ⊢ e ∶ t₂ ⍮ ϕ →
    (m ≡ ∞ → Unrᶜ Γ) →
    Γ ⊢ (λ[ m ] x ⇒ e) ∶ (t₁ –[ m ⍮ ϕ ]→ t₂) ⍮ 𝟎
  ⊢· :
    Γ ≡ ext m Γ₁ Γ₂ →
    EffRestr m ϕ₁ ϕ₂ →
    Γ₁ ⊢ e₁ ∶ (t₁ –[ m ⍮ ϕ ]→ t₂) ⍮ ϕ₁ →
    Γ₂ ⊢ e₂ ∶ t₁ ⍮ ϕ₂ →
    Γ ⊢ (e₁ `· e₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ)
  ⊢let :
    Γ ≡ C [ Γ₁ ] →
    x ∉ dom Γ →
    Γ₁ ⊢ e₁ ∶ t₁ ⍮ ϕ₁ →
    (¬ LeftCtx C → ϕ₁ ≡ 𝟎) →
    (C [ x ∶ t₁ ]) ⊢ e₂ ∶ t₂ ⍮ ϕ₂ →
    Γ ⊢ (let[ x ≔ e₁ ]in e₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂)
  ⊢, :
    Γ ≡ Γ₁ ⸴[ pmult→ord p ] Γ₂ →
    Γ₁ ⊢ e₁ ∶ t₁ ⍮ ϕ₁ →
    Γ₂ ⊢ e₂ ∶ t₂ ⍮ ϕ₂ →
    (¬ Unr t₁ → p ≡ ≻ → ϕ₂ ≡ 𝟎) →
    Γ ⊢ (e₁ ,[ p ] e₂) ∶ (t₁ ×[ p ] t₂) ⍮ (ϕ₁ ⊔ ϕ₂)
  ⊢let× :
    Γ ≡ C [ Γ₁ ] →
    x ∉ dom Γ →
    y ∉ dom Γ →
    x ≢ y →
    Γ₁ ⊢ e₁ ∶ (t₁ ×[ p ] t₂) ⍮ ϕ₁ →
    (¬ LeftCtx C → ϕ₁ ≡ 𝟎) →
    (C [ x ∶ t₁ ⸴[ pmult→ord p ] y ∶ t₂ ]) ⊢ e₂ ∶ t ⍮ ϕ₂ →
    Γ ⊢ (let[ x `, y ≔ e₁ ]in e₂) ∶ t  ⍮ (ϕ₁ ⊔ ϕ₂)
  ⊢inj : ∀ {l} →
    Γ ⊢ e ∶ selectₗ l t₁ t₂  ⍮ ϕ →
    Γ ⊢ `inj l e ∶ (t₁ + t₂) ⍮ ϕ
  ⊢case :
    Γ ≡ C [ Γ₁ ] →
    x₁ ∉ dom Γ →
    x₂ ∉ dom Γ →
    x₁ ≢ x₂ →
    Γ₁ ⊢ e₁ ∶ (t₁ + t₂) ⍮ ϕ₁ →
    (¬ LeftCtx C → ϕ₁ ≡ 𝟎) →
    (C [ x₁ ∶ t₁ ]) ⊢ e₂₁ ∶ t ⍮ ϕ₂ →
    (C [ x₂ ∶ t₂ ]) ⊢ e₂₂ ∶ t ⍮ ϕ₃ →
    Γ ⊢ case e₁ of[ x₁ ⇒ e₂₁ ⍮ x₂ ⇒ e₂₂ ] ∶ t ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ₃)
  ⊢wk :
    Γ₂ ≲ Γ₁ →
    ϕ₁ ⊑ ϕ₂ →
    Γ₁ ⊢ e ∶ t ⍮ ϕ₁ →
    Γ₂ ⊢ e ∶ t ⍮ ϕ₂
  ⊢unit :
    Γ ≲ · →
    Γ ⊢ unit ∶ Unit ⍮ 𝟎
  ⊢spawn :
    Γ ⊢ e ∶ Unit ⍮ ϕ →
    Γ ⊢ spawn e ∶ Unit ⍮ 𝟎
  ⊢new :
    Γ ≲ · →
    Γ ⊢ new s ∶ (Chan owned s ×[ 𝟙 ] Chan owned (dual s)) ⍮ 𝟎
  ⊢send :
    Γ ≡ Γ₁ ∥ Γ₂ →
    Γ₁ ⊢ e₁ ∶ t₁ ⍮ ϕ₁ →
    Γ₂ ⊢ e₂ ∶ Chan _ (op[ ‼ ] t₁ ⍮ return) ⍮ ϕ₂ →
    Γ ⊢ send e₁ e₂ ∶ Unit ⍮ 𝟏
  ⊢recv :
    Γ ⊢ e ∶ Chan _ (op[ ⁈ ] t ⍮ return) ⍮ ϕ →
    Γ ⊢ recv e ∶ t ⍮ 𝟏
  ⊢select : ∀ {l} →
    Γ ⊢ e ∶ Chan _ (choice[ ‼ ] s₁ ⍮ s₂) ⍮ ϕ →
    Γ ⊢ select l e ∶ Chan _ (selectₗ l s₁ s₂) ⍮ 𝟏
  ⊢branch :
    Γ ⊢ e ∶ Chan _ (choice[ ⁈ ] s₁ ⍮ s₂) ⍮ ϕ →
    Γ ⊢ branch e ∶ (Chan _ s₁ + Chan _ s₂) ⍮ 𝟏
  ⊢drop :
    Γ ⊢ e ∶ Chan _ return ⍮ ϕ →
    Γ ⊢ drop e ∶ Unit ⍮ 𝟏
  ⊢close : ∀ {o} →
    Γ ⊢ e ∶ Chan _ (end o) ⍮ ϕ →
    Γ ⊢ close o e ∶ Unit ⍮ 𝟏
  ⊢split :
    s ≡ s₁ ++ˢ s₂ →
    Γ ⊢ e ∶ (Chan _ s) ⍮ ϕ →
    Γ ⊢ (split[ s₁ ] e) ∶ (Chan _ s₁ ×[ ≻ ] Chan _ s₂) ⍮ ϕ
