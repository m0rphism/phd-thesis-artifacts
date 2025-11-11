open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Logical.Typing {M : OPM} (DM : DecidableOPM M) where

private module M = DecidableOPM DM

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
open import Function using (_$_; case_of_)

open import LawAndOrder.Util.Decidable
open import LawAndOrder.Multiplicities
open import LawAndOrder.Effect
open import LawAndOrder.Type DM
open import LawAndOrder.Util.List
open import LawAndOrder.Id
open import LawAndOrder.Util.Graph as G using (Graph)
open import LawAndOrder.Logical.Expression DM
open import LawAndOrder.Context DM

infix  3 _∶ᶜ_
data _∶ᶜ_ : Const → Type → Set where
  ⊢unit :
    unit ∶ᶜ Unit
  ⊢new :
    new r ∶ᶜ # r
  ⊢send :
    r₁ M.* r₂ M.≤' r →
    send r₁ ∶ᶜ (# r –[ ∞ ⍮ 𝟏 ]→ # r₂)
  ⊢split :
    r₁ M.* r₂ M.≤' r →
    split r₁ r₂ ∶ᶜ (# r –[ ∞ ⍮ 𝟎 ]→ (# r₁ ×[ 𝟙 ] # r₂))
  ⊢drop :
    M.ϵ M.≤ r →
    drop ∶ᶜ (# r –[ ∞ ⍮ 𝟎 ]→ Unit)

infix  3 _⊢_∶_[_]
data _⊢_∶_[_] : Ctx → Expr → Type → Effect → Set₁ where
  ⊢const :
    c ∶ᶜ t →
    · ⊢ const c ∶ t [ 𝟎 ]
  ⊢var :
    (x ∶ t) ⊢ ` x ∶ t [ 𝟎 ]
  ⊢λ :
    ¬ (x ∈ dom Γ) →
    (m ≡ ∞ → Unrᶜ Γ) →
    ext m Γ (x ∶ t₁) ⊢ e ∶ t₂ [ ϕ ] →
    Γ ⊢ (λ[ m ] x ⇒ e) ∶ (t₁ –[ m ⍮ ϕ ]→ t₂) [ 𝟎 ]
  ⊢· :
    (m ≡ ≺ → ϕ₂ ≡ 𝟎) →
    (m ≡ ≻ → ϕ₁ ≡ 𝟎) →
    Γ₁ ⊢ e₁ ∶ (t₁ –[ m ⍮ ϕ ]→ t₂) [ ϕ₁ ] →
    Γ₂ ⊢ e₂ ∶ t₁ [ ϕ₂ ] →
    ext m Γ₁ Γ₂ ⊢ (e₁ ·[ m ] e₂) ∶ t₂ [ ϕ ⊔ ϕ₁ ⊔ ϕ₂ ]
  ⊢, :
    (m ≡ 𝟙 ⊎ m ≡ ≻ × (Ord t₁ → ϕ₂ ≡ 𝟎)) →
    Γ₁ ⊢ e₁ ∶ t₁ [ ϕ₁ ] →
    Γ₂ ⊢ e₂ ∶ t₂ [ ϕ₂ ] →
    ext m Γ₁ Γ₂ ⊢ (e₁ ,[ m ] e₂) ∶ (t₁ ×[ m ] t₂) [ ϕ₁ ⊔ ϕ₂ ]
  ⊢let :
    x ∉ dom (C [ Γ ]) →
    y ∉ dom (C [ Γ ]) →
    y ≢ x →
    Γ ⊢ e₁ ∶ (t₁₁ ×[ m ] t₁₂) [ 𝟎 ] →
    C [ ext m (x ∶ t₁₁) (y ∶ t₁₂) ] ⊢ e₂ ∶ t₂ [ ϕ₂ ] →
    C [ Γ ] ⊢ (let[ x ,[ m ] y ≡ e₁ ]in e₂) ∶ t₂ [ ϕ₂ ]
  ⊢wk :
    Γ₂ ≲ Γ₁ →
    ϕ₁ ⊑ ϕ₂ →
    Γ₁ ⊢ e ∶ t [ ϕ₁ ] →
    Γ₂ ⊢ e ∶ t [ ϕ₂ ]
