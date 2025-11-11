open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Algorithmic.Typing {M : OPM} (DM : DecidableOPM M) where

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
open import LawAndOrder.Algorithmic.Expression DM
open import LawAndOrder.Context DM
open import LawAndOrder.Context.SyntacticSplit DM

mutual
  infix 3 _⊢_↑_[_]⇒_ _⊢_↓_[_]⇒_

  data _⊢_↓_[_]⇒_ : Ctx → Expr↓ → Type → Effect → Expr → Set₁ where
    ⊢λ :
      x ∉ dom Γ →
      (m ≡ ∞ → Unrᶜ Γ) →
      ϕ₁ ⊑ ϕ₂ →
      ext m Γ (x ∶ t₁) ⊢ eᶜ ↓ t₂ [ ϕ₁ ]⇒ e →
      Γ ⊢ (`λ x ⇒ eᶜ) ↓ (t₁ –[ m ⍮ ϕ₂ ]→ t₂) [ 𝟎 ]⇒ (λ[ m ] x ⇒ e)
    ⊢↑ :
      Γ ⊢ eⁱ ↑ t [ ϕ ]⇒ e →
      Γ ⊢ (↑ eⁱ) ↓ t [ ϕ ]⇒ e

  data _⊢_↑_[_]⇒_ : Ctx → Expr↑ → Type → Effect → Expr → Set₁ where
    ⊢unit :
      Γ ≲ · →
      Γ ⊢ unit ↑ Unit [ 𝟎 ]⇒ (const unit)
    ⊢new :
      Γ ≲ · →
      Γ ⊢ new r ↑ (# r) [ 𝟎 ]⇒ (const (new r))
    ⊢send :
      (p : r₁ M.* r₂ M.≤' r) →
      r₁ M.∃≤? r ≡ yes (r₂ , p) →
      Γ ⊢ eⁱ ↑ (# r) [ ϕ ]⇒ e →
      Γ ⊢ send r₁ eⁱ ↑ (# r₂) [ 𝟏 ]⇒ (const (send r₁) ·[ ∞ ] e)
    ⊢split :
      (p : r₁ M.* r₂ M.≤' r) →
      r₁ M.∃≤? r ≡ yes (r₂ , p) →
      Γ ⊢ eⁱ ↑ (# r) [ ϕ ]⇒ e →
      Γ ⊢ split r₁ eⁱ ↑ (# r₁ ×[ 𝟙 ] # r₂) [ ϕ ]⇒ (const (split r₁ r₂) ·[ ∞ ] e)
    ⊢drop :
      M.ϵ M.≤ r →
      Γ ⊢ eⁱ ↑ (# r) [ ϕ ]⇒ e →
      Γ ⊢ drop eⁱ ↑ Unit [ ϕ ]⇒ (const drop ·[ ∞ ] e)
    ⊢var :
      (p : Γ ≲ x ∶ t) →
      Γ ∃≲? x ≡ yes (t , p) →
      Γ ⊢ (` x) ↑ t [ 𝟎 ]⇒ (` x)
    ⊢· :
      Γ₁ ≡ Γ ↓ fvs↑ eⁱ₁ →
      Γ₂ ≡ Γ ↓ fvs↑ eⁱ₂ →
      Γ ≲ ext m Γ₁ Γ₂ →
      (m ≡ ≺ → ϕ₂ ≡ 𝟎) →
      (m ≡ ≻ → ϕ₁ ≡ 𝟎) →
      Γ₁ ⊢ eⁱ₁ ↑ (t₁ –[ m ⍮ ϕ ]→ t₂) [ ϕ₁ ]⇒ e₁ →
      Γ₂ ⊢ eⁱ₂ ↑ t₁ [ ϕ₂ ]⇒ e₂ →
      Γ ⊢ (eⁱ₁ `· eⁱ₂) ↑ t₂ [ ϕ ⊔ ϕ₁ ⊔ ϕ₂ ]⇒ (e₁ ·[ m ] e₂)
    ⊢, :
      Γ₁ ≡ Γ ↓ fvs↑ eⁱ₁ →
      Γ₂ ≡ Γ ↓ fvs↑ eⁱ₂ →
      Γ ≲ ext m Γ₁ Γ₂ →
      (m ≡ 𝟙 ⊎ m ≡ ≻ × ((Ord t₁ → ϕ₂ ≡ 𝟎) × ¬ (Γ ≲ ext 𝟙 Γ₁ Γ₂))) →
      Γ₁ ⊢ eⁱ₁ ↑ t₁ [ ϕ₁ ]⇒ e₁ →
      Γ₂ ⊢ eⁱ₂ ↑ t₂ [ ϕ₂ ]⇒ e₂ →
      Γ ⊢ (eⁱ₁ , eⁱ₂) ↑ (t₁ ×[ m ] t₂) [ ϕ₁ ⊔ ϕ₂ ]⇒ (e₁ ,[ m ] e₂)
    ⊢let :
      x ∉ dom Γ →
      y ∉ dom Γ →
      y ≢ x →
      Γ ↓ᶜ fvs↑ eⁱ₁ ≡ some (C , Γ₁) →
      Γ₁ ⊢ eⁱ₁ ↑ (t₁₁ ×[ m ] t₁₂) [ 𝟎 ]⇒ e₁ →
      C [ ext m (x ∶ t₁₁) (y ∶ t₁₂) ] ⊢ eⁱ₂ ↑ t₂ [ ϕ₂ ]⇒ e₂ →
      Γ ⊢ (let[ x , y ≡ eⁱ₁ ]in eⁱ₂) ↑ t₂ [ ϕ₂ ]⇒ (let[ x ,[ m ] y ≡ e₁ ]in e₂)
    ⊢∶ :
      Γ ⊢ eᶜ ↓ t [ ϕ ]⇒ e →
      Γ ⊢ (eᶜ ∶ t) ↑ t [ ϕ ]⇒ e

