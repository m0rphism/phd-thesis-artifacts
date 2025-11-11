open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Algorithmic.TypingSound {M : OPM} (DM : DecidableOPM M) where

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

open import LawAndOrder.Algorithmic.Expression DM
open import LawAndOrder.Algorithmic.Typing DM
open import LawAndOrder.Context DM
open import LawAndOrder.Context.SyntacticSplit DM
open import LawAndOrder.Effect
open import LawAndOrder.Id
open import LawAndOrder.Logical.Expression DM
open import LawAndOrder.Logical.Typing DM
open import LawAndOrder.Multiplicities
open import LawAndOrder.Type DM
open import LawAndOrder.Util.Decidable
open import LawAndOrder.Util.Graph as G using (Graph)
open import LawAndOrder.Util.List

mutual
  soundness↓ :
    Γ ⊢ eᶜ ↓ t [ ϕ ]⇒ e →
    Γ ⊢ e ∶ t [ ϕ ]
  soundness↓ (⊢λ x∉Γ unr ϕ₁⊑ϕ₂ ⊢e)                       = ⊢λ x∉Γ unr (⊢wk ≲-refl ϕ₁⊑ϕ₂ (soundness↓ ⊢e))
  soundness↓ (⊢↑ ⊢e)                                     = soundness↑ ⊢e

  soundness↑ :
    Γ ⊢ eⁱ ↑ t [ ϕ ]⇒ e →
    Γ ⊢ e ∶ t [ ϕ ]
  soundness↑ (⊢unit Γ≲·)                                 = ⊢wk Γ≲· ϕ⊑ϕ (⊢const ⊢unit)
  soundness↑ (⊢new Γ≲·)                                  = ⊢wk Γ≲· ϕ⊑ϕ (⊢const ⊢new)
  soundness↑ (⊢send p x ⊢E)                              = ⊢wk (≈→≲ ≈-·ˡ) ϕ⊑ϕ (⊢· (λ ()) (λ ()) (⊢const (⊢send p)) (soundness↑ ⊢E))
  soundness↑ (⊢split p x ⊢E)                             = ⊢wk (≈→≲ ≈-·ˡ) ϕ⊑ϕ (⊢· (λ ()) (λ ()) (⊢const (⊢split p)) (soundness↑ ⊢E))
  soundness↑ (⊢drop x ⊢E)                                = ⊢wk (≈→≲ ≈-·ˡ) ϕ⊑ϕ (⊢· (λ ()) (λ ()) (⊢const (⊢drop x)) (soundness↑ ⊢E))
  soundness↑ (⊢var Γ≲x∶t _)                              = ⊢wk Γ≲x∶t ϕ⊑ϕ ⊢var
  soundness↑ (⊢· eq-Γ₁ eq-Γ₂ Γ≲Γ₁⸴Γ ϕ₁≡?𝟎 ϕ₂≡?𝟎 ⊢E₁ ⊢E₂) = ⊢wk Γ≲Γ₁⸴Γ ϕ⊑ϕ (⊢· ϕ₁≡?𝟎 ϕ₂≡?𝟎 (soundness↑ ⊢E₁) (soundness↑ ⊢E₂))
  soundness↑ (⊢, eq-Γ₁ eq-Γ₂ Γ≲Γ₁⸴Γ eq ⊢E₁ ⊢E₂)          = ⊢wk Γ≲Γ₁⸴Γ ϕ⊑ϕ (⊢, (⊎.map (λ x → x) (λ (x , y , z) → x , y) eq)
                                                                              (soundness↑ ⊢E₁) (soundness↑ ⊢E₂))
  soundness↑ {Γ = Γ} (⊢let {eⁱ₁ = eⁱ₁} x∉Γ y∉Γ y≢x Γ↓≡some ⊢E₁ ⊢E₂)
                                                         = let Γ≲𝒢[Γ'] = ↓ᶜ-sound Γ (fvs↑ eⁱ₁) Γ↓≡some in
                                                           ⊢wk Γ≲𝒢[Γ'] ϕ⊑ϕ (⊢let (≲-pres-∉ Γ≲𝒢[Γ'] x∉Γ) (≲-pres-∉ Γ≲𝒢[Γ'] y∉Γ)
                                                                                 y≢x (soundness↑ ⊢E₁) (soundness↑ ⊢E₂))
  soundness↑ (⊢∶ ⊢E)                                     = soundness↓ ⊢E
