open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Algorithmic.TypingDecidable {M : OPM} (DM : DecidableOPM M) where

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
open import LawAndOrder.Algorithmic.Typing DM
open import LawAndOrder.Context DM
open import LawAndOrder.Context.SyntacticSplit DM

mutual
  ⊢↑-det :
    Γ ⊢ eⁱ ↑ t₁ [ ϕ₁ ]⇒ e₁ →
    Γ ⊢ eⁱ ↑ t₂ [ ϕ₂ ]⇒ e₂ →
    t₁ ≡ t₂ × ϕ₁ ≡ ϕ₂ × e₁ ≡ e₂
  ⊢↑-det (⊢unit x)(⊢unit x₁) = refl , refl , refl
  ⊢↑-det (⊢new x) (⊢new x₁) = refl , refl , refl
  ⊢↑-det (⊢send p x ⊢e) (⊢send p₁ x₁ ⊢e')
   with ⊢↑-det ⊢e ⊢e' 
  …   | refl , refl , refl
   with trans (sym x) x₁
  …   | refl = refl , refl , refl
  ⊢↑-det (⊢split p x ⊢e) (⊢split p₁ x₁ ⊢e')
   with ⊢↑-det ⊢e ⊢e' 
  …   | refl , refl , refl
   with trans (sym x) x₁
  …   | refl = refl , refl , refl
  ⊢↑-det (⊢drop x ⊢e) (⊢drop x₁ ⊢e')
   with ⊢↑-det ⊢e ⊢e' 
  …   | refl , refl , refl = refl , refl , refl
  ⊢↑-det (⊢var Γ≲x∶t eq) (⊢var Γ≲x∶t' eq')
   with trans (sym eq) eq'
  … | refl
   = refl , refl , refl
    -- Solvable with Wf Γ, but maybe also without
  ⊢↑-det (⊢· refl refl x₂ x₃ x₄ ⊢e₁ ⊢e₂) (⊢· refl refl x₇ x₈ x₉ ⊢e₁' ⊢e₂')
   with ⊢↑-det ⊢e₁ ⊢e₁' | ⊢↑-det ⊢e₂ ⊢e₂'
  …   | refl , refl , refl | refl , refl , refl = refl , refl , refl
  ⊢↑-det (⊢, refl refl x₂ x₃ ⊢e₁ ⊢e₂) (⊢, refl refl x₆ x₇ ⊢e₁' ⊢e₂')
   with ⊢↑-det ⊢e₁ ⊢e₁' | ⊢↑-det ⊢e₂ ⊢e₂'
  …   | refl , refl , refl | refl , refl , refl
   with x₃ | x₇
  ... | inj₁ refl | inj₁ refl = refl , refl , refl
  ... | inj₂ (refl , _) | inj₂ (refl , _) = refl , refl , refl
  ... | inj₁ refl | inj₂ (refl , _ , yy) = ⊥-elim (yy x₂) 
  ... | inj₂ (refl , _ , xx) | inj₁ refl = ⊥-elim (xx x₆)
  ⊢↑-det (⊢let x x₁ x₂ eq ⊢e₁ ⊢e₂)  (⊢let x₄ x₅ x₆ eq' ⊢e₁' ⊢e₂')
   with trans (sym eq) eq'
  … | refl
   with ⊢↑-det ⊢e₁ ⊢e₁'
  …   | refl , refl , refl
   with ⊢↑-det ⊢e₂ ⊢e₂'
  …   | refl , refl , refl
   = refl , refl , refl
  ⊢↑-det (⊢∶ ⊢e) (⊢∶ ⊢e')
   with ⊢↓-det ⊢e ⊢e'
  …   | refl , refl
   = refl , refl , refl
  
  ⊢↓-det :
    Γ ⊢ eᶜ ↓ t [ ϕ₁ ]⇒ e₁ →
    Γ ⊢ eᶜ ↓ t [ ϕ₂ ]⇒ e₂ →
    ϕ₁ ≡ ϕ₂ × e₁ ≡ e₂
  ⊢↓-det (⊢λ x x₁ x₂ ⊢e) (⊢λ x₃ x₄ x₅ ⊢e')
   with ⊢↓-det ⊢e ⊢e'
  … | refl , refl
   = refl , refl
  ⊢↓-det (⊢↑ ⊢e) (⊢↑ ⊢e')
   with ⊢↑-det ⊢e ⊢e'
  …   | refl , refl , refl
   = refl , refl

mutual
  check : ∀ Γ eᶜ t → Dec (∃[ ϕ ] ∃[ e ] Γ ⊢ eᶜ ↓ t [ ϕ ]⇒ e)
  check Γ (`λ x ⇒ eᶜ) (t₁ –[ m ⍮ ϕ ]→ t₂)
    with check (ext m Γ (x ∶ t₁)) eᶜ t₂
  … | no ¬p = no (λ { (_ , _ , ⊢λ _ _ _ p) → ¬p (_ , _ , p) })
  … | yes (ϕ' , e , ⊢eᶜ)
    with x ∈? dom Γ | m ≟ ∞ | Unrᶜ? Γ | ϕ' ⊑? ϕ
  … | no x∉Γ  | yes m≡∞ | yes unr-Γ | yes ϕ'⊑ϕ = yes (_ , _ , ⊢λ x∉Γ (λ m≡∞' → unr-Γ) ϕ'⊑ϕ ⊢eᶜ)
  … | no x∉Γ  | no ¬m≡∞ | _         | yes ϕ'⊑ϕ = yes (_ , _ , ⊢λ x∉Γ (λ m≡∞ → ⊥-elim (¬m≡∞ m≡∞)) ϕ'⊑ϕ ⊢eᶜ)
  … | _       | _       | _         | no ¬ϕ'⊑ϕ = no λ where (_ , _ , ⊢λ _ _ ϕ'⊑ϕ ⊢eᶜ') → case proj₁ (⊢↓-det ⊢eᶜ' ⊢eᶜ) of
                                                                                            λ where refl → ¬ϕ'⊑ϕ ϕ'⊑ϕ
  … | _       | yes m≡∞ | no ¬unr-Γ | _        = no λ where (_ , _ , ⊢λ _ unr-Γ _ _) → ¬unr-Γ (unr-Γ m≡∞)
  … | yes x∈Γ | _       | _         | _        = no λ where (_ , _ , ⊢λ x∉Γ _ _ _) → x∉Γ x∈Γ
  check Γ (`λ x ⇒ eᶜ) Unit = no (λ ())
  check Γ (`λ x ⇒ eᶜ) (# r) = no (λ ())
  check Γ (`λ x ⇒ eᶜ) (t₁ ×[ m ] t₂) = no (λ ())
  check Γ (↑ eⁱ) t with infer Γ eⁱ
  … | no ¬p = no λ where (ϕ , e , ⊢↑ ⊢eⁱ) → ¬p (t , ϕ , e , ⊢eⁱ)
  … | yes (t' , ϕ , e , ⊢eⁱ) with t ≟ t'
  …   | yes refl = yes (ϕ , e , ⊢↑ ⊢eⁱ)
  …   | no ¬t≡t' = no (λ { (_ , _ , ⊢↑ ⊢eⁱ') → ¬t≡t' (proj₁ (⊢↑-det ⊢eⁱ' ⊢eⁱ)) })

  infer : ∀ Γ eⁱ → Dec (∃[ t ] ∃[ ϕ ] ∃[ e ] Γ ⊢ eⁱ ↑ t [ ϕ ]⇒ e)
  infer Γ unit with Γ ≲? ·
  … | yes Γ≲· = yes (_ , _ , _ , ⊢unit Γ≲·)
  … | no ¬Γ≲· = no λ where (_ , _ , _ , ⊢unit Γ≲·) → ¬Γ≲· Γ≲·
  infer Γ (new x) with Γ ≲? ·
  … | yes Γ≲· = yes (_ , _ , _ , ⊢new Γ≲·)
  … | no ¬Γ≲· = no λ where (_ , _ , _ , ⊢new Γ≲·) → ¬Γ≲· Γ≲·
  infer Γ (send r₁ eⁱ) with infer Γ eⁱ
  … | no ¬pp                                 = no λ where (_ , _ , _ , ⊢send x _ ⊢eⁱ') → ¬pp (_ , _ , _ , ⊢eⁱ')
  … | yes (Unit , ϕ , e , ⊢eⁱ)               = no λ where (_ , _ , _ , ⊢send x _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (t –[ x₁ ⍮ x₂ ]→ t₁ , ϕ , e , ⊢eⁱ) = no λ where (_ , _ , _ , ⊢send x _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (t ×[ x₁ ] t₁ , ϕ , e , ⊢eⁱ)       = no λ where (_ , _ , _ , ⊢send x _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (# r , ϕ , e , ⊢eⁱ) with r₁ M.∃≤? r in eq∃
  …   | no ¬pp                               = no λ where (_ , _ , _ , ⊢send pp _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of
                                                                                          λ where refl → ¬pp (_ , pp)
  …   | yes (r₂ , pp)                        = yes (_ , _ , _ , ⊢send pp eq∃ ⊢eⁱ)
  infer Γ (split r₁ eⁱ) with infer Γ eⁱ
  … | no ¬pp                                 = no λ where (_ , _ , _ , ⊢split x _ ⊢eⁱ') → ¬pp (_ , _ , _ , ⊢eⁱ')
  … | yes (Unit , ϕ , e , ⊢eⁱ)               = no λ where (_ , _ , _ , ⊢split x _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (t –[ x₁ ⍮ x₂ ]→ t₁ , ϕ , e , ⊢eⁱ) = no λ where (_ , _ , _ , ⊢split x _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (t ×[ x₁ ] t₁ , ϕ , e , ⊢eⁱ)       = no λ where (_ , _ , _ , ⊢split x _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (# r , ϕ , e , ⊢eⁱ) with r₁ M.∃≤? r in eq∃
  …   | no ¬pp                               = no λ where (_ , _ , _ , ⊢split pp _ ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of
                                                                                          λ where refl → ¬pp (_ , pp)
  …   | yes (r₂ , pp)                        = yes (_ , _ , _ , ⊢split pp eq∃ ⊢eⁱ)
  infer Γ (drop eⁱ) with infer Γ eⁱ
  … | no ¬pp                                 = no λ where (_ , _ , _ , ⊢drop x ⊢eⁱ') → ¬pp (_ , _ , _ , ⊢eⁱ')
  … | yes (Unit , ϕ , e , ⊢eⁱ)               = no λ where (_ , _ , _ , ⊢drop x ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (t –[ x₁ ⍮ x₂ ]→ t₁ , ϕ , e , ⊢eⁱ) = no λ where (_ , _ , _ , ⊢drop x ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (t ×[ x₁ ] t₁ , ϕ , e , ⊢eⁱ)       = no λ where (_ , _ , _ , ⊢drop x ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of λ ()
  … | yes (# r , ϕ , e , ⊢eⁱ) with M.ϵ M.≤? r
  …   | no ¬ϵ≤r                              = no λ where (_ , _ , _ , ⊢drop ϵ≤r ⊢eⁱ') → case proj₁ (⊢↑-det ⊢eⁱ ⊢eⁱ') of
                                                                                            λ where refl → ¬ϵ≤r ϵ≤r
  …   | yes ϵ≤r                              = yes (_ , _ , _ , ⊢drop ϵ≤r ⊢eⁱ)
  infer Γ (` x) with Γ ∃≲? x in eqx
  … | no ¬Γ≲x∶t                              = no λ where (_ , _ , _ , ⊢var Γ≲x∶t _) → ¬Γ≲x∶t (_ , Γ≲x∶t)
  … | yes (t , Γ≲x∶t)                        = yes (_ , _ , _ , ⊢var Γ≲x∶t eqx)
  infer Γ (eⁱ₁ `· eⁱ₂) with infer (Γ ↓ fvs↑ eⁱ₁) eⁱ₁ | infer (Γ ↓ fvs↑ eⁱ₂) eⁱ₂
  … | no ¬⊢eⁱ₁                  | _                         = no λ where
    (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁ ⊢eⁱ₂) → ¬⊢eⁱ₁ (_ , _ , _ , ⊢eⁱ₁)
  … | _                         | no ¬⊢eⁱ₂                  = no λ where
    (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁ ⊢eⁱ₂) → ¬⊢eⁱ₂ (_ , _ , _ , ⊢eⁱ₂)
  … | yes (t₁ , ϕ₁ , e₁ , ⊢eⁱ₁) | yes (t₂ , ϕ₂ , e₂ , ⊢eⁱ₂)
    with t₁
  … | Unit                = no λ where (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case proj₁ (⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁') of λ ()
  … | # r                 = no λ where (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case proj₁ (⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁') of λ ()
  … | t₁₁ ×[ m ] t₁₂      = no λ where (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case proj₁ (⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁') of λ ()
  … | t₁₁ –[ m ⍮ ϕ ]→ t₁₂
    with t₁₁ ≟ t₂
  … | no ¬t₁₁≡t₂          = no λ where (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case proj₁ (⊢↑-det ⊢eⁱ₂ ⊢eⁱ₂') of λ { refl →
                                          case proj₁ (⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁') of λ { refl → ¬t₁₁≡t₂ refl } }
  … | yes refl
    with Γ ≲? ext m (Γ ↓ fvs↑ eⁱ₁) (Γ ↓ fvs↑ eⁱ₂)
  … | no ¬Γ≲Γ₁⸴Γ₂         = no λ where (_ , _ , _ , ⊢· {m = m'} refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (refl , refl , refl) →
                                          case ⊢↑-det ⊢eⁱ₂ ⊢eⁱ₂' of λ { (refl , refl , refl) →
                                          ¬Γ≲Γ₁⸴Γ₂ Γ≲Γ₁⸴Γ₂
                                          } }
  … | yes Γ≲Γ₁⸴Γ₂
    with m | ϕ₁ | ϕ₂
  … | ∞ | ϕ₁ | ϕ₂         = yes (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ (λ ()) (λ ()) ⊢eⁱ₁ ⊢eⁱ₂)
  … | 𝟙 | ϕ₁ | ϕ₂         = yes (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ (λ ()) (λ ()) ⊢eⁱ₁ ⊢eⁱ₂)
  … | ≻ | 𝟎  | ϕ₂         = yes (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ (λ ()) (λ z → refl) ⊢eⁱ₁ ⊢eⁱ₂)
  … | ≻ | 𝟏  | ϕ₂         = no λ where (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (refl , refl , refl) →
                                          case m≡≻→ϕ₂≡𝟎 refl of λ () }
  … | ≺ | ϕ₁ | 𝟎          = yes (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ (λ z → refl) (λ ()) ⊢eⁱ₁ ⊢eⁱ₂)
  … | ≺ | ϕ₁ | 𝟏          = no λ where (_ , _ , _ , ⊢· refl refl Γ≲Γ₁⸴Γ₂ m≡≺→ϕ₁≡𝟎 m≡≻→ϕ₂≡𝟎 ⊢eⁱ₁' ⊢eⁱ₂') →
                                          case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (refl , refl , refl) →
                                          case ⊢↑-det ⊢eⁱ₂ ⊢eⁱ₂' of λ { (refl , refl , refl) →
                                          case m≡≺→ϕ₁≡𝟎 refl of λ () } }
  infer Γ (eⁱ₁ , eⁱ₂) with infer (Γ ↓ fvs↑ eⁱ₁) eⁱ₁ | infer (Γ ↓ fvs↑ eⁱ₂) eⁱ₂
  … | no ¬⊢eⁱ₁                  | _                         = no λ where
    (_ , _ , _ , ⊢, refl refl Γ≲Γ₁⸴Γ₂ p ⊢eⁱ₁ ⊢eⁱ₂) → ¬⊢eⁱ₁ (_ , _ , _ , ⊢eⁱ₁)
  … | _                         | no ¬⊢eⁱ₂                  = no λ where
    (_ , _ , _ , ⊢, refl refl Γ≲Γ₁⸴Γ₂ p ⊢eⁱ₁ ⊢eⁱ₂) → ¬⊢eⁱ₂ (_ , _ , _ , ⊢eⁱ₂)
  … | yes (t₁ , ϕ₁ , e₁ , ⊢eⁱ₁) | yes (t₂ , ϕ₂ , e₂ , ⊢eⁱ₂)
    with Γ ≲? ext 𝟙 (Γ ↓ fvs↑ eⁱ₁) (Γ ↓ fvs↑ eⁱ₂)
  … | yes Γ≲Γ₁∥Γ₂         = yes (_ , _ , _ , ⊢, refl refl Γ≲Γ₁∥Γ₂ (inj₁ refl) ⊢eⁱ₁ ⊢eⁱ₂)
  … | no ¬Γ≲Γ₁∥Γ₂
    with Γ ≲? ext ≻ (Γ ↓ fvs↑ eⁱ₁) (Γ ↓ fvs↑ eⁱ₂)
  … | no ¬Γ≲Γ₁⸴Γ₂         = no λ where (_ , _ , _ , ⊢, refl refl Γ≲Γ₁⸴Γ₂ p ⊢eⁱ₁' ⊢eⁱ₂') →
                                            case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (refl , refl , refl) →
                                            case ⊢↑-det ⊢eⁱ₂ ⊢eⁱ₂' of λ { (refl , refl , refl) →
                                            case p of λ where
                                              (inj₁ refl) → ¬Γ≲Γ₁∥Γ₂ Γ≲Γ₁⸴Γ₂
                                              (inj₂ (refl , ord-t₁→ϕ₂≡𝟎)) → ¬Γ≲Γ₁⸴Γ₂ Γ≲Γ₁⸴Γ₂
                                            } }
  … | yes Γ≲Γ₁⸴Γ₂
    with Unr? t₁ | ϕ₂ ≟ 𝟎
  … | yes unr-t₁ | _        = yes (_ , _ , _ , ⊢, refl refl Γ≲Γ₁⸴Γ₂ (inj₂ (refl , (λ ord-t₁ → ⊥-elim (ord-t₁ unr-t₁)) , ¬Γ≲Γ₁∥Γ₂)) ⊢eⁱ₁ ⊢eⁱ₂)
  … | no  ord-t₁ | yes refl = yes (_ , _ , _ , ⊢, refl refl Γ≲Γ₁⸴Γ₂ (inj₂ (refl , (λ ord-t₁ → refl) , ¬Γ≲Γ₁∥Γ₂)) ⊢eⁱ₁ ⊢eⁱ₂)
  … | no  ord-t₁ | no ¬ϕ₂≡𝟎 = no λ where (_ , _ , _ , ⊢, refl refl Γ≲Γ₁⸴Γ₂ p ⊢eⁱ₁' ⊢eⁱ₂') →
                                            case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (refl , refl , refl) →
                                            case ⊢↑-det ⊢eⁱ₂ ⊢eⁱ₂' of λ { (refl , refl , refl) →
                                            case p of λ where
                                              (inj₁ refl) → ¬Γ≲Γ₁∥Γ₂ Γ≲Γ₁⸴Γ₂
                                              (inj₂ (m≡≻ , ord-t₁→ϕ₂≡𝟎)) →
                                                case proj₁ ord-t₁→ϕ₂≡𝟎 ord-t₁ of λ { ϕ₂≡𝟎 → ¬ϕ₂≡𝟎 ϕ₂≡𝟎 }
                                            } }
  infer Γ (let[ x , y ≡ eⁱ₁ ]in eⁱ₂)
    with x ∈? dom Γ
  … | yes x∈Γ = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq ⊢eⁱ₁ ⊢eⁱ₂) → x∉Γ x∈Γ
  … | no ¬x∈Γ
    with y ∈? dom Γ
  … | yes y∈Γ = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq ⊢eⁱ₁ ⊢eⁱ₂) → y∉Γ y∈Γ
  … | no ¬y∈Γ
    with y ≟ x
  … | yes y≡x = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq ⊢eⁱ₁ ⊢eⁱ₂) → y≢x y≡x
  … | no ¬y≡x
    with Γ ↓ᶜ fvs↑ eⁱ₁ in eq-↓ᶜ
  … | none = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁ ⊢eⁱ₂) → case trans (sym eq') eq-↓ᶜ of λ ()
  … | some (𝒢 , Γ')
    with infer Γ' eⁱ₁
  … | no ¬⊢eⁱ₁ = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁' ⊢eⁱ₂') →
                              case trans (sym eq') eq-↓ᶜ of λ { refl →
                              ¬⊢eⁱ₁ (_ , _ , _ , ⊢eⁱ₁') }
  … | yes (t₁ , ϕ₁ , e₁ , ⊢eⁱ₁)
    with t₁
  … | Unit              = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁' ⊢eⁱ₂') →
                                        case trans (sym eq') eq-↓ᶜ of λ { refl →
                                        case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (() , _ , _) } }
  … | # r               = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁' ⊢eⁱ₂') →
                                        case trans (sym eq') eq-↓ᶜ of λ { refl →
                                        case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (() , _ , _) } }
  … | t₁ –[ m ⍮ ϕ ]→ t₂ = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁' ⊢eⁱ₂') →
                                        case trans (sym eq') eq-↓ᶜ of λ { refl →
                                        case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (() , _ , _) } }
  … | t₁₁ ×[ m ] t₁₂
    with ϕ₁ ≟ 𝟎
  … | no ¬ϕ₁≡𝟎          = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁' ⊢eⁱ₂') →
                                        case trans (sym eq') eq-↓ᶜ of λ { refl →
                                        case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (_ , ϕ₁≡𝟎 , _) →
                                        ¬ϕ₁≡𝟎 ϕ₁≡𝟎 } }
  … | yes refl
    with infer (𝒢 [ ext m (x ∶ t₁₁) (y ∶ t₁₂) ]) eⁱ₂
  … | no ¬⊢eⁱ₂ = no λ where (_ , _ , _ , ⊢let x∉Γ y∉Γ y≢x eq' ⊢eⁱ₁' ⊢eⁱ₂') →
                              case trans (sym eq') eq-↓ᶜ of λ { refl →
                              case ⊢↑-det ⊢eⁱ₁ ⊢eⁱ₁' of λ { (refl , refl , refl) →
                              ¬⊢eⁱ₂ (_ , _ , _ , ⊢eⁱ₂') } }
  … | yes (t₂ , ϕ₂ , e₂ , ⊢eⁱ₂)
    = yes (_ , _ , _ , ⊢let ¬x∈Γ ¬y∈Γ ¬y≡x eq-↓ᶜ ⊢eⁱ₁ ⊢eⁱ₂)
  infer Γ (eᶜ ∶ t) with check Γ eᶜ t
  … | yes (ϕ , e , ⊢eᶜ) = yes (t , ϕ , e , ⊢∶ ⊢eᶜ)
  … | no ¬⊢eᶜ           = no λ where (t , ϕ , e , ⊢∶ ⊢eᶜ) → ¬⊢eᶜ (ϕ , e , ⊢eᶜ)
