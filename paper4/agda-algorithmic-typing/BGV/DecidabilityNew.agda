module BGV.Decidability where

import Data.List.Properties as ListP
import Data.List.Relation.Unary.Any.Properties as AnyP
import Data.Maybe.Properties as MaybeP
import Data.Product.Properties as ProdP
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_; _++_; map)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; _$_; _∘_) renaming (_∋_ to _by_)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)
open import Axiom.Extensionality.Propositional using (Extensionality)

open import BGV.Algorithmic
open import BGV.Context
open import BGV.Context.SyntacticSplit
open import BGV.Effect
open import BGV.Expressions
open import BGV.Id
open import BGV.Logical
open import BGV.Multiplicities
open import BGV.Ren
open import BGV.UsageMap
open import BGV.Split
open import BGV.SplitTyping
open import BGV.Translation
open import BGV.Types
open import BGV.Util.Decidable
open import BGV.Util.List
open import BGV.Soundness
open import BGV.Deterministic

check'-λ : ∀ Γ m x e t₁ m' ϕ₂ t₂ →
  Unique (dom Γ) →
  x ∉ dom Γ →
  Dec (∃[ u ] ∃[ ϕ ] ((ext m Γ (x ∶ t₁)) ⊢ e ∶[ chk ] t₂ ⍮ u ⍮ ϕ)) →
  Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ (λ[ m ] x ⇒ e) ∶[ chk ] (t₁ –[ m' ⍮ ϕ₂ ]→ t₂) ⍮ u ⍮ ϕ)
check'-λ Γ m x e t₁ m' ϕ₂ t₂ U-Γ x∉Γ ⊢e?
  with ⊢e?
… | no ¬⊢e = no λ where (u , ϕ , ⊢λ _ ⊢e _ _ _) → ¬⊢e (_ , _ , ⊢e)
… | yes (u , ϕ₁ , ⊢e)
  with ϕ₁ ⊑? ϕ₂
… | no ¬ϕ₁⊑ϕ₂ = no λ where
    (u , ϕ , ⊢λ _ ⊢e' _ _ ϕ₁⊑ϕ₂) →
      case ⊢↓-det (Unique-ext m Γ U-Γ x∉Γ) ⊢e ⊢e' of λ where
        (_ , refl) → ¬ϕ₁⊑ϕ₂ ϕ₁⊑ϕ₂ 
… | yes ϕ₁⊑ϕ₂
  with m ≟ m'
… | no m≢m' = no λ where
    (u , ϕ , ⊢λ _ ⊢e' _ _ _) →
      case ⊢↓-det (Unique-ext m Γ U-Γ x∉Γ) ⊢e ⊢e' of λ where
        (refl , _) → m≢m' refl
… | yes refl
  with m ≟ ∞
… | no m≢∞ =
    case Chan? t₁ of λ where
      (no ¬t₁≡chan) →
        yes $ _ , _ , ⊢λ x∉Γ ⊢e (λ m≡∞ → ⊥-elim (m≢∞ m≡∞))
                                (λ b s t₁≡chan → ⊥-elim (¬t₁≡chan (b , s , t₁≡chan))) ϕ₁⊑ϕ₂
      (yes (b , s , refl)) →
        case u x ≟ some (b , s) of λ where
          (yes eq) →
            yes $ _ , _ , ⊢λ x∉Γ ⊢e (λ m≡∞ → ⊥-elim (m≢∞ m≡∞))
                                    (λ { b s refl → eq }) ϕ₁⊑ϕ₂
          (no ¬eq) → no λ where 
            (u , ϕ , ⊢λ _ ⊢e' _ eq _) →
              case ⊢↓-det (Unique-ext m Γ U-Γ x∉Γ) ⊢e ⊢e' of λ where
                (refl , _) → ¬eq (eq b s refl)
… | yes refl
  with Unrᶜ? Γ
… | no ¬Unr-Γ = no λ where (u , ϕ , ⊢λ _ _ m≡∞→UnrΓ _ _) → ¬Unr-Γ (m≡∞→UnrΓ refl)
… | yes Unr-Γ =
    case Chan? t₁ of λ where
      (no ¬t₁≡chan) →
        yes $ _ , _ , ⊢λ x∉Γ ⊢e (λ _ → Unr-Γ)
                                (λ b s t₁≡chan → ⊥-elim (¬t₁≡chan (b , s , t₁≡chan))) ϕ₁⊑ϕ₂
      (yes (b , s , refl)) →
        case u x ≟ some (b , s) of λ where
          (yes eq) →
            yes $ _ , _ , ⊢λ x∉Γ ⊢e (λ _ → Unr-Γ)
                                    (λ { b s refl → eq }) ϕ₁⊑ϕ₂
          (no ¬eq) → no λ where 
            (u , ϕ , ⊢λ _ ⊢e' _ eq _) →
              case ⊢↓-det (Unique-ext m Γ U-Γ x∉Γ) ⊢e ⊢e' of λ where
                (refl , _) → ¬eq (eq b s refl)

check'-& : ∀ Γ x t →
  Unique (dom Γ) →
  Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ (& x) ∶[ chk ] t ⍮ u ⍮ ϕ)
check'-& Γ x t U-Γ
  with ChanB? t
… | no ¬ChanB = no λ { (u , ϕ , ⊢& _ _ _) → ¬ChanB (_ , refl) }
… | yes (s₁ , refl)
  with Γ ∃≲? x in eqx
… | no ¬Γ≲x∶t = no λ where (u , ϕ , ⊢& Γ≲x∶t _ _) → ¬Γ≲x∶t (_ , Γ≲x∶t)
… | yes (t , Γ≲x∶t)
  with Chan? t
… | no t≢Chan = no λ where
    (u , ϕ , ⊢& {t = t'} Γ≲x∶t' t'≡Chan _) →
      let t≡t' = ≲-single-det U-Γ Γ≲x∶t Γ≲x∶t' in
      t≢Chan (_ , _ , trans t≡t' t'≡Chan)
… | yes (b , s , refl)
  with s %? s₁
… | no  ¬∃[s₂]s≡s₁++s₂ = no λ where
    (u , ϕ , ⊢& {t = t'} Γ≲x∶t' refl refl) →
      let t≡t' = ≲-single-det U-Γ Γ≲x∶t Γ≲x∶t' in
      case Chan-injective t≡t' of λ where
        (refl , refl) → ¬∃[s₂]s≡s₁++s₂ (_ , refl)
… | yes (s₂ , refl)
  = yes (_ , _ , ⊢& Γ≲x∶t refl refl)

check'-inj : ∀ Γ l e t₁ t₂ →
  Unique (dom Γ) →
  Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ e ∶[ chk ] t₁ ⍮ u ⍮ ϕ) →
  Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ e ∶[ chk ] t₂ ⍮ u ⍮ ϕ) →
  Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ (`inj l e) ∶[ chk ] (t₁ + t₂) ⍮ u ⍮ ϕ)
check'-inj Γ [1] e t₁ t₂ U-Γ (yes (u , ϕ , ⊢e)) ⊢e₂? = yes (_ , _ , ⊢inj ⊢e)
check'-inj Γ [1] e t₁ t₂ U-Γ (no ¬⊢e)           ⊢e₂? = no λ { (u , ϕ , ⊢inj ⊢e) → ¬⊢e (_ , _ , ⊢e) }
check'-inj Γ [2] e t₁ t₂ U-Γ ⊢e₁? (yes (u , ϕ , ⊢e)) = yes (_ , _ , ⊢inj ⊢e)
check'-inj Γ [2] e t₁ t₂ U-Γ ⊢e₁? (no ¬⊢e)           = no λ { (u , ϕ , ⊢inj ⊢e) → ¬⊢e (_ , _ , ⊢e) }

data Checked : Expr alg → Set where
  chk-λ : ∀ m x e → Checked (λ[ m ] x ⇒ e)
  chk-& : ∀ x → Checked (& x)
  chk-inj : ∀ l e → Checked (`inj l e)

Checked? : ∀ e → Dec (Checked e)
Checked? (λ[ m ] x ⇒ e)                = yes (chk-λ m x e)
Checked? (`inj l e)                    = yes (chk-inj l e)
Checked? (& x)                         = yes (chk-& x)
Checked? (` x)                         = no λ()
Checked? (e `· e₁)                     = no λ()
Checked? (let[ x ≔ e ]in e₁)           = no λ()
Checked? (e ,[ x ] e₁)                 = no λ()
Checked? (let[ x `, x₁ ≔ e ]in e₁)     = no λ()
Checked? case e of[ x ⇒ e₁ ⍮ x₁ ⇒ e₂ ] = no λ()
Checked? (spawn e)                     = no λ()
Checked? (new x)                       = no λ()
Checked? (send e e₁)                   = no λ()
Checked? (recv e)                      = no λ()
Checked? (drop e)                      = no λ()
Checked? (close x e)                   = no λ()
Checked? unit                          = no λ()
Checked? (e `∶ x)                      = no λ()
Checked? (e ▸ e₁)                      = no λ()

check'-¬checked : ∀ Γ e t →
  Unique (dom Γ) →
  ¬ Checked e →
  Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ e ∶[ inf ] t ⍮ u ⍮ ϕ) →
  Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ e ∶[ chk ] t ⍮ u ⍮ ϕ)
check'-¬checked Γ e t U-Γ ¬checked ⊢e?
  with ⊢e?
… | no ¬⊢e = no λ where
    (u , ϕ , ⊢& x x₁ x₂) → ¬checked (chk-& _)
    (u , ϕ , ⊢λ x ⊢e x₁ x₂ x₃) → ¬checked (chk-λ _ _ _)
    (u , ϕ , ⊢inj ⊢e) → ¬checked (chk-inj _ _) 
    (u , ϕ , ⊢chk-inf ⊢e) → ¬⊢e (_ , _ , _ , ⊢e)
… | yes (t' , u , ϕ , ⊢e)
  with t' ≟ᵗ t
… | yes refl = yes (u , ϕ , ⊢chk-inf ⊢e)
… | no ¬t'≡t = no λ { (u , ϕ , ⊢chk-inf ⊢e') → ¬t'≡t (proj₁ (⊢↑-det U-Γ ⊢e ⊢e')) }

infer'-` : ∀ Γ x →
  Unique (dom Γ) →
  Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ ` x ∶[ inf ] t ⍮ u ⍮ ϕ)
infer'-` Γ x U-Γ
  with Γ ∃≲? x in eqx
… | no ¬Γ≲x∶t = no λ where
    (t' , u , ϕ , ⊢`-nochan Γ≲x∶t _) → ¬Γ≲x∶t (_ , Γ≲x∶t)
    (t' , u , ϕ , ⊢`-chan   Γ≲x∶t _) → ¬Γ≲x∶t (_ , Γ≲x∶t)
… | yes (t , Γ≲x∶t)
  with Chan? t
… | no t≢Chan =
    yes (_ , _ , _ , ⊢`-nochan Γ≲x∶t (λ b s eq → t≢Chan (b , s , eq)))
… | yes (b , s , refl) =
    yes (_ , _ , _ , ⊢`-chan Γ≲x∶t refl)

infer'-▸ : ∀ Γ e₁ e₂ u₁ t₁ ϕ₁ →
  Unique (dom Γ) →
  (Γ ↓ fvs e₁) ⊢ e₁ ∶[ inf ] t₁ ⍮ u₁ ⍮ ϕ₁ →
  Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] ((Γ ↓ fvs e₂) %ᶜ u₁) ⊢ e₂ ∶[ inf ] t ⍮ u ⍮ ϕ) →
  Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ (e₁ ▸ e₂) ∶[ inf ] t ⍮ u ⍮ ϕ)
infer'-▸ Γ e₁ e₂ u₁ t₁ ϕ₁ U-Γ ⊢e₁ ⊢e₂?
  using Γ₁ ← Γ ↓ fvs e₁
  using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
  using Γ₂ ← (Γ ↓ fvs e₂) %ᶜ u₁
  using U-Γ₂ ← Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ
  with ⊢e₂?
… | no ¬⊢e₂ = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) → ¬⊢e₂ (_ , _ , _ , ⊢e₂')
… | yes (t₂ , u₂ , ϕ₂ , ⊢e₂)
  with t₂
… | Chan b x          = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (() , refl , refl)
… | t + t₂            = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (() , refl , refl)
… | t ×[ x ] t₂       = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (() , refl , refl)
… | Unit              = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (() , refl , refl)
… | t₁' –[ m ⍮ ϕ ]→ t₂
  with t₁ ≟ t₁'
… | no t₁≢t₁' = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (refl , refl , refl) → t₁≢t₁' refl
… | yes refl
  with m ≟ ≺
… | no m≢≺ = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (refl , refl , refl) → m≢≺ refl
… | yes refl
  with ϕ₂
… | 𝟏 = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (refl , refl , ())
… | 𝟎
  with SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ ordered
… | no ¬salg = no λ where
    (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' salg') →
      case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
        (refl , refl , refl) →
          case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
            (refl , refl , refl) → ¬salg salg'
… | yes salg
  = yes (_ , _ , _ , ⊢·≺ refl ⊢e₁ refl ⊢e₂ salg)

mutual
  check' : ∀ Γ e t → Unique (dom Γ) → Dec (∃[ u ] ∃[ ϕ ] Γ ⊢ e ∶[ chk ] t ⍮ u ⍮ ϕ)
  check' Γ e' t U-Γ with Checked? e'
  check' Γ e' t U-Γ | yes (chk-λ m x e)
    with →? t
  … | no ¬→ = no λ { (u , ϕ , ⊢λ _ _ _ _ _) → ¬→ (_ , _ , _ , _ , refl) }
  … | yes (t₁ , m' , ϕ₂ , t₂ , refl)
    with x ∈? dom Γ
  … | yes x∈Γ = no λ where (u , ϕ , ⊢λ x∉Γ _ _ _ _) → x∉Γ x∈Γ
  … | no  x∉Γ = check'-λ Γ m x e t₁ m' ϕ₂ t₂ U-Γ x∉Γ
                         (check' (ext m Γ (x ∶ t₁)) e t₂ (Unique-ext m Γ U-Γ x∉Γ)) 
  check' Γ e' t U-Γ | yes (chk-& x) = check'-& Γ x t U-Γ
  check' Γ e' t U-Γ | yes (chk-inj l e)
    with +? t
  … | no ¬+ = no λ { (u , ϕ , ⊢inj ⊢e) → ¬+ (_ , _ , refl) }
  … | yes (t₁ , t₂ , refl) =
    check'-inj Γ l e t₁ t₂ U-Γ (check' Γ e t₁ U-Γ) (check' Γ e t₂ U-Γ)
  check' Γ e' t U-Γ | no ¬checked =
    check'-¬checked Γ e' t U-Γ ¬checked (infer' Γ e' U-Γ)

  infer'-· : ∀ Γ (e₁ e₂ : Expr alg) → Unique (dom Γ) → Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ (e₁ `· e₂) ∶[ inf ] t ⍮ u ⍮ ϕ)
  infer'-· Γ e₁ e₂ U-Γ 
    using Γ₁ ← Γ ↓ fvs e₁
    using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
    with infer' Γ₁ e₁ U-Γ₁
  … | no ¬⊢e₁ = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) → ¬⊢e₁ (_ , _ , _ , ⊢e₁')
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) → ¬⊢e₁ (_ , _ , _ , ⊢e₁')
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) → ¬⊢e₁ (_ , _ , _ , ⊢e₁')
  … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
    using Γ₂ ← (Γ ↓ fvs e₂) %ᶜ u₁
    using U-Γ₂ ← Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ
    with t₁
  … | Chan b x          = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
  … | t + t₂            = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
  … | t ×[ x ] t₂       = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
  … | Unit              = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where (() , _ , _)
  … | t₁ –[ m ⍮ ϕ ]→ t₂
    with check' Γ₂ e₂ t₁ U-Γ₂
  … | no ¬⊢e₂ = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) → ¬⊢e₂ (_ , _ , ⊢e₂')
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) → ¬⊢e₂ (_ , _ , ⊢e₂')
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) → ¬⊢e₂ (_ , _ , ⊢e₂')
  … | yes (u₂ , ϕ₂ , ⊢e₂)
    with m
  … | ∞ =
      case SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ ordered of λ where
        (no ¬salg) → no λ where
          (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
          (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
          (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (refl , refl , refl) →
                case ⊢↓-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
                  (refl , refl) →
                    ¬salg salg'
        (yes salg) →
          yes (_ , _ , _ , ⊢·∞ refl ⊢e₁ refl ⊢e₂ salg)
  … | 𝟙 =
      case SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ unordered of λ where
        (no ¬salg) → no λ where
          (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
          (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (refl , refl , refl) →
                case ⊢↓-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
                  (refl , refl) →
                    ¬salg salg'
          (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
        (yes salg) →
          yes (_ , _ , _ , ⊢·𝟙 refl ⊢e₁ refl ⊢e₂ salg)
  … | ≺ = no λ where
          (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
          (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
          (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
  … | ≻
    with ϕ₂
  … | 𝟏 = no λ where
      (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case ⊢↓-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
              (refl , ())
      (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (() , refl , refl)
      (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (() , refl , refl)
  … | 𝟎 =
      case SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ ordered of λ where
        (no ¬salg) → no λ where
          (_ , _ , _ , ⊢·≻ refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (refl , refl , refl) →
                case ⊢↓-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
                  (refl , refl) →
                    ¬salg salg'
          (_ , _ , _ , ⊢·𝟙 refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
          (_ , _ , _ , ⊢·∞ refl ⊢e₁' refl ⊢e₂' salg') →
            case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
              (() , refl , refl)
        (yes salg) →
          yes (_ , _ , _ , ⊢·≻ refl ⊢e₁ refl ⊢e₂ salg)

  infer'-, : ∀ Γ (e₁ e₂ : Expr alg) p → Unique (dom Γ) → Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ (e₁ ,[ p ] e₂) ∶[ inf ] t ⍮ u ⍮ ϕ)
  infer'-, Γ e₁ e₂ p U-Γ 
    using Γ₁ ← Γ ↓ fvs e₁
    using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
    with infer' Γ₁ e₁ U-Γ₁
  … | no ¬⊢e₁ = no (λ { (_ , _ , _ , ⊢, refl ⊢e₁ refl ⊢e₂ _ _) → ¬⊢e₁ (_ , _ , _ , ⊢e₁) })
  … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
    using Γ₂ ← (Γ ↓ fvs e₂) %ᶜ u₁
    using U-Γ₂ ← Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ
    with infer' Γ₂ e₂ U-Γ₂
  … | no ¬⊢e₂ = no λ where
      (_ , _ , _ , ⊢, refl ⊢e₁' refl ⊢e₂' _ _) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) → ¬⊢e₂ (_ , _ , _ , ⊢e₂')
  … | yes (t₂ , u₂ , ϕ₂ , ⊢e₂)
    with SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ (pmult→ord p)
  … | no ¬salg = no λ where
      (_ , _ , _ , ⊢, refl ⊢e₁' refl ⊢e₂' _ salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
              (refl , refl , refl) →
                ¬salg salg
  … | yes salg
    with Unr? t₁ | p | ϕ₂
  … | yes unr-t₁ | p | ϕ₂ =
    yes (_ , _ , _ , ⊢, refl ⊢e₁ refl ⊢e₂ (λ ¬unr-t₁ → ⊥-elim (¬unr-t₁ unr-t₁)) salg)
  … | no ¬unr-t₁ | 𝟙 | ϕ₂ =
    yes (_ , _ , _ , ⊢, refl ⊢e₁ refl ⊢e₂ (λ _ ()) salg)
  … | no ¬unr-t₁ | ≻ | 𝟎 =
    yes (_ , _ , _ , ⊢, refl ⊢e₁ refl ⊢e₂ (λ _ _ → refl) salg)
  … | no ¬unr-t₁ | ≻ | 𝟏 =
    no λ where
      (_ , _ , _ , ⊢, refl ⊢e₁' refl ⊢e₂' xx salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case ⊢↑-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
              (refl , refl , refl) →
                case xx ¬unr-t₁ refl of λ ()

  infer'-let : ∀ Γ x (e₁ e₂ : Expr alg) → Unique (dom Γ) → Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ (let[ x ≔ e₁ ]in e₂) ∶[ inf ] t ⍮ u ⍮ ϕ)
  infer'-let Γ x e₁ e₂ U-Γ 
    with x ∈? dom Γ
  … | yes x∈Γ = no λ where
      (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓ refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
        x∉Γ x∈Γ
  … | no x∉Γ
    using Γ₁ ← Γ ↓ fvs e₁
    using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
    with infer' Γ₁ e₁ U-Γ₁
  … | no ¬⊢e₁ = no λ where
      (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓ refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
        ¬⊢e₁ (_ , _ , _ , ⊢e₁')
  … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
    using sis ← (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁
    using ρ₁ , ρ₂ ← split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂)
    with split-ctx sis ρ₁ ρ₂ Γ ↓ᶜ (fvs e₁ ⋯ˡ ρ₁) in Γ↓
  … | none = no λ where
      (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓' refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ ()
  … | some (C' , Γ')
    using C ← C' ⋯ʳᶜ invertʳ (map proj₁ sis) ρ₂
    with dom (C [ · ]) ⊆ⁱ? dom Γ ⊣ U-Γ
  … | no ¬domC⊆domΓ = no λ where
      (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓' refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬domC⊆domΓ domC⊆domΓ
  … | yes domC⊆domΓ
    using U-C[·] ← Unique-⊆ domC⊆domΓ U-Γ
    using d-C[·]-x ← λ where x x∈C[·] (here refl) → x∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
    using U-C[x∶t₁] ← Unique-≈ (dom-C C (x ∶ t₁)) $
                      Unique-++ U-C[·] (Unique-single x) d-C[·]-x
    with infer' (C [ x ∶ t₁ ]) e₂ U-C[x∶t₁]
  … | no ¬⊢e₂ = no λ where
      (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓' refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬⊢e₂ (_ , _ , _ , ⊢e₂')
  … | yes (t₂ , u₂ , ϕ₂ , ⊢e₂)
    with SplitsAlg'? u₁ (u₂ -ᵘ x) e₁ (e₂ ∷ []) Γ Γ₁ C List.[ x ]
  … | no ¬salg = no λ where
      (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓' refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂ ⊢e₂' of λ where
                  (refl , refl , refl) →
                    ¬salg salg
  … | yes salg
    with ¬left→ϕ≡0? C ϕ₁
  … | inj₁ (¬C-left , refl) =
      no λ where
        (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓' refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
          case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
            (refl , refl , refl) →
              case trans (sym Γ↓) Γ↓' of λ where
                refl →
                  case ⊢↑-det U-C[x∶t₁] ⊢e₂ ⊢e₂' of λ where
                    (refl , refl , refl) →
                      case ¬left→ϕ₂≡0 ¬C-left of λ()
  … | inj₂ ¬left→ϕ₁≡𝟎
    with t≡Chan→used? t₁ u₂ x
  … | inj₁ (b , s , refl , u₂x-eq) =
          no λ where
            (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁' Γ↓' refl ¬left→ϕ₂≡0 domC⊆domΓ ⊢e₂' t₁≡Chan→used salg) →
              case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
                (refl , refl , refl) →
                  case trans (sym Γ↓) Γ↓' of λ where
                    refl →
                      case ⊢↑-det U-C[x∶t₁] ⊢e₂ ⊢e₂' of λ where
                        (refl , refl , refl) →
                          u₂x-eq (t₁≡Chan→used _ _ refl)
  … | inj₂ t₁≡Chan→used =
    yes (_ , _ , _ , ⊢let x∉Γ refl ⊢e₁ Γ↓ refl ¬left→ϕ₁≡𝟎 domC⊆domΓ ⊢e₂ t₁≡Chan→used salg)

  infer'-let× : ∀ Γ x y (e₁ e₂ : Expr alg) → Unique (dom Γ) → Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ (let[ x `, y ≔ e₁ ]in e₂) ∶[ inf ] t ⍮ u ⍮ ϕ)
  infer'-let× Γ x y e₁ e₂ U-Γ 
    with x ∈? dom Γ
  … | yes x∈Γ = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        x∉Γ x∈Γ
  … | no x∉Γ
    with y ∈? dom Γ
  … | yes y∈Γ = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        y∉Γ y∈Γ
  … | no y∉Γ
    with x ≟ y
  … | yes x≡y = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        x≢y x≡y
  … | no x≢y
    using Γ₁ ← Γ ↓ fvs e₁
    using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
    with infer' Γ₁ e₁ U-Γ₁
  … | no ¬⊢e₁ = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        ¬⊢e₁ (_ , _ , _ , ⊢e₁')
  … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
    with ×? t₁
  … | no ¬× = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            ¬× (_ , _ , _ , refl)
  … | yes (t₁ , p , t₂ , refl)
    using sis ← (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁
    using ρ₁ , ρ₂ ← split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂)
    with split-ctx sis ρ₁ ρ₂ Γ ↓ᶜ (fvs e₁ ⋯ˡ ρ₁) in Γ↓
  … | none = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ ()
  … | some (C' , Γ')
    using C ← C' ⋯ʳᶜ invertʳ (map proj₁ sis) ρ₂
    with dom (C [ · ]) ⊆ⁱ? dom Γ ⊣ U-Γ
  … | no ¬domC⊆domΓ = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬domC⊆domΓ domC⊆domΓ
  … | yes domC⊆domΓ
    using U-C[·] ← Unique-⊆ domC⊆domΓ U-Γ
    using d-C[·]-xy ← λ where
      x x∈C[·] (here refl) → x∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
      x x∈C[·] (there (here refl)) → y∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
    using U-C[x∶t₁⸴y∶t₂] ←
      Unique-≈ (dom-C C (x ∶ t₁ ⸴[ pmult→ord p ] y ∶ t₂)) $
      Unique-++ U-C[·]
                (Unique-∷ (λ { (here refl) → x≢y refl }) (Unique-single y))
                d-C[·]-xy
    with infer' (C [ x ∶ t₁ ⸴[ pmult→ord p ] y ∶ t₂ ]) e₂ U-C[x∶t₁⸴y∶t₂]
  … | no ¬⊢e₂ = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬⊢e₂ (_ , _ , _ , ⊢e₂')
  … | yes (t , u₂ , ϕ₂ , ⊢e₂)
    with SplitsAlg'? u₁ (u₂ -ᵘ x -ᵘ y) e₁ (e₂ ∷ []) Γ Γ₁ C (x ∷ y ∷ [])
  … | no ¬salg = no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁⸴y∶t₂] ⊢e₂ ⊢e₂' of λ where
                  (refl , refl , refl) →
                    ¬salg salg
  … | yes salg
    with ¬left→ϕ≡0? C ϕ₁
  … | inj₁ (¬C-left , refl) =
      no λ where
      (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
          case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
            (refl , refl , refl) →
              case trans (sym Γ↓) Γ↓' of λ where
                refl →
                  case ⊢↑-det U-C[x∶t₁⸴y∶t₂] ⊢e₂ ⊢e₂' of λ where
                    (refl , refl , refl) →
                      case ¬left→ϕ₂≡0 ¬C-left of λ()
  … | inj₂ ¬left→ϕ₁≡𝟎
    with t≡Chan→used? t₁ u₂ x
  … | inj₁ (b , s , refl , u₂x-eq) =
          no λ where
            (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                              domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
              case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
                (refl , refl , refl) →
                  case trans (sym Γ↓) Γ↓' of λ where
                    refl →
                      case ⊢↑-det U-C[x∶t₁⸴y∶t₂] ⊢e₂ ⊢e₂' of λ where
                        (refl , refl , refl) →
                          u₂x-eq (t₁≡Chan→used _ _ refl)
  … | inj₂ t₁≡Chan→used
    with t≡Chan→used? t₂ u₂ y
  … | inj₁ (b , s , refl , u₂x-eq) =
          no λ where
            (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                              domC⊆domΓ ⊢e₂' t₁≡Chan→used t₂≡Chan→used salg) →
              case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
                (refl , refl , refl) →
                  case trans (sym Γ↓) Γ↓' of λ where
                    refl →
                      case ⊢↑-det U-C[x∶t₁⸴y∶t₂] ⊢e₂ ⊢e₂' of λ where
                        (refl , refl , refl) →
                          u₂x-eq (t₂≡Chan→used _ _ refl)
  … | inj₂ t₂≡Chan→used =
    yes (_ , _ , _ , ⊢let× x∉Γ y∉Γ x≢y refl ⊢e₁ ¬left→ϕ₁≡𝟎 Γ↓ refl
                           domC⊆domΓ ⊢e₂ t₁≡Chan→used t₂≡Chan→used salg)

  infer'-case : ∀ Γ (e₁ : Expr alg) x (e₂₁ : Expr alg) y (e₂₂ : Expr alg) →
    Unique (dom Γ) →
    Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ (case e₁ of[ x ⇒ e₂₁ ⍮ y ⇒ e₂₂ ]) ∶[ inf ] t ⍮ u ⍮ ϕ)
  infer'-case Γ e₁ x e₂₁ y e₂₂ U-Γ
    with x ∈? dom Γ
  … | yes x∈Γ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        x∉Γ x∈Γ
  … | no x∉Γ
    with y ∈? dom Γ
  … | yes y∈Γ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        y∉Γ y∈Γ
  … | no y∉Γ
    with x ≟ y
  … | yes x≡y = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        x≢y x≡y
  … | no x≢y
    using Γ₁ ← Γ ↓ fvs e₁
    using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
    with infer' Γ₁ e₁ U-Γ₁
  … | no ¬⊢e₁ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        ¬⊢e₁ (_ , _ , _ , ⊢e₁')
  … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
    with +? t₁
  … | no ¬+ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            ¬+ (_ , _ , refl)
  … | yes (t₁ , t₂ , refl)
    using sis ← (fvs e₁ ∩ˡ (fvs e₂₁ ++ fvs e₂₂)) ↓ᵘ u₁
    using ρ₁ , ρ₂ ← split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂₁ ++ vars e₂₂)
    with split-ctx sis ρ₁ ρ₂ Γ ↓ᶜ (fvs e₁ ⋯ˡ ρ₁) in Γ↓
  … | none = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ ()
  … | some (C' , Γ')
    using C ← C' ⋯ʳᶜ invertʳ (map proj₁ sis) ρ₂
    with dom (C [ · ]) ⊆ⁱ? dom Γ ⊣ U-Γ
  … | no ¬domC⊆domΓ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬domC⊆domΓ domC⊆domΓ
  … | yes domC⊆domΓ
    using U-C[·] ← Unique-⊆ domC⊆domΓ U-Γ
    using d-C[·]-x ← λ where x x∈C[·] (here refl) → x∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
    using d-C[·]-y ← λ where y y∈C[·] (here refl) → y∉Γ (⊆ⁱ→⊆ domC⊆domΓ y∈C[·])
    using U-C[x∶t₁] ← Unique-≈ (dom-C C (x ∶ t₁)) $
                      Unique-++ U-C[·] (Unique-single x) d-C[·]-x
    using U-C[y∶t₂] ← Unique-≈ (dom-C C (y ∶ t₂)) $
                      Unique-++ U-C[·] (Unique-single y) d-C[·]-y
    with infer' (C [ x ∶ t₁ ]) e₂₁ U-C[x∶t₁]
  … | no ¬⊢e₂₁ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬⊢e₂₁ (_ , _ , _ , ⊢e₂₁')
  … | yes (t , u₂₁ , ϕ₂₁ , ⊢e₂₁)
    with infer' (C [ y ∶ t₂ ]) e₂₂ U-C[y∶t₂]
  … | no ¬⊢e₂₂ = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl → ¬⊢e₂₂ (_ , _ , _ , ⊢e₂₂')
  … | yes (t' , u₂₂ , ϕ₂₂ , ⊢e₂₂)
    with t ≟ t'
  … | no t≢t' = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂₁ ⊢e₂₁' of λ where
                  (refl , refl , refl) →
                    case ⊢↑-det U-C[y∶t₂] ⊢e₂₂ ⊢e₂₂' of λ where
                      (refl , refl , refl) →
                        t≢t' refl
  … | yes refl 
    with SplitsAlg'? u₁ (u₂₁ -ᵘ x) e₁ (e₂₁ ∷ e₂₂ ∷ []) Γ Γ₁ C (x ∷ y ∷ [])
  … | no ¬salg = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂₁ ⊢e₂₁' of λ where
                  (refl , refl , refl) →
                    case ⊢↑-det U-C[y∶t₂] ⊢e₂₂ ⊢e₂₂' of λ where
                      (refl , refl , refl) →
                        ¬salg salg
  … | yes salg
    with ¬left→ϕ≡0? C ϕ₁
  … | inj₁ (¬C-left , refl) =
      no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂₁ ⊢e₂₁' of λ where
                  (refl , refl , refl) →
                    case ⊢↑-det U-C[y∶t₂] ⊢e₂₂ ⊢e₂₂' of λ where
                      (refl , refl , refl) →
                        case ¬left→ϕ₂≡0 ¬C-left of λ()
  … | inj₂ ¬left→ϕ₁≡𝟎
    with t≡Chan→used? t₁ u₂₁ x
  … | inj₁ (b , s , refl , u₂x-eq) = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂₁ ⊢e₂₁' of λ where
                  (refl , refl , refl) →
                    case ⊢↑-det U-C[y∶t₂] ⊢e₂₂ ⊢e₂₂' of λ where
                      (refl , refl , refl) →
                        u₂x-eq (t₁≡Chan→used _ _ refl)
  … | inj₂ t₁≡Chan→used
    with t≡Chan→used? t₂ u₂₂ y
  … | inj₁ (b , s , refl , u₂x-eq) = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₁-x≡u₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂₁ ⊢e₂₁' of λ where
                  (refl , refl , refl) →
                    case ⊢↑-det U-C[y∶t₂] ⊢e₂₂ ⊢e₂₂' of λ where
                      (refl , refl , refl) →
                        u₂x-eq (t₂≡Chan→used _ _ refl)
  … | inj₂ t₂≡Chan→used
    with LocallyEqᵘ? (dom Γ) (u₂₁ -ᵘ x) (u₂₂ -ᵘ y)
  … | no u₂₁-x≢u₂₂-x = no λ where
      (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁' ¬left→ϕ₂≡0 Γ↓' refl
                         domC⊆domΓ ⊢e₂₁' ⊢e₂₂' u₂₁-x≡u₂₂-x t₁≡Chan→used t₂≡Chan→used salg) →
        case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
          (refl , refl , refl) →
            case trans (sym Γ↓) Γ↓' of λ where
              refl →
                case ⊢↑-det U-C[x∶t₁] ⊢e₂₁ ⊢e₂₁' of λ where
                  (refl , refl , refl) →
                    case ⊢↑-det U-C[y∶t₂] ⊢e₂₂ ⊢e₂₂' of λ where
                      (refl , refl , refl) →
                        u₂₁-x≢u₂₂-x u₂₁-x≡u₂₂-x
  … | yes u₂₁-x≡u₂₂-x
    = yes (_ , _ , _ , ⊢case x∉Γ y∉Γ x≢y refl ⊢e₁ ¬left→ϕ₁≡𝟎 Γ↓ refl domC⊆domΓ
                             ⊢e₂₁ ⊢e₂₂ u₂₁-x≡u₂₂-x t₁≡Chan→used t₂≡Chan→used salg)

  infer' : ∀ Γ e → Unique (dom Γ) → Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] Γ ⊢ e ∶[ inf ] t ⍮ u ⍮ ϕ)
  infer' Γ (` x) U-Γ = infer'-` Γ x U-Γ
  infer' Γ (e₁ ▸ e₂) U-Γ
    using Γ₁ ← Γ ↓ fvs e₁
    using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
    with infer' Γ₁ e₁ U-Γ₁
  … | no ¬⊢e₁ = no λ where
      (_ , _ , _ , ⊢·≺ refl ⊢e₁' refl ⊢e₂' _) → ¬⊢e₁ (_ , _ , _ , ⊢e₁')
  … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
    using Γ₂ ← (Γ ↓ fvs e₂) %ᶜ u₁
    using U-Γ₂ ← Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ
    = infer'-▸ Γ e₁ e₂ u₁ t₁ ϕ₁ U-Γ ⊢e₁ (infer' Γ₂ e₂ U-Γ₂)
  infer' Γ (e₁ `· e₂) U-Γ = infer'-· Γ e₁ e₂ U-Γ
  infer' Γ (e₁ ,[ p ] e₂) U-Γ = infer'-, Γ e₁ e₂ p U-Γ
  infer' Γ (let[ x ≔ e₁ ]in e₂) U-Γ = infer'-let Γ x e₁ e₂ U-Γ
  infer' Γ (let[ x `, y ≔ e₁ ]in e₂) U-Γ = infer'-let× Γ x y e₁ e₂ U-Γ
  infer' Γ case e₁ of[ x ⇒ e₂₁ ⍮ y ⇒ e₂₂ ] U-Γ = infer'-case Γ e₁ x e₂₁ y e₂₂ U-Γ
  -- infer' Γ (spawn e) U-Γ
  --   with infer' Γ e U-Γ
  -- … | no ¬⊢e = no λ where
  --     (_ , _ , _ , ⊢spawn ⊢e') → ¬⊢e (_ , _ , _ , ⊢e')
  -- … | yes (t , u , ϕ , ⊢e)
  --   with t ≟ Unit
  -- … | no t≢Unit = no λ where
  --     (_ , _ , _ , ⊢spawn ⊢e') →
  --       case ⊢↑-det U-Γ ⊢e ⊢e' of λ where
  --         (refl , refl , refl) → t≢Unit refl
  -- … | yes refl =
  --   yes (_ , _ , _ , ⊢spawn ⊢e)
  -- infer' Γ (new s) U-Γ
  --   with Γ ≲? ·
  -- … | no ¬Γ≲· = no (λ { (_ , _ , _ , ⊢new Γ≲·) → ¬Γ≲· Γ≲· })
  -- … | yes Γ≲· =
  --   yes (_ , _ , _ , ⊢new Γ≲·)
  -- infer' Γ (send e₁ e₂) U-Γ
  --   using Γ₁ ← Γ ↓ fvs e₁
  --   using U-Γ₁ ← Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ
  --   with infer' Γ₁ e₁ U-Γ₁
  -- … | no ¬⊢e₁ = no λ where
  --     (_ , _ , _ , ⊢send refl ⊢e₁' refl ⊢e₂' salg) → ¬⊢e₁ (_ , _ , _ , ⊢e₁')
  -- … | yes (t₁ , u₁ , ϕ₁ , ⊢e₁)
  --   using Γ₂ ← (Γ ↓ fvs e₂) %ᶜ u₁
  --   using U-Γ₂ ← Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ
  --   with check' Γ₂ e₂ (Chan _ (op[ ‼ ] t₁ ⍮ return)) U-Γ₂
  -- … | no ¬⊢e₂ = no λ where
  --     (_ , _ , _ , ⊢send refl ⊢e₁' refl ⊢e₂' salg) →
  --       case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
  --         (refl , refl , refl) → ¬⊢e₂ (_ , _ , ⊢e₂')
  -- … | yes (u₂ , ϕ₂ , ⊢e₂)
  --   with SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ unordered
  -- … | no ¬salg = no λ where
  --     (_ , _ , _ , ⊢send refl ⊢e₁' refl ⊢e₂' salg) →
  --       case ⊢↑-det U-Γ₁ ⊢e₁ ⊢e₁' of λ where
  --         (refl , refl , refl) →
  --           case ⊢↓-det U-Γ₂ ⊢e₂ ⊢e₂' of λ where
  --             (refl , refl) →
  --               ¬salg salg
  -- … | yes salg =
  --     yes (_ , _ , _ , ⊢send refl ⊢e₁ refl ⊢e₂ salg)
  -- infer' Γ (recv e) U-Γ
  --   with infer' Γ e U-Γ
  -- … | no ¬⊢e = no λ where
  --     (_ , _ , _ , ⊢recv ⊢e') → ¬⊢e (_ , _ , _ , ⊢e') 
  -- … | yes (t , u , ϕ , ⊢e)
  --   with RecvChan? t
  -- … | no t≢RecvChan = no λ where
  --     (_ , _ , _ , ⊢recv ⊢e') →
  --       case ⊢↑-det U-Γ ⊢e ⊢e' of λ where
  --         (refl , refl , refl) → t≢RecvChan (_ , refl)
  -- … | yes (t' , refl)
  --   = yes (_ , _ , _ , ⊢recv ⊢e)
  -- infer' Γ (drop e) U-Γ
  --   with infer' Γ e U-Γ
  -- … | no ¬⊢e = no λ where
  --     (_ , _ , _ , ⊢drop ⊢e') → ¬⊢e (_ , _ , _ , ⊢e')
  -- … | yes (t , u , ϕ , ⊢e)
  --   with t ≟ Chan _ return
  -- … | no t≢return = no λ where
  --     (_ , _ , _ , ⊢drop ⊢e') →
  --       case ⊢↑-det U-Γ ⊢e ⊢e' of λ where
  --         (refl , refl , refl) → t≢return refl
  -- … | yes refl =
  --   yes (_ , _ , _ , ⊢drop ⊢e)
  -- infer' Γ (close o e) U-Γ
  --   with infer' Γ e U-Γ
  -- … | no ¬⊢e = no λ where
  --     (_ , _ , _ , ⊢close ⊢e') → ¬⊢e (_ , _ , _ , ⊢e')
  -- … | yes (t , u , ϕ , ⊢e)
  --   with t ≟ Chan _ (end o)
  -- … | no t≢end = no λ where
  --     (_ , _ , _ , ⊢close ⊢e') →
  --       case ⊢↑-det U-Γ ⊢e ⊢e' of λ where
  --         (refl , refl , refl) → t≢end refl
  -- … | yes refl =
  --   yes (_ , _ , _ , ⊢close ⊢e)
  -- infer' Γ unit U-Γ
  --   with Γ ≲? ·
  -- … | no ¬Γ≲· = no (λ { (_ , _ , _ , ⊢unit Γ≲·) → ¬Γ≲· Γ≲· })
  -- … | yes Γ≲· =
  --   yes (_ , _ , _ , ⊢unit Γ≲·)
  -- infer' Γ (e `∶ t) U-Γ
  --   with check' Γ e t U-Γ
  -- … | no ¬⊢e = no (λ { (_ , _ , _ , ⊢∶ ⊢e) → ¬⊢e (_ , _ , ⊢e)})
  -- … | yes (u , ϕ , ⊢e) = yes (_ , _ , _ , ⊢∶ ⊢e)
  -- -- Checkable terms all work the same:
  -- infer' Γ (λ[ x ] x₁ ⇒ e) U-Γ = no λ { (t , u , ϕ , ()) }
  -- infer' Γ (& x) U-Γ = no λ { (t , u , ϕ , ()) }
  -- infer' Γ (`inj l e) U-Γ = no λ { (t , u , ϕ , ()) }

check : ∀ (e : Expr alg) (t : Type) →
  Dec (∃[ u ] ∃[ ϕ ] · ⊢ e ∶[ chk ] t ⍮ u ⍮ ϕ)
check e t = check' · e t Unique-[]

infer : ∀ (e : Expr alg) →
  Dec (∃[ t ] ∃[ u ] ∃[ ϕ ] · ⊢ e ∶[ inf ] t ⍮ u ⍮ ϕ)
infer e = infer' · e Unique-[]
