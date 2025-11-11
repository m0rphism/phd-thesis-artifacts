module BGV.Deterministic where

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

¬left→ϕ≡0? : ∀ C ϕ →
  (¬ LeftCtx C) × (ϕ ≡ 𝟏) ⊎
  ((¬ LeftCtx C) → ϕ ≡ 𝟎)
¬left→ϕ≡0? C 𝟎 = inj₂ (λ _ → refl)
¬left→ϕ≡0? C 𝟏 with left-ctx? C
… | yes C-left = inj₂ (λ ¬C-left → ⊥-elim (¬C-left C-left))
… | no ¬C-left = inj₁ (¬C-left , refl)

t≡Chan→used? : ∀ t (u : UsageMap) x →
  (∃[ b ] Σ[ s ∈ Session b ] t ≡ Chan b s × u x ≢ some (b , s)) ⊎
  (∀ b (s : Session b) → t ≡ Chan b s → u x ≡ some (b , s))
t≡Chan→used? t u x
  with Chan? t
… | no ¬t≡Chan = inj₂ λ b s t≡Chan → ⊥-elim (¬t≡Chan (b , s , t≡Chan))
… | yes (b , s , refl)
  with u x ≟ some (b , s)
… | yes ux-eq = inj₂ (λ { _ _ refl → ux-eq })
… | no ¬ux-eq = inj₁ (b , s , refl , ¬ux-eq)

Unique-ext : ∀ m Γ → Unique (dom Γ) → x ∉ dom Γ → Unique (dom (ext m Γ (x ∶ t)))
Unique-ext {x = x} {t = t} m Γ U-Γ x∉Γ =
  let eq = ≈ⁱ-trans (dom-ext m Γ (x ∶ t)) (≈ⁱ-comm (dom Γ) (dom (x ∶ t))) in
  Unique-≈ eq (Unique-∷ x∉Γ U-Γ)

≲-single-det : ∀ {Γ x t₁ t₂} →
  Unique (dom Γ) →
  Γ ≲ x ∶ t₁ →
  Γ ≲ x ∶ t₂ →
  t₁ ≡ t₂
≲-single-det {Γ = Γ} U-Γ p q =
  let x,t₁∈Γ = ≲-pres-∈' p (here refl) in
  let x,t₂∈Γ = ≲-pres-∈' q (here refl) in
  ∈binds-Unique Γ U-Γ x,t₁∈Γ x,t₂∈Γ

×? : ∀ t → Dec (∃[ t₁ ] ∃[ p ] ∃[ t₂ ] t ≡ t₁ ×[ p ] t₂)
×? (t₁ ×[ p ] t₂)      = yes (t₁ , p , t₂ , refl)
×? (Chan b x)          = no λ ()
×? (t + t₁)            = no λ ()
×? (t –[ x ⍮ x₁ ]→ t₁) = no λ ()
×? Unit                = no λ ()

+? : ∀ t → Dec (∃[ t₁ ] ∃[ t₂ ] t ≡ t₁ + t₂)
+? (t₁ + t₂)           = yes (t₁ , t₂ , refl)
+? (Chan b x)          = no λ ()
+? (t ×[ x ] t₁)       = no λ ()
+? (t –[ x ⍮ x₁ ]→ t₁) = no λ ()
+? Unit                = no λ ()

→? : ∀ t → Dec (∃[ t₁ ] ∃[ m ] ∃[ ϕ ] ∃[ t₂ ] t ≡ t₁ –[ m ⍮ ϕ ]→ t₂)
→? (t₁ –[ m ⍮ ϕ ]→ t₂) = yes (t₁ , m , ϕ , t₂ , refl)
→? (Chan b x)          = no λ ()
→? (t + t₁)            = no λ ()
→? (t ×[ x ] t₁)       = no λ ()
→? Unit                = no λ ()

ChanB? : ∀ t → Dec (∃[ s ] t ≡ Chan borrowed s)
ChanB? (Chan borrowed s)   = yes (s , refl)
ChanB? (Chan owned x)      = no λ ()
ChanB? (t + t₁)            = no λ ()
ChanB? (t ×[ x ] t₁)       = no λ ()
ChanB? (t –[ x ⍮ x₁ ]→ t₁) = no λ ()
ChanB? Unit                = no λ ()

RecvChan? : ∀ t → Dec (∃[ t' ] t ≡ Chan _ (op[ ⁈ ] t' ⍮ return))
RecvChan? (t + t₁)                                    = no λ ()
RecvChan? (t ×[ x ] t₁)                               = no λ ()
RecvChan? (t –[ x ⍮ x₁ ]→ t₁)                         = no λ ()
RecvChan? Unit                                        = no λ ()
RecvChan? (Chan b return)                             = no λ ()
RecvChan? (Chan b (end o))                            = no λ ()
RecvChan? (Chan b (choice[ o ] s₁ ⍮ s₂))              = no λ ()
RecvChan? (Chan b (op[ o ] t' ⍮ end o'))              = no λ ()
RecvChan? (Chan b (op[ o ] t' ⍮ (op[ o' ] t'' ⍮ s)))  = no λ ()
RecvChan? (Chan b (op[ o ] t' ⍮ choice[ p ] s₁ ⍮ s₂)) = no λ ()
RecvChan? (Chan b (op[ ‼ ] t' ⍮ return))              = no λ ()
RecvChan? (Chan b (op[ ⁈ ] t' ⍮ return))              = yes (t' , refl)

mutual
  ⊢↑-det :
    Unique (dom Γ) →
    Γ ⊢ e ∶[ inf ] t₁ ⍮ u₁ ⍮ ϕ₁ →
    Γ ⊢ e ∶[ inf ] t₂ ⍮ u₂ ⍮ ϕ₂ →
    t₁ ≡ t₂ × u₁ ≡ u₂ × ϕ₁ ≡ ϕ₂
  ⊢↑-det {Γ = Γ} U-Γ (⊢`-nochan Γ≲x∶t₁ ¬t₁≡chan) (⊢`-nochan Γ≲x∶t₂ ¬t₂≡chan)
    using t₁≡t₂ ← ≲-single-det U-Γ Γ≲x∶t₁ Γ≲x∶t₂
    = t₁≡t₂ , refl , refl 
  ⊢↑-det {Γ = Γ} U-Γ (⊢`-nochan Γ≲x∶t₁ ¬t₁≡chan) (⊢`-chan Γ≲x∶t₂ t₂≡chan)
    using t₁≡t₂ ← ≲-single-det U-Γ Γ≲x∶t₁ Γ≲x∶t₂
    = ⊥-elim (¬t₁≡chan _ _ (trans t₁≡t₂ t₂≡chan))
  ⊢↑-det {Γ = Γ} U-Γ (⊢`-chan Γ≲x∶t₁ t₁≡chan) (⊢`-nochan Γ≲x∶t₂ ¬t₂≡chan)
    using t₁≡t₂ ← ≲-single-det U-Γ Γ≲x∶t₁ Γ≲x∶t₂
    = ⊥-elim (¬t₂≡chan _ _ (trans (sym t₁≡t₂) t₁≡chan))
  ⊢↑-det {Γ = Γ} U-Γ (⊢`-chan Γ≲x∶t₁ refl) (⊢`-chan Γ≲x∶t₂ refl)
    using t₁≡t₂ ← ≲-single-det U-Γ Γ≲x∶t₁ Γ≲x∶t₂
    with refl ← t₁≡t₂
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢·≻ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·≻ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl --
    with ⊢↓-det (Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ) ⊢e₁₂ ⊢e₂₂
  … | refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢·𝟙 {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·𝟙 refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl --
    with ⊢↓-det (Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ) ⊢e₁₂ ⊢e₂₂
  … | refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢·∞ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·∞ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl --
    with ⊢↓-det (Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ) ⊢e₁₂ ⊢e₂₂
  … | refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢·≺ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·≺ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl --
    with ⊢↑-det (Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ) ⊢e₁₂ ⊢e₂₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢·≻ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·𝟙 refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | () , _ , _
  ⊢↑-det {Γ = Γ} U-Γ (⊢·≻ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·∞ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | () , _ , _
  ⊢↑-det {Γ = Γ} U-Γ (⊢·𝟙 {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·≻ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | () , _ , _
  ⊢↑-det {Γ = Γ} U-Γ (⊢·𝟙 {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·∞ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | () , _ , _
  ⊢↑-det {Γ = Γ} U-Γ (⊢·∞ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·≻ refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | () , _ , _
  ⊢↑-det {Γ = Γ} U-Γ (⊢·∞ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢·𝟙 refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | () , _ , _
  ⊢↑-det {Γ = Γ} U-Γ (⊢, {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁₁ refl ⊢e₁₂ eq-ϕ₁₂ alg₁)
                     (⊢, refl ⊢e₂₁ refl ⊢e₂₂ eq-ϕ₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl --
    with ⊢↑-det (Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ) ⊢e₁₂ ⊢e₂₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢let {x = x₁} {e₁ = e₁} {t₁ = t₁₁} {u₁ = u₁} {e₂ = e₂} {C = C₁}
                           x₁∉Γ refl ⊢e₁₁ Γ↓₁ refl left→₁ domC⊆domΓ₁ ⊢e₁₂ chan→used₁ alg₁)
                     (⊢let {C = C₂}
                           x₂∉Γ refl ⊢e₂₁ Γ↓₂ refl left→₂ domC⊆domΓ₂ ⊢e₂₂ chan→used₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl
    with trans (sym Γ↓₁) Γ↓₂
  … | eq
    with C₁⋯ρ₂≡C₂⋯ρ₂ , refl ← ProdP.,-injective (MaybeP.just-injective eq)
    using C₁≡C₂ ← C₁ ≡ C₂ by cong (_⋯ʳᶜ _) C₁⋯ρ₂≡C₂⋯ρ₂
    using U-C[·] ← Unique-⊆ domC⊆domΓ₁ U-Γ
    using d-C[·]-x ← λ where x x∈C[·] (here refl) → x₁∉Γ (⊆ⁱ→⊆ domC⊆domΓ₁ x∈C[·])
    using U-C[x∶t₁] ← Unique-≈ (dom-C C₁ (x₁ ∶ t₁₁)) $
                      Unique-++ U-C[·] (Unique-single x₁) d-C[·]-x
    with ⊢↑-det U-C[x∶t₁] ⊢e₁₂
                (subst (λ ■ → (■ [ _ ]) ⊢ _ ∶[ inf ] _ ⍮ _ ⍮ _) (sym C₁≡C₂) ⊢e₂₂)
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ
       (⊢let× {x = x} {y = y} {e₁ = e₁} {t₁ = t₁₁} {p = p} {t₂ = t₁₂} {u₁ = u₁}
              {C = C₁} {e₂ = e₂}
              x₁∉Γ y₁∉Γ x₁≢y₁ refl ⊢e₁₁ left→₁ Γ↓₁ refl domC⊆domΓ₁
              ⊢e₁₂ eq-chan-x₁ eq-chan-y₁ alg₁)
       (⊢let× {C = C₂}
              x₂∉Γ y₂∉Γ x₂≢y₂ refl ⊢e₂₁ left→₂ Γ↓₂ refl domC⊆domΓ₂
              ⊢e₂₂ eq-chan-x₂ eq-chan-y₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl
    with trans (sym Γ↓₁) Γ↓₂
  … | eq
    with C₁⋯ρ₂≡C₂⋯ρ₂ , refl ← ProdP.,-injective (MaybeP.just-injective eq)
    using C₁≡C₂ ← C₁ ≡ C₂ by cong (_⋯ʳᶜ _) C₁⋯ρ₂≡C₂⋯ρ₂
    using U-C[·] ← Unique-⊆ domC⊆domΓ₁ U-Γ
    using d-C[·]-xy ← λ where
      x x∈C[·] (here refl) → x₁∉Γ (⊆ⁱ→⊆ domC⊆domΓ₁ x∈C[·])
      x x∈C[·] (there (here refl)) → y₁∉Γ (⊆ⁱ→⊆ domC⊆domΓ₁ x∈C[·])
    using U-C[x∶t₁₁⸴y∶t₁₂] ←
      Unique-≈ (dom-C C₁ (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂)) $
      Unique-++ U-C[·]
                (Unique-∷ (λ { (here refl) → x₁≢y₁ refl }) (Unique-single y))
                d-C[·]-xy
    with ⊢↑-det U-C[x∶t₁₁⸴y∶t₁₂] ⊢e₁₂
                (subst (λ ■ → (■ [ _ ]) ⊢ _ ∶[ inf ] _ ⍮ _ ⍮ _) (sym C₁≡C₂) ⊢e₂₂)
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ
      (⊢case {x₁ = x₁} {x₂ = y₁} {e₁ = e₁} {t₁ = t₁₁} {t₂ = t₁₂} {u₁ = u₁}
             {C = C₁} {e₂₁ = e₂} {e₂₂ = e₃}
             x₁∉Γ y₁∉Γ x₁≢y₁ refl ⊢e₁₁ left→₁ Γ↓₁ refl domC⊆domΓ₁
             ⊢e₁₂ ⊢e₁₃ eq-u₁ eq-chan-x₁ eq-chan-y₁ alg₁)
      (⊢case {C = C₂}
             x₂∉Γ y₂∉Γ x₂≢y₂ refl ⊢e₂₁ left→₂ Γ↓₂ refl domC⊆domΓ₂
             ⊢e₂₂ ⊢e₂₃ eq-u₂ eq-chan-x₂ eq-chan-y₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl
    with trans (sym Γ↓₁) Γ↓₂
  … | eq
    with C₁⋯ρ₂≡C₂⋯ρ₂ , refl ← ProdP.,-injective (MaybeP.just-injective eq)
    using C₁≡C₂ ← C₁ ≡ C₂ by cong (_⋯ʳᶜ _) C₁⋯ρ₂≡C₂⋯ρ₂
    using U-C[·] ← Unique-⊆ domC⊆domΓ₁ U-Γ
    using d-C[·]-x ← λ where x x∈C[·] (here refl) → x₁∉Γ (⊆ⁱ→⊆ domC⊆domΓ₁ x∈C[·])
    using d-C[·]-y ← λ where y y∈C[·] (here refl) → y₁∉Γ (⊆ⁱ→⊆ domC⊆domΓ₁ y∈C[·])
    using U-C[x∶t₁₁] ← Unique-≈ (dom-C C₁ (x₁ ∶ t₁₁)) $
                       Unique-++ U-C[·] (Unique-single x₁) d-C[·]-x
    using U-C[y∶t₁₂] ← Unique-≈ (dom-C C₁ (y₁ ∶ t₁₂)) $
                       Unique-++ U-C[·] (Unique-single y₁) d-C[·]-y
    with ⊢↑-det U-C[x∶t₁₁] ⊢e₁₂
                (subst (λ ■ → (■ [ _ ]) ⊢ _ ∶[ inf ] _ ⍮ _ ⍮ _) (sym C₁≡C₂) ⊢e₂₂)
  … | refl , refl , refl
    with ⊢↑-det U-C[y∶t₁₂] ⊢e₁₃
                (subst (λ ■ → (■ [ _ ]) ⊢ _ ∶[ inf ] _ ⍮ _ ⍮ _) (sym C₁≡C₂) ⊢e₂₃)
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢unit Γ≲·₁) (⊢unit Γ≲·₂) =
    refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢spawn ⊢e₁) (⊢spawn ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢new Γ≲·₁) (⊢new Γ≲·₂) =
    refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢send {e₁ = e₁} {u₁ = u₁} {e₂ = e₂}
                            refl ⊢e₁₁ refl ⊢e₁₂ alg₁)
                     (⊢send refl ⊢e₂₁ refl ⊢e₂₂ alg₂)
    with ⊢↑-det (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢e₁₁ ⊢e₂₁
  … | refl , refl , refl --
    with ⊢↓-det (Unique-⊆ (domΓ₂⊆domΓ Γ e₂ u₁) U-Γ) ⊢e₁₂ ⊢e₂₂
  … | refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢recv ⊢e₁) (⊢recv ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢select ⊢e₁) (⊢select ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢branch ⊢e₁) (⊢branch ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢drop ⊢e₁) (⊢drop ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢close ⊢e₁) (⊢close ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl , refl
  ⊢↑-det {Γ = Γ} U-Γ (⊢∶ ⊢e₁) (⊢∶ ⊢e₂)
    with ⊢↓-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl
    = refl , refl , refl

  ⊢↓-det :
    Unique (dom Γ) →
    Γ ⊢ e ∶[ chk ] t ⍮ u₁ ⍮ ϕ₁ →
    Γ ⊢ e ∶[ chk ] t ⍮ u₂ ⍮ ϕ₂ →
    u₁ ≡ u₂ × ϕ₁ ≡ ϕ₂
  ⊢↓-det {Γ = Γ} U-Γ (⊢& Γ≲x∶t₁ refl refl) (⊢& Γ≲x∶t₂ refl refl)
    using t₁≡t₂ ← ≲-single-det U-Γ Γ≲x∶t₁ Γ≲x∶t₂
    with (refl , s₁++s₃≡s₂++s₄) ← Chan-injective t₁≡t₂
    = refl , refl
  ⊢↓-det {Γ = Γ} U-Γ (⊢λ {x = x} {m = m} {t₁ = t₁}
                         x∉Γ₁ ⊢e₁ ∞→unr₁ chan-used₁ ϕ₁⊑ϕ₂₁)
                     (⊢λ x∉Γ₂ ⊢e₂ ∞→unr₂ chan-used₂ ϕ₁⊑ϕ₂₂)
    with ⊢↓-det (Unique-ext m Γ U-Γ x∉Γ₁) ⊢e₁ ⊢e₂
  … | refl , refl
    = refl , refl
  ⊢↓-det {Γ = Γ} U-Γ (⊢chk-inf ⊢e₁) (⊢chk-inf ⊢e₂)
    with ⊢↑-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl , refl
    = refl , refl
  ⊢↓-det {Γ = Γ} U-Γ (⊢inj ⊢e₁) (⊢inj ⊢e₂)
    with ⊢↓-det U-Γ ⊢e₁ ⊢e₂
  … | refl , refl
    = refl , refl
