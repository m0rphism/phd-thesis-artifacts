module BGV.Soundness where

import Data.List.Properties as ListP
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
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open import BGV.Algorithmic
open import BGV.Context
open import BGV.Context.SyntacticSplit using (LeftCtx; cct-⸴₁; cct-⸴₂; cct-[])
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

x∉⋯ʳ : ∀ {dom-ρ ρ} Γ C u₂ Γ₁ u₁ (e₁ : Expr §) (e₂s : List (Expr §)) extra →
  (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  dom Γ₁ ⊆ dom Γ →
  dom (C [ · ]) ⊆ dom Γ →
  x ∈ extra →
  x ∉ dom Γ →
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvss e₂s) u₁ (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
               dom-ρ ρ Γ₁ (C [ · ]) in
  x ∉ dom ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
x∉⋯ʳ {x = x} {dom-ρ = dom-ρ} {ρ = ρ}
     Γ C u₂ Γ₁ u₁ e₁ e₂s extra ⊢ρ domΓ₁⊆domΓ domC⊆domΓ x∈extra x∉Γ x∈Γ' =
  let
    (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
      splits (fvs e₁) (fvss e₂s) u₁ (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
             dom-ρ ρ Γ₁ (C [ · ])

    ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ (C [ · ]) Γ e₁ e₂s u₁ extra domΓ₁⊆domΓ domC⊆domΓ ⊢ρ

    p : x ∈ dom ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ · ]) ++ dom (Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁)
    p = ≈ⁱ→⊆ (dom-C (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) (Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁)) x∈Γ'
  in
    case AnyP.++⁻ (dom ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ · ])) p of λ where
      (inj₁ x∈C⋯) →
        let
          x∈C⋯ : x ∈ map ρ₂ (dom ((C ⋯ᵘᶜ u₂) [ · ]))
          x∈C⋯ = subst (x ∈_)
                        (trans (cong dom (sym (⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂) · ρ₂)))
                              (⋯ʳ-dom ((C ⋯ᵘᶜ u₂) [ · ]) ρ₂ ))
                        x∈C⋯

          x∈ρ₂C : x ∈ map ρ₂ (dom (C [ · ]))
          x∈ρ₂C = subst (λ ■ → x ∈ map ρ₂ ■)
                        (trans (cong dom (sym (⋯ᵘ-dist-[] C · u₂)))
                                (⋯ᵘ-dom (C [ · ]) u₂))
                        x∈C⋯

          x' , x'∈C , ρ₂x'≡x = map-∈-inv ρ₂ (dom (C [ · ])) x∈ρ₂C
        in
        case x' ∈? dom-ρ₂ of λ where
          (yes x'∈dom-ρ₂) →
            let
              x∈ρ₂-dom-ρ₂ : x ∈ map ρ₂ dom-ρ₂
              x∈ρ₂-dom-ρ₂ = subst (_∈ map ρ₂ dom-ρ₂) ρ₂x'≡x (∈-map ρ₂ x'∈dom-ρ₂)
            in
              ⊢ʳ-ρxs⊎ys ⊢ρ₂ x x∈ρ₂-dom-ρ₂ (AnyP.++⁺ʳ (dom (C [ · ])) (AnyP.++⁺ˡ x∈extra))
          (no x'∉dom-ρ₂) →
            let
              ρ₂x'≡x' = ⊢ʳ-∉xs-id ⊢ρ₂ x'∉dom-ρ₂
              x≡x' = trans (sym ρ₂x'≡x) ρ₂x'≡x'
            in
              x∉Γ (domC⊆domΓ (subst (_∈ _) (sym x≡x') x'∈C))
      (inj₂ x∈Γ₁⋯) →
        let
          ⊢ρ₁-extra = ⊢ʳ-splits-ρ₁-extra Γ₁ (C [ · ]) Γ e₁ e₂s u₁ extra
                                            domΓ₁⊆domΓ domC⊆domΓ ⊢ρ
          x∈ρ₁Γ₁ : x ∈ map ρ₁ (dom (Γ₁ ⋯ᵘ u₁))
          x∈ρ₁Γ₁ = subst (x ∈_)
                          (⋯ʳ-dom (Γ₁ ⋯ᵘ u₁) ρ₁)
                          x∈Γ₁⋯

          x∈ρ₁Γ₁ : x ∈ map ρ₁ (dom Γ₁)
          x∈ρ₁Γ₁ = subst (x ∈_)
                          (cong (map ρ₁) (⋯ᵘ-dom Γ₁ u₁))
                          x∈ρ₁Γ₁

          x' , x'∈Γ₁ , ρ₁x'≡x = map-∈-inv ρ₁ (dom Γ₁) x∈ρ₁Γ₁
        in
        case x' ∈? dom-ρ₁ of λ where
          (yes x'∈dom-ρ₁) →
            let
              x∈ρ₁-dom-ρ₁ : x ∈ map ρ₁ dom-ρ₁
              x∈ρ₁-dom-ρ₁ = subst (_∈ map ρ₁ dom-ρ₁) ρ₁x'≡x (∈-map ρ₁ x'∈dom-ρ₁)
            in
              ⊢ʳ-ρxs⊎ys ⊢ρ₁-extra x x∈ρ₁-dom-ρ₁ (AnyP.++⁺ʳ (dom Γ₁) (AnyP.++⁺ˡ x∈extra))
          (no x'∉dom-ρ₁) →
            let
              ρ₁x'≡x' = ⊢ʳ-∉xs-id ⊢ρ₁ x'∉dom-ρ₁
              x≡x' = trans (sym ρ₁x'≡x) ρ₁x'≡x'
            in
              x∉Γ (domΓ₁⊆domΓ (subst (_∈ _) (sym x≡x') x'∈Γ₁))

--------------------------------------------------------------------------------

soundness' : ∀ {i} → (⊢e : Γ ⊢ e ∶[ i ] t ⍮ u ⍮ ϕ) → (dom-ρ : List Id) (ρ : Ren) →
  Disjoint (bvs e) (fvs e) →
  Unique (bvs e) →
  Unique (dom Γ) →
  (dom Γ ++ vars e) % dom-ρ ⊢ʳ ρ →
  dom-ρ ⊆ dom Γ →
  ((Γ ⋯ᵘ u) ⋯ʳ ρ) ⊢ (⟪ ⊢e ⟫ dom-ρ ρ) ∶ t ⍮ ϕ

soundness' (⊢`-nochan {x = x} {t = t} Γ≲x∶t not-chan) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢` (≲-single-⋯ʳ (subst (_≲ x ∶ t) (sym (⋯ᵘ-id _)) Γ≲x∶t))

soundness' (⊢`-chan Γ≲x∶t refl) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢` (≲-single-⋯ʳ (≲-single-⋯ᵘ Γ≲x∶t))

soundness' (⊢& Γ≲x∶t refl refl) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢` (≲-single-⋯ʳ (≲-single-⋯ᵘ Γ≲x∶t))

soundness' (⊢λ {x = x} {Γ = Γ} {m = m} {t₁ = t₁} {e = e} {u = u} x∉Γ ⊢e ∞→UnrΓ x∉uˡ ϕ₁⊑ϕ₂)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢λ (pp x∉Γ)
     (⊢wk ≲-refl ϕ₁⊑ϕ₂
        (subst (_⊢ ⟪ ⊢e ⟫ dom-ρ ρ ∶ _ ⍮ _)
                eq
                (soundness' ⊢e dom-ρ ρ bvs⊎fvs' (Unique-tail U-bvs)
                            (Unique-dom-ext m Γ t₁ x∉Γ U-Γ)
                            (⊢ʳ-≈-ys eq₂ ⊢ρ)
                            sub)))
     (λ m≡∞ → Unrᶜ-⋯ʳ (Γ ⋯ᵘ (u -ᵘ x)) ρ $
              Unrᶜ-⋯ᵘ Γ (u -ᵘ x) $
              ∞→UnrΓ m≡∞)
  where
    bvs⊎fvs' : Disjoint (bvs e) (fvs e)
    bvs⊎fvs' z z∈bvs z∈fvs =
      bvs⊎fvs z (there z∈bvs) (∈-ˡ⁺ z∈fvs (∈∉→≢ z∈bvs (Unique-∈-∷ x (bvs e) U-bvs)))
    sub : dom-ρ ⊆ dom (ext m Γ (x ∶ t₁))
    sub = let open ⊆-Reasoning in
          begin
            dom-ρ
          ⊆⟨ dom-ρ⊆domΓ ⟩
            dom Γ
          ⊆⟨ ⊆-++₁' ⟩
            dom Γ ++ dom (x ∶ t₁)
          ≈⟨ ≈ⁱ→≈ˡ (≈ⁱ-sym (dom-ext m Γ (x ∶ t₁))) ⟩
            dom (ext m Γ (x ∶ t₁))
          ∎
    pp : x ∉ dom Γ → x ∉ dom ((Γ ⋯ᵘ (u -ᵘ x)) ⋯ʳ ρ)
    pp x∉domΓ x∈domρΓ' =
      let x∈ρdomΓ' = subst (x ∈_) (⋯ʳ-dom (Γ ⋯ᵘ (u -ᵘ x)) ρ) x∈domρΓ' in
      let y , y∈domΓ' , ρy≡x = map-∈-inv ρ (dom (Γ ⋯ᵘ (u -ᵘ x))) x∈ρdomΓ' in
      let y∈domΓ = ⋯ᵘ-∈ Γ (u -ᵘ x) y∈domΓ' in
      case y ∈? dom-ρ of λ where
        (yes y∈dom-ρ) →
          let x∈ρdom-ρ = subst (_∈ _) ρy≡x $ ∈-map ρ y∈dom-ρ in
          ⊢ʳ-ρxs⊎ys ⊢ρ x x∈ρdom-ρ (AnyP.++⁺ʳ _ (here refl))
        (no ¬y∈dom-ρ) →
          let ρy≡y = ⊢ʳ-∉xs-id ⊢ρ ¬y∈dom-ρ in
          let x≡y = trans (sym ρy≡x) ρy≡y in
          x∉domΓ $ subst (_∈ _) (sym x≡y) y∈domΓ
    eq = let open ≡-Reasoning in
         begin
           (ext m Γ (x ∶ t₁) ⋯ᵘ u) ⋯ʳ ρ
         ≡⟨ cong (_⋯ʳ ρ) (⋯ᵘ-ext m Γ (x ∶ t₁) u) ⟩
           (ext m (Γ ⋯ᵘ u) ((x ∶ t₁) ⋯ᵘ u)) ⋯ʳ ρ
         ≡⟨ ⋯ʳ-ext m (Γ ⋯ᵘ u) ((x ∶ t₁) ⋯ᵘ u) ρ ⟩
           ext m ((Γ ⋯ᵘ u) ⋯ʳ ρ) (((x ∶ t₁) ⋯ᵘ u) ⋯ʳ ρ)
         ≡⟨ cong (λ ■ → ext m ((Γ ⋯ᵘ u) ⋯ʳ ρ) (■ ⋯ʳ ρ)) (⋯ᵘ-id' x t₁ u x∉uˡ) ⟩
           ext m ((Γ ⋯ᵘ u) ⋯ʳ ρ) ((x ∶ t₁) ⋯ʳ ρ)
         ≡⟨ cong (λ ■ → ext m (Γ ⋯ᵘ u ⋯ʳ ρ) (■ ∶ t₁))
                 (⊢ʳ-∉xs-id ⊢ρ (⊆-∉ dom-ρ⊆domΓ x∉Γ)) ⟩
           ext m ((Γ ⋯ᵘ u) ⋯ʳ ρ) (x ∶ t₁)
         ≡⟨ cong (λ ■ → ext m (■ ⋯ʳ ρ) (x ∶ t₁)) (sym (⋯ᵘ--ᵘ-∉ Γ u x∉Γ)) ⟩
           ext m ((Γ ⋯ᵘ (u -ᵘ x)) ⋯ʳ ρ) (x ∶ t₁)
         ∎
    eq₂ = let open ≈ˡ-Reasoning in
          begin
            dom (ext m Γ (x ∶ t₁)) ++ vars e
          ≈⟨ ≈ˡ-++ (≈ⁱ→≈ˡ (dom-ext m Γ (x ∶ t₁))) ≈ˡ-refl ⟩
            (dom Γ ++ dom (x ∶ t₁)) ++ vars e
          ≈⟨ ≈ˡ-assoc (dom Γ) (x ∷ []) (vars e)  ⟩
            dom Γ ++ x ∷ vars e
          ∎

soundness' {Γ = Γ}
           ⊢e@(⊢·≻ {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {ϕ = ϕ} {t₂ = t₂} {u₁ = u₁} {ϕ₁ = ϕ₁}
                   {Γ₂ = Γ₂} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let bvs⊎fvs₁ , bvs⊎fvs₂ = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂) bvs⊎fvs in
  let U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) U-bvs in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  let Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁) in
  let domΓ₁⊆domΓ = ↓-⊆ⁱdom Γ (fvs e₁) in
  let domΓ₂⊆domΓ = subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u₁)) (↓-⊆ⁱdom Γ (fvs e₂)) in
  let ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ Γ₂ Γ e₁ (e₂ ∷ []) u₁ [] (⊆ⁱ→⊆ domΓ₁⊆domΓ) (⊆ⁱ→⊆ domΓ₂⊆domΓ) ⊢ρ in
  let dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ in
  let ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ domΓ₁⊆domΓ U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ (Unique-⊆ domΓ₂⊆domΓ U-Γ) ⊢ρ₂ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₁'·e₂' : (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ⸴ ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)) ⊢
                 ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ t₂ ⍮ (ϕ₁ ⊔ 𝟎 ⊔ ϕ)
      ⊢e₁'·e₂' = ⊢· refl (er-≻ refl) ⊢e₁' ⊢e₂' in
  let ⊢e₁'·e₂'' = subst (_ ⊢ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ _ ⍮_)
                        (cong (_⊔ ϕ) (⊔-neutralʳ ϕ₁))
                        ⊢e₁'·e₂' in
  (((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ))
    by ⊢splits {Γ = Γ} _`·_ ⊢e₁ ⊢e₂ bvs⊎fvs₁ Γ₁⊆Γ (⊆ⁱ→⊆ domΓ₂⊆domΓ) U-Γ ⊢ρ
               (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ [] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁) Γ≲ ⊢e₁'·e₂''

soundness' {Γ = Γ}
           (⊢·≺ {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {u₁ = u₁} {ϕ₁ = ϕ₁}
                {Γ₂ = Γ₂} {e₂ = e₂} {ϕ = ϕ} {t₂ = t₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let bvs⊎fvs₁ , bvs⊎fvs₂ = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂) bvs⊎fvs in
  let U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) U-bvs in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ ▸ e₂)) dom-ρ ρ Γ₁ Γ₂ in
  let Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁) in
  let domΓ₁⊆domΓ = ↓-⊆ⁱdom Γ (fvs e₁) in
  let domΓ₂⊆domΓ = subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u₁)) (↓-⊆ⁱdom Γ (fvs e₂)) in
  let ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ Γ₂ Γ e₁ (e₂ ∷ []) u₁ [] (⊆ⁱ→⊆ domΓ₁⊆domΓ) (⊆ⁱ→⊆ domΓ₂⊆domΓ) ⊢ρ in
  let dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ in
  let ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ domΓ₁⊆domΓ U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ (Unique-⊆ domΓ₂⊆domΓ U-Γ) ⊢ρ₂ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂'·e₁' : (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ⸴ ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)) ⊢
                 ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ `· ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ)
      ⊢e₂'·e₁' = ⊢· refl (er-≺ refl) ⊢e₂' ⊢e₁' in
  (((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ `· ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ))
  by ⊢splits {Γ = Γ} (λ e₁ e₂ → e₂ `· e₁) ⊢e₁ ⊢e₂ bvs⊎fvs₁ Γ₁⊆Γ (⊆ⁱ→⊆ domΓ₂⊆domΓ) U-Γ ⊢ρ
             (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ [] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁) Γ≲ ⊢e₂'·e₁'

soundness' {Γ = Γ}
           (⊢·𝟙 {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {ϕ = ϕ} {t₂ = t₂} {u₁ = u₁} {ϕ₁ = ϕ₁}
                {Γ₂ = Γ₂} {e₂ = e₂} {u₂ = u₂} {ϕ₂ = ϕ₂} refl ⊢e₁ refl ⊢e₂ Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let bvs⊎fvs₁ , bvs⊎fvs₂ = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂) bvs⊎fvs in
  let U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) U-bvs in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  let Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁) in
  let domΓ₁⊆domΓ = ↓-⊆ⁱdom Γ (fvs e₁) in
  let domΓ₂⊆domΓ = subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u₁)) (↓-⊆ⁱdom Γ (fvs e₂)) in
  let ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ Γ₂ Γ e₁ (e₂ ∷ []) u₁ [] (⊆ⁱ→⊆ domΓ₁⊆domΓ) (⊆ⁱ→⊆ domΓ₂⊆domΓ) ⊢ρ in
  let dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ in
  let ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ domΓ₁⊆domΓ U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ (Unique-⊆ domΓ₂⊆domΓ U-Γ) ⊢ρ₂ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₁'·e₂' : (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ∥ ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)) ⊢
                 ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ)
      ⊢e₁'·e₂' = ⊢· refl er-𝟙 ⊢e₁' ⊢e₂' in
  (((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ))
    by ⊢splits {Γ = Γ} _`·_ ⊢e₁ ⊢e₂ bvs⊎fvs₁ Γ₁⊆Γ (⊆ⁱ→⊆ domΓ₂⊆domΓ) U-Γ ⊢ρ
               (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ [] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁) Γ≲ ⊢e₁'·e₂'

soundness' {Γ = Γ}
           (⊢·∞ {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {ϕ = ϕ} {t₂ = t₂} {u₁ = u₁} {ϕ₁ = ϕ₁}
                {Γ₂ = Γ₂} {e₂ = e₂} {u₂ = u₂} {ϕ₂ = ϕ₂} refl ⊢e₁ refl ⊢e₂ Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let bvs⊎fvs₁ , bvs⊎fvs₂ = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂) bvs⊎fvs in
  let U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) U-bvs in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  let Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁) in
  let domΓ₁⊆domΓ = ↓-⊆ⁱdom Γ (fvs e₁) in
  let domΓ₂⊆domΓ = subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u₁)) (↓-⊆ⁱdom Γ (fvs e₂)) in
  let ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ Γ₂ Γ e₁ (e₂ ∷ []) u₁ [] (⊆ⁱ→⊆ domΓ₁⊆domΓ) (⊆ⁱ→⊆ domΓ₂⊆domΓ) ⊢ρ in
  let dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ in
  let ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ domΓ₁⊆domΓ U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ (Unique-⊆ domΓ₂⊆domΓ U-Γ) ⊢ρ₂ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₁'·e₂' : (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ⸴ ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)) ⊢
                 ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ)
      ⊢e₁'·e₂' = ⊢· refl er-∞ ⊢e₁' ⊢e₂' in
  (((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ `· ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ))
    by ⊢splits {Γ = Γ} _`·_ ⊢e₁ ⊢e₂ bvs⊎fvs₁ Γ₁⊆Γ (⊆ⁱ→⊆ domΓ₂⊆domΓ) U-Γ ⊢ρ
               (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ [] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁) Γ≲ ⊢e₁'·e₂'

soundness' {Γ = Γ}
           (⊢, {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {u₁ = u₁} {ϕ₁ = ϕ₁}
               {Γ₂ = Γ₂} {e₂ = e₂} {t₂ = t₂} {u₂ = u₂} {ϕ₂ = ϕ₂} {p = p}
               refl ⊢e₁ refl ⊢e₂ ϕ-eq Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let bvs⊎fvs₁ , bvs⊎fvs₂ = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂) bvs⊎fvs in
  let U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) U-bvs in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  let Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁) in
  let domΓ₁⊆domΓ = ↓-⊆ⁱdom Γ (fvs e₁) in
  let domΓ₂⊆domΓ = subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u₁)) (↓-⊆ⁱdom Γ (fvs e₂)) in
  let ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ Γ₂ Γ e₁ (e₂ ∷ []) u₁ [] (⊆ⁱ→⊆ domΓ₁⊆domΓ) (⊆ⁱ→⊆ domΓ₂⊆domΓ) ⊢ρ in
  let dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ in
  let ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ domΓ₁⊆domΓ U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ (Unique-⊆ domΓ₂⊆domΓ U-Γ) ⊢ρ₂ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₁'·e₂' = ⊢, refl ⊢e₁' ⊢e₂' ϕ-eq in
  (((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ,[ p ] ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ (t₁ ×[ p ] t₂) ⍮ (ϕ₁ ⊔ ϕ₂))
    by ⊢splits {Γ = Γ} _,[ p ]_ ⊢e₁ ⊢e₂ bvs⊎fvs₁ Γ₁⊆Γ (⊆ⁱ→⊆ domΓ₂⊆domΓ) U-Γ ⊢ρ
               (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ [] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁) Γ≲ ⊢e₁'·e₂'

soundness' {Γ = Γ}
           (⊢let {x = x} {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {u₁ = u₁} {ϕ₁ = ϕ₁} {e₂ = e₂} {C = C}
                 {t₂ = t₂} {u₂ = u₂} {ϕ₂ = ϕ₂}
                 x∉Γ refl ⊢e₁ Γ⇓≡someC' refl C-left→ϕ₁≡𝟎 domC⊆domΓ ⊢e₂ t₁≡Chan→used Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let
    bvs⊎fvs₁ , bvs⊎fvs₂' = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂ -ˡ x) $
                           Disjoint-⊆₁ ⊆-∷ bvs⊎fvs
    bvs⊎fvs₂ : Disjoint (bvs e₂) (fvs e₂)
    bvs⊎fvs₂ z z∈bvs z∈fvs =
      bvs⊎fvs₂' z z∈bvs $ ∈-ˡ⁺ z∈fvs $ ∈∉→≢ z∈bvs $ proj₂ $
      ∉-++⁻ (bvs e₁) (bvs e₂) $ Unique-∈-∷ x (bvs e₁ ++ bvs e₂) U-bvs
    U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) $ Unique-tail U-bvs

    (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
      splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (let[ x ≔ e₁ ]in e₂))
             dom-ρ ρ Γ₁ (C [ · ])
    sisₐ = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁
    sis = sisₐ ⋯ˢⁱ ρ
    Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁)
    ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ (C [ · ]) Γ e₁ (e₂ ∷ []) u₁ List.[ x ]
                            (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) ⊢ρ
    eq =
      let open ≈ˡ-Reasoning in
      begin
        dom (C [ x ∶ t₁ ]) ++ vars e₂
      ≈⟨ (≈ˡ-++ (≈ⁱ→≈ˡ (dom-C C (x ∶ t₁))) ≈ˡ-refl) ⟩
        (dom (C [ · ]) ++ List.[ x ]) ++ vars e₂
      ≈⟨ ≈ˡ-assoc (dom (C [ · ])) List.[ x ] (vars e₂)  ⟩
        dom (C [ · ]) ++ x ∷ vars e₂
      ∎
    ⊢ρ₂' = ⊢ʳ-≈-ys eq ⊢ρ₂
    U-C[·] : Unique (dom (C [ · ]))
    U-C[·] = Unique-⊆ domC⊆domΓ U-Γ
    d-C[·]-x : Disjoint (dom (C [ · ])) List.[ x ]
    d-C[·]-x = λ where x x∈C[·] (here refl) → x∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
    U-C[x∶t₁] = Unique-≈ (dom-C C (x ∶ t₁)) $
                Unique-++ U-C[·] (Unique-single x) d-C[·]-x
    domC⊆domC[x∶t₁] : dom (C [ · ]) ⊆ dom (C [ x ∶ t₁ ])
    domC⊆domC[x∶t₁] =
      let open ⊆-Reasoning in
      begin
        dom (C [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        dom (C [ · ]) ++ dom (x ∶ t₁)
      ≈⟨ ≈ˡ-sym (≈ⁱ→≈ˡ (dom-C C (x ∶ t₁))) ⟩
        dom (C [ x ∶ t₁ ])
      ∎
    dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ
    ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _)
    ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ U-C[x∶t₁] ⊢ρ₂' (⊆-trans (∩ˡ-⊆₂ dom-ρ' _) domC⊆domC[x∶t₁])
    x∉dom-ρ₂ : x ∉ dom-ρ₂
    x∉dom-ρ₂ = ⊆-∉ (⊆-trans (∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))) (⊆ⁱ→⊆ domC⊆domΓ)) x∉Γ
    eq =
      let open ≡-Reasoning in
      begin
        (C [ x ∶ t₁ ]) ⋯ᵘ u₂ ⋯ʳ ρ₂
      ≡⟨ cong (_⋯ʳ ρ₂) (⋯ᵘ-dist-[] C  (x ∶ t₁) u₂) ⟩
        ((C ⋯ᵘᶜ u₂) [ (x ∶ t₁) ⋯ᵘ u₂ ]) ⋯ʳ ρ₂
      ≡⟨ ⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂) ((x ∶ t₁) ⋯ᵘ u₂) ρ₂ ⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ x ∶ t₁ ⋯ᵘ u₂ ⋯ʳ ρ₂ ]
      ≡⟨ cong (λ ■ → (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ ■ ⋯ʳ ρ₂ ]) (⋯ᵘ-used x t₁ u₂ t₁≡Chan→used) ⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ x ∶ t₁ ⋯ʳ ρ₂ ]
      ≡⟨ cong (λ ■ → (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ ■ ∶ t₁ ])
              (⊢ʳ-∉xs-id ⊢ρ₂ x∉dom-ρ₂) ⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ x ∶ t₁ ]
      ∎
    x∉Γ' : x ∉ dom ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
    x∉Γ' = x∉⋯ʳ Γ C u₂ Γ₁ u₁ e₁ (e₂ ∷ []) (x ∷ [])
                ⊢ρ (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) (here refl) x∉Γ
    C'-left→ϕ₁≡𝟎 : ¬ LeftCtx (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) → ϕ₁ ≡ 𝟎
    C'-left→ϕ₁≡𝟎 f = C-left→ϕ₁≡𝟎 λ C-left →
      f $ ⋯ʳᶜ-pres-LeftCtx (C ⋯ᵘᶜ u₂) ρ₂ $ ⋯ᵘᶜ-pres-LeftCtx C u₂ C-left
    ⊢let[x≔e₁']in[e₂'] : ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ]) ⊢
                         let[ x ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂)
    ⊢let[x≔e₁']in[e₂'] = ⊢let refl x∉Γ' ⊢e₁' C'-left→ϕ₁≡𝟎
                              (subst (_⊢ ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ _ ⍮ _) eq ⊢e₂')
    eq' : Γ ⋯ᵘ u₁ ·ᵘ (u₂ -ᵘ x) ≡ Γ ⋯ᵘ u₁ ·ᵘ u₂
    eq' = ⋯ᵘ-locally-eq Γ (u₁ ·ᵘ (u₂ -ᵘ x)) (u₁ ·ᵘ u₂) $
          ·ᵘ-locally-eq (dom Γ) u₁ (u₂ -ᵘ x) u₁ u₂ reflᵘ $
          -ᵘ-locally-eq-∉ u₂ x∉Γ
  in
  ((Γ ⋯ᵘ u₁ ·ᵘ (u₂ -ᵘ x) ⋯ʳ ρ) ⊢
   E (let[ x ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂))
    by subst 
        (λ ■ → (■ ⋯ʳ ρ) ⊢ E (let[ x ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂)
                        ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂))
        (sym eq') (
  ((Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ) ⊢
   E (let[ x ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂))
    by ⊢splits' {e₁ = e₁} {Γ = Γ} (e₂ ∷ []) (x ∷ []) ⊢e₁ bvs⊎fvs₁
                Γ₁⊆Γ (⊆ⁱ→⊆ domC⊆domΓ) U-Γ ⊢ρ
                (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ List.[ x ] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁)
                (SplitsAlg'-eqᵘ u₁ (u₂ -ᵘ x) u₂ e₁ (e₂ ∷ []) Γ Γ₁ C List.[ x ]
                                (⊆ⁱ→⊆ domC⊆domΓ) (-ᵘ-locally-eq-∉ u₂ x∉Γ) Γ≲)
                ⊢let[x≔e₁']in[e₂'])

soundness' {Γ = Γ}
           (⊢let× {x = x} {y = y} {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁₁} {p = p} {t₂ = t₁₂} {u₁ = u₁}
                  {ϕ₁ = ϕ₁} {C = C} {e₂ = e₂} {t = t₂} {u₂ = u₂} {ϕ₂ = ϕ₂}
                  x∉Γ y∉Γ x≢y refl ⊢e₁ C-left→ϕ₁≡𝟎 Γ⇓≡someC refl domC⊆domΓ ⊢e₂ t₁≡Chan→used t₂≡Chan→used Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let
    bvs⊎fvs₁ , bvs⊎fvs₂' = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂ -ˡ x -ˡ y) $
                           Disjoint-⊆₁ ⊆-∷ $ Disjoint-⊆₁ ⊆-∷ bvs⊎fvs
    bvs⊎fvs₂ : Disjoint (bvs e₂) (fvs e₂)
    bvs⊎fvs₂ z z∈bvs z∈fvs =
      bvs⊎fvs₂' z z∈bvs $
      ∈-ˡ⁺ (∈-ˡ⁺ z∈fvs $
            ∈∉→≢ z∈bvs $ proj₂ $ ∉-++⁻ (bvs e₁) (bvs e₂) $ ∉-tail $
            Unique-∈-∷ x (y ∷ bvs e₁ ++ bvs e₂) U-bvs)
           (∈∉→≢ z∈bvs $ proj₂ $ ∉-++⁻ (bvs e₁) (bvs e₂) $ 
            Unique-∈-∷ y (bvs e₁ ++ bvs e₂) (Unique-tail U-bvs))
    U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) $ Unique-tail $ Unique-tail U-bvs
    (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
      splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (let[ x `, y ≔ e₁ ]in e₂))
             dom-ρ ρ Γ₁ (C [ · ])
    sis = ((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ
    Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁)
    -- domC⊆domΓ : dom (C [ · ]) ⊆ dom Γ
    -- domC⊆domΓ = {!same problem as in fvs⊆Γ!}
    ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ (C [ · ]) Γ e₁ (e₂ ∷ []) u₁ (x ∷ y ∷ [])
                            (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) ⊢ρ
    eq =
      let open ≈ˡ-Reasoning in
      begin
        dom (C [ x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂ ]) ++ vars e₂
      ≈⟨ ≈ˡ-++ (≈ⁱ→≈ˡ (dom-C C (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂))) ≈ˡ-refl ⟩
        (dom (C [ · ]) ++ (x ∷ y ∷ [])) ++ vars e₂
      ≈⟨ ≈ˡ-assoc (dom (C [ · ])) (x ∷ y ∷ []) (vars e₂) ⟩
        dom (C [ · ]) ++ x ∷ y ∷ vars e₂
      ∎
    ⊢ρ₂' = ⊢ʳ-≈-ys eq ⊢ρ₂
    U-C[·] : Unique (dom (C [ · ]))
    U-C[·] = Unique-⊆ domC⊆domΓ U-Γ
    d-C[·]-xy : Disjoint (dom (C [ · ])) (x ∷ y ∷ [])
    d-C[·]-xy = λ where
      x x∈C[·] (here refl) → x∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
      x x∈C[·] (there (here refl)) → y∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
    U-C[x∶t₁₁⸴y∶t₁₂] =
      Unique-≈ (dom-C C (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂)) $
      Unique-++ U-C[·]
                (Unique-∷ (λ { (here refl) → x≢y refl }) (Unique-single y))
                d-C[·]-xy
    domC⊆domC[x∶t₁₁⸴y∶t₁₂] : dom (C [ · ]) ⊆ dom (C [ x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂ ])
    domC⊆domC[x∶t₁₁⸴y∶t₁₂] =
      let open ⊆-Reasoning in
      begin
        dom (C [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        dom (C [ · ]) ++ dom (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂)
      ≈⟨ ≈ˡ-sym (≈ⁱ→≈ˡ (dom-C C (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂))) ⟩
        dom (C [ x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂ ])
      ∎
    dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ
    ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _)
    ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ U-C[x∶t₁₁⸴y∶t₁₂] ⊢ρ₂' $
           ⊆-trans (∩ˡ-⊆₂ dom-ρ' _) domC⊆domC[x∶t₁₁⸴y∶t₁₂]
    x∉dom-ρ₂ : x ∉ dom-ρ₂
    x∉dom-ρ₂ = ⊆-∉ (⊆-trans (∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))) (⊆ⁱ→⊆ domC⊆domΓ)) x∉Γ
    y∉dom-ρ₂ : y ∉ dom-ρ₂
    y∉dom-ρ₂ = ⊆-∉ (⊆-trans (∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))) (⊆ⁱ→⊆ domC⊆domΓ)) y∉Γ
    eq =
      let open ≡-Reasoning in
      begin
        (C [ x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂ ]) ⋯ᵘ u₂ ⋯ʳ ρ₂
      ≡⟨ cong (_⋯ʳ ρ₂) (⋯ᵘ-dist-[] C  (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂) u₂) ⟩
        ((C ⋯ᵘᶜ u₂) [ (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂) ⋯ᵘ u₂ ]) ⋯ʳ ρ₂
      ≡⟨ ⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂) ((x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂) ⋯ᵘ u₂) ρ₂ ⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂) ⋯ᵘ u₂ ⋯ʳ ρ₂ ]
      ≡⟨⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ ((x ∶ t₁₁) ⋯ᵘ u₂ ⋯ʳ ρ₂) ⸴[ pmult→ord p ] ((y ∶ t₁₂) ⋯ᵘ u₂ ⋯ʳ ρ₂) ]
      ≡⟨ cong₂ (λ ■₁ ■₂ → (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ ■₁ ⋯ʳ ρ₂ ⸴[ pmult→ord p ] ■₂ ⋯ʳ ρ₂ ])
               (⋯ᵘ-used x t₁₁ u₂ t₁≡Chan→used)
               (⋯ᵘ-used y t₁₂ u₂ t₂≡Chan→used) ⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ (x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂) ⋯ʳ ρ₂ ]
      ≡⟨ cong₂ (λ ■₁ ■₂ → (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ ■₁ ∶ t₁₁ ⸴[ pmult→ord p ] ■₂ ∶ t₁₂ ])
              (⊢ʳ-∉xs-id ⊢ρ₂ x∉dom-ρ₂)
              (⊢ʳ-∉xs-id ⊢ρ₂ y∉dom-ρ₂) ⟩
        (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ x ∶ t₁₁ ⸴[ pmult→ord p ] y ∶ t₁₂ ]
      ∎
    x∉Γ' : x ∉ dom ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
    x∉Γ' = x∉⋯ʳ Γ C u₂ Γ₁ u₁ e₁ (e₂ ∷ []) (x ∷ y ∷ [])
                ⊢ρ (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) (here refl) x∉Γ
    y∉Γ' : y ∉ dom ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
    y∉Γ' = x∉⋯ʳ Γ C u₂ Γ₁ u₁ e₁ (e₂ ∷ []) (x ∷ y ∷ [])
                ⊢ρ (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) (there (here refl)) y∉Γ
    C'-left→ϕ₁≡𝟎 : ¬ LeftCtx (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) → ϕ₁ ≡ 𝟎
    C'-left→ϕ₁≡𝟎 f = C-left→ϕ₁≡𝟎 λ C-left →
      f $ ⋯ʳᶜ-pres-LeftCtx (C ⋯ᵘᶜ u₂) ρ₂ $ ⋯ᵘᶜ-pres-LeftCtx C u₂ C-left
    ⊢let[x,y≔e₁']in[e₂'] : ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ]) ⊢
                           let[ x `, y ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶
                           t₂ ⍮ (ϕ₁ ⊔ ϕ₂)
    ⊢let[x,y≔e₁']in[e₂'] = ⊢let× refl x∉Γ' y∉Γ' x≢y ⊢e₁' C'-left→ϕ₁≡𝟎
                                 (subst (_⊢ ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ∶ _ ⍮ _) eq ⊢e₂')
    eq' : Γ ⋯ᵘ u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y) ≡ Γ ⋯ᵘ u₁ ·ᵘ u₂
    eq' = ⋯ᵘ-locally-eq Γ (u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y)) (u₁ ·ᵘ u₂) $
          ·ᵘ-locally-eq (dom Γ) u₁ (u₂ -ᵘ x -ᵘ y) u₁ u₂ reflᵘ $
          transᵘ (-ᵘ-locally-eq-∉ (u₂ -ᵘ x) y∉Γ)
                 (-ᵘ-locally-eq-∉ u₂ x∉Γ)
  in
  ((Γ ⋯ᵘ u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y) ⋯ʳ ρ) ⊢
   E (let[ x `, y ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂))
    by subst 
        (λ ■ → (■ ⋯ʳ ρ) ⊢ E (let[ x `, y ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂)
                        ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂))
        (sym eq') (
  ((Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ) ⊢
   E (let[ x `, y ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t₂ ⍮ (ϕ₁ ⊔ ϕ₂))
    by ⊢splits' {e₁ = e₁} {Γ = Γ} (e₂ ∷ []) (x ∷ y ∷ []) ⊢e₁ bvs⊎fvs₁
                Γ₁⊆Γ (⊆ⁱ→⊆ domC⊆domΓ) U-Γ ⊢ρ
                (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ (x ∷ y ∷ []) bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁)
                (SplitsAlg'-eqᵘ u₁ (u₂ -ᵘ x -ᵘ y) u₂ e₁ (e₂ ∷ []) Γ Γ₁ C (x ∷ y ∷ []) (⊆ⁱ→⊆ domC⊆domΓ)
                  (transᵘ (-ᵘ-locally-eq-∉ (u₂ -ᵘ x) y∉Γ)
                          (-ᵘ-locally-eq-∉ u₂ x∉Γ))
                  Γ≲)
                ⊢let[x,y≔e₁']in[e₂'])

soundness' (⊢inj ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢inj (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' {Γ = Γ}
           (⊢case {x₁ = x} {x₂ = y} {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁₁} {t₂ = t₁₂} {u₁ = u₁}
                  {ϕ₁ = ϕ₁} {C = C} {e₂₁ = e₂₁} {e₂₂ = e₂₂} {t = t₂}
                  {u₂₁ = u₂₁} {ϕ₂ = ϕ₂} {u₂₂ = u₂₂} {ϕ₃ = ϕ₃}
                  x∉Γ y∉Γ x≢y refl ⊢e₁ C-left→ϕ₁≡𝟎 Γ⇓≡someC refl domC⊆domΓ ⊢e₂₁ ⊢e₂₂
                  u₂₁-x≡u₂₂-y t₁≡Chan→used t₂≡Chan→used Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let
    bvs⊎fvs₁ , bvs⊎fvs₂' = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂₁ ++ bvs e₂₂)
                                         (fvs e₁) ((fvs e₂₁ -ˡ x) ++ (fvs e₂₂ -ˡ y)) $
                           Disjoint-⊆₁ ⊆-∷ $ Disjoint-⊆₁ ⊆-∷ bvs⊎fvs
    bvs⊎fvs₂₁' , bvs⊎fvs₂₂' = Disjoint-++⁻⁻ (bvs e₂₁) (bvs e₂₂) (fvs e₂₁ -ˡ x) (fvs e₂₂ -ˡ y)
                                            bvs⊎fvs₂'
    bvs⊎fvs₂₁ : Disjoint (bvs e₂₁) (fvs e₂₁)
    bvs⊎fvs₂₁ z z∈bvs z∈fvs =
      bvs⊎fvs₂₁' z z∈bvs $
      ∈-ˡ⁺ z∈fvs
           (∈∉→≢ z∈bvs (proj₁ $ ∉-++⁻ (bvs e₂₁) (bvs e₂₂) $
                        proj₂ $ ∉-++⁻ (bvs e₁) (bvs e₂₁ ++ bvs e₂₂) $ ∉-tail $
                        Unique-∈-∷ x (y ∷ bvs e₁ ++ bvs e₂₁ ++ bvs e₂₂) U-bvs))
    bvs⊎fvs₂₂ : Disjoint (bvs e₂₂) (fvs e₂₂)
    bvs⊎fvs₂₂ z z∈bvs z∈fvs =
      bvs⊎fvs₂₂' z z∈bvs $
      ∈-ˡ⁺ z∈fvs
           (∈∉→≢ z∈bvs (proj₂ $ ∉-++⁻ (bvs e₂₁) (bvs e₂₂) $
                        proj₂ $ ∉-++⁻ (bvs e₁) (bvs e₂₁ ++ bvs e₂₂) $
                        Unique-∈-∷ y (bvs e₁ ++ bvs e₂₁ ++ bvs e₂₂) (Unique-tail U-bvs)))
    U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂₁ ++ bvs e₂₂) $
                          Unique-tail $ Unique-tail U-bvs
    U-bvs₂₁ , U-bvs₂₂ , _ = Unique-++⁻ (bvs e₂₁) (bvs e₂₂) $ U-bvs₂
    (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
      splits (fvs e₁) (fvs e₂₁ ++ fvs e₂₂) u₁
             (dom Γ ++ vars (case e₁ of[ x ⇒ e₂₁ ⍮ y ⇒ e₂₂ ]))
             dom-ρ ρ Γ₁ (C [ · ])
    sis = ((fvs e₁ ∩ˡ (fvs e₂₁ ++ fvs e₂₂)) ↓ᵘ u₁) ⋯ˢⁱ ρ
    Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁)
    ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ (C [ · ]) Γ e₁ (e₂₁ ∷ e₂₂ ∷ []) u₁ (x ∷ y ∷ [])
                               (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) ⊢ρ
    eq₁ =
      let open ≈ˡ-Reasoning in
      begin
        dom (C [ x ∶ t₁₁ ]) ++ vars e₂₁
      ≈⟨ (≈ˡ-++ (≈ⁱ→≈ˡ (dom-C C (x ∶ t₁₁))) ≈ˡ-refl) ⟩
        (dom (C [ · ]) ++ List.[ x ]) ++ vars e₂₁
      ≈⟨ ≈ˡ-assoc (dom (C [ · ])) List.[ x ] (vars e₂₁)  ⟩
        dom (C [ · ]) ++ x ∷ vars e₂₁
      ∎
    eq₂ =
      let open ≈ˡ-Reasoning in
      begin
        dom (C [ y ∶ t₁₂ ]) ++ vars e₂₂
      ≈⟨ (≈ˡ-++ (≈ⁱ→≈ˡ (dom-C C (y ∶ t₁₂))) ≈ˡ-refl) ⟩
        (dom (C [ · ]) ++ List.[ y ]) ++ vars e₂₂
      ≈⟨ ≈ˡ-assoc (dom (C [ · ])) List.[ y ] (vars e₂₂)  ⟩
        dom (C [ · ]) ++ y ∷ vars e₂₂
      ∎
    -- ⊢ρ₂₁ = ⊢ʳ-≈-ys eq₁ {!⊢ρ₂!}
    ⊢ρ₂₁-sub₁ : dom (C [ x ∶ t₁₁ ]) ++ vars e₂₁ ⊆
                dom (C [ · ]) ++ x ∷ y ∷ vars e₂₁ ++ vars e₂₂
    ⊢ρ₂₁-sub₁ =
      let open ⊆-Reasoning in
      begin
        dom (C [ x ∶ t₁₁ ]) ++ vars e₂₁
      ≈⟨ eq₁ ⟩
        dom (C [ · ]) ++ List.[ x ] ++ vars e₂₁
      ⊆⟨ ⊆-++ (⊆-refl {xs = dom(C [ · ])})
              (⊆-++ (⊆-refl {xs = x ∷ []})
                    (⊆-trans (⊆-++₂' (y ∷ [])) ⊆-++₁')) ⟩
        dom (C [ · ]) ++ x ∷ y ∷ vars e₂₁ ++ vars e₂₂
      ∎
    ⊢ρ₂₂-sub₁ : dom (C [ y ∶ t₁₂ ]) ++ vars e₂₂ ⊆
                dom (C [ · ]) ++ x ∷ y ∷ vars e₂₁ ++ vars e₂₂
    ⊢ρ₂₂-sub₁ =
      let open ⊆-Reasoning in
      begin
        dom (C [ y ∶ t₁₂ ]) ++ vars e₂₂
      ≈⟨ eq₂ ⟩
        dom (C [ · ]) ++ List.[ y ] ++ vars e₂₂
      ⊆⟨ ⊆-++ (⊆-refl {xs = dom(C [ · ])})
              (⊆-trans (⊆-++₂' (x ∷ []))
                       (⊆-++ (⊆-refl {xs = x ∷ y ∷ []})
                             (⊆-++₂' (vars e₂₁)))) ⟩
        dom (C [ · ]) ++ x ∷ y ∷ vars e₂₁ ++ vars e₂₂
      ∎
    ⊢ρ₂₁-sub₂ : (map proj₁ sis ++ dom-ρ) ∩ˡ dom (C [ · ]) ⊆ dom (C [ x ∶ t₁₁ ]) ++ vars e₂₁
    ⊢ρ₂₁-sub₂ =
      let open ⊆-Reasoning in
      begin
        (map proj₁ sis ++ dom-ρ) ∩ˡ dom (C [ · ]) 
      ⊆⟨ ∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))   ⟩
        dom (C [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        dom (C [ · ]) ++ List.[ x ] ++ vars e₂₁
      ≈⟨ ≈ˡ-sym eq₁ ⟩
        dom (C [ x ∶ t₁₁ ]) ++ vars e₂₁
      ∎
    ⊢ρ₂₂-sub₂ : (map proj₁ sis ++ dom-ρ) ∩ˡ dom (C [ · ]) ⊆ dom (C [ y ∶ t₁₂ ]) ++ vars e₂₂
    ⊢ρ₂₂-sub₂ =
      let open ⊆-Reasoning in
      begin
        (map proj₁ sis ++ dom-ρ) ∩ˡ dom (C [ · ]) 
      ⊆⟨ ∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))   ⟩
        dom (C [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        dom (C [ · ]) ++ List.[ y ] ++ vars e₂₂
      ≈⟨ ≈ˡ-sym eq₂ ⟩
        dom (C [ y ∶ t₁₂ ]) ++ vars e₂₂
      ∎
    ⊢ρ₂₁ = ⊢ʳ-⊆-ys ⊢ρ₂₁-sub₁ ⊢ρ₂₁-sub₂ ⊢ρ₂
    ⊢ρ₂₂ = ⊢ʳ-⊆-ys ⊢ρ₂₂-sub₁ ⊢ρ₂₂-sub₂ ⊢ρ₂
    U-C[·] : Unique (dom (C [ · ]))
    U-C[·] = Unique-⊆ domC⊆domΓ U-Γ
    d-C[·]-x : Disjoint (dom (C [ · ])) List.[ x ]
    d-C[·]-x = λ where x x∈C[·] (here refl) → x∉Γ (⊆ⁱ→⊆ domC⊆domΓ x∈C[·])
    d-C[·]-y : Disjoint (dom (C [ · ])) List.[ y ]
    d-C[·]-y = λ where y y∈C[·] (here refl) → y∉Γ (⊆ⁱ→⊆ domC⊆domΓ y∈C[·])
    U-C[x∶t₁₁] = Unique-≈ (dom-C C (x ∶ t₁₁)) $
                 Unique-++ U-C[·] (Unique-single x) d-C[·]-x
    U-C[y∶t₁₂] = Unique-≈ (dom-C C (y ∶ t₁₂)) $
                 Unique-++ U-C[·] (Unique-single y) d-C[·]-y
    domC⊆domC[x∶t₁₁] : dom (C [ · ]) ⊆ dom (C [ x ∶ t₁₁ ])
    domC⊆domC[x∶t₁₁] =
      let open ⊆-Reasoning in
      begin
        dom (C [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        dom (C [ · ]) ++ dom (x ∶ t₁₁)
      ≈⟨ ≈ˡ-sym (≈ⁱ→≈ˡ (dom-C C (x ∶ t₁₁))) ⟩
        dom (C [ x ∶ t₁₁ ])
      ∎
    domC⊆domC[y∶t₁₂] : dom (C [ · ]) ⊆ dom (C [ y ∶ t₁₂ ])
    domC⊆domC[y∶t₁₂] =
      let open ⊆-Reasoning in
      begin
        dom (C [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        dom (C [ · ]) ++ dom (y ∶ t₁₂)
      ≈⟨ ≈ˡ-sym (≈ⁱ→≈ˡ (dom-C C (y ∶ t₁₂))) ⟩
        dom (C [ y ∶ t₁₂ ])
      ∎
    dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ (fvs e₂₁ ++ fvs e₂₂)) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ
    ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ (domΓ₁⊆domΓ Γ e₁) U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _)
    ⊢e₂₁' = soundness' ⊢e₂₁ dom-ρ₂ ρ₂ bvs⊎fvs₂₁ U-bvs₂₁ U-C[x∶t₁₁] ⊢ρ₂₁
              (⊆-trans (∩ˡ-⊆₂ dom-ρ' _) domC⊆domC[x∶t₁₁])
    ⊢e₂₂' = soundness' ⊢e₂₂ dom-ρ₂ ρ₂ bvs⊎fvs₂₂ U-bvs₂₂ U-C[y∶t₁₂] ⊢ρ₂₂
              (⊆-trans (∩ˡ-⊆₂ dom-ρ' _) domC⊆domC[y∶t₁₂])
    x∉dom-ρ₂ : x ∉ dom-ρ₂
    x∉dom-ρ₂ = ⊆-∉ (⊆-trans (∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))) (⊆ⁱ→⊆ domC⊆domΓ)) x∉Γ
    y∉dom-ρ₂ : y ∉ dom-ρ₂
    y∉dom-ρ₂ = ⊆-∉ (⊆-trans (∩ˡ-⊆₂ (map proj₁ sis ++ dom-ρ) (dom (C [ · ]))) (⊆ⁱ→⊆ domC⊆domΓ)) y∉Γ
    eq₁ =
      let open ≡-Reasoning in
      begin
        (C [ x ∶ t₁₁ ]) ⋯ᵘ u₂₁ ⋯ʳ ρ₂
      ≡⟨ cong (_⋯ʳ ρ₂) (⋯ᵘ-dist-[] C (x ∶ t₁₁) u₂₁) ⟩
        ((C ⋯ᵘᶜ u₂₁) [ (x ∶ t₁₁) ⋯ᵘ u₂₁ ]) ⋯ʳ ρ₂
      ≡⟨ ⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂₁) ((x ∶ t₁₁) ⋯ᵘ u₂₁) ρ₂ ⟩
        (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ x ∶ t₁₁ ⋯ᵘ u₂₁ ⋯ʳ ρ₂ ]
      ≡⟨ cong (λ ■ → (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ ■ ⋯ʳ ρ₂ ]) (⋯ᵘ-used x t₁₁ u₂₁ t₁≡Chan→used) ⟩
        (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ x ∶ t₁₁ ⋯ʳ ρ₂ ]
      ≡⟨ cong (λ ■ → (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ ■ ∶ t₁₁ ])
              (⊢ʳ-∉xs-id ⊢ρ₂ x∉dom-ρ₂) ⟩
        (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ x ∶ t₁₁ ]
      ∎
    eq₂ =
      let open ≡-Reasoning in
      begin
        (C [ y ∶ t₁₂ ]) ⋯ᵘ u₂₂ ⋯ʳ ρ₂
      ≡⟨ cong (_⋯ʳ ρ₂) (⋯ᵘ-dist-[] C (y ∶ t₁₂) u₂₂) ⟩
        ((C ⋯ᵘᶜ u₂₂) [ (y ∶ t₁₂) ⋯ᵘ u₂₂ ]) ⋯ʳ ρ₂
      ≡⟨ ⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂₂) ((y ∶ t₁₂) ⋯ᵘ u₂₂) ρ₂ ⟩
        (C ⋯ᵘᶜ u₂₂ ⋯ʳᶜ ρ₂) [ y ∶ t₁₂ ⋯ᵘ u₂₂ ⋯ʳ ρ₂ ]
      ≡⟨ cong (λ ■ → (C ⋯ᵘᶜ u₂₂ ⋯ʳᶜ ρ₂) [ ■ ⋯ʳ ρ₂ ]) (⋯ᵘ-used y t₁₂ u₂₂ t₂≡Chan→used) ⟩
        (C ⋯ᵘᶜ u₂₂ ⋯ʳᶜ ρ₂) [ y ∶ t₁₂ ⋯ʳ ρ₂ ]
      ≡⟨ cong (λ ■ → (C ⋯ᵘᶜ u₂₂ ⋯ʳᶜ ρ₂) [ ■ ∶ t₁₂ ])
              (⊢ʳ-∉xs-id ⊢ρ₂ y∉dom-ρ₂) ⟩
        (C ⋯ᵘᶜ u₂₂ ⋯ʳᶜ ρ₂) [ y ∶ t₁₂ ]
      ∎
    x∉Γ' : x ∉ dom ((C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
    x∉Γ' = x∉⋯ʳ Γ C u₂₁ Γ₁ u₁ e₁ (e₂₁ ∷ e₂₂ ∷ []) (x ∷ y ∷ [])
                ⊢ρ (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) (here refl) x∉Γ
    y∉Γ' : y ∉ dom ((C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
    y∉Γ' = x∉⋯ʳ Γ C u₂₁ Γ₁ u₁ e₁ (e₂₁ ∷ e₂₂ ∷ []) (x ∷ y ∷ [])
                ⊢ρ (⊆ⁱ→⊆ (domΓ₁⊆domΓ Γ e₁)) (⊆ⁱ→⊆ domC⊆domΓ) (there (here refl)) y∉Γ
    eq₂' =
      let open ≡-Reasoning in
      begin
        (C [ y ∶ t₁₂ ]) ⋯ᵘ u₂₂ ⋯ʳ ρ₂
      ≡⟨ eq₂ ⟩
        (C ⋯ᵘᶜ u₂₂ ⋯ʳᶜ ρ₂) [ y ∶ t₁₂ ]
      ≡⟨ cong (λ ■ → (■ ⋯ʳᶜ ρ₂) [ y ∶ t₁₂ ])
              (⋯ᵘᶜ-locally-eq C u₂₂ u₂₁
                (transᵘ (symᵘ (-ᵘ-locally-eq-∉ u₂₂ (⊆-∉ (⊆ⁱ→⊆ domC⊆domΓ) y∉Γ)))
                (transᵘ (LocallyEqᵘ-⊆ (⊆ⁱ→⊆ domC⊆domΓ) (symᵘ u₂₁-x≡u₂₂-y))
                        (-ᵘ-locally-eq-∉ u₂₁ (⊆-∉ (⊆ⁱ→⊆ domC⊆domΓ) x∉Γ))))) ⟩
        (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ y ∶ t₁₂ ]
      ∎
    u₂ = u₂₁ -ᵘ x
    C'-left→ϕ₁≡𝟎 : ¬ LeftCtx (C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) → ϕ₁ ≡ 𝟎
    C'-left→ϕ₁≡𝟎 f = C-left→ϕ₁≡𝟎 λ C-left →
      f $ ⋯ʳᶜ-pres-LeftCtx (C ⋯ᵘᶜ u₂₁) ρ₂ $ ⋯ᵘᶜ-pres-LeftCtx C u₂₁ C-left
    ⊢case' : ((C ⋯ᵘᶜ u₂₁ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ]) ⊢
             case ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ of[ x ⇒ ⟪ ⊢e₂₁ ⟫ dom-ρ₂ ρ₂ ⍮ y ⇒ ⟪ ⊢e₂₂ ⟫ dom-ρ₂ ρ₂ ] ∶
             t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ₃)
    ⊢case' = ⊢case refl x∉Γ' y∉Γ' x≢y ⊢e₁' C'-left→ϕ₁≡𝟎
                   (subst (_⊢ ⟪ ⊢e₂₁ ⟫ dom-ρ₂ ρ₂ ∶ _ ⍮ _) eq₁ ⊢e₂₁')
                   (subst (_⊢ ⟪ ⊢e₂₂ ⟫ dom-ρ₂ ρ₂ ∶ _ ⍮ _) eq₂' ⊢e₂₂')
    eq' : Γ ⋯ᵘ u₁ ·ᵘ (u₂₁ -ᵘ x) ≡ Γ ⋯ᵘ u₁ ·ᵘ u₂₁
    eq' = ⋯ᵘ-locally-eq Γ (u₁ ·ᵘ (u₂₁ -ᵘ x)) (u₁ ·ᵘ u₂₁) $
          ·ᵘ-locally-eq (dom Γ) u₁ (u₂₁ -ᵘ x) u₁ u₂₁ reflᵘ $
          -ᵘ-locally-eq-∉ u₂₁ x∉Γ
  in
  ((Γ ⋯ᵘ u₁ ·ᵘ (u₂₁ -ᵘ x) ⋯ʳ ρ) ⊢
   E (case ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ of[ x ⇒ ⟪ ⊢e₂₁ ⟫ dom-ρ₂ ρ₂ ⍮ y ⇒ ⟪ ⊢e₂₂ ⟫ dom-ρ₂ ρ₂ ]) ∶
   t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ₃))
    by subst 
        (λ ■ → (■ ⋯ʳ ρ) ⊢ E (case ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ of[ x ⇒ ⟪ ⊢e₂₁ ⟫ dom-ρ₂ ρ₂
                                                      ⍮ y ⇒ ⟪ ⊢e₂₂ ⟫ dom-ρ₂ ρ₂ ]) ∶
   t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ₃))
        (sym eq') (
  ((Γ ⋯ᵘ u₁ ·ᵘ u₂₁ ⋯ʳ ρ) ⊢
   E (case ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ of[ x ⇒ ⟪ ⊢e₂₁ ⟫ dom-ρ₂ ρ₂ ⍮ y ⇒ ⟪ ⊢e₂₂ ⟫ dom-ρ₂ ρ₂ ]) ∶
   t₂ ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ₃))
    by ⊢splits' {e₁ = e₁} {Γ = Γ} (e₂₁ ∷ e₂₂ ∷ []) (x ∷ y ∷ []) ⊢e₁ bvs⊎fvs₁ Γ₁⊆Γ
                (⊆ⁱ→⊆ domC⊆domΓ) U-Γ ⊢ρ
                (⊧ˢ-split Γ e₁ (e₂₁ ∷ e₂₂ ∷ []) u₁ u₂₁ (x ∷ y ∷ []) bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁)
                (SplitsAlg'-eqᵘ u₁ (u₂₁ -ᵘ x) u₂₁ e₁ (e₂₁ ∷ e₂₂ ∷ []) Γ Γ₁ C (x ∷ y ∷ [])
                                (⊆ⁱ→⊆ domC⊆domΓ) (-ᵘ-locally-eq-∉ u₂₁ x∉Γ) Γ≲)
                ⊢case')

soundness' (⊢unit Γ≲·) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢unit (≲-⋯ʳ ρ (≲-⋯ᵘ ∅ᵘ Γ≲·))

soundness' (⊢spawn ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢spawn (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' (⊢new Γ≲·) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢new (≲-⋯ʳ ρ (≲-⋯ᵘ ∅ᵘ Γ≲·))

soundness' {Γ = Γ}
           (⊢send {Γ₁ = Γ₁} {e₁ = e₁} {t₁ = t₁} {u₁ = u₁} {ϕ₁ = ϕ₁}
                  {Γ₂ = Γ₂} {e₂ = e₂} {u₂ = u₂} {ϕ₂ = ϕ₂} refl ⊢e₁ refl ⊢e₂ Γ≲)
           dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  let bvs⊎fvs₁ , bvs⊎fvs₂ = Disjoint-++⁻⁻ (bvs e₁) (bvs e₂) (fvs e₁) (fvs e₂) bvs⊎fvs in
  let U-bvs₁ , U-bvs₂ , _ = Unique-++⁻ (bvs e₁) (bvs e₂) U-bvs in
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  let Γ₁⊆Γ = ↓-⊆ Γ (fvs e₁) in
  let domΓ₁⊆domΓ = ↓-⊆ⁱdom Γ (fvs e₁) in
  let domΓ₂⊆domΓ = subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u₁)) (↓-⊆ⁱdom Γ (fvs e₂)) in
  let ⊢ρ₁ , ⊢ρ₂ = ⊢ʳ-splits-ρ Γ₁ Γ₂ Γ e₁ (e₂ ∷ []) u₁ [] (⊆ⁱ→⊆ domΓ₁⊆domΓ) (⊆ⁱ→⊆ domΓ₂⊆domΓ) ⊢ρ in
  let dom-ρ' = map proj₁ (((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ) ++ dom-ρ in
  let ⊢e₁' = soundness' ⊢e₁ dom-ρ₁ ρ₁ bvs⊎fvs₁ U-bvs₁ (Unique-⊆ domΓ₁⊆domΓ U-Γ) ⊢ρ₁ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₂' = soundness' ⊢e₂ dom-ρ₂ ρ₂ bvs⊎fvs₂ U-bvs₂ (Unique-⊆ domΓ₂⊆domΓ U-Γ) ⊢ρ₂ (∩ˡ-⊆₂ dom-ρ' _) in
  let ⊢e₁'·e₂' : (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ∥ ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)) ⊢
                 send (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ Unit ⍮ 𝟏
      ⊢e₁'·e₂' = ⊢send refl ⊢e₁' ⊢e₂' in
  ⊢splits {Γ = Γ} send ⊢e₁ ⊢e₂ bvs⊎fvs₁ Γ₁⊆Γ (⊆ⁱ→⊆ domΓ₂⊆domΓ) U-Γ ⊢ρ
          (⊧ˢ-split Γ e₁ (e₂ ∷ []) u₁ u₂ [] bvs⊎fvs₁ ⊢ρ Γ₁⊆Γ ⊢e₁) Γ≲ ⊢e₁'·e₂'

soundness' (⊢recv ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢recv (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' (⊢select {l = l} ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢select (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' (⊢branch ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢branch (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' (⊢drop ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢drop (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' (⊢close ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  ⊢close (soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ)

soundness' (⊢∶ ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ

soundness' (⊢chk-inf ⊢e) dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ =
  soundness' ⊢e dom-ρ ρ bvs⊎fvs U-bvs U-Γ ⊢ρ dom-ρ⊆domΓ

--------------------------------------------------------------------------------

soundness'' : ∀ {i} →
  Disjoint (bvs e) (fvs e) →
  Unique (bvs e) →
  (⊢e : Γ ⊢ e ∶[ i ] t ⍮ u ⍮ ϕ) →
  Unique (dom Γ) →
  Γ ⋯ᵘ u ≡ Γ →
  Γ ⊢ (⟪ ⊢e ⟫ [] idʳ) ∶ t ⍮ ϕ
soundness'' {Γ = Γ} {u = u} bvs⊎fvs U-bvs ⊢e U-Γ Γ-used =
  subst (_⊢ (⟪ ⊢e ⟫ [] idʳ) ∶ _ ⍮ _)
        eq
        (soundness' ⊢e [] idʳ bvs⊎fvs U-bvs U-Γ ⊢ʳ-id ([]⊆ _))
  where
    eq = let open ≡-Reasoning in
         begin
           Γ ⋯ᵘ u ⋯ʳ idʳ
         ≡⟨ ⋯ʳ-id (Γ ⋯ᵘ u) ⟩
           Γ ⋯ᵘ u
         ≡⟨ Γ-used ⟩
           Γ
         ∎

--------------------------------------------------------------------------------

soundness : ∀ {i} →
  Disjoint (bvs e) (fvs e) →
  Unique (bvs e) →
  (⊢e : · ⊢ e ∶[ i ] t ⍮ ∅ᵘ ⍮ ϕ) →
  · ⊢ (⟪ ⊢e ⟫ [] idʳ) ∶ t ⍮ ϕ
soundness bvs⊎fvs U-bvs ⊢e = soundness'' bvs⊎fvs U-bvs ⊢e Unique-[] refl
