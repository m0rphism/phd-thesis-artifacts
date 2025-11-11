module BGV.Translation where

open import Data.List as L using (List; []; _∷_; _++_)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)

open import BGV.Id
open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Types
open import BGV.Expressions
open import BGV.Context
open import BGV.Util.Decidable
open import BGV.Util.List
open import BGV.Algorithmic
open import BGV.Split
open import BGV.Ren
open import BGV.UsageMap

⟪_⟫ : ∀ {i} → Γ ⊢ e ∶[ i ] t ⍮ u ⍮ ϕ → List Id → Ren → Expr log
⟪ ⊢`-nochan {x = x} Γ≲x∶t ¬Chan ⟫ dom-ρ ρ =
  ` ρ x
⟪ ⊢`-chan {x = x} Γ≲x∶t isChan ⟫ dom-ρ ρ =
  ` ρ x
⟪ ⊢& {x = x} Γ≲x∶t t≡Chan s≡++ ⟫ dom-ρ ρ =
  ` ρ x
⟪ ⊢λ {x = x} {m = m} _ ⊢e ∞→UnrΓ x∉uˡ _ ⟫ dom-ρ ρ = λ[ m ] x ⇒ ⟪ ⊢e ⟫ dom-ρ ρ
⟪ ⊢·≻ {Γ₁ = Γ₁} {Γ = Γ} {e₁ = e₁} {u₁ = u₁} {Γ₂ = Γ₂} {e₂ = e₂} x ⊢e₁ x₁ ⊢e₂ x₂ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  E ((⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) `· (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂))
⟪ ⊢·≺ {Γ₁ = Γ₁} {Γ = Γ} {e₁ = e₁} {u₁ = u₁} {Γ₂ = Γ₂} {e₂ = e₂} x ⊢e₁ x₁ ⊢e₂ x₂ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  E ((⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) `· (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁))
⟪ ⊢·𝟙 {Γ₁ = Γ₁} {Γ = Γ} {e₁ = e₁} {u₁ = u₁} {Γ₂ = Γ₂} {e₂ = e₂} x ⊢e₁ x₁ ⊢e₂ x₂ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  E ((⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) `· (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂))
⟪ ⊢·∞ {Γ₁ = Γ₁} {Γ = Γ} {e₁ = e₁} {u₁ = u₁} {Γ₂ = Γ₂} {e₂ = e₂} x ⊢e₁ x₁ ⊢e₂ x₂ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  E ((⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) `· (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂))
⟪ ⊢, {Γ₁ = Γ₁} {Γ = Γ} {e₁ = e₁} {u₁ = u₁} {Γ₂ = Γ₂} {e₂ = e₂} {p = p} x ⊢e₁ x₁ ⊢e₂ x₂ x₃ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (e₁ `· e₂)) dom-ρ ρ Γ₁ Γ₂ in
  E ((⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) ,[ p ] (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂))
⟪ ⊢let {x = x} {Γ = Γ} {Γ₁ = Γ₁} {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {C = C} _ a ⊢e₁ _ _ _ x₁ ⊢e₂ x₂ _ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (let[ x ≔ e₁ ]in e₂))
               dom-ρ ρ Γ₁ (C [ · ]) in
  E (let[ x ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂)
⟪ ⊢let× {x = x} {Γ = Γ} {y = y} {Γ₁ = Γ₁} {e₁ = e₁} {u₁ = u₁} {C = C} {e₂ = e₂} _ _ _ a ⊢e₁ _ _ _ x₁ ⊢e₂ x₂ x₃ _ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (let[ x `, y ≔ e₁ ]in e₂))
               dom-ρ ρ Γ₁ (C [ · ]) in
  E (let[ x `, y ≔ ⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁ ]in ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂)
⟪ ⊢inj {l = l} ⊢e ⟫ dom-ρ ρ =
  `inj l (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢case {x₁ = x₁} {Γ = Γ} {x₂ = x₂}  {Γ₁ = Γ₁}{e₁ = e₁} {u₁ = u₁} {C = C} {e₂₁ = e₂₁} {e₂₂ = e₂₂} _ _ _ x ⊢e _ _ _ y₁ ⊢e₁ ⊢e₂ y₂ x₃ x₄ _ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂₁ ++ fvs e₂₂) u₁ (dom Γ ++ vars (case e₁ of[ x₁ ⇒ e₂₁ ⍮ x₂ ⇒ e₂₂ ]))
               dom-ρ ρ Γ₁ (C [ · ]) in
  E (case ⟪ ⊢e ⟫ dom-ρ₁ ρ₁ of[ x₁ ⇒ ⟪ ⊢e₁ ⟫ dom-ρ₂ ρ₂ ⍮ x₂ ⇒ ⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂ ])
⟪ ⊢unit _ ⟫ dom-ρ ρ =
  unit
⟪ ⊢spawn ⊢e ⟫ dom-ρ ρ =
  spawn (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢new {s = s} _ ⟫ dom-ρ ρ =
  new s
⟪ ⊢send {Γ₁ = Γ₁} {Γ = Γ} {e₁ = e₁} {u₁ = u₁} {Γ₂ = Γ₂} {e₂ = e₂} x ⊢e₁ x₁ ⊢e₂ x₂ ⟫ dom-ρ ρ =
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ vars (send e₁ e₂)) dom-ρ ρ Γ₁ Γ₂ in
  E (send (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂))
⟪ ⊢recv ⊢e ⟫ dom-ρ ρ =
  recv (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢select {l = l} ⊢e ⟫ dom-ρ ρ =
  select l (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢branch ⊢e ⟫ dom-ρ ρ =
  branch (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢drop ⊢e ⟫ dom-ρ ρ =
  drop (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢close {o = o} ⊢e ⟫ dom-ρ ρ =
  close o (⟪ ⊢e ⟫ dom-ρ ρ)
⟪ ⊢∶ ⊢e ⟫ dom-ρ ρ =
  ⟪ ⊢e ⟫ dom-ρ ρ
⟪ ⊢chk-inf ⊢e ⟫ dom-ρ ρ =
  ⟪ ⊢e ⟫ dom-ρ ρ

