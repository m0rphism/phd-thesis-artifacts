module BGV.Context.SyntacticSplit where

open import Data.List as L using (List; []; _∷_; _++_)
open import Data.Nat as ℕ using (ℕ; suc; zero)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.String as String using (String)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax; Σ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)
open import Level using (Level; 0ℓ) renaming (suc to lsuc; _⊔_ to _⊔ₗ_)
open import Data.Unit using (⊤; tt)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Function using (case_of_; _$_)

open import BGV.Effect
open import BGV.Context
open import BGV.Id
open import BGV.Util.Decidable
open import BGV.Util.Graph as G using (Graph)
open import BGV.Util.List
open import BGV.Types

-- ∈-ˡ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x y : A} {xs : List A} →
--   x ∈ (xs -ˡ y) →
--   x ∈ xs
-- ∈-ˡ {x = x} {y = y} {xs = x' ∷ xs} x∈ with x' ≟ y
-- … | yes p = there (∈-ˡ x∈)
-- … | no ¬p with x∈
-- …   | here px = here px
-- …   | there x∈' = there (∈-ˡ x∈')

∈-ˡ≡ : ∀ {ℓ} {A : Set ℓ} ⦃ _ : DecEq A ⦄ {x y : A} {xs : List A} →
  x ∈ (xs -ˡ y) →
  x ≢ y
∈-ˡ≡ {x = x} {y = y} {xs = x' ∷ xs} x∈ with x' ≟ y
… | yes p = ∈-ˡ≡ {xs = xs} x∈
… | no ¬p with x∈
…   | here x≡x' = λ x≡y → ¬p (trans (sym x≡x') x≡y)
…   | there x∈' = ∈-ˡ≡ {xs = xs} x∈'

-- ∈-↓ :
--   x ∶ t ∈ (Γ ↓ xs) →
--   x ∶ t ∈ Γ
-- ∈-↓ = {!!}

-- ∈-↓≡ :
--   x ∶ t ∈ (Γ ↓ xs) →
--   x ∉ˡ xs
-- ∈-↓≡ = {!!}

-- ∈dom-↓ :
--   x ∈dom (Γ ↓ xs) →
--   x ∈dom Γ
-- ∈dom-↓ (t , xt∈) = t , ∈-↓ xt∈

-- Unr-↓ :
--   Unrᶜ Γ →
--   Unrᶜ (Γ ↓ xs)
-- Unr-↓ = {!!}

-- _↓ᶜ_ : Ctx → List Id → Maybe (CtxPat × Ctx)
-- Γ ↓ᶜ xs = {!!}

-- ↓ᶜ-sound : ∀ {xs : List Id} →
--   Γ ↓ᶜ xs ≡ some (C , Γ') →
--   Γ ≲ C [ Γ' ]
-- ↓ᶜ-sound = {!!}

data CtxPatTy : Set where
  left right : CtxPatTy

variable
  d d₁ d₂ d' d₁' d₂' : CtxPatTy

data _∶ᶜᶜ_ : CtxPat → CtxPatTy → Set where
  cct-[] :
    [] ∶ᶜᶜ d
  cct-⸴₁ :
    (d ≡ right → o ≡ unordered ⊎ Unrᶜ Γ) →
    𝒢 ∶ᶜᶜ d →
    (𝒢 ⸴[ o ]₁ Γ) ∶ᶜᶜ d
  cct-⸴₂ :
    (d ≡ left → o ≡ unordered ⊎ Unrᶜ Γ) →
    𝒢 ∶ᶜᶜ d →
    (Γ ⸴[ o ]₂ 𝒢) ∶ᶜᶜ d

LeftCtx : CtxPat → Set
LeftCtx 𝒢 = 𝒢 ∶ᶜᶜ left

RightCtx : CtxPat → Set
RightCtx 𝒢 = 𝒢 ∶ᶜᶜ right

ParCtx : CtxPat → Set
ParCtx 𝒢 = 𝒢 ∶ᶜᶜ left × 𝒢 ∶ᶜᶜ right

ClosedCtx : CtxPat → Set
ClosedCtx 𝒢 = ¬ 𝒢 ∶ᶜᶜ left × ¬ 𝒢 ∶ᶜᶜ right

_∶ᶜᶜ?_ : (𝒢 : CtxPat) (c : CtxPatTy) → Dec (𝒢 ∶ᶜᶜ c)
[]            ∶ᶜᶜ? c = yes cct-[]
(𝒢 ⸴[ o ]₁ Γ) ∶ᶜᶜ? c with 𝒢 ∶ᶜᶜ? c
…                    | no ¬⊢𝒢 = no (λ { (cct-⸴₁ _ ⊢𝒢) → ¬⊢𝒢 ⊢𝒢 })
…                    | yes ⊢𝒢 with c
…                             | left  = yes (cct-⸴₁ (λ ()) ⊢𝒢)
…                             | right with o         | Unrᶜ? Γ
…                                        | _         | yes unr-Γ = yes $ cct-⸴₁ (λ z → inj₂ unr-Γ) ⊢𝒢
…                                        | unordered | _         = yes $ cct-⸴₁ (λ z → inj₁ refl) ⊢𝒢
…                                        | ordered   | no ¬unr-Γ = no $ λ { (cct-⸴₁ x p) → case x refl of λ { (inj₂ y) → ¬unr-Γ y } }
(Γ ⸴[ o ]₂ 𝒢) ∶ᶜᶜ? c with 𝒢 ∶ᶜᶜ? c
…                    | no ¬⊢𝒢 = no (λ { (cct-⸴₂ _ ⊢𝒢) → ¬⊢𝒢 ⊢𝒢 })
…                    | yes ⊢𝒢 with c
…                             | right = yes (cct-⸴₂ (λ ()) ⊢𝒢)
…                             | left  with o         | Unrᶜ? Γ
…                                        | _         | yes unr-Γ = yes $ cct-⸴₂ (λ z → inj₂ unr-Γ) ⊢𝒢
…                                        | unordered | _         = yes $ cct-⸴₂ (λ z → inj₁ refl) ⊢𝒢
…                                        | ordered   | no ¬unr-Γ = no $ λ { (cct-⸴₂ x p) → case x refl of λ { (inj₂ y) → ¬unr-Γ y } }

left-ctx? : (𝒢 : CtxPat) → Dec (LeftCtx 𝒢)
left-ctx? 𝒢 = 𝒢 ∶ᶜᶜ? left

right-ctx? : (𝒢 : CtxPat) → Dec (RightCtx 𝒢)
right-ctx? 𝒢 = 𝒢 ∶ᶜᶜ? right

par-ctx? : (𝒢 : CtxPat) → Dec (ParCtx 𝒢)
par-ctx? 𝒢 with 𝒢 ∶ᶜᶜ? left | 𝒢 ∶ᶜᶜ? right
…             | yes 𝒢∶l     | yes 𝒢∶r = yes (𝒢∶l , 𝒢∶r)
…             | _           | no ¬𝒢∶r = no (λ z → ¬𝒢∶r (proj₂ z))
…             | no ¬𝒢∶l     | _       = no (λ z → ¬𝒢∶l (proj₁ z))

closed-ctx? : (𝒢 : CtxPat) → Dec (ClosedCtx 𝒢)
closed-ctx? 𝒢 with 𝒢 ∶ᶜᶜ? left | 𝒢 ∶ᶜᶜ? right
…             | no ¬𝒢∶l     | no ¬𝒢∶r = yes (¬𝒢∶l , ¬𝒢∶r)
…             | _           | yes 𝒢∶r = no λ z → proj₂ z 𝒢∶r
…             | yes 𝒢∶l     | _       = no λ z → proj₁ z 𝒢∶l

instance
  Dec-∶ᶜᶜ : Dec (𝒢 ∶ᶜᶜ d)
  Dec-∶ᶜᶜ = _ ∶ᶜᶜ? _

  Dec-ParCtx : Dec (ParCtx 𝒢)
  Dec-ParCtx = par-ctx? _

  Dec-ClosedCtx : Dec (ClosedCtx 𝒢)
  Dec-ClosedCtx = closed-ctx? _

LeftCtx→Ctx :
  LeftCtx 𝒢 →
  ∃[ Γ𝒢 ] (∀ Γ → 𝒢 [ Γ ] ≲ Γ ⸴ Γ𝒢)
LeftCtx→Ctx cct-[] = · , λ Γ₁ → ≈→≲ ≈-·ʳ
LeftCtx→Ctx (cct-⸴₁ {o = o} {Γ = Γ} {𝒢 = 𝒢} q lc) with LeftCtx→Ctx lc
… | Γ𝒢 , 𝒢[Γ]≲Γ⸴Γ𝒢 =
  Γ𝒢 ⸴[ o ] Γ , λ Γ₁ →
    let open ≲-Reasoning in
    begin
      𝒢 [ Γ₁ ] ⸴[ o ] Γ
    ≲⟨ ≲-⸴ (𝒢[Γ]≲Γ⸴Γ𝒢 Γ₁) ≲-refl ⟩
      (Γ₁ ⸴ Γ𝒢) ⸴[ o ] Γ
    ≲⟨ ≲-lem₁ _ _ _ ⟩
      Γ₁ ⸴ (Γ𝒢 ⸴[ o ] Γ)
    ∎
LeftCtx→Ctx (cct-⸴₂ {o = o} {Γ = Γ} {𝒢 = 𝒢} Unord∨Empty lc) with LeftCtx→Ctx lc
… | Γ𝒢 , 𝒢[Γ]≲Γ⸴Γ𝒢 =
  Γ𝒢 ⸴[ o ] Γ , λ Γ₁ →
    let open ≲-Reasoning in
    begin
      Γ ⸴[ o ] (𝒢 [ Γ₁ ])
    ≲⟨ ≲-⸴  ≲-refl (𝒢[Γ]≲Γ⸴Γ𝒢 Γ₁) ⟩
      Γ ⸴[ o ] (Γ₁ ⸴ Γ𝒢)
    ≲⟨ ≲-lem₂ _ _ _ (Unord∨Empty refl) ⟩
      Γ₁ ⸴ (Γ𝒢 ⸴[ o ] Γ)
    ∎

RightCtx→Ctx :
  RightCtx 𝒢 →
  ∃[ Γ𝒢 ] (∀ Γ → 𝒢 [ Γ ] ≲ Γ𝒢 ⸴ Γ)
RightCtx→Ctx cct-[] = · , λ Γ₁ → ≈→≲ ≈-·ˡ
RightCtx→Ctx (cct-⸴₁ {o = o} {Γ = Γ} {𝒢 = 𝒢} Unord∨Empty rc-𝒢) with RightCtx→Ctx rc-𝒢
… | Γ𝒢 , 𝒢[Γ]≲Γ𝒢⸴Γ =
  Γ ⸴[ o ] Γ𝒢 , λ Γ₁ →
    let open ≲-Reasoning in
    begin
      (𝒢 [ Γ₁ ]) ⸴[ o ] Γ
    ≲⟨ ≲-⸴ (𝒢[Γ]≲Γ𝒢⸴Γ Γ₁) ≲-refl ⟩
      (Γ𝒢 ⸴ Γ₁) ⸴[ o ] Γ
    ≲⟨ ≲-lem₂' _ _ _ (Unord∨Empty refl) ⟩
      (Γ ⸴[ o ] Γ𝒢) ⸴ Γ₁
    ∎
RightCtx→Ctx (cct-⸴₂ {o = o} {Γ = Γ} {𝒢 = 𝒢} p rc-𝒢) with RightCtx→Ctx rc-𝒢
… | Γ𝒢 , 𝒢[Γ]≲Γ𝒢⸴Γ =
  Γ ⸴[ o ] Γ𝒢 , λ Γ₁ →
    let open ≲-Reasoning in
    begin
      Γ ⸴[ o ] (𝒢 [ Γ₁ ])
    ≲⟨ ≲-⸴ ≲-refl (𝒢[Γ]≲Γ𝒢⸴Γ Γ₁) ⟩
      Γ ⸴[ o ] (Γ𝒢 ⸴ Γ₁)
    ≲⟨ ≲-lem₁' _ _ _ ⟩
      (Γ ⸴[ o ] Γ𝒢) ⸴ Γ₁
    ∎

ParCtx→Ctx :
  ParCtx 𝒢 →
  ∃[ Γ𝒢 ] (∀ Γ → 𝒢 [ Γ ] ≲ Γ𝒢 ∥ Γ)
ParCtx→Ctx (cct-[] , cct-[]) = · , λ Γ₂ → ≈→≲ ≈-·ˡ
ParCtx→Ctx (cct-⸴₁ {o = o} {Γ = Γ} {𝒢 = 𝒢} q lc , cct-⸴₁ Unord∨Empty rc)
 with ParCtx→Ctx (lc , rc)
... | Γ𝒢 , 𝒢[Γ']≲Γ𝒢∥Γ'
 = Γ𝒢 ⸴[ o ] Γ , λ Γ' →
    let open ≲-Reasoning in
    begin
      (𝒢 [ Γ' ]) ⸴[ o ] Γ
    ≲⟨ ≲-⸴ (𝒢[Γ']≲Γ𝒢∥Γ' Γ') ≲-refl ⟩
      (Γ𝒢 ∥ Γ') ⸴[ o ] Γ
    ≲⟨ ≲-lem₂'' _ _ _ (Unord∨Empty refl) ⟩
      (Γ𝒢 ⸴[ o ] Γ) ∥ Γ'
    ∎
ParCtx→Ctx (cct-⸴₂ {o = o} {Γ = Γ} {𝒢 = 𝒢} Unord∨Empty lc , cct-⸴₂ q rc)
 with ParCtx→Ctx (lc , rc)
... | Γ𝒢 , 𝒢[Γ']≲Γ𝒢∥Γ'
 = Γ ⸴[ o ] Γ𝒢  , λ Γ' →
    let open ≲-Reasoning in
    begin
      Γ ⸴[ o ] (𝒢 [ Γ' ])
    ≲⟨ ≲-⸴ ≲-refl (𝒢[Γ']≲Γ𝒢∥Γ' Γ') ⟩
      Γ ⸴[ o ] (Γ𝒢 ∥ Γ')
    ≲⟨ ≲-lem₂''' _ _ _ (Unord∨Empty refl) ⟩
      (Γ ⸴[ o ] Γ𝒢) ∥ Γ'
    ∎

ClosedCtx→Ctx : ∀ 𝒢 →
  ∃[ Γ𝒢₁ ] ∃[ Γ𝒢₂ ] (∀ Γ → 𝒢 [ Γ ] ≲ (Γ𝒢₁ ⸴ (Γ ⸴ Γ𝒢₂)))
ClosedCtx→Ctx [] =
  · , · , λ Γ →
    ≲-trans (≈→≲ ≈-·ʳ) (≈→≲ ≈-·ˡ)
ClosedCtx→Ctx (𝒢 ⸴[ o ]₁ Γ) with ClosedCtx→Ctx 𝒢
... | Γ𝒢₁ , Γ𝒢₂ , 𝒢[Γ']≲Γ𝒢₁⸴Γ'⸴Γ𝒢₂ =
  Γ𝒢₁ , (Γ𝒢₂ ⸴[ o ] Γ) , λ Γ' →
    let open ≲-Reasoning in
    begin
      𝒢 [ Γ' ] ⸴[ o ] Γ
    ≲⟨ ≲-⸴ (𝒢[Γ']≲Γ𝒢₁⸴Γ'⸴Γ𝒢₂ Γ') ≲-refl  ⟩
      (Γ𝒢₁ ⸴ (Γ' ⸴ Γ𝒢₂)) ⸴[ o ] Γ
    ≲⟨ ≲-lem₁ _ _ _ ⟩
      Γ𝒢₁ ⸴ ((Γ' ⸴ Γ𝒢₂) ⸴[ o ] Γ)
    ≲⟨ ≲-⸴ ≲-refl (≲-lem₁ _ _ _) ⟩
      Γ𝒢₁ ⸴ (Γ' ⸴ (Γ𝒢₂ ⸴[ o ] Γ))
    ∎
ClosedCtx→Ctx (Γ ⸴[ o ]₂ 𝒢) with ClosedCtx→Ctx 𝒢
... | Γ𝒢₁ , Γ𝒢₂ , 𝒢[Γ']≲Γ𝒢₁⸴Γ'⸴Γ𝒢₂ =
  Γ ⸴[ o ] Γ𝒢₁ , Γ𝒢₂ , λ Γ' →
    let open ≲-Reasoning in
    begin
      Γ ⸴[ o ] 𝒢 [ Γ' ]
    ≲⟨ ≲-⸴  ≲-refl (𝒢[Γ']≲Γ𝒢₁⸴Γ'⸴Γ𝒢₂ Γ') ⟩
      Γ ⸴[ o ] (Γ𝒢₁ ⸴ (Γ' ⸴ Γ𝒢₂))
    ≲⟨ ≲-lem₁' _ _ _ ⟩
      (Γ ⸴[ o ] Γ𝒢₁) ⸴ (Γ' ⸴ Γ𝒢₂)
    ∎

infixr 4 _,'_ 
_,'_ : ∀ {a b} {A : Set a} {B : Set b} → A → B → A × B
_,'_ = _,_

infixl 6 _↓ᶜ_
_↓ᶜ_ : Ctx → List Id → Maybe (CtxPat × Ctx)
·              ↓ᶜ xs = some ([] , ·)
(x ∶ t)        ↓ᶜ xs
 with x ∈? xs
…   | no ¬x∈xs = some ((x ∶ t ∥₂ []) , ·)
…   | yes x∈xs with Unr? t
…     | yes unr-t = some ((x ∶ t ∥₂ []) , (x ∶ t))
…     | no ¬unr-t = some ([] , (x ∶ t))
(Γ₁ ⸴[ o ] Γ₂) ↓ᶜ xs
 with Γ₁ ↓ᶜ xs        | Γ₂ ↓ᶜ xs
…   | none            | _               = none
…   | _               | none            = none
…   | some (𝒢₁ , Γ₁') | some (𝒢₂ , Γ₂')
 with xs ¬⊎? dom Γ₁ | xs ¬⊎? dom Γ₂ 
…   | no  xs⊎Γ₁     | _             = some ((Γ₁ ⸴[ o ]₂ 𝒢₂) , Γ₂')
…   | _             | no  xs⊎Γ₁     = some ((𝒢₁ ⸴[ o ]₁ Γ₂) , Γ₁')
…   | yes xs¬⊎Γ₁    | yes xs¬⊎Γ₂
 with o
…   | ordered = case (right-ctx? 𝒢₁ ,' left-ctx? 𝒢₂) of λ where
        (yes rc-𝒢₁ , yes lc-𝒢₂) →
          let (Γ𝒢₁ , _) = RightCtx→Ctx rc-𝒢₁ in
          let (Γ𝒢₂ , _) = LeftCtx→Ctx lc-𝒢₂ in
          some ((Γ𝒢₁ ⸴₂ ([] ⸴₁ Γ𝒢₂)) , (Γ₁' ⸴ Γ₂'))
        _ →
          none
…   | unordered = case (left-ctx? 𝒢₁ ,' right-ctx? 𝒢₁ ,' left-ctx? 𝒢₂ ,' right-ctx? 𝒢₂) of λ where
        -- Both Parallel
        (yes lc-𝒢₁ , yes rc-𝒢₁ , yes lc-𝒢₂ , yes rc-𝒢₂) →
          let (Γ𝒢₁ , _) = ParCtx→Ctx (lc-𝒢₁ , rc-𝒢₁) in
          let (Γ𝒢₂ , _) = ParCtx→Ctx (lc-𝒢₂ , rc-𝒢₂) in
          some (((Γ𝒢₁ ∥ Γ𝒢₂) ∥₂ []) , (Γ₁' ∥ Γ₂'))
        -- Both Left
        (yes lc-𝒢₁ , _         , yes lc-𝒢₂ , _        ) →
          let (Γ𝒢₁ , _) = LeftCtx→Ctx lc-𝒢₁ in
          let (Γ𝒢₂ , _) = LeftCtx→Ctx lc-𝒢₂ in
          some (([] ⸴₁ (Γ𝒢₁ ∥ Γ𝒢₂)) , (Γ₁' ∥ Γ₂'))
          -- (Γ₁ ∥ Γ₂)
          -- Γ₁ ≲ (𝒢₁ [ Γ₁' ])
          -- Γ₂ ≲ (𝒢₂ [ Γ₂' ])
          -- (Γ₁ ∥ Γ₂) ≲ (𝒢₁ [ Γ₁' ] ∥ 𝒢₂ [ Γ₂' ])
          --           ≲ (Γ𝒢₁ ⸴ Γ₁') ∥ (Γ𝒢₂ ⸴ Γ₂')
          --           ≲ (Γ𝒢₁ ∥ Γ𝒢₂) ⸴ (Γ₁' ∥ Γ₂')
        -- Both Right
        (_         , yes rc-𝒢₁ , _         , yes rc-𝒢₂) →
          let (Γ𝒢₁ , _) = RightCtx→Ctx rc-𝒢₁ in
          let (Γ𝒢₂ , _) = RightCtx→Ctx rc-𝒢₂ in
          some (((Γ𝒢₁ ∥ Γ𝒢₂) ⸴₂ []) , (Γ₁' ∥ Γ₂'))
        -- Left Right
        (yes lc-𝒢₁ , _         , _         , yes rc-𝒢₂) →
          let (Γ𝒢₁ , _) = LeftCtx→Ctx lc-𝒢₁ in
          let (Γ𝒢₂ , _) = RightCtx→Ctx rc-𝒢₂ in
          some ((Γ𝒢₂ ⸴₂ ([] ⸴₁ Γ𝒢₁)) , (Γ₁' ⸴ Γ₂'))
        -- Right Left
        (_         , yes rc-𝒢₁ , yes lc-𝒢₂ , _        ) →
          let (Γ𝒢₁ , _) = RightCtx→Ctx rc-𝒢₁ in
          let (Γ𝒢₂ , _) = LeftCtx→Ctx lc-𝒢₂ in
          some ((Γ𝒢₁ ⸴₂ ([] ⸴₁ Γ𝒢₂)) , (Γ₂' ⸴ Γ₁'))
        -- Closed x / x Closed
        _ →
          let (Γ𝒢₁₁ , Γ𝒢₁₂ , _) = ClosedCtx→Ctx 𝒢₁ in
          let (Γ𝒢₂₁ , Γ𝒢₂₂ , _) = ClosedCtx→Ctx 𝒢₂ in
          some (((Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴₂ ([] ⸴₁ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))) , (Γ₁' ∥ Γ₂'))

↓ᶜ-sound : ∀ Γ xs →
  Γ ↓ᶜ xs ≡ some (𝒢 , Γ') →
  Γ ≲ 𝒢 [ Γ' ]
↓ᶜ-sound · xs refl = ≲-refl
↓ᶜ-sound (x ∶ t) xs eq with x ∈? xs
↓ᶜ-sound (x ∶ t) xs refl | no ¬x∈xs = ≈→≲ ≈-·ʳ
↓ᶜ-sound (x ∶ t) xs eq   | yes x∈xs with Unr? t
↓ᶜ-sound (x ∶ t) xs refl | yes x∈xs | yes unr-t = ≈→≲ (≈-dup-unr unr-t)
↓ᶜ-sound (x ∶ t) xs refl | yes x∈xs | no ¬unr-t = ≲-refl
↓ᶜ-sound (Γ₁ ⸴[ o ] Γ₂) xs eq
 with Γ₁ ↓ᶜ xs in eq₁ | Γ₂ ↓ᶜ xs in eq₂
…   | none            | _               = case eq of λ ()
…   | some _          | none            = case eq of λ ()
…   | some (𝒢₁ , Γ₁') | some (𝒢₂ , Γ₂')
 with xs ¬⊎? dom Γ₁ | xs ¬⊎? dom Γ₂ 
…   | no  xs⊎Γ₁     | _             = case eq of λ where
  refl → let open ≲-Reasoning in
         begin
           Γ₁ ⸴[ o ] Γ₂
         ≲⟨ ≲-⸴ ≲-refl (↓ᶜ-sound Γ₂ xs eq₂) ⟩
           Γ₁ ⸴[ o ] (𝒢₂ [ Γ₂' ])
         ∎
…   | yes _         | no  xs⊎Γ₁     = case eq of λ where
  refl → let open ≲-Reasoning in
         begin
           Γ₁ ⸴[ o ] Γ₂
         ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) ≲-refl ⟩
           (𝒢₁ [ Γ₁' ]) ⸴[ o ] Γ₂
         ∎
…   | yes xs¬⊎Γ₁    | yes xs¬⊎Γ₂
 with o
↓ᶜ-sound (Γ₁ ⸴[ o ] Γ₂) xs eq | some (𝒢₁ , Γ₁') | some (𝒢₂ , Γ₂') | yes xs¬⊎Γ₁ | yes xs¬⊎Γ₂ | ordered
  with right-ctx? 𝒢₁ in eq₁' | left-ctx? 𝒢₂ in eq₂' 
… | yes rc-𝒢₁ | yes lc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲Γ𝒢₁⸴x) = RightCtx→Ctx rc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲x⸴Γ𝒢₂) = LeftCtx→Ctx lc-𝒢₂ in
           begin
             Γ₁ ⸴ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             𝒢₁ [ Γ₁' ] ⸴ 𝒢₂ [ Γ₂' ]
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁⸴x Γ₁') (𝒢₂[x]≲x⸴Γ𝒢₂ Γ₂') ⟩
             (Γ𝒢₁ ⸴ Γ₁') ⸴ (Γ₂' ⸴ Γ𝒢₂)
           ≈⟨ ⸴-assoc _ _ _ ⟩
             Γ𝒢₁ ⸴ (Γ₁' ⸴ (Γ₂' ⸴ Γ𝒢₂))
           ≈⟨ ≈-⸴ ≈-refl (≈-sym (⸴-assoc _ _ _)) ⟩
             Γ𝒢₁ ⸴ ((Γ₁' ⸴ Γ₂') ⸴ Γ𝒢₂)
           ≡⟨⟩
             (Γ𝒢₁ ⸴₂ ([] ⸴₁ Γ𝒢₂)) [ Γ₁' ⸴ Γ₂' ]
           ∎
… | no ¬rc-𝒢₁     | _ = case eq of λ ()
↓ᶜ-sound (Γ₁ ⸴[ o ] Γ₂) xs eq | some (𝒢₁ , Γ₁') | some (𝒢₂ , Γ₂') | yes xs¬⊎Γ₁ | yes xs¬⊎Γ₂ | unordered
  with left-ctx? 𝒢₁ | right-ctx? 𝒢₁ | left-ctx? 𝒢₂ | right-ctx? 𝒢₂
        -- Both Parallel
… | yes lc-𝒢₁ | yes rc-𝒢₁ | yes lc-𝒢₂ | yes rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲Γ𝒢₁∥x) = ParCtx→Ctx (lc-𝒢₁ , rc-𝒢₁) in
           let (Γ𝒢₂ , 𝒢₂[x]≲Γ𝒢₂∥x) = ParCtx→Ctx (lc-𝒢₂ , rc-𝒢₂) in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁∥x Γ₁') (𝒢₂[x]≲Γ𝒢₂∥x Γ₂') ⟩
             (Γ𝒢₁ ∥ Γ₁') ∥ (Γ𝒢₂ ∥ Γ₂')
           ≈⟨ ⸴-assoc _ _ _ ⟩
             Γ𝒢₁ ∥ (Γ₁' ∥ (Γ𝒢₂ ∥ Γ₂'))
           ≈⟨ ≈-⸴ ≈-refl (≈-sym (∥-comm _ _)) ⟩
             Γ𝒢₁ ∥ ((Γ𝒢₂ ∥ Γ₂') ∥ Γ₁')
           ≈⟨ ≈-⸴ ≈-refl (⸴-assoc _ _ _) ⟩
             Γ𝒢₁ ∥ (Γ𝒢₂ ∥ (Γ₂' ∥ Γ₁'))
           ≈⟨ ≈-sym (⸴-assoc _ _ _) ⟩
             (Γ𝒢₁ ∥ Γ𝒢₂) ∥ (Γ₂' ∥ Γ₁')
           ≈⟨ ≈-⸴ ≈-refl (∥-comm _ _) ⟩
             (Γ𝒢₁ ∥ Γ𝒢₂) ∥ (Γ₁' ∥ Γ₂')
           ≡⟨⟩
             ((Γ𝒢₁ ∥ Γ𝒢₂) ∥₂ []) [ Γ₁' ∥ Γ₂' ]
           ∎
        -- Both Left
… | yes lc-𝒢₁ | no ¬rc-𝒢₁ | yes lc-𝒢₂ | _         = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲x⸴Γ𝒢₁) = LeftCtx→Ctx lc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲x⸴Γ𝒢₂) = LeftCtx→Ctx lc-𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲x⸴Γ𝒢₁ Γ₁') (𝒢₂[x]≲x⸴Γ𝒢₂ Γ₂') ⟩
             (Γ₁' ⸴ Γ𝒢₁) ∥ (Γ₂' ⸴ Γ𝒢₂)
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ₁' ∥ Γ₂') ⸴ (Γ𝒢₁ ∥ Γ𝒢₂)
           ≡⟨⟩
             ([] ⸴₁ (Γ𝒢₁ ∥ Γ𝒢₂)) [ Γ₁' ∥ Γ₂' ]
           ∎
… | yes lc-𝒢₁ | yes _     | yes lc-𝒢₂ | no _      = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲x⸴Γ𝒢₁) = LeftCtx→Ctx lc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲x⸴Γ𝒢₂) = LeftCtx→Ctx lc-𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲x⸴Γ𝒢₁ Γ₁') (𝒢₂[x]≲x⸴Γ𝒢₂ Γ₂') ⟩
             (Γ₁' ⸴ Γ𝒢₁) ∥ (Γ₂' ⸴ Γ𝒢₂)
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ₁' ∥ Γ₂') ⸴ (Γ𝒢₁ ∥ Γ𝒢₂)
           ≡⟨⟩
             ([] ⸴₁ (Γ𝒢₁ ∥ Γ𝒢₂)) [ Γ₁' ∥ Γ₂' ]
           ∎
        -- Both Right
… | no ¬lc-𝒢₁ | yes rc-𝒢₁ | _         | yes rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲Γ𝒢₁⸴x) = RightCtx→Ctx rc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲Γ𝒢₂⸴x) = RightCtx→Ctx rc-𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁⸴x Γ₁') (𝒢₂[x]≲Γ𝒢₂⸴x Γ₂') ⟩
             (Γ𝒢₁ ⸴ Γ₁') ∥ (Γ𝒢₂ ⸴ Γ₂')
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁ ∥ Γ𝒢₂) ⸴ (Γ₁' ∥ Γ₂')
           ≡⟨⟩
             ((Γ𝒢₁ ∥ Γ𝒢₂) ⸴₂ []) [ Γ₁' ∥ Γ₂' ]
           ∎
… | yes _     | yes rc-𝒢₁ | no _      | yes rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲Γ𝒢₁⸴x) = RightCtx→Ctx rc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲Γ𝒢₂⸴x) = RightCtx→Ctx rc-𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁⸴x Γ₁') (𝒢₂[x]≲Γ𝒢₂⸴x Γ₂') ⟩
             (Γ𝒢₁ ⸴ Γ₁') ∥ (Γ𝒢₂ ⸴ Γ₂')
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁ ∥ Γ𝒢₂) ⸴ (Γ₁' ∥ Γ₂')
           ≡⟨⟩
             ((Γ𝒢₁ ∥ Γ𝒢₂) ⸴₂ []) [ Γ₁' ∥ Γ₂' ]
           ∎
        -- Left Right
… | yes lc-𝒢₁ | no ¬rc-𝒢₁ | no ¬lc-𝒢₂ | yes rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲x⸴Γ𝒢₁) = LeftCtx→Ctx lc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲Γ𝒢₂⸴x) = RightCtx→Ctx rc-𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲x⸴Γ𝒢₁ Γ₁') (𝒢₂[x]≲Γ𝒢₂⸴x Γ₂') ⟩
             (Γ₁' ⸴ Γ𝒢₁) ∥ (Γ𝒢₂ ⸴ Γ₂')
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ₁' ∥ Γ𝒢₂) ⸴ (Γ𝒢₁ ∥ Γ₂')
           ≈⟨ ≈-⸴ (∥-comm _ _) (∥-comm _ _) ⟩
             (Γ𝒢₂ ∥ Γ₁') ⸴ (Γ₂' ∥ Γ𝒢₁)
           ≲⟨ ≲-⸴ (∥≲⸴ _ _) (∥≲⸴ _ _) ⟩
             (Γ𝒢₂ ⸴ Γ₁') ⸴ (Γ₂' ⸴ Γ𝒢₁)
           ≈⟨ ⸴-assoc _ _ _ ⟩
             Γ𝒢₂ ⸴ (Γ₁' ⸴ (Γ₂' ⸴ Γ𝒢₁))
           ≈⟨ ≈-⸴ ≈-refl (≈-sym (⸴-assoc _ _ _)) ⟩
             Γ𝒢₂ ⸴ ((Γ₁' ⸴ Γ₂') ⸴ Γ𝒢₁)
           ≡⟨⟩
             (Γ𝒢₂ ⸴₂ ([] ⸴₁ Γ𝒢₁)) [ Γ₁' ⸴ Γ₂' ]
           ∎
        -- Right Left
… | no ¬lc-𝒢₁ | yes rc-𝒢₁ | yes lc-𝒢₂ | no ¬rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁ , 𝒢₁[x]≲Γ𝒢₁⸴x) = RightCtx→Ctx rc-𝒢₁ in
           let (Γ𝒢₂ , 𝒢₂[x]≲x⸴Γ𝒢₂) = LeftCtx→Ctx lc-𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁⸴x Γ₁') (𝒢₂[x]≲x⸴Γ𝒢₂ Γ₂') ⟩
             (Γ𝒢₁ ⸴ Γ₁') ∥ (Γ₂' ⸴ Γ𝒢₂)
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁ ∥ Γ₂') ⸴ (Γ₁' ∥ Γ𝒢₂)
           ≲⟨ ≲-⸴ (∥≲⸴ _ _) (∥≲⸴ _ _) ⟩
             (Γ𝒢₁ ⸴ Γ₂') ⸴ (Γ₁' ⸴ Γ𝒢₂)
           ≈⟨ ⸴-assoc _ _ _ ⟩
             Γ𝒢₁ ⸴ (Γ₂' ⸴ (Γ₁' ⸴ Γ𝒢₂))
           ≈⟨ ≈-⸴ ≈-refl (≈-sym (⸴-assoc _ _ _)) ⟩
             Γ𝒢₁ ⸴ ((Γ₂' ⸴ Γ₁') ⸴ Γ𝒢₂)
           ≡⟨⟩
             (Γ𝒢₁ ⸴₂ ([] ⸴₁ Γ𝒢₂)) [ Γ₂' ⸴ Γ₁' ]
           ∎
        -- Closed x / x Closed

-- The following cases are all identical, but without the matching `eq` doesn't reduce...
… | yes lc-𝒢₁ | yes rc-𝒢₁ | no ¬lc-𝒢₂ | no rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁₁ , Γ𝒢₁₂ , 𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁) = ClosedCtx→Ctx 𝒢₁ in
           let (Γ𝒢₂₁ , Γ𝒢₂₂ , 𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂) = ClosedCtx→Ctx 𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁ Γ₁') (𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂ Γ₂') ⟩
             (Γ𝒢₁₁ ⸴ (Γ₁' ⸴ Γ𝒢₁₂)) ∥ (Γ𝒢₂₁ ⸴ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ⸴ Γ𝒢₁₂) ∥ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-⸴ ≲-refl (≲-dist-∥-⸴ _ _ _ _) ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ∥ Γ₂') ⸴ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))
           ≡⟨⟩
             ((Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴₂ ([] ⸴₁ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))) [ Γ₁' ∥ Γ₂' ]
           ∎
… | yes lc-𝒢₁ | no ¬rc-𝒢₁ | no ¬lc-𝒢₂ | no rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁₁ , Γ𝒢₁₂ , 𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁) = ClosedCtx→Ctx 𝒢₁ in
           let (Γ𝒢₂₁ , Γ𝒢₂₂ , 𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂) = ClosedCtx→Ctx 𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁ Γ₁') (𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂ Γ₂') ⟩
             (Γ𝒢₁₁ ⸴ (Γ₁' ⸴ Γ𝒢₁₂)) ∥ (Γ𝒢₂₁ ⸴ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ⸴ Γ𝒢₁₂) ∥ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-⸴ ≲-refl (≲-dist-∥-⸴ _ _ _ _) ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ∥ Γ₂') ⸴ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))
           ≡⟨⟩
             ((Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴₂ ([] ⸴₁ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))) [ Γ₁' ∥ Γ₂' ]
           ∎
… | no ¬lc-𝒢₁ | yes rc-𝒢₁ | no ¬lc-𝒢₂ | no rc-𝒢₂ = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁₁ , Γ𝒢₁₂ , 𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁) = ClosedCtx→Ctx 𝒢₁ in
           let (Γ𝒢₂₁ , Γ𝒢₂₂ , 𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂) = ClosedCtx→Ctx 𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁ Γ₁') (𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂ Γ₂') ⟩
             (Γ𝒢₁₁ ⸴ (Γ₁' ⸴ Γ𝒢₁₂)) ∥ (Γ𝒢₂₁ ⸴ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ⸴ Γ𝒢₁₂) ∥ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-⸴ ≲-refl (≲-dist-∥-⸴ _ _ _ _) ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ∥ Γ₂') ⸴ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))
           ≡⟨⟩
             ((Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴₂ ([] ⸴₁ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))) [ Γ₁' ∥ Γ₂' ]
           ∎
… | no ¬lc-𝒢₁ | no ¬rc-𝒢₁ | lc-𝒢₂     | rc-𝒢₂    = case eq of λ where
    refl → let open ≲-Reasoning in
           let (Γ𝒢₁₁ , Γ𝒢₁₂ , 𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁) = ClosedCtx→Ctx 𝒢₁ in
           let (Γ𝒢₂₁ , Γ𝒢₂₂ , 𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂) = ClosedCtx→Ctx 𝒢₂ in
           begin
             Γ₁ ∥ Γ₂
           ≲⟨ ≲-⸴ (↓ᶜ-sound Γ₁ xs eq₁) (↓ᶜ-sound Γ₂ xs eq₂) ⟩
             (𝒢₁ [ Γ₁' ]) ∥ (𝒢₂ [ Γ₂' ])
           ≲⟨ ≲-⸴ (𝒢₁[x]≲Γ𝒢₁₁⸴x⸴Γ𝒢₂₁ Γ₁') (𝒢₂[x]≲Γ𝒢₂₁⸴x⸴Γ𝒢₂₂ Γ₂') ⟩
             (Γ𝒢₁₁ ⸴ (Γ₁' ⸴ Γ𝒢₁₂)) ∥ (Γ𝒢₂₁ ⸴ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-dist-∥-⸴ _ _ _ _ ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ⸴ Γ𝒢₁₂) ∥ (Γ₂' ⸴ Γ𝒢₂₂))
           ≲⟨ ≲-⸴ ≲-refl (≲-dist-∥-⸴ _ _ _ _) ⟩
             (Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴ ((Γ₁' ∥ Γ₂') ⸴ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))
           ≡⟨⟩
             ((Γ𝒢₁₁ ∥ Γ𝒢₂₁) ⸴₂ ([] ⸴₁ (Γ𝒢₁₂ ∥ Γ𝒢₂₂))) [ Γ₁' ∥ Γ₂' ]
           ∎

-- lem-rc-completeness :
--   (∀ Γ₂ → 𝒢 [ Γ₂ ] ≲ Γ₁ ⸴[ o ] Γ₂) →
--   RightCtx 𝒢
-- lem-rc-completeness {𝒢 = []}           p = rc-[]
-- lem-rc-completeness {𝒢 = 𝒢 ⸴[ o' ]₁ Γ} p = {!!}
-- lem-rc-completeness {𝒢 = Γ ⸴[ o' ]₂ 𝒢} p = {!!}

-- data Split (xs : List Id) (Γ : Ctx) : Set₁ where
--   nosplit :
--     Dec (IsEmpty Γ) →
--     (∀ x → x ∈ˡ xs → ¬ (x ∈dom Γ)) →
--     Split xs Γ
--   split   :
--     (𝒢 : CtxPat) →
--     Dec (LeftCtx 𝒢) →
--     Dec (RightCtx 𝒢) →
--     (Γ' : Ctx) →
--     (∀ x → x ∈dom Γ' → x ∈ˡ xs) →
--     (∀ x → x ∈dom 𝒢 [ · ] → x ∉ˡ xs) →
--     ¬ IsEmpty Γ' →
--     Γ ≲ 𝒢 [ Γ' ] →
--     Split xs Γ

-- ≲ᵍ-⸴ : ∀ {g₁ g₁' g₂ g₂' : Graph (Id × Type)} → g₁ ≲ᵍ g₁' → g₂ ≲ᵍ g₂' → g₁ G.+ g₂ ≲ᵍ g₁' G.+ g₂'
-- ≲ᵍ-⸴ (g₁# , g₁'# , g₁≃g₁# , g₁#≲g₁'# , g₁'#≃g₁') (g₂# , g₂'# , g₂≃g₂# , g₂#≲g₂'# , g₂'#≃g₂') =
--   (g₁# G.+ g₂#) , (g₁'# G.+ g₂'#) , G.≃-+ g₁≃g₁# g₂≃g₂# , G.≲-+ g₁#≲g₁'# g₂#≲g₂'# , G.≃-+ g₁'#≃g₁' g₂'#≃g₂' 

-- ≲-⸴ : Γ₁ ≲ Γ₁' → Γ₂ ≲ Γ₂' → Γ₁ ⸴ Γ₂ ≲ Γ₁' ⸴ Γ₂'
-- ≲-⸴ (mk-≲ (p₁ , p₂)) (mk-≲ (q₁ , q₂)) = mk-≲ (≲ᵍ-⸴ p₁ q₁ , {!!})

-- ≲-∥ : Γ₁ ≲ Γ₁' → Γ₂ ≲ Γ₂' → Γ₁ ∥ Γ₂ ≲ Γ₁' ∥ Γ₂'
-- ≲-∥ (mk-≲ (p₁ , p₂)) (mk-≲ (q₁ , q₂)) = {!!}

-- ≲-refl : Γ ≲ Γ
-- ≲-refl = mk-≲ ≲ˢ-refl

-- splitᶜ : (xs : List Id) → (Γ : Ctx) → Maybe (Split xs Γ)
-- splitᶜ xs ·         = some (nosplit decide (λ x x₁ ()))
-- splitᶜ xs (x ∶ t)   with x ∈? xs
-- …                      | yes x∈xs = some (split [] decide decide
--                                                 (x ∶ t) (λ { _ (t , ∈-bind) → x∈xs }) (λ x ()) (λ z → z x t ∈-bind)
--                                                 ≲-refl)
-- …                      | no ¬x∈xs = some (nosplit decide λ { _ x∈xs (fst , ∈-bind) → ¬x∈xs x∈xs })
-- splitᶜ xs (Γ₁ ⸴ Γ₂) with splitᶜ xs Γ₁ | splitᶜ xs Γ₂
-- … | some (nosplit Γ₁-empty? xs∉Γ₁) | some (nosplit Γ₂-empty? xs∉Γ₂) =
--   some $ nosplit decide xs∉Γ₁⸴Γ₂ where
--     xs∉Γ₁⸴Γ₂ = λ where
--       x x∈xs (t , ∈-⸴₁ x∶t∈Γ₁) → xs∉Γ₁ x x∈xs (t , x∶t∈Γ₁)
--       x x∈xs (t , ∈-⸴₂ x∶t∈Γ₂) → xs∉Γ₂ x x∈xs (t , x∶t∈Γ₂) 
-- … | some (nosplit Γ₁-empty? xs∉Γ₁) | some (split 𝒢₂ 𝒢₂-lc? 𝒢₂-rc? Γ₂' Γ₂'⊆xs 𝒢₂⊊xs ¬empty-Γ₂' Γ₂≲𝒢₂[Γ₂']) =
--   some (split (Γ₁ ⸴₂ 𝒢₂) decide decide Γ₂' Γ₂'⊆xs Γ₁⸴𝒢₂⊊xs ¬empty-Γ₂' Γ₁⸴Γ₂≲Γ₁⸴𝒢₂[Γ₂'])
--   where
--     Γ₁⸴𝒢₂⊊xs = λ where
--       x (t , ∈-⸴₁ x∶t∈Γ₁) p → xs∉Γ₁ x p (t , x∶t∈Γ₁)
--       x (t , ∈-⸴₂ x∶t∈𝒢₂) p → 𝒢₂⊊xs x (t , x∶t∈𝒢₂) p
--     Γ₁⸴Γ₂≲Γ₁⸴𝒢₂[Γ₂'] =
--       ≲-⸴ {Γ₁ = Γ₁} {Γ₁' = Γ₁} {Γ₂ = Γ₂} {Γ₂' = 𝒢₂ [ Γ₂' ]} ≲-refl Γ₂≲𝒢₂[Γ₂']
-- … | some (split 𝒢₁ 𝒢₁-lc? 𝒢₁-rc? Γ₁' Γ₁'⊆xs 𝒢₁⊊xs ¬empty-Γ₁' Γ₁≲𝒢₁[Γ₁']) | some (nosplit Γ₂-empty? xs∉Γ₂) =
--   some (split (𝒢₁ ⸴₁ Γ₂) decide decide Γ₁' Γ₁'⊆xs 𝒢₁⸴Γ₂⊊xs ¬empty-Γ₁' Γ₁⸴Γ₂≲𝒢₁⸴Γ₂[Γ₁'])
--   where
--     𝒢₁⸴Γ₂⊊xs = λ where
--       x (t , ∈-⸴₁ x∶t∈𝒢₁) p → 𝒢₁⊊xs x (t , x∶t∈𝒢₁) p
--       x (t , ∈-⸴₂ x∶t∈Γ₂) p → xs∉Γ₂ x p (t , x∶t∈Γ₂)
--     Γ₁⸴Γ₂≲𝒢₁⸴Γ₂[Γ₁'] =
--       ≲-⸴ {Γ₁ = Γ₁} {Γ₁' = 𝒢₁ [ Γ₁' ]} {Γ₂ = Γ₂} {Γ₂' = Γ₂} Γ₁≲𝒢₁[Γ₁'] ≲-refl
-- … | some (split 𝒢₁ 𝒢₁-lc? (yes 𝒢₁-rc) Γ₁' Γ₁'⊆xs 𝒢₁⊊xs ¬empty-Γ₁' Γ₁≲𝒢₁[Γ₁'])
--   | some (split 𝒢₂ (yes 𝒢₂-lc) 𝒢₂-rc? Γ₂' Γ₂'⊆xs 𝒢₂⊊xs ¬empty-Γ₂' Γ₂≲𝒢₂[Γ₂']) =
--     let (Γ₁# , o , 𝒢₁≲Γ₁#⸴[]) = RightCtx→Ctx 𝒢₁-rc in -- 𝒢₁ ≲ Γ₁# ,[ o ] []
--     let (Γ₂# , o , 𝒢₂≲[]⸴Γ₂#) = LeftCtx→Ctx 𝒢₂-lc in  -- 𝒢₂ ≲ [] ,[ o ] Γ₂#
--     some (split ((Γ₁# ⸴₂ []) ⸴₁ Γ₂#) decide decide (Γ₁' ⸴ Γ₂') Γ₁'⸴Γ₂'⊆xs Γ₁#⸴[]⸴Γ₂#⊊xs ¬empty-Γ₁'⸴Γ₂' Γ₁⸴Γ₂≲Γ₁#⸴Γ₁'⸴Γ₂'⸴Γ₂#)
--     where
--       Γ₁'⸴Γ₂'⊆xs = λ where
--         x (t , ∈-⸴₁ x∶t∈Γ₁') → Γ₁'⊆xs x (t , x∶t∈Γ₁')
--         x (t , ∈-⸴₂ x∶t∈Γ₂') → Γ₂'⊆xs x (t , x∶t∈Γ₂')
--       Γ₁#⸴[]⸴Γ₂#⊊xs = λ where
--         x (t , ∈-⸴₁ (∈-⸴₁ x∶t∈Γ₁#)) q → {!requires to transfer proof from 𝒢₁ to Γ₁#!}
--         x (t , ∈-⸴₂ x∶t∈Γ₂#) q → {!requires to transfer proof from 𝒢₂ to Γ₂#!}
--       ¬empty-Γ₁'⸴Γ₂' = λ empty-Γ₁'⸴Γ₂' → ¬empty-Γ₁' (λ x t x∶t∈Γ₁' → empty-Γ₁'⸴Γ₂' x t (∈-⸴₁ x∶t∈Γ₁'))
--       Γ₁⸴Γ₂≲Γ₁#⸴Γ₁'⸴Γ₂'⸴Γ₂# = {!!}
--       -- works:
--       --   Γ₁ ⸴ Γ₂ ≲
--       --   𝒢₁[Γ₁'] ⸴ 𝒢₂[Γ₂'] ≲
--       --   Γ₁# ⸴ Γ₁' , Γ₂' , Γ₂#
-- … | _                                  | _                                       = none
-- splitᶜ xs (Γ₁ ∥ Γ₂) with splitᶜ xs Γ₁ | splitᶜ xs Γ₂
-- … | some (nosplit Γ₁-empty? xs∉Γ₁) | some (nosplit Γ₂-empty? xs∉Γ₂) =
--   some $ nosplit decide xs∉Γ₁⸴Γ₂ where
--     xs∉Γ₁⸴Γ₂ = λ where
--       x x∈xs (t , ∈-⸴₁ x∶t∈Γ₁) → xs∉Γ₁ x x∈xs (t , x∶t∈Γ₁)
--       x x∈xs (t , ∈-⸴₂ x∶t∈Γ₂) → xs∉Γ₂ x x∈xs (t , x∶t∈Γ₂) 
-- … | some (nosplit Γ₁-empty? xs∉Γ₁) | some (split 𝒢₂ 𝒢₂-lc? 𝒢₂-rc? Γ₂' Γ₂'⊆xs 𝒢₂⊊xs ¬empty-Γ₂' Γ₂≲𝒢₂[Γ₂']) =
--   some (split (Γ₁ ∥₂ 𝒢₂) decide decide Γ₂' Γ₂'⊆xs Γ₁∥𝒢₂⊊xs ¬empty-Γ₂' Γ₁∥Γ₂≲Γ₁∥𝒢₂[Γ₂'])
--   where
--     Γ₁∥𝒢₂⊊xs = λ where
--       x (t , ∈-⸴₁ x∶t∈Γ₁) p → xs∉Γ₁ x p (t , x∶t∈Γ₁)
--       x (t , ∈-⸴₂ x∶t∈𝒢₂) p → 𝒢₂⊊xs x (t , x∶t∈𝒢₂) p
--     Γ₁∥Γ₂≲Γ₁∥𝒢₂[Γ₂'] =
--       ≲-∥ {Γ₁ = Γ₁} {Γ₁' = Γ₁} {Γ₂ = Γ₂} {Γ₂' = 𝒢₂ [ Γ₂' ]} ≲-refl Γ₂≲𝒢₂[Γ₂']
-- … | some (split 𝒢₁ 𝒢₁-lc? 𝒢₁-rc? Γ₁' Γ₁'⊆xs 𝒢₁⊊xs ¬empty-Γ₁' Γ₁≲𝒢₁[Γ₁']) | some (nosplit Γ₂-empty? xs∉Γ₂) =
--   some (split (𝒢₁ ∥₁ Γ₂) decide decide Γ₁' Γ₁'⊆xs 𝒢₁∥Γ₂⊊xs ¬empty-Γ₁' Γ₁∥Γ₂≲𝒢₁∥Γ₂[Γ₁'])
--   where
--     𝒢₁∥Γ₂⊊xs = λ where
--       x (t , ∈-⸴₁ x∶t∈𝒢₁) p → 𝒢₁⊊xs x (t , x∶t∈𝒢₁) p
--       x (t , ∈-⸴₂ x∶t∈Γ₂) p → xs∉Γ₂ x p (t , x∶t∈Γ₂)
--     Γ₁∥Γ₂≲𝒢₁∥Γ₂[Γ₁'] =
--       ≲-∥ {Γ₁ = Γ₁} {Γ₁' = 𝒢₁ [ Γ₁' ]} {Γ₂ = Γ₂} {Γ₂' = Γ₂} Γ₁≲𝒢₁[Γ₁'] ≲-refl
-- … | some (split 𝒢₁ (yes 𝒢₁-lc) (yes 𝒢₁-rc) Γ₁' Γ₁'⊆xs 𝒢₁⊊xs ¬empty-Γ₁' Γ₁≲𝒢₁[Γ₁'])
--   | some (split 𝒢₂ (yes 𝒢₂-lc) (yes 𝒢₂-rc) Γ₂' Γ₂'⊆xs 𝒢₂⊊xs ¬empty-Γ₂' Γ₂≲𝒢₂[Γ₂']) =
--     let (Γ₁# , 𝒢₁≲Γ₁#∥[]) = ParCtx→Ctx 𝒢₁-lc 𝒢₁-rc in -- 𝒢₁ ≲ Γ₁# ∥ []
--     let (Γ₂# , 𝒢₂≲Γ₂#∥[]) = ParCtx→Ctx 𝒢₂-lc 𝒢₂-rc in -- 𝒢₂ ≲ Γ₂# ∥ Γ₂#
--     some (split ((Γ₁# ∥ Γ₂#) ∥₂ []) decide decide (Γ₁' ∥ Γ₂') Γ₁'∥Γ₂'⊆xs Γ₁#∥Γ₂#∥·⊊xs ¬empty-Γ₁'∥Γ₂' Γ₁∥Γ₂≲Γ₁#∥Γ₂#∥Γ₁'∥Γ₂')
--     where
--       Γ₁'∥Γ₂'⊆xs = λ where
--         x (t , ∈-⸴₁ x∶t∈Γ₁') → Γ₁'⊆xs x (t , x∶t∈Γ₁')
--         x (t , ∈-⸴₂ x∶t∈Γ₂') → Γ₂'⊆xs x (t , x∶t∈Γ₂')
--       Γ₁#∥Γ₂#∥·⊊xs = λ where
--         x (t , ∈-⸴₁ (∈-⸴₁ x∶t∈𝒢₁)) p → {!see above!}
--         x (t , ∈-⸴₁ (∈-⸴₂ x∶t∈Γ₂)) p → {!see above!}
--       ¬empty-Γ₁'∥Γ₂' = λ empty-Γ₁'∥Γ₂' → ¬empty-Γ₁' (λ x t xt∈ → empty-Γ₁'∥Γ₂' x t (∈-⸴₁ xt∈))
--       Γ₁∥Γ₂≲Γ₁#∥Γ₂#∥Γ₁'∥Γ₂' = {!!}
--       -- works:
--       --   Γ₁ ∥ Γ₂ ≲
--       --   𝒢₁[Γ₁'] ∥ 𝒢₂[Γ₂'] ≲
--       --   Γ₁# ∥ Γ₁' ∥ Γ₂# ∥ Γ₂' ≃
--       --   (Γ₁# ∥ Γ₂#) ∥ (Γ₁' ∥ Γ₂')
-- … | some (split 𝒢₁ (yes 𝒢₁-lc) (yes 𝒢₁-rc) Γ₁' Γ₁'⊆xs 𝒢₁⊊xs ¬empty-Γ₁' Γ₁≲𝒢₁[Γ₁'])
--   | some (split 𝒢₂ (yes 𝒢₂-lc) (no 𝒢₂-rc) Γ₂' Γ₂'⊆xs 𝒢₂⊊xs ¬empty-Γ₂' Γ₂≲𝒢₂[Γ₂']) =
--     {!!}
-- … | some (split 𝒢₁ 𝒢₁-lc? 𝒢₁-rc? Γ₁' Γ₁'⊆xs 𝒢₁⊊xs ¬empty-Γ₁' Γ₁≲𝒢₁[Γ₁'])
--   | some (split 𝒢₂ 𝒢₂-lc? 𝒢₂-rc? Γ₂' Γ₂'⊆xs 𝒢₂⊊xs ¬empty-Γ₂' Γ₂≲𝒢₂[Γ₂']) =
--     {!!}
    
-- … | _                                  | _                                       = none
-- -- … | some empty             | some s                 = some s
-- -- … | some s                 | some empty             = some s
-- -- … | some (nosplit Γ₁')     | some (nosplit Γ₂')     = some (nosplit (Γ₁' ⸴ Γ₂'))
-- -- … | some (nosplit Γ₁')     | some (split 𝒢₂ Γ₂' t₂) = some (split (Γ₁' ⸴₂ 𝒢₂) Γ₂' (left ∘ₜ t₂))
-- -- … | some (split 𝒢₁ Γ₁' t₁) | some (nosplit Γ₂')     = some (split (𝒢₁ ⸴₁ Γ₂') Γ₁ (right ∘ₜ t₁))
-- -- … | some (split 𝒢₁ Γ₁' right) | some (split 𝒢₂ Γ₂' left) = some (split {!Γ₁' ⸴₂ []!} {!!} closed)
-- -- … | _                      | _                      = none
-- -- splitᶜ xs (Γ₁ ∥ Γ₂) = {!!}

-- -- data SplitType : Set where
-- --   left right par closed : SplitType

-- -- _∘ₜ_ : SplitType → SplitType → SplitType

-- -- closed ∘ₜ _      = closed
-- -- _      ∘ₜ closed = closed

-- -- left   ∘ₜ left   = closed
-- -- right  ∘ₜ left   = left
-- -- par    ∘ₜ left   = left

-- -- left   ∘ₜ right  = right
-- -- right  ∘ₜ right  = closed
-- -- par    ∘ₜ right  = right

-- -- left   ∘ₜ par    = right
-- -- right  ∘ₜ par    = left
-- -- par    ∘ₜ par    = {!unused?!}

-- -- data Split : Set where
-- --   empty   : Split
-- --   nosplit : Ctx → Split
-- --   split   : CtxPat → Ctx → SplitType → Split

-- -- splitᶜ : List Id → Ctx → Maybe Split
-- -- splitᶜ xs ·         = some empty
-- -- splitᶜ xs (x ∶ t)   with x ∈? xs
-- -- …                      | yes x∈xs = some (split [] (x ∶ t) par)
-- -- …                      | no ¬x∈xs = some (nosplit (x ∶ t))
-- -- splitᶜ xs (Γ₁ ⸴ Γ₂) with splitᶜ xs Γ₁ | splitᶜ xs Γ₂
-- -- … | some empty             | some s                 = some s
-- -- … | some s                 | some empty             = some s
-- -- … | some (nosplit Γ₁')     | some (nosplit Γ₂')     = some (nosplit (Γ₁' ⸴ Γ₂'))
-- -- … | some (nosplit Γ₁')     | some (split 𝒢₂ Γ₂' t₂) = some (split (Γ₁' ⸴₂ 𝒢₂) Γ₂' (left ∘ₜ t₂))
-- -- … | some (split 𝒢₁ Γ₁' t₁) | some (nosplit Γ₂')     = some (split (𝒢₁ ⸴₁ Γ₂') Γ₁ (right ∘ₜ t₁))
-- -- … | some (split 𝒢₁ Γ₁' right) | some (split 𝒢₂ Γ₂' left) = some (split {!Γ₁' ⸴₂ []!} {!!} closed)
-- -- … | _                      | _                      = none
-- -- splitᶜ xs (Γ₁ ∥ Γ₂) = {!!}

-- -- vars : Ctx → List Id
-- -- vars ·              = []
-- -- vars (x ∶ t)        = L.[ x ]
-- -- vars (Γ₁ ⸴[ o ] Γ₂) = vars Γ₁ ++ vars Γ₂

-- -- split-sound : {𝒢 : CtxPat} →
-- --   Γ ≈ 𝒢 [ Γ' ] →
-- --   case splitᶜ (vars Γ') Γ of λ where
-- --     (some empty)             → Γ' ≈ ·
-- --     (some (nosplit Γ''))     → Γ' ≈ ·
-- --     (some (split 𝒢'' Γ'' t)) → Γ ≈ 𝒢'' [ Γ'' ] × Γ' ≈ Γ''
-- --     none                     → ⊥
-- -- split-sound = {!!}


  
  
