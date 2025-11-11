module BGV.UsageMap where

import Data.List.Properties as ListP
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; _$_; _∘_; const)
open import Relation.Binary.PropositionalEquality using
  (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; module ≡-Reasoning)

open import BGV.Id
open import BGV.Types
open import BGV.Expressions
open import BGV.Multiplicities
open import BGV.Context
open import BGV.Context.SyntacticSplit using (LeftCtx; cct-⸴₁; cct-⸴₂; cct-[])
open import BGV.Util.Decidable
open import BGV.Util.FunMap
open import BGV.Util.List
open import BGV.Ren

-- Definitions -----------------------------------------------------------------

UsageMap : Set
UsageMap = Id → Maybe AnySession

variable
  u u₁ u₂ u₃ u₂₁ u₂₂ : UsageMap

∅ᵘ : UsageMap
∅ᵘ = const none

⟨_⟩ᵘ : Id × AnySession → UsageMap
⟨ x , s ⟩ᵘ = (x , some s) ∷ᶠ ∅ᵘ

infixl 7 _·ᵘ_ _-ᵘ_

_-ᵘ_ : UsageMap → Id → UsageMap
u -ᵘ x = (x , none) ∷ᶠ u

_·ᵘᵐ_ : Maybe AnySession → Maybe AnySession → Maybe AnySession
none    ·ᵘᵐ s₂      = s₂
s₁      ·ᵘᵐ none    = s₁
some s₁ ·ᵘᵐ some s₂ = some (s₁ +++ˢ s₂)

_·ᵘ_ : UsageMap → UsageMap → UsageMap
(u₁ ·ᵘ u₂) x = u₁ x ·ᵘᵐ u₂ x

·ᵘ-some₁ : ∀ {s₁} u₁ u₂ x →
  u₁ x ≡ some (borrowed , s₁) →
  (u₁ ·ᵘ u₂) x ≡ some (borrowed , s₁) ⊎
  ∃[ b₂ ] Σ[ s₂ ∈ Session b₂ ]
    u₂ x ≡ some (b₂ , s₂) ×
    (u₁ ·ᵘ u₂) x ≡ some (b₂ , s₁ ++ˢ s₂)
·ᵘ-some₁ u₁ u₂ x eq
  rewrite eq
  with u₂ x
… | none = inj₁ refl
… | some (b₂ , s₂) = inj₂ (b₂ , s₂ , refl , refl)

app-rep : UsageMap → Id → Type → Ctx
app-rep u x t
  with Chan? t
… | no _ = x ∶ t
… | yes _
  with u x
… | none           = x ∶ t
… | (some (b , s)) = x ∶ Chan b s

infixl 6 _⋯ᵘ_ _⋯ᵘᶜ_

_⋯ᵘ_ : Ctx → UsageMap → Ctx
Γ ⋯ᵘ r = Γ >>=ᶜ app-rep r

_⋯ᵘᶜ_ : CtxPat → UsageMap → CtxPat
C ⋯ᵘᶜ r = C >>=ᶜᶜ app-rep r

app-% : UsageMap → Id → Type → Ctx
app-% r x t
 with Chan? t
… | no _             = x ∶ t
… | yes (b , s , _)
 with r x
… | none             = x ∶ t
… | (some (owned , s₁)) = x ∶ t
… | (some (borrowed , s₁))
 with s % s₁
… | none             = x ∶ t
… | some s₂          = x ∶ Chan b s₂

_%ᶜ_ : Ctx → UsageMap → Ctx
Γ %ᶜ u = Γ >>=ᶜ app-% u

-- _%ᶜ_ : Ctx → UsageMap → Maybe UsageMap
-- · %ᶜ u = some Map.∅
-- (x ∶ t) %ᶜ u = {!!}
-- (Γ ⸴[ x ] Γ₁) %ᶜ u = {!!}

app-%-dom : ∀ x t u → dom (app-% u x t) ≡ x ∷ []
app-%-dom x t u
  with Chan? t
… | no ¬chan = refl
… | yes (b , s , refl)
  with u x
… | none = refl
… | (some (owned , s₁)) = refl
… | (some (borrowed , s₁))
 with s % s₁
… | none             = refl
… | some s₂          = refl

%ᶜ-dom : ∀ Γ u → dom (Γ %ᶜ u) ≡ dom Γ
%ᶜ-dom · u = refl
%ᶜ-dom (x ∶ t) u = app-%-dom x t u
%ᶜ-dom (Γ₁ ⸴[ o ] Γ₂) u =
  let open ≡-Reasoning in
  begin
    dom ((Γ₁ ⸴[ o ] Γ₂) %ᶜ u)
  ≡⟨⟩
    map proj₁ (binds (Γ₁ %ᶜ u) ++ binds (Γ₂ %ᶜ u))
  ≡⟨ ListP.map-++ proj₁ (binds (Γ₁ %ᶜ u)) (binds (Γ₂ %ᶜ u)) ⟩
    dom (Γ₁ %ᶜ u) ++ dom (Γ₂ %ᶜ u)
  ≡⟨ cong₂ _++_ (%ᶜ-dom Γ₁ u) (%ᶜ-dom Γ₂ u) ⟩
    dom Γ₁ ++ dom Γ₂
  ≡⟨ sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) ⟩
    map proj₁ (binds Γ₁ ++ binds Γ₂)
  ≡⟨⟩
    dom (Γ₁ ⸴[ o ] Γ₂)
  ∎

-- Properties ------------------------------------------------------------------

⋯ᵘ-id : ∀ Γ → Γ ⋯ᵘ ∅ᵘ ≡ Γ
⋯ᵘ-id · = refl
⋯ᵘ-id (x ∶ t)
  with Chan? t
… | no _ = refl
… | yes _ = refl
⋯ᵘ-id (Γ₁ ⸴[ o ] Γ₂) = cong₂ _⸴[ o ]_ (⋯ᵘ-id Γ₁) (⋯ᵘ-id Γ₂) 

⋯ᵘ-ext : ∀ m Γ₁ Γ₂ u →
  ext m Γ₁ Γ₂ ⋯ᵘ u ≡ ext m (Γ₁ ⋯ᵘ u) (Γ₂ ⋯ᵘ u)
⋯ᵘ-ext ∞ Γ₁ Γ₂ ρ = refl
⋯ᵘ-ext 𝟙 Γ₁ Γ₂ ρ = refl
⋯ᵘ-ext ≻ Γ₁ Γ₂ ρ = refl
⋯ᵘ-ext ≺ Γ₁ Γ₂ ρ = refl

⋯ᵘ-dom : ∀ Γ u →
  dom (Γ ⋯ᵘ u) ≡ dom Γ
⋯ᵘ-dom · u = refl
⋯ᵘ-dom (Γ₁ ⸴[ o ] Γ₂) u =
  let open ≡-Reasoning in
  begin
    dom ((Γ₁ ⸴[ o ] Γ₂) ⋯ᵘ u)
  ≡⟨⟩
    List.map proj₁ (binds (Γ₁ ⋯ᵘ u) ++ binds (Γ₂ ⋯ᵘ u))
  ≡⟨ ListP.map-++ proj₁ (binds (Γ₁ ⋯ᵘ u)) (binds (Γ₂ ⋯ᵘ u)) ⟩
    List.map proj₁ (binds (Γ₁ ⋯ᵘ u)) ++ List.map proj₁ (binds (Γ₂ ⋯ᵘ u))
  ≡⟨ cong₂ _++_ (⋯ᵘ-dom Γ₁ u) (⋯ᵘ-dom Γ₂ u) ⟩
    List.map proj₁ (binds Γ₁) ++ List.map proj₁ (binds Γ₂)
  ≡⟨ sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) ⟩
    List.map proj₁ (binds Γ₁ ++ binds Γ₂)
  ≡⟨⟩
    dom (Γ₁ ⸴[ o ] Γ₂)
  ∎
⋯ᵘ-dom (x ∶ t) u with Chan? t
… | no  _ = refl
… | yes _ with u x
…   | none   = refl
…   | some _ = refl

import BGV.Util.Graph as G

app-repˢ : UsageMap → Id × Type → Id × Type
app-repˢ u (x , t)
  with Chan? t
… | no _ = x , t
… | yes _
  with u x
… | none           = x , t
… | (some (b , s)) = x , Chan b s

_⋯ᵘˢ_ : SemCtx → UsageMap → SemCtx
(O , U) ⋯ᵘˢ u = map-graph (app-repˢ u) O , map (app-repˢ u) U

⋯ᵘ-⟦⟧ : ∀ Γ u → ⟦ Γ ⋯ᵘ u ⟧ ≈ˢ ⟦ Γ ⟧ ⋯ᵘˢ u
⋯ᵘ-⟦⟧ · u = G.≃-sym (map-∅ (app-repˢ u)) , ≈ˡ-refl
⋯ᵘ-⟦⟧ (x ∶ t) u with Unr? t in eq-unr
⋯ᵘ-⟦⟧ (x ∶ t) u | yes unr-t with Chan? t
⋯ᵘ-⟦⟧ (x ∶ t) u | yes unr-t | yes (b , s , refl) with () ← unr-t
⋯ᵘ-⟦⟧ (x ∶ t) u | yes unr-t | no ¬chan rewrite eq-unr = G.≃-sym (map-∅ (app-repˢ u)) , ≈ˡ-refl
⋯ᵘ-⟦⟧ (x ∶ t) u | no ¬unr-t with Chan? t
⋯ᵘ-⟦⟧ (x ∶ t) u | no ¬unr-t | yes (b , s , refl) with u x
⋯ᵘ-⟦⟧ (x ∶ t) u | no ¬unr-t | yes (b , s , refl) | none = G.≃-refl , ≈ˡ-refl
⋯ᵘ-⟦⟧ (x ∶ t) u | no ¬unr-t | yes (b , s , refl) | some s₁ = G.≃-refl , ≈ˡ-refl
⋯ᵘ-⟦⟧ (x ∶ t) u | no ¬unr-t | no ¬chan rewrite eq-unr = G.≃-refl , ≈ˡ-refl
⋯ᵘ-⟦⟧ (Γ₁ ⸴[ o ] Γ₂) u =
  ≈ˢ-trans (≈ˢ-⸴ (⋯ᵘ-⟦⟧ Γ₁ u) (⋯ᵘ-⟦⟧ Γ₂ u))
           (eq-g , eq-l)
  where
    eq-g =
      let open G.≃-Reasoning in
      begin
        map-graph (app-repˢ u) (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⸴ᵍ[ o ] map-graph (app-repˢ u) (SemCtx.ord-graph ⟦ Γ₂ ⟧)
      ≃⟨ map-graph-⸴ᵍ (app-repˢ u) _ _ ⟩
        map-graph (app-repˢ u) (SemCtx.ord-graph ⟦ Γ₁ ⟧ ⸴ᵍ[ o ] SemCtx.ord-graph ⟦ Γ₂ ⟧)
      ∎
    eq-l =
      let open ≈ˡ-Reasoning in
      begin
        map (app-repˢ u) (SemCtx.unr-set ⟦ Γ₁ ⟧ ++ SemCtx.unr-set ⟦ Γ₂ ⟧)
      ≡⟨ ListP.map-++ (app-repˢ u) (SemCtx.unr-set ⟦ Γ₁ ⟧) (SemCtx.unr-set ⟦ Γ₂ ⟧) ⟩
        map (app-repˢ u) (SemCtx.unr-set ⟦ Γ₁ ⟧) ++ map (app-repˢ u) (SemCtx.unr-set ⟦ Γ₂ ⟧)
      ∎

≲ˢ-⋯ᵘ' : ∀ {γ₁ γ₂} u →
  γ₁ ≲ˢ γ₂ →
  (γ₁ ⋯ᵘˢ u) ≲ˢ (γ₂ ⋯ᵘˢ u)
≲ˢ-⋯ᵘ' u (g₁≲g₂ , l₁⊆l₂) = map-pres-≲ᵍ (app-repˢ u) g₁≲g₂ , ⊆-map (app-repˢ u) l₁⊆l₂

≲ˢ-⋯ᵘ : ∀ Γ₁ Γ₂ u →
  ⟦ Γ₁ ⟧ ≲ˢ ⟦ Γ₂ ⟧ →
  ⟦ Γ₁ ⋯ᵘ u ⟧ ≲ˢ ⟦ Γ₂ ⋯ᵘ u ⟧
≲ˢ-⋯ᵘ Γ₁ Γ₂ u γ₁≲γ₂ =
  ≲ˢ-trans (≈ˢ→≲ˢ (⋯ᵘ-⟦⟧ Γ₁ u))
           (≲ˢ-trans (≲ˢ-⋯ᵘ' u γ₁≲γ₂)
                     (≈ˢ→≲ˢ (≈ˢ-sym (⋯ᵘ-⟦⟧ Γ₂ u))))

≲-⋯ᵘ : ∀ u →
  Γ₁ ≲ Γ₂ →
  (Γ₁ ⋯ᵘ u) ≲ (Γ₂ ⋯ᵘ u)
≲-⋯ᵘ {Γ₁ = Γ₁} {Γ₂ = Γ₂} u (mk-≲ Γ₁≲Γ₂) = mk-≲ (≲ˢ-⋯ᵘ Γ₁ Γ₂ u Γ₁≲Γ₂)

⋯ᵘ-⟨⟩ᵘ : ∀ x b s b' s' →
  x ∶ Chan b s ⋯ᵘ ⟨ x , b' , s' ⟩ᵘ ≡ x ∶ Chan b' s'
⋯ᵘ-⟨⟩ᵘ x b s b' s' rewrite ≟-yes x = refl

≲-single-⋯ᵘ : ∀ {Γ x b s b' s'} →
  Γ ≲ x ∶ Chan b s →
  (Γ ⋯ᵘ ⟨ x , (b' , s') ⟩ᵘ) ≲ x ∶ Chan b' s'
≲-single-⋯ᵘ {Γ = Γ} {x = x} {b = b} {s = s} {b' = b'} {s' = s'} Γ≲x∶t =
  let open ≲-Reasoning in
  begin
    Γ ⋯ᵘ ⟨ x , b' , s' ⟩ᵘ
  ≲⟨ ≲-⋯ᵘ ⟨ x , (b' , s') ⟩ᵘ Γ≲x∶t ⟩
    x ∶ Chan b s ⋯ᵘ ⟨ x , b' , s' ⟩ᵘ
  ≡⟨ ⋯ᵘ-⟨⟩ᵘ x b s b' s' ⟩
    x ∶ Chan b' s'
  ∎

Unrᶜ-⋯ᵘ : ∀ Γ u →
  Unrᶜ Γ →
  Unrᶜ (Γ ⋯ᵘ u)
Unrᶜ-⋯ᵘ (x ∶ t) u unr-Γ p with Chan? t
… | no _ = unr-Γ p
… | yes (b , s₁ , refl) with u x
…   | none = unr-Γ p
…   | some s with p
…     | here refl with unr-Γ (here refl)
…       | ()
Unrᶜ-⋯ᵘ (Γ₁ ⸴[ o ] Γ₂) u unr-Γ y∈Γ with AnyP.++⁻ (binds (Γ₁ ⋯ᵘ u)) y∈Γ
… | inj₁ y∈Γ₁ = Unrᶜ-⋯ᵘ Γ₁ u (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ) y∈Γ₁
… | inj₂ y∈Γ₂ = Unrᶜ-⋯ᵘ Γ₂ u (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ) y∈Γ₂

⋯ᵘ-∈ : ∀ Γ u →
  x ∈ dom (Γ ⋯ᵘ u) →
  x ∈ dom Γ
⋯ᵘ-∈ ·              u x∈Γu = x∈Γu
⋯ᵘ-∈ (x ∶ t)        u x∈Γu with Chan? t
… | no _ = x∈Γu
… | yes _ with u x
…   | none = x∈Γu
…   | some _ = x∈Γu
⋯ᵘ-∈ (Γ₁ ⸴[ o ] Γ₂) u x∈Γu
  rewrite ListP.map-++ proj₁ (binds (Γ₁ ⋯ᵘ u)) (binds (Γ₂ ⋯ᵘ u))
 with AnyP.++⁻ (dom (Γ₁ ⋯ᵘ u)) x∈Γu
… | inj₁ x∈Γ₁u =
  subst (_ ∈_) (sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))) $
  AnyP.++⁺ˡ $
  ⋯ᵘ-∈ Γ₁ u x∈Γ₁u
… | inj₂ x∈Γ₂u =
  subst (_ ∈_) (sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))) $
  AnyP.++⁺ʳ _ $
  ⋯ᵘ-∈ Γ₂ u x∈Γ₂u

⋯ᵘ-∉ : ∀ Γ u →
  x ∉ dom Γ →
  x ∉ dom (Γ ⋯ᵘ u)
⋯ᵘ-∉ Γ u x∉Γ x∈Γu = x∉Γ (⋯ᵘ-∈ Γ u x∈Γu)

⋯ᵘ-dist-[] : ∀ C Γ u →
  (C [ Γ ]) ⋯ᵘ u ≡ (C ⋯ᵘᶜ u) [ Γ ⋯ᵘ u ]
⋯ᵘ-dist-[] C Γ u = >>=ᶜ-dist-[] C Γ (app-rep u)

⋯ᵘ-id' : ∀ x t u →
 (∀ b (s : Session b) → t ≡ Chan b s → u x ≡ some (b , s)) →
 (x ∶ t) ⋯ᵘ u ≡ x ∶ t
⋯ᵘ-id' x t u f
 with Chan? t
… | no _ = refl
… | yes (b , s , refl)
 with u x
… | none           = refl
… | (some (b₁ , s₁)) with refl ← f b s refl = refl

-ᵘ-∉ : ∀ u x y →
  x ≢ y →
  (u -ᵘ x) y ≡ u y
-ᵘ-∉ u x y x≢y rewrite ≟-no x y x≢y = refl

⋯ᵘ--ᵘ-∉ : ∀ Γ u →
  x ∉ dom Γ →
  Γ ⋯ᵘ (u -ᵘ x) ≡ Γ ⋯ᵘ u 
⋯ᵘ--ᵘ-∉ {x = x} · u x∉Γ = refl
⋯ᵘ--ᵘ-∉ {x = x} (y ∶ t) u x∉Γ
  with Chan? t
… | no _ = refl
… | yes _
  with x ≟ y
… | yes refl = ⊥-elim (x∉Γ (here refl))
… | no ¬x≡y 
  with u y in eq
… | none = refl
… | (some (b , s)) = refl
⋯ᵘ--ᵘ-∉ {x = x} (Γ₁ ⸴[ o ] Γ₂) u x∉Γ =
  let x∉Γ₁++Γ₂ = subst (x ∉_) (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) x∉Γ in
  let x∉Γ₁ , x∉Γ₂ = ∉-++⁻ (dom Γ₁) (dom Γ₂) x∉Γ₁++Γ₂ in
  cong₂ _⸴[ o ]_ (⋯ᵘ--ᵘ-∉ Γ₁ u x∉Γ₁) (⋯ᵘ--ᵘ-∉ Γ₂ u x∉Γ₂)

⋯ᵘ-used : ∀ x t u →
  (∀ b (s : Session b) → t ≡ Chan b s → u x ≡ some (b , s)) →
  x ∶ t ⋯ᵘ u ≡ x ∶ t
⋯ᵘ-used x t u chan→used
 with Chan? t
… | no _ = refl
… | yes (b , s , refl) rewrite chan→used _ _ refl = refl

⋯ᵘ-pres-Unrᶜ : ∀ Γ u → Unrᶜ Γ → Unrᶜ (Γ ⋯ᵘ u)
⋯ᵘ-pres-Unrᶜ · u unr-Γ = λ ()
⋯ᵘ-pres-Unrᶜ (x ∶ t) u unr-Γ p
  with Chan? t
… | no _ = unr-Γ p
… | yes (b , s , refl)
  with u x
… | none           = unr-Γ p
… | (some (b , s)) with here refl ← p with () ← unr-Γ (here refl)
⋯ᵘ-pres-Unrᶜ (Γ₁ ⸴[ o ] Γ₂) u unr-Γ =
  Unrᶜ-⸴ (Γ₁ ⋯ᵘ u) o (Γ₂ ⋯ᵘ u)
         (⋯ᵘ-pres-Unrᶜ Γ₁ u (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ))
         (⋯ᵘ-pres-Unrᶜ Γ₂ u (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ))

⋯ᵘᶜ-pres-LeftCtx : ∀ C u → LeftCtx C → LeftCtx (C ⋯ᵘᶜ u)
⋯ᵘᶜ-pres-LeftCtx [] u cct-[] = cct-[]
⋯ᵘᶜ-pres-LeftCtx (C ⸴[ o ]₁ Γ) u (cct-⸴₁ q C-left) =
  cct-⸴₁ (λ ()) (⋯ᵘᶜ-pres-LeftCtx C u C-left)
⋯ᵘᶜ-pres-LeftCtx (Γ ⸴[ o ]₂ C) u (cct-⸴₂ q C-left)
  with q refl
… | inj₁ o≡unordered = cct-⸴₂ (λ _ → inj₁ o≡unordered)
                              (⋯ᵘᶜ-pres-LeftCtx C u C-left)
… | inj₂ unr-Γ       = cct-⸴₂ (λ _ → inj₂ (⋯ᵘ-pres-Unrᶜ Γ u unr-Γ))
                              (⋯ᵘᶜ-pres-LeftCtx C u C-left)

LocallyEqᵘ : List Id → UsageMap → UsageMap → Set
LocallyEqᵘ xs u₁ u₂ = ∀ x → x ∈ xs → u₁ x ≡ u₂ x

reflᵘ : ∀ {xs} {u} → LocallyEqᵘ xs u u
reflᵘ x x∈xs = refl

symᵘ :  ∀ {xs} {u₁ u₂} →
  LocallyEqᵘ xs u₁ u₂ →
  LocallyEqᵘ xs u₂ u₁
symᵘ eq x x∈xs = sym (eq x x∈xs)

eqᵘ : 
  u₁ ≡ u₂ →
  LocallyEqᵘ xs u₁ u₂
eqᵘ refl = reflᵘ

transᵘ :  ∀ {xs} {u₁ u₂ u₃} →
  LocallyEqᵘ xs u₁ u₂ →
  LocallyEqᵘ xs u₂ u₃ →
  LocallyEqᵘ xs u₁ u₃
transᵘ eq₁ eq₂ x x∈xs = trans (eq₁ x x∈xs) (eq₂ x x∈xs)

LocallyEqᵘ-⊆ : ∀ {xs ys u₁ u₂} →
  xs ⊆ ys →
  LocallyEqᵘ ys u₁ u₂ →
  LocallyEqᵘ xs u₁ u₂
LocallyEqᵘ-⊆ xs⊆ys eq x x∈xs = eq x (xs⊆ys x∈xs)

LocallyEqᵘ-split : ∀ Γ₁ o Γ₂ u₁ u₂ →
  LocallyEqᵘ (dom (Γ₁ ⸴[ o ] Γ₂)) u₁ u₂ →
  LocallyEqᵘ (dom Γ₁) u₁ u₂ × LocallyEqᵘ (dom Γ₂) u₁ u₂
LocallyEqᵘ-split Γ₁ o Γ₂ u₁ u₂ eq =
  let eq' : LocallyEqᵘ (dom Γ₁ ++ dom Γ₂) u₁ u₂
      eq' = subst (λ ■ → LocallyEqᵘ ■ u₁ u₂)
                  (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))
                  eq in
  (λ x x∈Γ₁ → eq' x (AnyP.++⁺ˡ x∈Γ₁)) , λ x x∈Γ₂ → eq' x (AnyP.++⁺ʳ _ x∈Γ₂)

⋯ᵘ-locally-eq : ∀ Γ u₁ u₂ → LocallyEqᵘ (dom Γ) u₁ u₂ → Γ ⋯ᵘ u₁ ≡ Γ ⋯ᵘ u₂
⋯ᵘ-locally-eq · u₁ u₂ eq = refl
⋯ᵘ-locally-eq (x ∶ t) u₁ u₂ eq
  with Chan? t
… | no _ = refl
… | yes _
  using u₁x≡u₂x ← eq x (here refl)
  with u₁ x in eq₁
… | none           rewrite trans (sym u₁x≡u₂x) eq₁ = refl
… | (some (b , s)) rewrite trans (sym u₁x≡u₂x) eq₁ = refl
⋯ᵘ-locally-eq (Γ₁ ⸴[ o ] Γ₂) u₁ u₂ eq =
  let eq₁ , eq₂ = LocallyEqᵘ-split Γ₁ o Γ₂ u₁ u₂ eq in
  cong₂ _⸴[ o ]_
        (⋯ᵘ-locally-eq Γ₁ u₁ u₂ eq₁)
        (⋯ᵘ-locally-eq Γ₂ u₁ u₂ eq₂)

⋯ᵘᶜ-locally-eq : ∀ C u₁ u₂ → LocallyEqᵘ (dom (C [ · ])) u₁ u₂ → C ⋯ᵘᶜ u₁ ≡ C ⋯ᵘᶜ u₂
⋯ᵘᶜ-locally-eq [] u₁ u₂ eq = refl
⋯ᵘᶜ-locally-eq (C ⸴[ o ]₁ Γ) u₁ u₂ eq =
  let eq₁ , eq₂ = LocallyEqᵘ-split (C [ · ]) o Γ u₁ u₂ eq in
  cong₂ _⸴[ o ]₁_
        (⋯ᵘᶜ-locally-eq C u₁ u₂ eq₁)
        (⋯ᵘ-locally-eq Γ u₁ u₂ eq₂)
⋯ᵘᶜ-locally-eq (Γ ⸴[ o ]₂ C) u₁ u₂ eq =
  let eq₁ , eq₂ = LocallyEqᵘ-split Γ o (C [ · ]) u₁ u₂ eq in
  cong₂ _⸴[ o ]₂_
        (⋯ᵘ-locally-eq Γ u₁ u₂ eq₁)
        (⋯ᵘᶜ-locally-eq C u₁ u₂ eq₂)

·ᵘ-locally-eq : ∀ xs u₁₁ u₁₂ u₂₁ u₂₂ →
  LocallyEqᵘ xs u₁₁ u₂₁ →
  LocallyEqᵘ xs u₁₂ u₂₂ →
  LocallyEqᵘ xs (u₁₁ ·ᵘ u₁₂) (u₂₁ ·ᵘ u₂₂)
·ᵘ-locally-eq xs u₁₁ u₁₂ u₂₁ u₂₂ eq₁ eq₂ x x∈xs =
  cong₂ _·ᵘᵐ_ (eq₁ x x∈xs) (eq₂ x x∈xs)

-ᵘ-locally-eq-∉ : ∀ {x} {xs} u  →
  x ∉ xs →
  LocallyEqᵘ xs (u -ᵘ x) u
-ᵘ-locally-eq-∉ {x} {xs} u x∉xs y y∈xs
  with x ≟ y
… | yes refl = ⊥-elim (x∉xs y∈xs)
… | no ¬x≡y  = refl

LocallyEqᵘ? : ∀ xs u₁ u₂ → Dec (LocallyEqᵘ xs u₁ u₂)
LocallyEqᵘ? [] u₁ u₂ = yes (λ _ ())
LocallyEqᵘ? (x ∷ xs) u₁ u₂
  with LocallyEqᵘ? xs u₁ u₂
… | no u₁≢u₂ = no (λ u₁≡u₂ → u₁≢u₂ (λ y y∈xs → u₁≡u₂ y (there y∈xs)))
… | yes u₁≡u₂
  with u₁ x ≟ u₂ x
… | no u₁x≢u₂x = no (λ u₁≡u₂ → u₁x≢u₂x (u₁≡u₂ x (here refl)))
… | yes u₁x≡u₂x = yes λ where
  y (here refl) → u₁x≡u₂x
  y (there y∈) → u₁≡u₂ y y∈
