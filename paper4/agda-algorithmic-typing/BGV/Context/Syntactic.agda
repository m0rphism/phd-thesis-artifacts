module BGV.Context.Syntactic where

open import Data.List as L using (List; []; _∷_; _++_)
import Data.List.Properties as ListP
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
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Function using (case_of_; _$_)

open import BGV.Util.Decidable
open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Types
open import BGV.Util.List
open import BGV.Id
open import BGV.Util.Graph as G using (Graph)
open import BGV.Context.Semantic

-- Specification

infix  7 _∶_

data Ctx : Set where
  ·      : Ctx
  _∶_    : Id → Type → Ctx
  _⸴[_]_ : Ctx → IsOrd → Ctx → Ctx

pattern _∥_ Γ₁ Γ₂ = _⸴[_]_ Γ₁ unordered Γ₂
pattern _⸴_ Γ₁ Γ₂ = _⸴[_]_ Γ₁ ordered Γ₂

infix 5 _⸴[_]_ _⸴_ _∥_

variable
  Γ Γ₁ Γ₂ Γ₃ Γ' Γ₁' Γ₂' Γ₃' Γ'' Γᵤ : Ctx

binds : Ctx → List (Id × Type)
binds ·              = []
binds (x ∶ t)        = L.[ x , t ]
binds (Γ₁ ⸴[ o ] Γ₂) = binds Γ₁ ++ binds Γ₂

dom : Ctx → List Id
dom Γ = L.map proj₁ (binds Γ)

ext : Mult → Ctx → Ctx → Ctx
ext ∞ Γ₁ Γ₂ = Γ₁ ⸴ Γ₂
ext 𝟙 Γ₁ Γ₂ = Γ₁ ∥ Γ₂
ext ≻ Γ₁ Γ₂ = Γ₁ ⸴ Γ₂
ext ≺ Γ₁ Γ₂ = Γ₂ ⸴ Γ₁

Unrᶜ : Ctx → Set
Unrᶜ Γ = ∀ {x t} → (x , t) ∈ binds Γ → Unr t

⟦_⟧ : Ctx → SemCtx
⟦ ·            ⟧ = ∅
⟦ x ∶ t        ⟧ = x ∶ˢ t
⟦ Γ₁ ⸴[ o ] Γ₂ ⟧ = ⟦ Γ₁ ⟧ ⸴ˢ[ o ] ⟦ Γ₂ ⟧

infix 3 _≈_ _≲_

record _≈_ (Γ₁ Γ₂ : Ctx) : Set₁ where
  constructor mk-≈
  field
    prf : ⟦ Γ₁ ⟧ ≈ˢ ⟦ Γ₂ ⟧

record _≲_ (Γ₁ Γ₂ : Ctx) : Set₁ where
  constructor mk-≲
  field
    prf : ⟦ Γ₁ ⟧ ≲ˢ ⟦ Γ₂ ⟧

infixl 6 _↓_
_↓_ : Ctx → List Id → Ctx
·              ↓ xs = ·
x ∶ t          ↓ xs with x ∈? xs
...                    | no ¬x∈xs = ·
...                    | yes x∈xs = x ∶ t
(Γ₁ ⸴[ o ] Γ₂) ↓ xs = (Γ₁ ↓ xs) ⸴[ o ] (Γ₂ ↓ xs)

-- Properties

Unrᶜ? : (Γ : Ctx) → Dec (Unrᶜ Γ)
Unrᶜ? ·              = yes λ()
Unrᶜ? (x ∶ t)        with Unr? t
… | yes unr-t = yes λ { (here refl) → unr-t }
… | no ¬unr-t = no λ unrᶜ → ¬unr-t (unrᶜ (here refl))
Unrᶜ? (Γ₁ ⸴[ o ] Γ₂) with Unrᶜ? Γ₁ | Unrᶜ? Γ₂
… | yes unr-Γ₁ | yes unr-Γ₂ = yes λ x∈Γ₁⸴Γ₂ → case AnyP.++⁻ _ x∈Γ₁⸴Γ₂ of λ where
                                                (inj₁ x∈Γ₁) → unr-Γ₁ x∈Γ₁
                                                (inj₂ x∈Γ₂) → unr-Γ₂ x∈Γ₂
… | no ¬unr-Γ₁ | _          = no λ unrᶜ-Γ₁⸴Γ₂ → ¬unr-Γ₁ λ x∈Γ₁ → unrᶜ-Γ₁⸴Γ₂ (AnyP.++⁺ˡ x∈Γ₁)
… | _          | no ¬unr-Γ₂ = no λ unrᶜ-Γ₁⸴Γ₂ → ¬unr-Γ₂ λ x∈Γ₂ → unrᶜ-Γ₁⸴Γ₂ (AnyP.++⁺ʳ _ x∈Γ₂)

instance
  Dec-Unrᶜ : ∀ {Γ : Ctx} → Dec (Unrᶜ Γ)
  Dec-Unrᶜ {Γ} = Unrᶜ? Γ

≲-refl : Γ ≲ Γ
≲-refl {Γ = Γ} = mk-≲ ≲ˢ-refl

≲-trans : ∀ {Γ₁ Γ₂ Γ₃} → Γ₁ ≲ Γ₂ → Γ₂ ≲ Γ₃ → Γ₁ ≲ Γ₃
≲-trans (mk-≲ p) (mk-≲ q) = mk-≲ (≲ˢ-trans p q)

_≲?_ : ∀ Γ₁ Γ₂ → Dec (Γ₁ ≲ Γ₂)
Γ₁ ≲? Γ₂ with ⟦ Γ₁ ⟧ ≲ˢ? ⟦ Γ₂ ⟧
… | yes p = yes (mk-≲ p)
… | no ¬p = no λ (mk-≲ p) → ¬p p

∈→∈ˢ : ∀ {xt} Γ →
 xt ∈ binds Γ →
 xt ∈ˢ ⟦ Γ ⟧
∈→∈ˢ (x ∶ t) (here refl) = x∈ˢx {t = t}
∈→∈ˢ (Γ₁ ⸴[ o ] Γ₂) x∈
 with AnyP.++⁻ (binds Γ₁) x∈
... | inj₁ xt∈Γ₁ = ∈ˢ-⸴₁ o (∈→∈ˢ Γ₁ xt∈Γ₁)
... | inj₂ xt∈Γ₂ = ∈ˢ-⸴₂ o (∈→∈ˢ Γ₂ xt∈Γ₂)

∈ˢ→∈ : ∀ {xt} Γ →
 xt ∈ˢ ⟦ Γ ⟧ →
 xt ∈ binds Γ
∈ˢ→∈ · (inj₁ ())
∈ˢ→∈ · (inj₂ ())
∈ˢ→∈ (x ∶ t) (inj₁ (n , refl)) with Unr? t
… | yes unr-t = case n of λ ()
… | no ¬unr-t = here refl
∈ˢ→∈ (x ∶ t) (inj₂ y) with Unr? t
… | yes unr-t = y
… | no ¬unr-t = there y
∈ˢ→∈ (Γ₁ ⸴[ o ] Γ₂) xt∈ with ∈ˢ-⸴ {γ₁ = ⟦ Γ₁ ⟧} o xt∈
... | inj₁ xt∈Γ₁ = AnyP.++⁺ˡ (∈ˢ→∈ Γ₁ xt∈Γ₁)
... | inj₂ xt∈Γ₂ = AnyP.++⁺ʳ _ (∈ˢ→∈ Γ₂ xt∈Γ₂)

∉→∉ˢ : ∀ {xt} Γ →
 xt ∉ binds Γ →
 ¬ xt ∈ˢ ⟦ Γ ⟧
∉→∉ˢ Γ x∉ x∈ˢ = x∉ (∈ˢ→∈ Γ x∈ˢ)

∉ˢ→∉ : ∀ {xt} Γ →
 ¬ xt ∈ˢ ⟦ Γ ⟧ →
 xt ∉ binds Γ
∉ˢ→∉ Γ x∉ˢ x∈ = x∉ˢ (∈→∈ˢ Γ x∈)

≲-pres-∉' : ∀ {xt} →
  Γ₁ ≲ Γ₂ →
  xt ∉ binds Γ₁ →
  xt ∉ binds Γ₂
≲-pres-∉' {Γ₁ = Γ₁} {Γ₂ = Γ₂} (mk-≲ p) x∉ = ∉ˢ→∉ Γ₂ (≲ˢ-pres-∉ p (∉→∉ˢ Γ₁ x∉))

∈dom→∈binds : ∀ Γ →
  x ∈ dom Γ →
  ∃[ t ] (x , t) ∈ binds Γ
∈dom→∈binds (x ∶ t) (here refl) = t , here refl
∈dom→∈binds (Γ₁ ⸴[ o ] Γ₂) x∈
 with AnyP.++⁻ _ (AnyP.map⁻ x∈)
... | inj₁ x∈Γ₁ = let (t , x) = ∈dom→∈binds Γ₁ (AnyP.map⁺ x∈Γ₁) in t , AnyP.++⁺ˡ x
... | inj₂ x∈Γ₂ = let (t , x) = ∈dom→∈binds Γ₂ (AnyP.map⁺ x∈Γ₂) in t , AnyP.++⁺ʳ _ x

∈binds→∈dom : ∀ Γ →
  (x , t) ∈ binds Γ →
  x ∈ dom Γ
∈binds→∈dom (x ∶ t) (here refl) = here refl
∈binds→∈dom (Γ₁ ⸴[ o ] Γ₂) xt∈
 with AnyP.++⁻ _ xt∈
... | inj₁ xt∈Γ₁ = AnyP.map⁺ (AnyP.++⁺ˡ (AnyP.map⁻ (∈binds→∈dom Γ₁ xt∈Γ₁)))
... | inj₂ xt∈Γ₂ = AnyP.map⁺ (AnyP.++⁺ʳ _ (AnyP.map⁻ (∈binds→∈dom Γ₂ xt∈Γ₂)))

∉dom→∉binds : ∀ Γ →
  x ∉ dom Γ →
  ¬ (∃[ t ] (x , t) ∈ binds Γ)
∉dom→∉binds Γ p (t , q) = p (∈binds→∈dom Γ q)

∉binds→∉dom : ∀ Γ →
  ¬ (∃[ t ] (x , t) ∈ binds Γ) →
  x ∉ dom Γ
∉binds→∉dom Γ p q = p (∈dom→∈binds Γ q)

≲-pres-∉ :
  Γ₁ ≲ Γ₂ →
  x ∉ dom Γ₁ →
  x ∉ dom Γ₂
≲-pres-∉ {Γ₁ = Γ₁} {Γ₂ = Γ₂} p x∉Γ₁ = ∉binds→∉dom Γ₂ λ (t , pp) → ≲-pres-∉' p (λ x₁ → ∉dom→∉binds Γ₁ x∉Γ₁ (t , x₁)) pp

≈-·ˡ : Γ ≈ · ⸴[ o ] Γ
≈-·ˡ = mk-≈ ≈ˢ-·ˡ

≈-·ʳ : Γ ≈ Γ ⸴[ o ] ·
≈-·ʳ = mk-≈ ≈ˢ-·ʳ

≈-dup-unr : Unr t → (x ∶ t) ≈ (x ∶ t) ⸴[ o ] (x ∶ t)
≈-dup-unr unr-t = mk-≈ (≈ˢ-dup-unr unr-t)

≈-⸴ : Γ₁ ≈ Γ₁' → Γ₂ ≈ Γ₂' → (Γ₁ ⸴[ o ] Γ₂) ≈ (Γ₁' ⸴[ o ] Γ₂')
≈-⸴ (mk-≈ p) (mk-≈ q) = mk-≈ (≈ˢ-⸴ p q)

≈-sym : Γ₁ ≈ Γ₂ → Γ₂ ≈ Γ₁
≈-sym (mk-≈ p) = mk-≈ (≈ˢ-sym p)

≈-refl : Γ ≈ Γ
≈-refl = mk-≈ ≈ˢ-refl

≲-⸴ : Γ₁ ≲ Γ₁' → Γ₂ ≲ Γ₂' → (Γ₁ ⸴[ o ] Γ₂) ≲ (Γ₁' ⸴[ o ] Γ₂')
≲-⸴ (mk-≲ p) (mk-≲ q) = mk-≲ (≲ˢ-⸴ p q)

⸴-assoc : ∀ Γ₁ Γ₂ Γ₃ → ((Γ₁ ⸴[ o ] Γ₂) ⸴[ o ] Γ₃) ≈ (Γ₁ ⸴[ o ] (Γ₂ ⸴[ o ] Γ₃))
⸴-assoc Γ₁ Γ₂ Γ₃ = mk-≈ (⸴ˢ-assoc ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ ⟦ Γ₃ ⟧)

∥-comm : ∀ Γ₁ Γ₂ → Γ₁ ∥ Γ₂ ≈ Γ₂ ∥ Γ₁
∥-comm Γ₁ Γ₂ = mk-≈ (∥ˢ-comm ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧)

≲-dist-∥-⸴ : ∀ Γ₁₁ Γ₁₂ Γ₂₁ Γ₂₂ → (Γ₁₁ ⸴ Γ₁₂) ∥ (Γ₂₁ ⸴ Γ₂₂) ≲ (Γ₁₁ ∥ Γ₂₁) ⸴ (Γ₁₂ ∥ Γ₂₂)
≲-dist-∥-⸴ Γ₁₁ Γ₁₂ Γ₂₁ Γ₂₂ = mk-≲ (≲ˢ-dist-∥-⸴ ⟦ Γ₁₁ ⟧ ⟦ Γ₁₂ ⟧ ⟦ Γ₂₁ ⟧ ⟦ Γ₂₂ ⟧)

∥≲⸴ : ∀ Γ₁ Γ₂ → Γ₁ ∥ Γ₂ ≲ Γ₁ ⸴ Γ₂
∥≲⸴ Γ₁ Γ₂ = mk-≲ (∥≲ˢ⸴ ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧)

≈→≲ : Γ₁ ≈ Γ₂ → Γ₁ ≲ Γ₂
≈→≲ (mk-≈ p) = mk-≲ (≈ˢ→≲ˢ p)

Unrᶜ-⸴₁ : ∀ Γ₁ o Γ₂ → Unrᶜ (Γ₁ ⸴[ o ] Γ₂) → Unrᶜ Γ₁
Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ xt∈Γ₁ = unr-Γ (AnyP.++⁺ˡ xt∈Γ₁)

Unrᶜ-⸴₂ : ∀ Γ₁ o Γ₂ → Unrᶜ (Γ₁ ⸴[ o ] Γ₂) → Unrᶜ Γ₂
Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ xt∈Γ₂ = unr-Γ (AnyP.++⁺ʳ _ xt∈Γ₂)

Unrᶜ→∅ : ∀ Γ → Unrᶜ Γ → SemCtx.ord-graph ⟦ Γ ⟧ G.≃ G.∅
Unrᶜ→∅ · unr-Γ = G.≃-refl
Unrᶜ→∅ (x ∶ t) unr-Γ with Unr? t
… | yes unr-t = G.≃-refl
… | no ¬unr-t = ⊥-elim (¬unr-t (unr-Γ (here refl)))
Unrᶜ→∅ (Γ₁ ⸴[ ordered   ] Γ₂) unr-Γ =
  let open G.≃-Reasoning in
  begin
    SemCtx.ord-graph ⟦ Γ₁ ⟧ G.+ SemCtx.ord-graph ⟦ Γ₂ ⟧
  ≃⟨ G.≃-+ (Unrᶜ→∅ Γ₁ (Unrᶜ-⸴₁ Γ₁ ordered Γ₂ unr-Γ)) (Unrᶜ→∅ Γ₂ (Unrᶜ-⸴₂ Γ₁ ordered Γ₂ unr-Γ)) ⟩
    G.∅ G.+ G.∅
  ≃⟨ G.+-identityˡ G.∅ ⟩
    G.∅
  ∎
Unrᶜ→∅ (Γ₁ ⸴[ unordered ] Γ₂) unr-Γ =
  let open G.≃-Reasoning in
  begin
    SemCtx.ord-graph ⟦ Γ₁ ⟧ G.∪ SemCtx.ord-graph ⟦ Γ₂ ⟧
  ≃⟨ G.≃-∪ (Unrᶜ→∅ Γ₁ (Unrᶜ-⸴₁ Γ₁ ordered Γ₂ unr-Γ)) (Unrᶜ→∅ Γ₂ (Unrᶜ-⸴₂ Γ₁ ordered Γ₂ unr-Γ)) ⟩
    G.∅ G.∪ G.∅
  ≃⟨ G.∪-identityˡ G.∅ ⟩
    G.∅
  ∎

≲-lem₁ : ∀ Γ₁ Γ₂ Γ₃ → (Γ₁ ⸴ Γ₂) ⸴[ o ] Γ₃ ≲ Γ₁ ⸴ (Γ₂ ⸴[ o ] Γ₃)
≲-lem₁ Γ₁ Γ₂ Γ₃ = mk-≲ (≲ˢ-lem₁ ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ ⟦ Γ₃ ⟧)

≲-lem₁' : ∀ Γ₁ Γ₂ Γ₃ → Γ₁ ⸴[ o ] (Γ₂ ⸴ Γ₃) ≲ (Γ₁ ⸴[ o ] Γ₂) ⸴ Γ₃
≲-lem₁' Γ₁ Γ₂ Γ₃ = mk-≲ (≲ˢ-lem₁' ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ ⟦ Γ₃ ⟧)

≲-lem₂ : ∀ Γ Γ₁ Γ₂ → o ≡ unordered ⊎ Unrᶜ Γ → Γ ⸴[ o ] (Γ₁ ⸴ Γ₂) ≲ Γ₁ ⸴ (Γ₂ ⸴[ o ] Γ)
≲-lem₂ Γ Γ₁ Γ₂ x = mk-≲ (≲ˢ-lem₂ ⟦ Γ ⟧ ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ (⊎.map (λ x → x) (Unrᶜ→∅ Γ) x))

≲-lem₂''' : ∀ Γ Γ₁ Γ₂ → o ≡ unordered ⊎ Unrᶜ Γ → Γ ⸴[ o ] (Γ₁ ∥ Γ₂) ≲ (Γ ⸴[ o ] Γ₁) ∥ Γ₂
≲-lem₂''' Γ Γ₁ Γ₂ x = mk-≲ (≲ˢ-lem₂''' ⟦ Γ ⟧ ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ (⊎.map (λ x → x) (Unrᶜ→∅ Γ) x))

≲-lem₂' : ∀ Γ Γ₁ Γ₂ → o ≡ unordered ⊎ Unrᶜ Γ → (Γ₂ ⸴ Γ₁) ⸴[ o ] Γ ≲ (Γ ⸴[ o ] Γ₂) ⸴ Γ₁
≲-lem₂' Γ Γ₁ Γ₂ x = mk-≲ (≲ˢ-lem₂' ⟦ Γ ⟧ ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ (⊎.map (λ x → x) (Unrᶜ→∅ Γ) x))

≲-lem₂'' : ∀ Γ Γ₁ Γ₂ → o ≡ unordered ⊎ Unrᶜ Γ → (Γ₁ ∥ Γ₂) ⸴[ o ] Γ ≲ (Γ₁ ⸴[ o ] Γ) ∥ Γ₂
≲-lem₂'' Γ Γ₁ Γ₂ x = mk-≲ (≲ˢ-lem₂'' ⟦ Γ ⟧ ⟦ Γ₁ ⟧ ⟦ Γ₂ ⟧ (⊎.map (λ x → x) (Unrᶜ→∅ Γ) x))

module ≲-Reasoning where
  infix 1 begin_
  infixr 2 _≲⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_ _≈⟨_⟩_
  infix 3 _∎

  begin_ : Γ₁ ≲ Γ₂ → Γ₁ ≲ Γ₂
  begin p = p

  _≲⟨_⟩_ : ∀ Γ₁ {Γ₂ Γ₃} → Γ₁ ≲ Γ₂ → Γ₂ ≲ Γ₃ → Γ₁ ≲ Γ₃
  _ ≲⟨ p ⟩ q = ≲-trans p q

  _≈⟨_⟩_ : ∀ Γ₁ {Γ₂ Γ₃} → Γ₁ ≈ Γ₂ → Γ₂ ≲ Γ₃ → Γ₁ ≲ Γ₃
  _ ≈⟨ p ⟩ q = ≲-trans (≈→≲ p) q

  _≡⟨_⟩_ : ∀ Γ₁ {Γ₂ Γ₃} → Γ₁ ≡ Γ₂ → Γ₂ ≲ Γ₃ → Γ₁ ≲ Γ₃
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ :  ∀ Γ₁ {Γ₂} → Γ₁ ≲ Γ₂ → Γ₁ ≲ Γ₂
  _ ≡⟨⟩ q = q

  _∎ : ∀ Γ → Γ ≲ Γ
  _ ∎ = ≲-refl

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; module ≅-Reasoning)
open import Function using (_∋_)

⊆binds→⊆dom : ∀ Γ₁ Γ₂ →
  binds Γ₁ ⊆ binds Γ₂ →
  dom Γ₁ ⊆ dom  Γ₂
⊆binds→⊆dom Γ₁ Γ₂ Γ₁⊆Γ₂ x∈dom₁ =
  let (t , xt∈Γ₁) = ∈dom→∈binds Γ₁ x∈dom₁ in
  let xt∈Γ₂ = Γ₁⊆Γ₂ xt∈Γ₁ in
  ∈binds→∈dom Γ₂ xt∈Γ₂ 

∈→∈ˢ' : ∀ {xt} Γ →
 xt ∈ binds Γ →
 xt ∈ˢ' ⟦ Γ ⟧
∈→∈ˢ' (x ∶ t) (here refl) = x∈ˢ'x {t = t} -- x∈ˢx {t = t}
∈→∈ˢ' (Γ₁ ⸴[ o ] Γ₂) x∈
 with AnyP.++⁻ (binds Γ₁) x∈
... | inj₁ xt∈Γ₁ = ∈ˢ'-⸴₁ o (∈→∈ˢ' Γ₁ xt∈Γ₁)
... | inj₂ xt∈Γ₂ = ∈ˢ'-⸴₂ o (∈→∈ˢ' Γ₂ xt∈Γ₂)

≲-pres-∈' : ∀ {xt} →
  Γ₁ ≲ Γ₂ →
  xt ∈ binds Γ₂ →
  xt ∈ binds Γ₁
≲-pres-∈' {Γ₁ = Γ₁} {Γ₂ = Γ₂} (mk-≲ p) x∈ = ∈ˢ→∈ Γ₁ (≲ˢ-pres-∈ p (∈→∈ˢ Γ₂ x∈))

≲→⊆binds :
  Γ₁ ≲ Γ₂ →
  binds Γ₂ ⊆ binds Γ₁
≲→⊆binds Γ₁≲Γ₂ = ≲-pres-∈' Γ₁≲Γ₂

≲→⊆dom :
  Γ₁ ≲ Γ₂ →
  dom Γ₂ ⊆ dom Γ₁
≲→⊆dom {Γ₁ = Γ₁} {Γ₂ = Γ₂} Γ₁≲Γ₂ = ⊆binds→⊆dom Γ₂ Γ₁ (≲→⊆binds Γ₁≲Γ₂)

no₁ : ∀ Γ → (x , t) ∉ binds Γ → ¬ (Γ ≲ x ∶ t)
no₁ {t = t} Γ xt∉ p = xt∉ (≲-pres-∈' p (here refl))

x∶t≲ˢ∅ : Unr t → x ∶ˢ t ≲ˢ ∅
x∶t≲ˢ∅ {t} unr-t with Unr? t
… | yes unr-t = ≲ᵍ-refl , λ ()
… | no ¬unr-t = ⊥-elim (¬unr-t unr-t)

UnrΓ≲· : Unrᶜ Γ → Γ ≲ ·
UnrΓ≲· {Γ = ·} unr-Γ = ≲-refl
UnrΓ≲· {Γ = x ∶ t} unr-Γ = mk-≲ (x∶t≲ˢ∅ (unr-Γ (here refl)))
UnrΓ≲· {Γ = Γ₁ ⸴[ o ] Γ₂} unr-Γ =
  let open ≲-Reasoning in
  begin
    Γ₁ ⸴[ o ] Γ₂
  ≲⟨ ≲-⸴ (UnrΓ≲· (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ)) (UnrΓ≲· (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ)) ⟩
    · ⸴[ o ] ·
  ≈⟨ ≈-sym ≈-·ˡ ⟩
    ·
  ∎

≲-UnrΓʳ : Unrᶜ Γ' → Γ ⸴[ o ] Γ' ≲ Γ
≲-UnrΓʳ {Γ'} {Γ} {o} unr-Γ' =
  let open ≲-Reasoning in
  begin
    Γ ⸴[ o ] Γ'
  ≲⟨ ≲-⸴ ≲-refl (UnrΓ≲· unr-Γ') ⟩
    Γ ⸴[ o ] ·
  ≈⟨ ≈-sym ≈-·ʳ ⟩
    Γ
  ∎

≲-UnrΓˡ : Unrᶜ Γ' → Γ' ⸴[ o ] Γ ≲ Γ
≲-UnrΓˡ {Γ'} {o} {Γ} unr-Γ' =
  let open ≲-Reasoning in
  begin
    Γ' ⸴[ o ] Γ
  ≲⟨ ≲-⸴ (UnrΓ≲· unr-Γ') ≲-refl ⟩
    · ⸴[ o ] Γ
  ≈⟨ ≈-sym ≈-·ˡ ⟩
    Γ
  ∎

-- Remove the left-most occurence of a binding
infixl 6 _↓ᵇ_
_↓ᵇ_ : Ctx → (Id × Type) → Ctx
·              ↓ᵇ (x , t) = ·
y ∶ t'         ↓ᵇ (x , t) with x ≟ y | t ≟ t'
...                     | yes p | yes q = ·
...                     | _     | _     = y ∶ t'
(Γ₁ ⸴[ o ] Γ₂) ↓ᵇ b with b ∈? binds Γ₁
… | yes b∈Γ₁ = (Γ₁ ↓ᵇ b) ⸴[ o ] Γ₂
… | no ¬b∈Γ₁ = Γ₁ ⸴[ o ] (Γ₂ ↓ᵇ b)

build-≲x∶t : ∀ Γ → (x , t) ∈ binds Γ → Unrᶜ (Γ ↓ᵇ (x , t)) → Γ ≲ x ∶ t
build-≲x∶t (x ∶ t) (here refl) unr-Γ↓xt = ≲-refl
build-≲x∶t {x = x} {t = t} (Γ₁ ⸴[ o ] Γ₂) xt∈Γ unr-Γ↓xt
 with (x , t) ∈? binds Γ₁
… | yes xt∈Γ₁ =
  let open ≲-Reasoning in
  begin
    Γ₁ ⸴[ o ] Γ₂
  ≲⟨ ≲-⸴ (build-≲x∶t Γ₁ xt∈Γ₁ (Unrᶜ-⸴₁ (Γ₁ ↓ᵇ (x , t)) o Γ₂ unr-Γ↓xt)) ≲-refl ⟩
    x ∶ t ⸴[ o ] Γ₂
  ≲⟨ ≲-UnrΓʳ (Unrᶜ-⸴₂ (Γ₁ ↓ᵇ (x , t)) o Γ₂ unr-Γ↓xt) ⟩
    x ∶ t
  ∎
… | no ¬b∈Γ₁ with AnyP.++⁻ (binds Γ₁) xt∈Γ
…   | inj₁ b∈Γ₁ = ⊥-elim (¬b∈Γ₁ b∈Γ₁)
…   | inj₂ xt∈Γ₂ =
  let open ≲-Reasoning in
  begin
    Γ₁ ⸴[ o ] Γ₂
  ≲⟨ ≲-⸴ ≲-refl (build-≲x∶t Γ₂ xt∈Γ₂ (Unrᶜ-⸴₂ Γ₁ o (Γ₂ ↓ᵇ (x , t)) unr-Γ↓xt)) ⟩
    Γ₁ ⸴[ o ] x ∶ t
  ≲⟨ ≲-UnrΓˡ (Unrᶜ-⸴₁ Γ₁ o (Γ₂ ↓ᵇ (x , t)) unr-Γ↓xt) ⟩
    x ∶ t
  ∎

Unrᶜ-⸴ : ∀ Γ₁ o Γ₂ → Unrᶜ Γ₁ → Unrᶜ Γ₂ → Unrᶜ (Γ₁ ⸴[ o ] Γ₂)
Unrᶜ-⸴ Γ₁ o Γ₂ u₁ u₂ x with AnyP.++⁻ (binds Γ₁) x
... | inj₁ x = u₁ x
... | inj₂ y = u₂ y

↓ᵇ-pres-Unrᶜ : ∀ Γ {b} → Unrᶜ Γ → Unrᶜ (Γ ↓ᵇ b)
↓ᵇ-pres-Unrᶜ · {b} unr-Γ = λ ()
↓ᵇ-pres-Unrᶜ (y ∶ t') {(x , t)} unr-Γ with x ≟ y | t ≟ t'
… | yes _ | yes _ = λ ()
… | yes _ | no _ = unr-Γ
… | no _ | _ = unr-Γ
↓ᵇ-pres-Unrᶜ (Γ₁ ⸴[ o ] Γ₂) {b} unr-Γ with b ∈? binds Γ₁
… | yes _ = Unrᶜ-⸴ (Γ₁ ↓ᵇ b) o Γ₂ (↓ᵇ-pres-Unrᶜ Γ₁ (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ)) (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ)
… | no  _ = Unrᶜ-⸴ Γ₁ o (Γ₂ ↓ᵇ b) (Unrᶜ-⸴₁ Γ₁ o Γ₂ unr-Γ) (↓ᵇ-pres-Unrᶜ Γ₂ (Unrᶜ-⸴₂ Γ₁ o Γ₂ unr-Γ))

dec∈ : ∀ Γ x → Dec (∃[ t ] (x , t) ∈ binds Γ)
dec∈ · x = no (λ ())
dec∈ (y ∶ t) x with x ≟ y
… | yes refl = yes (t , here refl)
… | no ¬x≡y = no (λ { (t , here refl) → ¬x≡y refl })
dec∈ (Γ₁ ⸴[ o ] Γ₂) x with dec∈ Γ₁ x | dec∈ Γ₂ x
… | yes (t , p) | _ = yes (t , AnyP.++⁺ˡ p)
… | _ | yes (t , p) = yes (t , AnyP.++⁺ʳ _ p)
… | no p | no q = no λ (t , r) → case AnyP.++⁻ _ r of λ where
  (inj₁ x) → p (t , x)
  (inj₂ y) → q (t , y)

dec∈-ord : ∀ Γ x → Dec (∃[ t ] (x , t) ∈ binds Γ × Ord t)
dec∈-ord · x = no (λ ())
dec∈-ord (y ∶ t) x with x ≟ y
… | no ¬x≡y = no (λ { (t , here refl , _) → ¬x≡y refl })
… | yes refl with Unr? t
…   | yes unr-t = no (λ { (t , here refl , p) → p unr-t })
…   | no ¬unr-t = yes (t , here refl , ¬unr-t)
dec∈-ord (Γ₁ ⸴[ o ] Γ₂) x with dec∈-ord Γ₁ x | dec∈-ord Γ₂ x
… | yes (t , p , a) | _ = yes (t , AnyP.++⁺ˡ p , a)
… | _ | yes (t , p , a) = yes (t , AnyP.++⁺ʳ _ p , a)
… | no p | no q = no λ (t , r , a) → case AnyP.++⁻ _ r of λ where
  (inj₁ x) → p (t , x , a)
  (inj₂ y) → q (t , y , a)

¬Unrᶜ-⸴ : ∀ Γ₁ o Γ₂ → ¬ Unrᶜ (Γ₁ ⸴[ o ] Γ₂) → ¬ Unrᶜ Γ₁ ⊎ ¬ Unrᶜ Γ₂
¬Unrᶜ-⸴ Γ₁ o Γ₂ ¬Unr-Γ with Unrᶜ? Γ₁ | Unrᶜ? Γ₂
… | yes unr-Γ₁ | yes unr-Γ₂ = ⊥-elim (¬Unr-Γ (Unrᶜ-⸴ Γ₁ o Γ₂ unr-Γ₁ unr-Γ₂))
… | _          | no ¬unr-Γ₂ = inj₂ ¬unr-Γ₂
… | no ¬unr-Γ₁ | _          = inj₁ ¬unr-Γ₁

¬Unrᶜ→∃ : ∀ Γ → ¬ Unrᶜ Γ → ∃[ x ] ∃[ t ] ((x , t) ∈ binds Γ × Ord t)
¬Unrᶜ→∃ · ¬unr-Γ = ⊥-elim (¬unr-Γ (λ ()))
¬Unrᶜ→∃ (x ∶ t) ¬unr-Γ with Unr? t
… | yes unr-t = ⊥-elim (¬unr-Γ (λ { (here refl) → unr-t }))
… | no ¬unr-t = x , t , here refl , ¬unr-t
¬Unrᶜ→∃ (Γ₁ ⸴[ o ] Γ₂) ¬unr-Γ with ¬Unrᶜ-⸴ Γ₁ o Γ₂ ¬unr-Γ
... | inj₁ ¬unr-Γ₁ = let (x , t , xt∈ , ord-t) = ¬Unrᶜ→∃ Γ₁ ¬unr-Γ₁ in x , t , AnyP.++⁺ˡ xt∈ , ord-t
... | inj₂ ¬unr-Γ₂ = let (x , t , xt∈ , ord-t) = ¬Unrᶜ→∃ Γ₂ ¬unr-Γ₂ in x , t , AnyP.++⁺ʳ (binds Γ₁) xt∈ , ord-t

lem₁' : (y , t') ∈ binds Γ → Ord t' → (Γ ≲ x ∶ t) → x ≡ y × t ≡ t'
lem₁' {y = y} {t' = t'} {Γ = Γ} {t = t} yt'∈Γ ord-t' (mk-≲ (o , u))
 with Unr? t
… | yes unr-t =
  -- Here we have SemCtx.ord-graph ⟦ x ∶ t ⟧ ≡ G.∅
  let yt'∈ˢΓ = ∈→∈ˢ' Γ yt'∈Γ in
  case yt'∈ˢΓ of λ where
    (inj₁ ((n , snd), _)) →
      let (_ , _ , p , q , r) = o in
      case G.≃.to r (G.≲.to q (G.≃.to p n)) of λ ()
    (inj₂ (yt'∈unr , unr-t')) →
      ⊥-elim (ord-t' unr-t')
… | no ¬unr-t =
  -- Here we have SemCtx.ord-graph ⟦ x ∶ t ⟧ ≡ G.[ x , t ]
  let yt'∈ˢΓ = ∈→∈ˢ' Γ yt'∈Γ in
  case yt'∈ˢΓ of λ where
    (inj₁ ((n , snd), _)) →
      let (_ , _ , p , q , r) = o in
      case trans (sym snd) (trans (G.≃.labels p n) (trans (G.≲.labels q _) (G.≃.labels r _))) of λ { refl → refl , refl }
    (inj₂ (yt'∈unr , unr-t')) →
      ⊥-elim (ord-t' unr-t')

-- Contradiction: The ord binding for y is not in x ∶ t
lem₁ : (y , t') ∈ binds Γ → Ord t' → x ≢ y → ¬ (Γ ≲ x ∶ t)
lem₁ {t = t} yt'∈Γ ord-t' x≢y Γ≲x∶t =
  x≢y (proj₁ (lem₁' yt'∈Γ ord-t' Γ≲x∶t))

x∈Γ→graph≢∅ : ∀ Γ → Ord t → (x , t) ∈ binds Γ → 
      Σ[ A ∈ Set ] Graph.Node (SemCtx.ord-graph ⟦ Γ ⟧) G.Type.≃ (⊤ ⊎ A)
x∈Γ→graph≢∅ (x ∶ t) ord-t (here refl) with Unr? t
… | yes unr-t = ⊥-elim (ord-t unr-t)
… | no ¬unr-t = ⊥ , G.Type.≃-sym G.Type.⊎-⊥
x∈Γ→graph≢∅ (Γ₁ ⸴[ ordered ] Γ₂) ord-t xt∈
 with AnyP.++⁻ (binds Γ₁) xt∈
... | inj₁ xt∈ =
  let (A , p) = x∈Γ→graph≢∅ Γ₁ ord-t xt∈ in
  _ ,
  let open G.Type.≃-Reasoning in
  begin
    (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
  ≃⟨ G.Type.≃-⊎ p G.Type.≃-refl ⟩
    ((⊤ ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
  ≃⟨ G.Type.⊎-assoc ⟩
    (⊤ ⊎ _)
  ∎
... | inj₂ xt∈ = 
  let (A , p) = x∈Γ→graph≢∅ Γ₂ ord-t xt∈ in
  _ ,
  let open G.Type.≃-Reasoning in
  begin
    (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
  ≃⟨ G.Type.≃-⊎ G.Type.≃-refl p ⟩
    (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ (⊤ ⊎ A))
  ≃⟨ G.Type.⊎-comm ⟩
    ((⊤ ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧))
  ≃⟨ G.Type.⊎-assoc ⟩
    (⊤ ⊎ _)
  ∎
x∈Γ→graph≢∅ (Γ₁ ⸴[ unordered ] Γ₂) ord-t xt∈
 with AnyP.++⁻ (binds Γ₁) xt∈
... | inj₁ xt∈ =
  let (A , p) = x∈Γ→graph≢∅ Γ₁ ord-t xt∈ in
  _ ,
  let open G.Type.≃-Reasoning in
  begin
    (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
  ≃⟨ G.Type.≃-⊎ p G.Type.≃-refl ⟩
    ((⊤ ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
  ≃⟨ G.Type.⊎-assoc ⟩
    (⊤ ⊎ _)
  ∎
... | inj₂ xt∈ = 
  let (A , p) = x∈Γ→graph≢∅ Γ₂ ord-t xt∈ in
  _ ,
  let open G.Type.≃-Reasoning in
  begin
    (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
  ≃⟨ G.Type.≃-⊎ G.Type.≃-refl p ⟩
    (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ (⊤ ⊎ A))
  ≃⟨ G.Type.⊎-comm ⟩
    ((⊤ ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧))
  ≃⟨ G.Type.⊎-assoc ⟩
    (⊤ ⊎ _)
  ∎

xy∈Γ→graph≡⊤⊎⊤⊎A : ∀ Γ → Ord t → Ord t' → (x , t) ∈ binds Γ → (y , t') ∈ binds (Γ ↓ᵇ (x , t)) →
       Σ[ A ∈ Set ] Graph.Node (SemCtx.ord-graph ⟦ Γ ⟧) G.Type.≃ ((⊤ ⊎ ⊤) ⊎ A)
xy∈Γ→graph≡⊤⊎⊤⊎A (x ∶ t) ord-t ord-t' (here refl) yt'∈ with x ≟ x | t ≟ t
… | yes _ | yes _ = case yt'∈ of λ ()
… | no ¬x≡x | _       = ⊥-elim (¬x≡x refl)
… | _       | no ¬t≡t = ⊥-elim (¬t≡t refl)
xy∈Γ→graph≡⊤⊎⊤⊎A {t = t} {t' = t'} {x = x} {y = y} (Γ₁ ⸴[ ordered ] Γ₂) ord-t ord-t' xt∈ yt'∈
 with (x , t) ∈? binds Γ₁
… | yes xt∈Γ₁ = case AnyP.++⁻ (binds (Γ₁ ↓ᵇ (x , t))) yt'∈ of λ where
    (inj₁ yt'∈Γ₁) →
      let (A , p) = xy∈Γ→graph≡⊤⊎⊤⊎A Γ₁ ord-t ord-t' xt∈Γ₁ yt'∈Γ₁ in
      _ ,
      let open G.Type.≃-Reasoning in
      begin
        (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
      ≃⟨ G.Type.≃-⊎ p G.Type.≃-refl ⟩
        (((⊤ ⊎ ⊤) ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
      ≃⟨ G.Type.⊎-assoc {B = A} ⟩
        ((⊤ ⊎ ⊤) ⊎ (A ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧)))
      ∎
    (inj₂ yt'∈Γ₂) →
      _ ,
      let (A , p) = x∈Γ→graph≢∅ Γ₂ ord-t' yt'∈Γ₂ in
      let (B , q) = x∈Γ→graph≢∅ Γ₁ ord-t xt∈Γ₁ in
      let open G.Type.≃-Reasoning in
      begin
        (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
      ≃⟨ G.Type.≃-⊎ q p ⟩
        ((⊤ ⊎ B) ⊎ (⊤ ⊎ A))
      ≃⟨ G.Type.⊎-assoc ⟩
        (⊤ ⊎ (B ⊎ (⊤ ⊎ A)))
      ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-sym G.Type.⊎-assoc) ⟩
        (⊤ ⊎ ((B ⊎ ⊤) ⊎ A))
      ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-⊎ G.Type.⊎-comm G.Type.≃-refl) ⟩
        (⊤ ⊎ ((⊤ ⊎ B) ⊎ A))
      ≃⟨ G.Type.≃-⊎ G.Type.≃-refl G.Type.⊎-assoc ⟩
        (⊤ ⊎ (⊤ ⊎ (B ⊎ A)))
      ≃⟨ G.Type.≃-sym G.Type.⊎-assoc ⟩
        ((⊤ ⊎ ⊤) ⊎ _)
      ∎

… | no ¬xt∈Γ₁ = case AnyP.++⁻ (binds Γ₁) xt∈ of λ where
  (inj₁ xt∈Γ₁) → ⊥-elim (¬xt∈Γ₁ xt∈Γ₁)
  (inj₂ xt∈Γ₂) → case AnyP.++⁻ (binds Γ₁) yt'∈ of λ where
     (inj₁ yt'∈Γ₁) →
        _ ,
        let (A , p) = x∈Γ→graph≢∅ Γ₂ ord-t xt∈Γ₂ in
        let (B , q) = x∈Γ→graph≢∅ Γ₁ ord-t' yt'∈Γ₁ in
        let open G.Type.≃-Reasoning in
        begin
          (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
        ≃⟨ G.Type.≃-⊎ q p ⟩
          ((⊤ ⊎ B) ⊎ (⊤ ⊎ A))
        ≃⟨ G.Type.⊎-assoc ⟩
          (⊤ ⊎ (B ⊎ (⊤ ⊎ A)))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-sym G.Type.⊎-assoc) ⟩
          (⊤ ⊎ ((B ⊎ ⊤) ⊎ A))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-⊎ G.Type.⊎-comm G.Type.≃-refl) ⟩
          (⊤ ⊎ ((⊤ ⊎ B) ⊎ A))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl G.Type.⊎-assoc ⟩
          (⊤ ⊎ (⊤ ⊎ (B ⊎ A)))
        ≃⟨ G.Type.≃-sym G.Type.⊎-assoc ⟩
          ((⊤ ⊎ ⊤) ⊎ _)
        ∎
     (inj₂ yt'∈Γ₂↓) →
        let (A , p) = xy∈Γ→graph≡⊤⊎⊤⊎A Γ₂ ord-t ord-t' xt∈Γ₂ yt'∈Γ₂↓ in
        _ ,
        let open G.Type.≃-Reasoning in
        begin
          (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl p ⟩
          (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ ((⊤ ⊎ ⊤) ⊎ A))
        ≃⟨ G.Type.⊎-comm ⟩
          (((⊤ ⊎ ⊤) ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧))
        ≃⟨ G.Type.⊎-assoc ⟩
          ((⊤ ⊎ ⊤) ⊎ (_ ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧)))
        ∎
xy∈Γ→graph≡⊤⊎⊤⊎A {t = t} {t' = t'} {x = x} {y = y} (Γ₁ ⸴[ unordered ] Γ₂) ord-t ord-t' xt∈ yt'∈
 with (x , t) ∈? binds Γ₁
… | yes xt∈Γ₁ = case AnyP.++⁻ (binds (Γ₁ ↓ᵇ (x , t))) yt'∈ of λ where
    (inj₁ yt'∈Γ₁) →
      let (A , p) = xy∈Γ→graph≡⊤⊎⊤⊎A Γ₁ ord-t ord-t' xt∈Γ₁ yt'∈Γ₁ in
      _ ,
      let open G.Type.≃-Reasoning in
      begin
        (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
      ≃⟨ G.Type.≃-⊎ p G.Type.≃-refl ⟩
        (((⊤ ⊎ ⊤) ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
      ≃⟨ G.Type.⊎-assoc {B = A} ⟩
        ((⊤ ⊎ ⊤) ⊎ (A ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧)))
      ∎
    (inj₂ yt'∈Γ₂) →
      _ ,
      let (A , p) = x∈Γ→graph≢∅ Γ₂ ord-t' yt'∈Γ₂ in
      let (B , q) = x∈Γ→graph≢∅ Γ₁ ord-t xt∈Γ₁ in
      let open G.Type.≃-Reasoning in
      begin
        (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
      ≃⟨ G.Type.≃-⊎ q p ⟩
        ((⊤ ⊎ B) ⊎ (⊤ ⊎ A))
      ≃⟨ G.Type.⊎-assoc ⟩
        (⊤ ⊎ (B ⊎ (⊤ ⊎ A)))
      ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-sym G.Type.⊎-assoc) ⟩
        (⊤ ⊎ ((B ⊎ ⊤) ⊎ A))
      ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-⊎ G.Type.⊎-comm G.Type.≃-refl) ⟩
        (⊤ ⊎ ((⊤ ⊎ B) ⊎ A))
      ≃⟨ G.Type.≃-⊎ G.Type.≃-refl G.Type.⊎-assoc ⟩
        (⊤ ⊎ (⊤ ⊎ (B ⊎ A)))
      ≃⟨ G.Type.≃-sym G.Type.⊎-assoc ⟩
        ((⊤ ⊎ ⊤) ⊎ _)
      ∎

… | no ¬xt∈Γ₁ = case AnyP.++⁻ (binds Γ₁) xt∈ of λ where
  (inj₁ xt∈Γ₁) → ⊥-elim (¬xt∈Γ₁ xt∈Γ₁)
  (inj₂ xt∈Γ₂) → case AnyP.++⁻ (binds Γ₁) yt'∈ of λ where
     (inj₁ yt'∈Γ₁) →
        _ ,
        let (A , p) = x∈Γ→graph≢∅ Γ₂ ord-t xt∈Γ₂ in
        let (B , q) = x∈Γ→graph≢∅ Γ₁ ord-t' yt'∈Γ₁ in
        let open G.Type.≃-Reasoning in
        begin
          (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
        ≃⟨ G.Type.≃-⊎ q p ⟩
          ((⊤ ⊎ B) ⊎ (⊤ ⊎ A))
        ≃⟨ G.Type.⊎-assoc ⟩
          (⊤ ⊎ (B ⊎ (⊤ ⊎ A)))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-sym G.Type.⊎-assoc) ⟩
          (⊤ ⊎ ((B ⊎ ⊤) ⊎ A))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl (G.Type.≃-⊎ G.Type.⊎-comm G.Type.≃-refl) ⟩
          (⊤ ⊎ ((⊤ ⊎ B) ⊎ A))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl G.Type.⊎-assoc ⟩
          (⊤ ⊎ (⊤ ⊎ (B ⊎ A)))
        ≃⟨ G.Type.≃-sym G.Type.⊎-assoc ⟩
          ((⊤ ⊎ ⊤) ⊎ _)
        ∎
     (inj₂ yt'∈Γ₂↓) →
        let (A , p) = xy∈Γ→graph≡⊤⊎⊤⊎A Γ₂ ord-t ord-t' xt∈Γ₂ yt'∈Γ₂↓ in
        _ ,
        let open G.Type.≃-Reasoning in
        begin
          (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₂ ⟧))
        ≃⟨ G.Type.≃-⊎ G.Type.≃-refl p ⟩
          (Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧) ⊎ ((⊤ ⊎ ⊤) ⊎ A))
        ≃⟨ G.Type.⊎-comm ⟩
          (((⊤ ⊎ ⊤) ⊎ A) ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧))
        ≃⟨ G.Type.⊎-assoc ⟩
          ((⊤ ⊎ ⊤) ⊎ (_ ⊎ Graph.Node (SemCtx.ord-graph ⟦ Γ₁ ⟧)))
        ∎

lem₂ : (x , t') ∈ binds Γ → Ord t' → ¬ Unrᶜ (Γ ↓ᵇ (x , t')) → ¬ (Γ ≲ x ∶ t)
lem₂ {x = x} {t' = t'} {Γ = Γ} {t = t} xt'∈Γ ord-t' ¬unr-Γ↓xt' (mk-≲ (o , u))
 with Unr? t
… | yes unr-t =
  -- Here we have SemCtx.ord-graph ⟦ x ∶ t ⟧ ≡ G.∅
  let xt'∈ˢΓ = ∈→∈ˢ' Γ xt'∈Γ in
  case xt'∈ˢΓ of λ where
    (inj₁ ((n , snd), _)) →
      let (_ , _ , p , q , r) = o in
      case G.≃.to r (G.≲.to q (G.≃.to p n)) of λ ()
    (inj₂ (yt'∈unr , unr-t')) →
      ⊥-elim (ord-t' unr-t')
… | no ¬unr-t =
  -- Here we have SemCtx.ord-graph ⟦ x ∶ t ⟧ ≡ G.[ x , t ]
  let xt'∈ˢΓ = ∈→∈ˢ' Γ xt'∈Γ in
  case xt'∈ˢΓ of λ where
    (inj₁ ((n , snd), _)) →
      let (o₁ , o₂ , p , q , r) = o in
      let (y , t# , yt#∈Γ↓xt' , ord-t#) = ¬Unrᶜ→∃ (Γ ↓ᵇ (x , t')) ¬unr-Γ↓xt' in
      let (A , ⟦Γ⟧≃⊤⊎⊤⊎A) = xy∈Γ→graph≡⊤⊎⊤⊎A Γ ord-t' ord-t# xt'∈Γ yt#∈Γ↓xt'  in
      let bad-iso = let open G.Type.≃-Reasoning in
                    begin
                      ((⊤ ⊎ ⊤) ⊎ A)
                    ≃⟨ G.Type.≃-sym ⟦Γ⟧≃⊤⊎⊤⊎A ⟩
                      Graph.Node (SemCtx.ord-graph ⟦ Γ ⟧)
                    ≃⟨ G.≃.iso p ⟩
                      Graph.Node (proj₁ o)
                    ≃⟨ G.≲.iso q ⟩
                      Graph.Node (proj₁ (proj₂ o))
                    ≃⟨ G.≃.iso r ⟩
                      ⊤
                    ∎ in
      let bad-eq = let open ≡-Reasoning in
                   let open G.Type.≃ bad-iso in
                   begin
                     inj₁ (inj₁ tt)
                   ≡⟨ sym (from∘to (inj₁ (inj₁ tt))) ⟩
                     from (to (inj₁ (inj₁ tt)))
                   ≡⟨ refl ⟩
                     from (to (inj₁ (inj₂ tt)))
                   ≡⟨ from∘to (inj₁ (inj₂ tt)) ⟩
                     inj₁ (inj₂ tt)
                   ∎ in
      case bad-eq of λ ()
    (inj₂ (yt'∈unr , unr-t')) →
      ⊥-elim (ord-t' unr-t')

_∃≲?_ : ∀ Γ x → Dec (∃[ t ] Γ ≲ x ∶ t)
Γ ∃≲? x with dec∈-ord Γ x
Γ ∃≲? x | yes (t , xt∈Γ , ord-t)
 with Unrᶜ? (Γ ↓ᵇ (x , t))
… | yes unr-Γ↓xt = yes (t , build-≲x∶t Γ xt∈Γ unr-Γ↓xt)
… | no ¬unr-Γ↓xt = no (λ (t' , Γ≲x∶t') → lem₂ xt∈Γ ord-t ¬unr-Γ↓xt Γ≲x∶t')
Γ ∃≲? x | no ¬x∈Γ-ord with Unrᶜ? Γ
Γ ∃≲? x | no ¬x∈Γ-ord | no ¬unr-Γ =
  let (y , t' , yt'∈Γ , ord-t') = ¬Unrᶜ→∃ Γ ¬unr-Γ in
  case x ≟ y of λ where
    (yes refl) → ⊥-elim (¬x∈Γ-ord (t' , yt'∈Γ , ord-t'))
    (no ¬x≡y) → no λ (t' , Γ≲x∶t') → lem₁ yt'∈Γ ord-t' ¬x≡y Γ≲x∶t'
Γ ∃≲? x | no ¬x∈Γ-ord | yes unr-Γ with dec∈ Γ x
Γ ∃≲? x | no ¬x∈Γ-ord | yes unr-Γ | no ¬x∈Γ = no λ x₁ → no₁ Γ (λ z → ¬x∈Γ (proj₁ x₁ , z)) (proj₂ x₁)
Γ ∃≲? x | no ¬x∈Γ-ord | yes unr-Γ | yes (t , xt∈Γ) =
  yes (t , build-≲x∶t Γ xt∈Γ (↓ᵇ-pres-Unrᶜ Γ unr-Γ))

_>>=ᶜ_ : Ctx → (Id → Type → Ctx) → Ctx
·              >>=ᶜ f = ·
(x ∶ t)        >>=ᶜ f = f x t
(Γ₁ ⸴[ o ] Γ₂) >>=ᶜ f = (Γ₁ >>=ᶜ f) ⸴[ o ] (Γ₂ >>=ᶜ f)

dom-ext : ∀ m Γ₁ Γ₂ → dom (ext m Γ₁ Γ₂) ≈ⁱ dom Γ₁ ++ dom Γ₂
dom-ext ∞ Γ₁ Γ₂ rewrite ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂) = ≈ⁱ-refl
dom-ext 𝟙 Γ₁ Γ₂ rewrite ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂) = ≈ⁱ-refl
dom-ext ≻ Γ₁ Γ₂ rewrite ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂) = ≈ⁱ-refl
dom-ext ≺ Γ₁ Γ₂ rewrite ListP.map-++ proj₁ (binds Γ₂) (binds Γ₁) = ≈ⁱ-comm (dom Γ₂) (dom Γ₁)

ext-injective : ∀ {Γ₁₁ Γ₁₂ Γ₂₁ Γ₂₂} →
  ext m Γ₁₁ Γ₁₂ ≡ ext m Γ₂₁ Γ₂₂ →
  Γ₁₁ ≡ Γ₂₁ × Γ₁₂ ≡ Γ₂₂
ext-injective {m = ∞} refl = refl , refl
ext-injective {m = 𝟙} refl = refl , refl
ext-injective {m = ≻} refl = refl , refl
ext-injective {m = ≺} refl = refl , refl

Unique-dom-ext : ∀ m Γ t →
  x ∉ dom Γ  →
  Unique (dom Γ) →
  Unique (dom (ext m Γ (x ∶ t)))
Unique-dom-ext {x} m Γ t x∉Γ U-Γ =
  Unique-⊆
    (≈ⁱ→⊆ⁱ (≈ⁱ-trans (dom-ext m Γ (x ∶ t))
                     (≈ⁱ-comm (dom Γ) (dom (x ∶ t)))))
    (Unique-∷ x∉Γ U-Γ)

↓-∈ : ∀ {x t} Γ xs →
  (x , t) ∈ binds (Γ ↓ xs) →
  (x , t) ∈ binds Γ
↓-∈ {x} {t} (x' ∶ t') xs p  with x' ∈? xs
↓-∈ {x} {t} (x' ∶ t') xs () | no _
↓-∈ {x} {t} (x' ∶ t') xs p  | yes _ = p
↓-∈ {x} {t} (Γ₁ ⸴[ o ] Γ₂) xs p with AnyP.++⁻ (binds (Γ₁ ↓ xs)) p
… | inj₁ p₁ = AnyP.++⁺ˡ (↓-∈ Γ₁ xs p₁)
… | inj₂ p₂ = AnyP.++⁺ʳ (binds Γ₁) (↓-∈ Γ₂ xs p₂)

↓-⊆ : ∀ Γ xs → binds (Γ ↓ xs) ⊆ binds Γ
↓-⊆ Γ xs = ↓-∈ Γ xs

↓-⊆-inj : ∀ Γ xs → LocalInj (binds (Γ ↓ xs)) (↓-⊆ Γ xs)
↓-⊆-inj (x' ∶ t') xs x p q eq
  with x' ∈? xs
… | no x'∉xs with () ← p
… | yes x'∈xs = eq
↓-⊆-inj (Γ₁ ⸴[ o ] Γ₂) xs x p q eq
  with AnyP.++⁻ (binds (Γ₁ ↓ xs)) p in eq-p | AnyP.++⁻ (binds (Γ₁ ↓ xs)) q in eq-q
… | inj₁ p' | inj₁ q' = let p'≡q' = ↓-⊆-inj Γ₁ xs x p' q' (++⁺ˡ-injective eq) in
                        ++⁻-injective (trans eq-p (trans (cong inj₁ p'≡q') (sym eq-q)))
… | inj₁ p' | inj₂ q' = ⊥-elim (++⁺ʳ≢++⁺ˡ (sym eq))
… | inj₂ p' | inj₁ q' = ⊥-elim (++⁺ʳ≢++⁺ˡ eq)
… | inj₂ p' | inj₂ q' = let p'≡q' = ↓-⊆-inj Γ₂ xs x p' q' (++⁺ʳ-injective eq) in
                        ++⁻-injective (trans eq-p (trans (cong inj₂ p'≡q') (sym eq-q)))

↓-⊆ⁱ : ∀ Γ xs → binds (Γ ↓ xs) ⊆ⁱ binds Γ
↓-⊆ⁱ Γ xs = mk-⊆ⁱ (↓-⊆ Γ xs) (↓-⊆-inj Γ xs)

↓-∈dom : ∀ {x} Γ xs →
  x ∈ dom (Γ ↓ xs) →
  x ∈ dom Γ
↓-∈dom {x} (x' ∶ t') xs p  with x' ∈? xs
↓-∈dom {x} (x' ∶ t') xs () | no _
↓-∈dom {x} (x' ∶ t') xs p  | yes _ = p
↓-∈dom {x} (Γ₁ ⸴[ o ] Γ₂) xs p
  using p ← subst (x ∈_) (ListP.map-++ proj₁ (binds (Γ₁ ↓ xs)) (binds (Γ₂ ↓ xs))) p
  using eq ← sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))
  with AnyP.++⁻ (dom (Γ₁ ↓ xs)) p
… | inj₁ p₁ = subst (x ∈_) eq (AnyP.++⁺ˡ (↓-∈dom Γ₁ xs p₁))
… | inj₂ p₂ = subst (x ∈_) eq (AnyP.++⁺ʳ (dom Γ₁) (↓-∈dom Γ₂ xs p₂))

↓-⊆dom : ∀ Γ xs → dom (Γ ↓ xs) ⊆ dom Γ
↓-⊆dom Γ xs = ↓-∈dom Γ xs

↓-⊆dom-inj : ∀ Γ xs → LocalInj (dom (Γ ↓ xs)) (↓-⊆dom Γ xs)
↓-⊆dom-inj (x' ∶ t') xs x p q eq
  with x' ∈? xs
… | no x'∉xs with () ← p
… | yes x'∈xs = eq
↓-⊆dom-inj (Γ₁ ⸴[ o ] Γ₂) xs x p q eq
  using eq'' ← ListP.map-++ proj₁ (binds (Γ₁ ↓ xs)) (binds (Γ₂ ↓ xs))
  using p ← subst (x ∈_) eq'' p
  using q ← subst (x ∈_) eq'' q
  using eq' ← sym (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂))
  with AnyP.++⁻ (dom (Γ₁ ↓ xs)) p in eq-p | AnyP.++⁻ (dom (Γ₁ ↓ xs)) q in eq-q
… | inj₁ p' | inj₁ q' = let p'≡q' = ↓-⊆dom-inj Γ₁ xs x p' q' $
                                    ++⁺ˡ-injective $
                                    subst-injective eq' eq' eq in
                        subst-injective eq'' eq'' $
                        ++⁻-injective $
                        trans eq-p (trans (cong inj₁ p'≡q') (sym eq-q))
… | inj₁ p' | inj₂ q' = ⊥-elim $ ++⁺ʳ≢++⁺ˡ $ sym $ subst-injective eq' eq' eq
… | inj₂ p' | inj₁ q' = ⊥-elim $ ++⁺ʳ≢++⁺ˡ $ subst-injective eq' eq' eq
… | inj₂ p' | inj₂ q' = let p'≡q' = ↓-⊆dom-inj Γ₂ xs x p' q' $
                                    ++⁺ʳ-injective $
                                    subst-injective eq' eq' eq in
                        subst-injective eq'' eq'' $
                        ++⁻-injective $
                        trans eq-p (trans (cong inj₂ p'≡q') (sym eq-q))

↓-⊆ⁱdom : ∀ Γ xs → dom (Γ ↓ xs) ⊆ⁱ dom Γ
↓-⊆ⁱdom Γ xs = mk-⊆ⁱ (↓-⊆dom Γ xs) (↓-⊆dom-inj Γ xs)

-- ↓-∈dom : ∀ {x} Γ xs →
--   x ∈ dom (Γ ↓ xs) →
--   x ∈ dom Γ
-- ↓-∈dom Γ xs x∈Γ↓ =
--   let t , xt∈Γ↓ = ∈dom→∈binds (Γ ↓ xs) x∈Γ↓ in
--   let xt∈Γ = ↓-∈ Γ xs xt∈Γ↓ in
--   ∈binds→∈dom Γ xt∈Γ

-- ↓-⊆dom : ∀ Γ xs → dom (Γ ↓ xs) ⊆ dom Γ
-- ↓-⊆dom Γ xs = ↓-∈dom Γ xs

∈binds-Unique : ∀ {x t₁ t₂} Γ →
  Unique (dom Γ) →
  (x , t₁) ∈ binds Γ →
  (x , t₂) ∈ binds Γ →
  t₁ ≡ t₂
∈binds-Unique {x} {t₁} {t₂} (y ∶ t) U-Γ (here refl) (here refl) = refl
∈binds-Unique {x} {t₁} {t₂} (Γ₁ ⸴[ o ] Γ₂) U-Γ xt₁∈Γ xt₂∈Γ
  using U-Γ' ← subst Unique (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) U-Γ
  using U-Γ₁ , U-Γ₂ , D-Γ₁-Γ₂ ← Unique-++⁻ (dom Γ₁) (dom Γ₂) U-Γ'
  with AnyP.++⁻ (binds Γ₁) xt₁∈Γ | AnyP.++⁻ (binds Γ₁) xt₂∈Γ
… | inj₁ xt₁∈Γ₁ | inj₁ xt₂∈Γ₁ = ∈binds-Unique Γ₁ U-Γ₁ xt₁∈Γ₁ xt₂∈Γ₁
… | inj₂ xt₁∈Γ₂ | inj₂ xt₂∈Γ₂ = ∈binds-Unique Γ₂ U-Γ₂ xt₁∈Γ₂ xt₂∈Γ₂
… | inj₁ xt₁∈Γ₁ | inj₂ xt₂∈Γ₂ = ⊥-elim $ D-Γ₁-Γ₂ x (∈binds→∈dom Γ₁ xt₁∈Γ₁)
                                                   (∈binds→∈dom Γ₂ xt₂∈Γ₂)
… | inj₂ xt₁∈Γ₂ | inj₁ xt₂∈Γ₁ = ⊥-elim $ D-Γ₁-Γ₂ x (∈binds→∈dom Γ₁ xt₂∈Γ₁)
                                                   (∈binds→∈dom Γ₂ xt₁∈Γ₂)
