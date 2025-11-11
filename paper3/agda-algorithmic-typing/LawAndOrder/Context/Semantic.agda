open import LawAndOrder.Util.OrderedPartialMonoid

module LawAndOrder.Context.Semantic {M : OPM} (DM : DecidableOPM M) where

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
open import Function using (_$_)

open import LawAndOrder.Util.Decidable
open import LawAndOrder.Multiplicities
open import LawAndOrder.Effect
open import LawAndOrder.Type DM
open import LawAndOrder.Util.List
open import LawAndOrder.Id
open import LawAndOrder.Util.Graph as G using (Graph)
open import LawAndOrder.Util.List

-- Specification

record SemCtx : Set₁ where
  constructor _,_
  field
    ord-graph : Graph (Id × Type)
    unr-set   : List (Id × Type)

variable
  γ γ₁ γ₂ γ₃ γ' γ₁' γ₂' γ₃' : SemCtx
  O O₁ O₂ O₃ O' O₁' O₂' O₃' : Graph (Id × Type)
  U U₁ U₂ U₃ U' U₁' U₂' U₃' : List (Id × Type)

∅ : SemCtx
∅ = G.∅ , []

infix  7 _∶ˢ_

_∶ˢ_ : Id → Type → SemCtx
x ∶ˢ t with Unr? t
…         | yes unr-t = G.∅ , L.[ x , t ]
…         | no ¬unr-t = G.[ x , t ] , []

infix 5 _⸴ˢ_ _∥ˢ_

_∥ˢ_ : SemCtx → SemCtx → SemCtx
(O₁ , U₁) ∥ˢ (O₂ , U₂) = (O₁ G.∪ O₂) , U₁ ++ U₂

_⸴ˢ_ : SemCtx → SemCtx → SemCtx
(O₁ , U₁) ⸴ˢ (O₂ , U₂) = (O₁ G.+ O₂) , U₁ ++ U₂

data IsOrd : Set where
  ordered unordered : IsOrd

variable o o₁ o₂ o' o₁' o₂' : IsOrd

_⸴ᵍ[_]_ : ∀ {ℓ} {L : Set ℓ} → Graph L → IsOrd → Graph L → Graph L
g₁ ⸴ᵍ[ ordered ]   g₂ = g₁ G.+ g₂
g₁ ⸴ᵍ[ unordered ] g₂ = g₁ G.∪ g₂

_⸴ˢ[_]_ : SemCtx → IsOrd → SemCtx → SemCtx
(O₁ , U₁) ⸴ˢ[ o ] (O₂ , U₂) = (O₁ ⸴ᵍ[ o ] O₂) , U₁ ++ U₂

infix 3 _≲ᵍ_ _≲ˢ_ _≈ˢ_

_≲ᵍ_ : ∀ {ℓ} {L : Set ℓ} → G.Graph L → G.Graph L → Set _
g₁ ≲ᵍ g₂ = ∃[ g₁' ] ∃[ g₂' ] g₁ G.≃ g₁' × g₁' G.≲ g₂' × g₂' G.≃ g₂

_≲ˢ_ : SemCtx → SemCtx → Set₁
(O₁ , U₁) ≲ˢ (O₂ , U₂) = (O₁ ≲ᵍ O₂) × (U₂ ⊆ U₁)

_≈ˢ_ : SemCtx → SemCtx → Set
(O₁ , U₁) ≈ˢ (O₂ , U₂) = O₁ G.≃ O₂ × (U₂ ≈ˡ U₁)

-- Properties

postulate
  -- The following postulate is a standard result of graph theory
  -- for finite directed acyclic graphs like the graphs resulting from
  -- the semantics of a typing context. 
  --
  -- Informally, this theorem states that for two finite, directed,
  -- acyclic graphs g₁ and g₂, it is decidable whether g₁ has the same
  -- nodes, but a subset of the edges of g₂ up to isomorphism.
  _≲ᵍ?_ : ∀ {ℓ} {L : Set ℓ} → (g₁ g₂ : G.Graph L) → Dec (g₁ ≲ᵍ g₂)

_≲ˢ?_ : ∀ γ₁ γ₂ → Dec (γ₁ ≲ˢ γ₂)
(o₁ , u₁) ≲ˢ? (o₂ , u₂) with o₁ ≲ᵍ? o₂ | u₂ ⊆? u₁
… | yes o₁≲o₂ | yes u₂⊆u₁ = yes (o₁≲o₂ , u₂⊆u₁)
… | no ¬o₁≲o₂ | _         = no λ { (o₁≲o₂ , u₂⊆u₁) → ¬o₁≲o₂ o₁≲o₂ }
… | _         | no ¬u₂⊆u₁ = no λ { (o₁≲o₂ , u₂⊆u₁) → ¬u₂⊆u₁ u₂⊆u₁ }


≲ᵍ-refl : ∀ {ℓ} {L : Set ℓ} {g : Graph L} → g ≲ᵍ g
≲ᵍ-refl = _ , _ , G.≃-refl , G.≲-refl , G.≃-refl

≲ˢ-refl : ∀ {γ} → γ ≲ˢ γ
≲ˢ-refl = ≲ᵍ-refl , ⊆-refl

≲ᵍ-trans : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ g₃ : Graph L} → g₁ ≲ᵍ g₂ → g₂ ≲ᵍ g₃ → g₁ ≲ᵍ g₃
≲ᵍ-trans (g₁' , g₂' , g₁≃g₁' , g₁'≲g₂' , g₂≃g₂') (g₂'' , g₃'' , g₂≃g₂'' , g₂''≲g₃'' , g₃≃g₃'') =
  _ , _ , G.≃-refl , G.≲-trans (G.≃-≲-trans g₁≃g₁' g₁'≲g₂' g₂≃g₂') (G.≃-≲-trans g₂≃g₂'' g₂''≲g₃'' g₃≃g₃'') , G.≃-refl

≲ˢ-trans : ∀ {γ₁ γ₂ γ₃} → γ₁ ≲ˢ γ₂ → γ₂ ≲ˢ γ₃ → γ₁ ≲ˢ γ₃
≲ˢ-trans (p₁ , p₂) (q₁ , q₂) = ≲ᵍ-trans p₁ q₁ , (⊆-trans q₂ p₂)


≈ˢ-refl : ∀ {γ} → γ ≈ˢ γ
≈ˢ-refl = G.≃-refl , ≈ˡ-refl

≈ˢ-sym : ∀ {γ₁ γ₂} → γ₁ ≈ˢ γ₂ → γ₂ ≈ˢ γ₁
≈ˢ-sym (p₁ , p₂) = G.≃-sym p₁ , ≈ˡ-sym p₂

≈ˢ-trans : ∀ {γ₁ γ₂ γ₃} → γ₁ ≈ˢ γ₂ → γ₂ ≈ˢ γ₃ → γ₁ ≈ˢ γ₃
≈ˢ-trans (p₁ , p₂) (q₁ , q₂) = G.≃-trans p₁ q₁ , (≈ˡ-trans q₂ p₂)

_∈ᵍ_ : ∀ {ℓ} {L : Set ℓ} → L → G.Graph L → Set ℓ
l ∈ᵍ g = ∃[ n ] G.label g n ≡ l

∈ᵍ-⸴₁ : ∀ {ℓ} {L : Set ℓ} {l} {g₁ g₂ : Graph L} o →
  l ∈ᵍ g₁ →
  l ∈ᵍ (g₁ ⸴ᵍ[ o ] g₂)
∈ᵍ-⸴₁ ordered (n , refl) = (inj₁ n) , refl
∈ᵍ-⸴₁ unordered (n , refl) = (inj₁ n) , refl

∈ᵍ-⸴₂ : ∀ {ℓ} {L : Set ℓ} {l} {g₁ g₂ : Graph L} o →
  l ∈ᵍ g₂ →
  l ∈ᵍ (g₁ ⸴ᵍ[ o ] g₂)
∈ᵍ-⸴₂ ordered (n , refl) = (inj₂ n) , refl
∈ᵍ-⸴₂ unordered (n , refl) = (inj₂ n) , refl

∈ᵍ-⸴ : ∀ {ℓ} {L : Set ℓ} {l} {g₁ g₂ : Graph L} o →
  l ∈ᵍ (g₁ ⸴ᵍ[ o ] g₂) →
  l ∈ᵍ g₁ ⊎ l ∈ᵍ g₂
∈ᵍ-⸴ ordered (inj₁ n , refl) = inj₁ (n , refl)
∈ᵍ-⸴ ordered (inj₂ n , refl) = inj₂ (n , refl)
∈ᵍ-⸴ unordered (inj₁ n , refl) = inj₁ (n , refl)
∈ᵍ-⸴ unordered (inj₂ n , refl) = inj₂ (n , refl)

_∈ˢ_ : Id × Type → SemCtx → Set
xt ∈ˢ (o , u) = xt ∈ᵍ o ⊎ xt ∈ u

∈ˢ-⸴₁ : ∀ {xt} o →
  xt ∈ˢ γ₁ →
  xt ∈ˢ (γ₁ ⸴ˢ[ o ] γ₂)
∈ˢ-⸴₁ o (inj₁ x∈o) = inj₁ (∈ᵍ-⸴₁ o x∈o)
∈ˢ-⸴₁ o (inj₂ x∈u) = inj₂ (AnyP.++⁺ˡ x∈u)

∈ˢ-⸴₂ : ∀ {xt} o →
  xt ∈ˢ γ₂ →
  xt ∈ˢ (γ₁ ⸴ˢ[ o ] γ₂)
∈ˢ-⸴₂ o (inj₁ x∈o) = inj₁ (∈ᵍ-⸴₂ o x∈o)
∈ˢ-⸴₂ o (inj₂ x∈u) = inj₂ (AnyP.++⁺ʳ _ x∈u)

∈ˢ-⸴ : ∀ {xt} o →
  xt ∈ˢ (γ₁ ⸴ˢ[ o ] γ₂) →
  xt ∈ˢ γ₁ ⊎ xt ∈ˢ γ₂
∈ˢ-⸴ o (inj₁ x∈o₁⸴o₂) with ∈ᵍ-⸴ o x∈o₁⸴o₂
... | inj₁ x∈o₁ = inj₁ (inj₁ x∈o₁)
... | inj₂ x∈o₂ = inj₂ (inj₁ x∈o₂)
∈ˢ-⸴ o (inj₂ y) with AnyP.++⁻ _ y
... | inj₁ x = inj₁ (inj₂ x)
... | inj₂ y₁ = inj₂ (inj₂ y₁)

x∈ˢx : (x , t) ∈ˢ (x ∶ˢ t)
x∈ˢx {t = t} with Unr? t
… | yes unr-t = inj₂ (here refl)
… | no ¬unr-t = inj₁ (tt , refl)

_∈ˢ'_ : Id × Type → SemCtx → Set
(x , t) ∈ˢ' (o , u) = ((x , t) ∈ᵍ o × Ord t) ⊎ ((x , t) ∈ u × Unr t)

∈ˢ'-⸴₁ : ∀ {xt} o →
  xt ∈ˢ' γ₁ →
  xt ∈ˢ' (γ₁ ⸴ˢ[ o ] γ₂)
∈ˢ'-⸴₁ o (inj₁ (x∈o , p)) = inj₁ (∈ᵍ-⸴₁ o x∈o , p)
∈ˢ'-⸴₁ o (inj₂ (x∈u , p)) = inj₂ (AnyP.++⁺ˡ x∈u , p)

∈ˢ'-⸴₂ : ∀ {xt} o →
  xt ∈ˢ' γ₂ →
  xt ∈ˢ' (γ₁ ⸴ˢ[ o ] γ₂)
∈ˢ'-⸴₂ o (inj₁ (x∈o , p)) = inj₁ (∈ᵍ-⸴₂ o x∈o , p)
∈ˢ'-⸴₂ o (inj₂ (x∈u , p)) = inj₂ (AnyP.++⁺ʳ _ x∈u , p)

∈ˢ'-⸴ : ∀ {xt} o →
  xt ∈ˢ' (γ₁ ⸴ˢ[ o ] γ₂) →
  xt ∈ˢ' γ₁ ⊎ xt ∈ˢ' γ₂
∈ˢ'-⸴ o (inj₁ (x∈o₁⸴o₂ , p)) with ∈ᵍ-⸴ o x∈o₁⸴o₂
... | inj₁ x∈o₁ = inj₁ (inj₁ (x∈o₁ , p))
... | inj₂ x∈o₂ = inj₂ (inj₁ (x∈o₂ , p))
∈ˢ'-⸴ o (inj₂ (y , p)) with AnyP.++⁻ _ y
... | inj₁ x = inj₁ (inj₂ (x , p))
... | inj₂ y₁ = inj₂ (inj₂ (y₁ , p))

x∈ˢ'x : (x , t) ∈ˢ' (x ∶ˢ t)
x∈ˢ'x {t = t} with Unr? t
… | yes unr-t = inj₂ (here refl , unr-t)
… | no ¬unr-t = inj₁ ((tt , refl) , ¬unr-t)

≲ᵍ'-pres-∈ : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ : Graph L} {l : L} →
  g₁ G.≲ g₂ →
  l ∈ᵍ g₂ →
  l ∈ᵍ g₁
≲ᵍ'-pres-∈ {g₂ = g₂} p (n , refl) =
  G.≲.from p n , trans (G.≲.labels p (G.≲.from p n)) (cong (Graph.label g₂) (G.≲.to∘from p n))

≃ᵍ-pres-∈ : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ : Graph L} {l : L} →
  g₁ G.≃ g₂ →
  l ∈ᵍ g₂ →
  l ∈ᵍ g₁
≃ᵍ-pres-∈ {g₂ = g₂} p (n , refl) =
  G.≃.from p n , trans (G.≃.labels p (G.≃.from p n)) (cong (Graph.label g₂) (G.≃.to∘from p n))

≲ᵍ-pres-∈ : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ : Graph L} {l : L} →
  g₁ ≲ᵍ g₂ →
  l ∈ᵍ g₂ →
  l ∈ᵍ g₁
≲ᵍ-pres-∈ (g₁' , g₂' , g₁≈g₁' , g₁'≲g₂' , g₂'≲g₂) l∈g₂ =
  ≃ᵍ-pres-∈ g₁≈g₁' (≲ᵍ'-pres-∈ g₁'≲g₂' (≃ᵍ-pres-∈ g₂'≲g₂ l∈g₂))

≲ˢ-pres-∈ :
  γ₁ ≲ˢ γ₂ →
  (x , t) ∈ˢ γ₂ →
  (x , t) ∈ˢ γ₁
≲ˢ-pres-∈ (o₁≲o₂ , u₂⊆u₁) (inj₁ x∈o) = inj₁ (≲ᵍ-pres-∈ o₁≲o₂ x∈o)
≲ˢ-pres-∈ (o₁≲o₂ , u₂⊆u₁) (inj₂ x∈u) = inj₂ (u₂⊆u₁ x∈u)

≲ˢ-pres-∉ :
  γ₁ ≲ˢ γ₂ →
  ¬ (x , t) ∈ˢ γ₁ →
  ¬ (x , t) ∈ˢ γ₂
≲ˢ-pres-∉ p x∉ x∈ = x∉ (≲ˢ-pres-∈ p x∈)

⸴ᵍ-identityˡ : ∀ {ℓ} {L : Set ℓ} (g : Graph L) → G.∅ ⸴ᵍ[ o ] g G.≃ g
⸴ᵍ-identityˡ {o = ordered}   g = G.+-identityˡ g
⸴ᵍ-identityˡ {o = unordered} g = G.∪-identityˡ g

⸴ᵍ-identityʳ : ∀ {ℓ} {L : Set ℓ} (g : Graph L) → g ⸴ᵍ[ o ] G.∅ G.≃ g
⸴ᵍ-identityʳ {o = ordered}   g = G.+-identityʳ g
⸴ᵍ-identityʳ {o = unordered} g = G.∪-identityʳ g

≈ˢ-·ˡ : γ ≈ˢ ∅ ⸴ˢ[ o ] γ
≈ˢ-·ˡ {γ = (o , u)} = G.≃-sym (⸴ᵍ-identityˡ o) , ≈ˡ-refl

≈ˢ-·ʳ : γ ≈ˢ γ ⸴ˢ[ o ] ∅
≈ˢ-·ʳ {γ = (o , u)}  = G.≃-sym (⸴ᵍ-identityʳ o) , ≈ˡ-sym (≈ˡ-identityʳ _)

≈ˢ-dup-unr : Unr t → (x ∶ˢ t) ≈ˢ (x ∶ˢ t) ⸴ˢ[ o ] (x ∶ˢ t)
≈ˢ-dup-unr {t = t} unr-t with Unr? t
… | no ¬unr-t = ⊥-elim (¬unr-t unr-t)
… | yes _ = G.≃-sym (⸴ᵍ-identityʳ _) , ≈ˡ-dup _

≃ᵍ-⸴ : ∀ {ℓ} {L : Set ℓ} {g₁ g₁' g₂ g₂' : Graph L} → g₁ G.≃ g₁' → g₂ G.≃ g₂' → (g₁ ⸴ᵍ[ o ] g₂) G.≃ (g₁' ⸴ᵍ[ o ] g₂')
≃ᵍ-⸴ {o = ordered}   g₁≈g₁' g₂≈g₂' = G.≃-+ g₁≈g₁' g₂≈g₂'
≃ᵍ-⸴ {o = unordered} g₁≈g₁' g₂≈g₂' = G.≃-∪ g₁≈g₁' g₂≈g₂'

≈ˢ-⸴ : γ₁ ≈ˢ γ₁' → γ₂ ≈ˢ γ₂' → (γ₁ ⸴ˢ[ o ] γ₂) ≈ˢ (γ₁' ⸴ˢ[ o ] γ₂')
≈ˢ-⸴ (o₁≈o₁' , u₁≈u₁') (o₂≈o₂' , u₂≈u₂') = ≃ᵍ-⸴ o₁≈o₁' o₂≈o₂' , ≈ˡ-++ u₁≈u₁' u₂≈u₂'

≲ᵍ-⸴ : ∀ {ℓ} {L : Set ℓ} {g₁ g₁' g₂ g₂' : Graph L} → g₁ G.≲ g₁' → g₂ G.≲ g₂' → (g₁ ⸴ᵍ[ o ] g₂) G.≲ (g₁' ⸴ᵍ[ o ] g₂')
≲ᵍ-⸴ {o = ordered}   g₁≲g₁' g₂≲g₂' = G.≲-+ g₁≲g₁' g₂≲g₂'
≲ᵍ-⸴ {o = unordered} g₁≲g₁' g₂≲g₂' = G.≲-∪ g₁≲g₁' g₂≲g₂'

≲ᵍ'-⸴ : ∀ {ℓ} {L : Set ℓ} {g₁ g₁' g₂ g₂' : Graph L} → g₁ ≲ᵍ g₁' → g₂ ≲ᵍ g₂' → (g₁ ⸴ᵍ[ o ] g₂) ≲ᵍ (g₁' ⸴ᵍ[ o ] g₂')
≲ᵍ'-⸴ {o = o} (g₁' , g₂' , g₁≈g₁' , g₁'≲g₂' , g₂'≲g₂) (h₁' , h₂' , h₁≈h₁' , h₁'≲h₂' , h₂'≲h₂) =
  _ , _ , ≃ᵍ-⸴ g₁≈g₁' h₁≈h₁' , ≲ᵍ-⸴ g₁'≲g₂' h₁'≲h₂' , ≃ᵍ-⸴ g₂'≲g₂ h₂'≲h₂

≲ˢ-⸴ : γ₁ ≲ˢ γ₁' → γ₂ ≲ˢ γ₂' → (γ₁ ⸴ˢ[ o ] γ₂) ≲ˢ (γ₁' ⸴ˢ[ o ] γ₂')
≲ˢ-⸴ (o₁≲o₁' , u₁≲u₁') (o₂≲o₂' , u₂≲u₂') = ≲ᵍ'-⸴ o₁≲o₁' o₂≲o₂' , ⊆-++ u₁≲u₁' u₂≲u₂'

⸴ᵍ-assoc : ∀ {ℓ} {L : Set ℓ} (g₁ g₂ g₃ : Graph L) → ((g₁ ⸴ᵍ[ o ] g₂) ⸴ᵍ[ o ] g₃) G.≃ (g₁ ⸴ᵍ[ o ] (g₂ ⸴ᵍ[ o ] g₃))
⸴ᵍ-assoc {o = ordered}   g₁ g₂ g₃ = G.+-assoc g₁ g₂ g₃
⸴ᵍ-assoc {o = unordered} g₁ g₂ g₃ = G.∪-assoc g₁ g₂ g₃

⸴ˢ-assoc : ∀ γ₁ γ₂ γ₃ → ((γ₁ ⸴ˢ[ o ] γ₂) ⸴ˢ[ o ] γ₃) ≈ˢ (γ₁ ⸴ˢ[ o ] (γ₂ ⸴ˢ[ o ] γ₃))
⸴ˢ-assoc (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) = ⸴ᵍ-assoc o₁ o₂ o₃ , ≈ˡ-sym (≈ˡ-assoc u₁ u₂ u₃)

∥ˢ-comm : ∀ γ₁ γ₂ → γ₁ ∥ˢ γ₂ ≈ˢ γ₂ ∥ˢ γ₁
∥ˢ-comm (o₁ , u₁) (o₂ , u₂) = (G.∪-comm o₁ o₂) , ≈ˡ-comm u₂ u₁

≲ᵍ-dist-∥-⸴ : ∀ {ℓ} {L : Set ℓ} (g₁₁ g₁₂ g₂₁ g₂₂ : Graph L) → (g₁₁ G.+ g₁₂) G.∪ (g₂₁ G.+ g₂₂) ≲ᵍ (g₁₁ G.∪ g₂₁) G.+ (g₁₂ G.∪ g₂₂)
≲ᵍ-dist-∥-⸴ g₁₁ g₁₂ g₂₁ g₂₂ = _ , _ , G.≃-refl , G.≲-dist-∪-+ g₁₁ g₁₂ g₂₁ g₂₂ , G.≃-refl

≲ˢ-dist-∥-⸴ : ∀ γ₁₁ γ₁₂ γ₂₁ γ₂₂ → (γ₁₁ ⸴ˢ γ₁₂) ∥ˢ (γ₂₁ ⸴ˢ γ₂₂) ≲ˢ (γ₁₁ ∥ˢ γ₂₁) ⸴ˢ (γ₁₂ ∥ˢ γ₂₂)
≲ˢ-dist-∥-⸴ (o₁₁ , u₁₁) (o₁₂ , u₁₂) (o₂₁ , u₂₁) (o₂₂ , u₂₂) =
  ≲ᵍ-dist-∥-⸴ o₁₁ o₁₂ o₂₁ o₂₂ , ⊆-dist-∥-⸴ u₁₁ u₁₂ u₂₁ u₂₂ 

∥≲ᵍ⸴ : ∀ {ℓ} {L : Set ℓ} (g₁ g₂ : Graph L) → g₁ G.∪ g₂ ≲ᵍ g₁ G.+ g₂
∥≲ᵍ⸴ g₁ g₂ = _ , _ , G.≃-refl , G.∪≲+ g₁ g₂ , G.≃-refl

∥≲ˢ⸴ : ∀ γ₁ γ₂ → γ₁ ∥ˢ γ₂ ≲ˢ γ₁ ⸴ˢ γ₂
∥≲ˢ⸴ (o₁ , u₁) (o₂ , u₂) = ∥≲ᵍ⸴ o₁ o₂ , ⊆-refl

≃→≲ᵍ : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ : Graph L} → g₁ G.≃ g₂ → g₁ ≲ᵍ g₂
≃→≲ᵍ p = _ , _ , p , G.≲-refl , G.≃-refl

≈ˢ→≲ˢ : γ₁ ≈ˢ γ₂ → γ₁ ≲ˢ γ₂
≈ˢ→≲ˢ (o₁ , u₁) = ≃→≲ᵍ o₁ , ≈ˡ→⊆ u₁

≲ᵍ'-lem₁ : ∀ {ℓ} {L : Set ℓ} (g₁ g₂ g₃ : Graph L) → (g₁ G.+ g₂) ⸴ᵍ[ o ] g₃ G.≲ g₁ G.+ (g₂ ⸴ᵍ[ o ] g₃)
≲ᵍ'-lem₁ {o = ordered}   g₁ g₂ g₃ = G.≃→≲ (G.+-assoc g₁ g₂ g₃)
≲ᵍ'-lem₁ {o = unordered} g₁ g₂ g₃ = G.∪≲+'' g₁ g₂ g₃

≲ᵍ-lem₁ : ∀ {ℓ} {L : Set ℓ} (g₁ g₂ g₃ : Graph L) → (g₁ G.+ g₂) ⸴ᵍ[ o ] g₃ ≲ᵍ g₁ G.+ (g₂ ⸴ᵍ[ o ] g₃)
≲ᵍ-lem₁ g₁ g₂ g₃ = _ , _ , G.≃-refl , ≲ᵍ'-lem₁ g₁ g₂ g₃ , G.≃-refl

≲ˢ-lem₁ : ∀ γ₁ γ₂ γ₃ → (γ₁ ⸴ˢ γ₂) ⸴ˢ[ o ] γ₃ ≲ˢ γ₁ ⸴ˢ (γ₂ ⸴ˢ[ o ] γ₃)
≲ˢ-lem₁ (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) = ≲ᵍ-lem₁ o₁ o₂ o₃ , ⊆-assoc' u₁ u₂ u₃

≲ᵍ'-lem₁' : ∀ {ℓ} {L : Set ℓ} (g₁ g₂ g₃ : Graph L) → g₁ ⸴ᵍ[ o ] (g₂ G.+ g₃) G.≲ (g₁ ⸴ᵍ[ o ] g₂) G.+ g₃
≲ᵍ'-lem₁' {o = ordered}   g₁ g₂ g₃ = G.≃→≲ (G.≃-sym (G.+-assoc g₁ g₂ g₃))
≲ᵍ'-lem₁' {o = unordered} g₁ g₂ g₃ = G.∪≲+' g₁ g₂ g₃

≲ᵍ-lem₁' : ∀ {ℓ} {L : Set ℓ} (g₁ g₂ g₃ : Graph L) → g₁ ⸴ᵍ[ o ] (g₂ G.+ g₃) ≲ᵍ (g₁ ⸴ᵍ[ o ] g₂) G.+ g₃
≲ᵍ-lem₁' g₁ g₂ g₃ = _ , _ , G.≃-refl , ≲ᵍ'-lem₁' g₁ g₂ g₃ , G.≃-refl

≲ˢ-lem₁' : ∀ γ₁ γ₂ γ₃ → γ₁ ⸴ˢ[ o ] (γ₂ ⸴ˢ γ₃) ≲ˢ (γ₁ ⸴ˢ[ o ] γ₂) ⸴ˢ γ₃
≲ˢ-lem₁' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) = ≲ᵍ-lem₁' o₁ o₂ o₃ , ⊆-assoc u₁ u₂ u₃

≈ˡ-lem₂ : ∀ {ℓ} {A : Set ℓ} (xs ys zs : List A) → ys ++ (zs ++ xs) ≈ˡ xs ++ (ys ++ zs)
≈ˡ-lem₂ u₁ u₂ u₃ = 
  let open ≈ˡ-Reasoning in
  begin
    u₂ ++ (u₃ ++ u₁)
  ≈⟨ ≈ˡ-++ {xs₁ = u₂} ≈ˡ-refl (≈ˡ-comm u₃ u₁) ⟩
    u₂ ++ (u₁ ++ u₃)
  ≈⟨ ≈ˡ-sym (≈ˡ-assoc u₂ u₁ u₃) ⟩
    (u₂ ++ u₁) ++ u₃
  ≈⟨ ≈ˡ-++ (≈ˡ-comm u₂ u₁) ≈ˡ-refl ⟩
    (u₁ ++ u₂) ++ u₃
  ≈⟨ ≈ˡ-assoc u₁ u₂ u₃ ⟩
    u₁ ++ (u₂ ++ u₃)
  ∎

≈ˡ-lem₂' : ∀ {ℓ} {A : Set ℓ} (u₁ u₂ u₃ : List A) → ((u₁ ++ u₃) ++ u₂) ≈ˡ ((u₃ ++ u₂) ++ u₁)
≈ˡ-lem₂' u₁ u₂ u₃ =
  let open ≈ˡ-Reasoning in
  begin
    (u₁ ++ u₃) ++ u₂
  ≈⟨ ≈ˡ-assoc u₁ u₃ u₂ ⟩
    u₁ ++ (u₃ ++ u₂)
  ≈⟨ ≈ˡ-comm u₁ (u₃ ++ u₂) ⟩
    (u₃ ++ u₂) ++ u₁
  ∎

≈ˡ-lem₂'' : ∀ {ℓ} {A : Set ℓ} (u₁ u₂ u₃ : List A) → ((u₂ ++ u₁) ++ u₃) ≈ˡ ((u₂ ++ u₃) ++ u₁)
≈ˡ-lem₂'' u₁ u₂ u₃ =
  let open ≈ˡ-Reasoning in
  begin
    (u₂ ++ u₁) ++ u₃
  ≈⟨ ≈ˡ-assoc u₂ u₁ u₃ ⟩
    u₂ ++ (u₁ ++ u₃)
  ≈⟨ ≈ˡ-++ {xs₁ = u₂} ≈ˡ-refl (≈ˡ-comm u₁ u₃) ⟩
    u₂ ++ (u₃ ++ u₁)
  ≈⟨ ≈ˡ-sym (≈ˡ-assoc u₂ u₃ u₁) ⟩
    (u₂ ++ u₃) ++ u₁
  ∎

≲→≲ᵍ : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ : Graph L} → g₁ G.≲ g₂ → g₁ ≲ᵍ g₂
≲→≲ᵍ p = _ , _ , G.≃-refl , p , G.≃-refl

≃-⸴ᵍ : ∀ {ℓ} {L : Set ℓ} {g₁ g₂ g₁' g₂' : Graph L} → g₁ G.≃ g₁' → g₂ G.≃ g₂' → (g₁ ⸴ᵍ[ o ] g₂) G.≃ (g₁' ⸴ᵍ[ o ] g₂')
≃-⸴ᵍ {o = ordered}   p q = G.≃-+ p q
≃-⸴ᵍ {o = unordered} p q = G.≃-∪ p q

≲ᵍ-lem₂ : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → g G.≃ G.∅ → g ⸴ᵍ[ o ] (g₁ G.+ g₂) ≲ᵍ g₁ G.+ (g₂ ⸴ᵍ[ o ] g)
≲ᵍ-lem₂ {o = o} g g₁ g₂ g≃∅ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    g ⸴ᵍ[ o ] (g₁ G.+ g₂)
  ≃⟨ ≃-⸴ᵍ g≃∅ G.≃-refl ⟩
    G.∅ ⸴ᵍ[ o ] (g₁ G.+ g₂)
  ≃⟨ ⸴ᵍ-identityˡ (g₁ G.+ g₂) ⟩
    g₁ G.+ g₂
  ≃⟨ G.≃-+ G.≃-refl (G.≃-sym (⸴ᵍ-identityʳ {o = o} g₂)) ⟩
    g₁ G.+ (g₂ ⸴ᵍ[ o ] G.∅)
  ≃⟨ G.≃-+ G.≃-refl (≃-⸴ᵍ {o = o} G.≃-refl (G.≃-sym g≃∅)) ⟩
    g₁ G.+ (g₂ ⸴ᵍ[ o ] g)
  ∎

≲ᵍ-lem₂''' : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → g G.≃ G.∅ → g ⸴ᵍ[ o ] (g₁ G.∪ g₂) ≲ᵍ (g ⸴ᵍ[ o ] g₁) G.∪ g₂
≲ᵍ-lem₂''' {o = o} g g₁ g₂ g≃∅ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    g ⸴ᵍ[ o ] (g₁ G.∪ g₂)
  ≃⟨ ≃-⸴ᵍ g≃∅ G.≃-refl ⟩
    G.∅ ⸴ᵍ[ o ] (g₁ G.∪ g₂)
  ≃⟨ ⸴ᵍ-identityˡ (g₁ G.∪ g₂) ⟩
    g₁ G.∪ g₂
  ≃⟨ G.≃-sym (G.≃-∪ (⸴ᵍ-identityˡ {o = o} g₁) G.≃-refl) ⟩
    (G.∅ ⸴ᵍ[ o ] g₁) G.∪ g₂
  ≃⟨ G.≃-sym (G.≃-∪ (≃-⸴ᵍ {o = o} g≃∅ G.≃-refl) G.≃-refl) ⟩
    (g ⸴ᵍ[ o ] g₁) G.∪ g₂
  ∎

≲ᵍ-lem₂' : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → g G.≃ G.∅ → (g₂ G.+ g₁) ⸴ᵍ[ o ] g ≲ᵍ (g ⸴ᵍ[ o ] g₂) G.+ g₁
≲ᵍ-lem₂' {o = o} g g₁ g₂ g≃∅ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    (g₂ G.+ g₁) ⸴ᵍ[ o ] g
  ≃⟨ ≃-⸴ᵍ G.≃-refl g≃∅ ⟩
    (g₂ G.+ g₁) ⸴ᵍ[ o ] G.∅
  ≃⟨ ⸴ᵍ-identityʳ (g₂ G.+ g₁) ⟩
    g₂ G.+ g₁
  ≃⟨ G.≃-sym (G.≃-+ (⸴ᵍ-identityˡ {o = o} g₂) G.≃-refl) ⟩
    (G.∅ ⸴ᵍ[ o ] g₂) G.+ g₁
  ≃⟨ G.≃-sym (G.≃-+ (≃-⸴ᵍ {o = o} g≃∅ G.≃-refl) G.≃-refl) ⟩
    (g ⸴ᵍ[ o ] g₂) G.+ g₁
  ∎

≲ᵍ-lem₂'' : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → g G.≃ G.∅ → (g₁ G.∪ g₂) ⸴ᵍ[ o ] g ≲ᵍ (g₁ ⸴ᵍ[ o ] g) G.∪ g₂
≲ᵍ-lem₂'' {o = o} g g₁ g₂ g≃∅ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    (g₁ G.∪ g₂) ⸴ᵍ[ o ] g
  ≃⟨ ≃-⸴ᵍ G.≃-refl g≃∅ ⟩
    (g₁ G.∪ g₂) ⸴ᵍ[ o ] G.∅
  ≃⟨ ⸴ᵍ-identityʳ (g₁ G.∪ g₂) ⟩
    g₁ G.∪ g₂
  ≃⟨ G.≃-sym (G.≃-∪ (⸴ᵍ-identityʳ {o = o} g₁) G.≃-refl) ⟩
    (g₁ ⸴ᵍ[ o ] G.∅) G.∪ g₂
  ≃⟨ G.≃-sym (G.≃-∪ (≃-⸴ᵍ {o = o} G.≃-refl g≃∅) G.≃-refl) ⟩
    (g₁ ⸴ᵍ[ o ] g) G.∪ g₂
  ∎

≲ᵍ-lem₂x : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → g G.∪ (g₁ G.+ g₂) ≲ᵍ g₁ G.+ (g₂ G.∪ g)
≲ᵍ-lem₂x g g₁ g₂ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    g G.∪ (g₁ G.+ g₂)
  ≃⟨ G.≃-∪ (G.≃-sym (G.+-identityˡ g)) G.≃-refl ⟩
    (G.∅ G.+ g) G.∪ (g₁ G.+ g₂)
  ≲⟨ G.≲-dist-∪-+ G.∅ g g₁ g₂ ⟩
    (G.∅ G.∪ g₁) G.+ (g G.∪ g₂)
  ≃⟨ G.≃-+ (G.∪-identityˡ g₁) (G.∪-comm g g₂) ⟩
    g₁ G.+ (g₂ G.∪ g)
  ∎

≲ᵍ-lem₂'''x : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → g G.∪ (g₁ G.∪ g₂) ≲ᵍ (g G.∪ g₁) G.∪ g₂
≲ᵍ-lem₂'''x g g₁ g₂ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    g G.∪ (g₁ G.∪ g₂)
  ≃⟨ G.≃-sym (G.∪-assoc g g₁ g₂) ⟩
    (g G.∪ g₁) G.∪ g₂
  ∎

≲ᵍ-lem₂'x : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → (g₂ G.+ g₁) G.∪ g ≲ᵍ (g G.∪ g₂) G.+ g₁
≲ᵍ-lem₂'x g g₁ g₂ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    (g₂ G.+ g₁) G.∪ g
  ≃⟨ G.≃-∪ G.≃-refl (G.≃-sym (G.+-identityʳ g)) ⟩
    (g₂ G.+ g₁) G.∪ (g G.+ G.∅)
  ≲⟨ G.≲-dist-∪-+ g₂ g₁ g G.∅ ⟩
    (g₂ G.∪ g) G.+ (g₁ G.∪ G.∅)
  ≃⟨ G.≃-+ (G.∪-comm g₂ g) (G.∪-identityʳ g₁) ⟩
    (g G.∪ g₂) G.+ g₁
  ∎

≲ᵍ-lem₂''x : ∀ {ℓ} {L : Set ℓ} (g g₁ g₂ : Graph L) → (g₁ G.∪ g₂) G.∪ g ≲ᵍ (g₁ G.∪ g) G.∪ g₂
≲ᵍ-lem₂''x g g₁ g₂ =
  ≲→≲ᵍ $
  let open G.≲-Reasoning in
  begin
    (g₁ G.∪ g₂) G.∪ g
  ≃⟨ G.∪-assoc g₁ g₂ g ⟩
    g₁ G.∪ (g₂ G.∪ g)
  ≃⟨ G.≃-∪ G.≃-refl (G.∪-comm g₂ g) ⟩
    g₁ G.∪ (g G.∪ g₂)
  ≃⟨ G.≃-sym (G.∪-assoc g₁ g g₂) ⟩
    (g₁ G.∪ g) G.∪ g₂
  ∎

≲ˢ-lem₂ : ∀ γ γ₁ γ₂ → o ≡ unordered ⊎ SemCtx.ord-graph γ G.≃ G.∅ → γ ⸴ˢ[ o ] (γ₁ ⸴ˢ γ₂) ≲ˢ γ₁ ⸴ˢ (γ₂ ⸴ˢ[ o ] γ)
≲ˢ-lem₂ (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₁ refl) = ≲ᵍ-lem₂x o₁ o₂ o₃ , ≈ˡ→⊆ (≈ˡ-lem₂ u₁ u₂ u₃)
≲ˢ-lem₂ (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₂ unr-γ) = ≲ᵍ-lem₂ o₁ o₂ o₃ unr-γ , ≈ˡ→⊆ (≈ˡ-lem₂ u₁ u₂ u₃)

≲ˢ-lem₂''' : ∀ γ γ₁ γ₂ → o ≡ unordered ⊎ SemCtx.ord-graph γ G.≃ G.∅ → γ ⸴ˢ[ o ] (γ₁ ∥ˢ γ₂) ≲ˢ (γ ⸴ˢ[ o ] γ₁) ∥ˢ γ₂
≲ˢ-lem₂''' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₁ refl) = ≲ᵍ-lem₂'''x o₁ o₂ o₃ , (≈ˡ→⊆ (≈ˡ-assoc u₁ u₂ u₃))
≲ˢ-lem₂''' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₂ unr-γ) = ≲ᵍ-lem₂''' o₁ o₂ o₃ unr-γ , (≈ˡ→⊆ (≈ˡ-assoc u₁ u₂ u₃))

≲ˢ-lem₂' : ∀ γ γ₁ γ₂ → o ≡ unordered ⊎ SemCtx.ord-graph γ G.≃ G.∅ → (γ₂ ⸴ˢ γ₁) ⸴ˢ[ o ] γ ≲ˢ (γ ⸴ˢ[ o ] γ₂) ⸴ˢ γ₁
≲ˢ-lem₂' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₁ refl) = ≲ᵍ-lem₂'x o₁ o₂ o₃ , ≈ˡ→⊆ (≈ˡ-lem₂' u₁ u₂ u₃)
≲ˢ-lem₂' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₂ unr-γ) = ≲ᵍ-lem₂' o₁ o₂ o₃ unr-γ , ≈ˡ→⊆ (≈ˡ-lem₂' u₁ u₂ u₃)

≲ˢ-lem₂'' : ∀ γ γ₁ γ₂ → o ≡ unordered ⊎ SemCtx.ord-graph γ G.≃ G.∅ → (γ₁ ∥ˢ γ₂) ⸴ˢ[ o ] γ ≲ˢ (γ₁ ⸴ˢ[ o ] γ) ∥ˢ γ₂
≲ˢ-lem₂'' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₁ refl) = ≲ᵍ-lem₂''x o₁ o₂ o₃ , ≈ˡ→⊆ (≈ˡ-lem₂'' u₁ u₂ u₃)
≲ˢ-lem₂'' (o₁ , u₁) (o₂ , u₂) (o₃ , u₃) (inj₂ unr-γ) = ≲ᵍ-lem₂'' o₁ o₂ o₃ unr-γ , ≈ˡ→⊆ (≈ˡ-lem₂'' u₁ u₂ u₃)
