module BGV.Algorithmic where

import Data.List.Properties as ListP
import Data.List.Relation.Unary.Any.Properties as AnyP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as L using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; _$_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)
open import Relation.Nullary using (¬_)

open import BGV.Id
open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Types
open import BGV.Expressions
open import BGV.Context
open import BGV.Context.SyntacticSplit
open import BGV.Split
open import BGV.Ren
open import BGV.UsageMap
open import BGV.Util.Decidable
open import BGV.Util.Map as Map using (Map)
open import BGV.Util.List

data InfChk : Set where
  inf chk : InfChk

AppInf : Mult → InfChk
AppInf ∞ = chk
AppInf 𝟙 = chk
AppInf ≻ = chk
AppInf ≺ = inf

SplitsAlg' : UsageMap → UsageMap → Expr § → List (Expr §) → Ctx → Ctx → CtxPat → List Id → Set₁
SplitsAlg' u₁ u₂ e₁ e₂s Γ Γ₁ C extra =
  let sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) in
  split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ≲ ((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ (Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁ ]

SplitsAlg'? : ∀ u₁ u₂ (e₁ : Expr §) (e₂s : List (Expr §)) Γ Γ₁ C extra →
  Dec (SplitsAlg' u₁ u₂ e₁ e₂s Γ Γ₁ C extra)
SplitsAlg'? u₁ u₂ e₁ e₂s Γ Γ₁ C extra =
  let sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) in
  split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ≲? (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ (Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁ ])

SplitsAlg'-eqᵘ : ∀ u₁ u₂ u₂' (e₁ : Expr §) (e₂s : List (Expr §)) Γ Γ₁ C extra →
  dom (C [ · ]) ⊆ dom Γ →
  LocallyEqᵘ (dom Γ) u₂ u₂' →
  SplitsAlg' u₁ u₂ e₁ e₂s Γ Γ₁ C extra →
  SplitsAlg' u₁ u₂' e₁ e₂s Γ Γ₁ C extra
SplitsAlg'-eqᵘ u₁ u₂ u₂' e₁ e₂s Γ Γ₁ C extra domC⊆domΓ eq salg =
  let fvs₂  = L.foldl _++_ [] (map fvs e₂s) in
  let vars₂ = L.foldl _++_ [] (map vars e₂s) in
  let sis = (fvs e₁ ∩ˡ fvs₂) ↓ᵘ u₁ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ extra ++ vars e₁ ++ vars₂) in
  subst₂
    (λ ■₁ ■₂ → split-ctx sis ρ₁ ρ₂ ■₁ ≲ (■₂ ⋯ʳᶜ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ ])
    (⋯ᵘ-locally-eq Γ (u₁ ·ᵘ u₂) (u₁ ·ᵘ u₂') (·ᵘ-locally-eq (dom Γ) u₁ u₂ u₁ u₂' reflᵘ eq))
    (⋯ᵘᶜ-locally-eq C u₂ u₂' (LocallyEqᵘ-⊆ domC⊆domΓ eq))
    salg
  
-- SplitsAlg : UsageMap → UsageMap → Expr § → Expr § → Ctx → Ctx → Ctx → IsOrd → Set₁
-- SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ o =
--   let sis = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁ in
--   let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂) in
--   split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ≲ ((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ⸴[ o ] ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)

SplitsAlg : UsageMap → UsageMap → Expr § → Expr § → Ctx → Ctx → Ctx → IsOrd → Set₁
SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ o =
  SplitsAlg' u₁ u₂ e₁ (e₂ ∷ []) Γ Γ₁ ([] ⸴[ o ]₁ Γ₂) []

SplitsAlg? : ∀ u₁ u₂ (e₁ e₂ : Expr §) Γ Γ₁ Γ₂ o →
  Dec (SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ o)
SplitsAlg? u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ o =
  let sis = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂) in
  split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ≲? (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ⸴[ o ] ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂))

data _⊢_∶[_]_⍮_⍮_ : Ctx → Expr alg → InfChk → Type → UsageMap → Effect → Set₁ where
  ⊢`-nochan :
    Γ ≲ (x ∶ t) →
    (∀ b s → t ≢ Chan b s) →
    Γ ⊢ (` x) ∶[ inf ] t ⍮ ∅ᵘ ⍮ 𝟎
  ⊢`-chan :
    Γ ≲ (x ∶ t) →
    t ≡ Chan b s →
    Γ ⊢ (` x) ∶[ inf ] t ⍮ ⟨ x , (b , s) ⟩ᵘ ⍮ 𝟎
  ⊢& :
    Γ ≲ (x ∶ t) →
    t ≡ Chan b s →
    s ≡ s₁ ++ˢ s₂ →
    Γ ⊢ (& x) ∶[ chk ] Chan borrowed s₁ ⍮ ⟨ x , (borrowed , s₁) ⟩ᵘ ⍮ 𝟎
  ⊢λ :
    x ∉ dom Γ →
    ext m Γ (x ∶ t₁) ⊢ e ∶[ chk ] t₂ ⍮ u ⍮ ϕ₁ →
    (m ≡ ∞ → Unrᶜ Γ) →
    (∀ b (s : Session b) → t₁ ≡ Chan b s → u x ≡ some (b , s)) → 
    ϕ₁ ⊑ ϕ₂ →
    Γ ⊢ (λ[ m ] x ⇒ e) ∶[ chk ] (t₁ –[ m ⍮ ϕ₂ ]→ t₂) ⍮ (u -ᵘ x) ⍮ 𝟎
  ⊢·≻ :
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] (t₁ –[ ≻ ⍮ ϕ ]→ t₂) ⍮ u₁ ⍮ ϕ₁ →
    Γ₂ ≡ (Γ ↓ fvs e₂) %ᶜ u₁ →
    Γ₂ ⊢ e₂ ∶[ chk ] t₁ ⍮ u₂ ⍮ 𝟎 →
    SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ ordered →
    Γ ⊢ (e₁ `· e₂) ∶[ inf ] t₂ ⍮ (u₁ ·ᵘ u₂) ⍮ (ϕ₁ ⊔ ϕ)
  ⊢·≺ :
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] t₁ ⍮ u₁ ⍮ ϕ₁ →
    Γ₂ ≡ (Γ ↓ fvs e₂) %ᶜ u₁ →
    Γ₂ ⊢ e₂ ∶[ inf ] (t₁ –[ ≺ ⍮ ϕ ]→ t₂) ⍮ u₂ ⍮ 𝟎 →
    SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ ordered →
    Γ ⊢ (e₁ ▸ e₂) ∶[ inf ] t₂ ⍮ (u₁ ·ᵘ u₂) ⍮ (ϕ₁ ⊔ ϕ)
  ⊢·𝟙 :
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] (t₁ –[ 𝟙 ⍮ ϕ ]→ t₂) ⍮ u₁ ⍮ ϕ₁ →
    Γ₂ ≡ (Γ ↓ fvs e₂) %ᶜ u₁ →
    Γ₂ ⊢ e₂ ∶[ chk ] t₁ ⍮ u₂ ⍮ ϕ₂ →
    SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ unordered →
    Γ ⊢ (e₁ `· e₂) ∶[ inf ] t₂ ⍮ (u₁ ·ᵘ u₂) ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ)
  ⊢·∞ :
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] (t₁ –[ ∞ ⍮ ϕ ]→ t₂) ⍮ u₁ ⍮ ϕ₁ →
    Γ₂ ≡ (Γ ↓ fvs e₂) %ᶜ u₁ →
    Γ₂ ⊢ e₂ ∶[ chk ] t₁ ⍮ u₂ ⍮ ϕ₂ →
    SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ ordered →
    Γ ⊢ (e₁ `· e₂) ∶[ inf ] t₂ ⍮ (u₁ ·ᵘ u₂) ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ)
  ⊢, :
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] t₁ ⍮ u₁ ⍮ ϕ₁ →
    Γ₂ ≡ (Γ ↓ fvs e₂) %ᶜ u₁ →
    Γ₂ ⊢ e₂ ∶[ inf ] t₂ ⍮ u₂ ⍮ ϕ₂ →
    (¬ Unr t₁ → p ≡ ≻ → ϕ₂ ≡ 𝟎) →
    SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ (pmult→ord p) →
    Γ ⊢ (e₁ ,[ p ] e₂) ∶[ inf ] (t₁ ×[ p ] t₂) ⍮ (u₁ ·ᵘ u₂) ⍮ (ϕ₁ ⊔ ϕ₂)
  ⊢let :
    x ∉ dom Γ →
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] t₁ ⍮ u₁ ⍮ ϕ₁ →
    let sis = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁ in
    let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂) in
    split-ctx sis ρ₁ ρ₂ Γ ↓ᶜ (fvs e₁ ⋯ˡ ρ₁) ≡ some (C' , Γ₁') →
    C ≡ C' ⋯ʳᶜ invertʳ (map proj₁ sis) ρ₂ →
    (¬ LeftCtx C → ϕ₁ ≡ 𝟎) →
    dom (C [ · ]) ⊆ⁱ dom Γ →
    (C [ x ∶ t₁ ]) ⊢ e₂ ∶[ inf ] t₂ ⍮ u₂ ⍮ ϕ₂ →
    (∀ b (s : Session b) → t₁ ≡ Chan b s → u₂ x ≡ some (b , s)) → 
    SplitsAlg' u₁ (u₂ -ᵘ x) e₁ (e₂ ∷ []) Γ Γ₁ C L.[ x ] →
    Γ ⊢ (let[ x ≔ e₁ ]in e₂) ∶[ inf ] t₂ ⍮ (u₁ ·ᵘ (u₂ -ᵘ x)) ⍮ (ϕ₁ ⊔ ϕ₂)
  ⊢let× :
    x ∉ dom Γ →
    y ∉ dom Γ →
    x ≢ y →
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] (t₁ ×[ p ] t₂) ⍮ u₁ ⍮ ϕ₁ →
    (¬ LeftCtx C → ϕ₁ ≡ 𝟎) →
    let sis = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁ in
    let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂) in
    split-ctx sis ρ₁ ρ₂ Γ ↓ᶜ (fvs e₁ ⋯ˡ ρ₁) ≡ some (C' , Γ') →
    C ≡ C' ⋯ʳᶜ invertʳ (map proj₁ sis) ρ₂ →
    dom (C [ · ]) ⊆ⁱ dom Γ →
    (C [ x ∶ t₁ ⸴[ pmult→ord p ] y ∶ t₂ ]) ⊢ e₂ ∶[ inf ] t ⍮ u₂ ⍮ ϕ₂ →
    (∀ b (s : Session b) → t₁ ≡ Chan b s → u₂ x ≡ some (b , s)) → 
    (∀ b (s : Session b) → t₂ ≡ Chan b s → u₂ y ≡ some (b , s)) → 
    SplitsAlg' u₁ (u₂ -ᵘ x -ᵘ y) e₁ (e₂ ∷ []) Γ Γ₁ C (x ∷ y ∷ []) →
    Γ ⊢ (let[ x `, y ≔ e₁ ]in e₂) ∶[ inf ] t ⍮ (u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y))⍮ (ϕ₁ ⊔ ϕ₂)
  ⊢inj : ∀ {l} →
    Γ ⊢ e ∶[ chk ] selectₗ l t₁ t₂ ⍮ u ⍮ ϕ →
    Γ ⊢ `inj l e ∶[ chk ] (t₁ + t₂) ⍮ u ⍮ ϕ
  ⊢case :
    x₁ ∉ dom Γ →
    x₂ ∉ dom Γ →
    x₁ ≢ x₂ →
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] (t₁ + t₂) ⍮ u₁ ⍮ ϕ₁ →
    (¬ LeftCtx C → ϕ₁ ≡ 𝟎) →
    let sis = (fvs e₁ ∩ˡ (fvs e₂₁ ++ fvs e₂₂)) ↓ᵘ u₁ in
    let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ vars e₂₁ ++ vars e₂₂) in
    split-ctx sis ρ₁ ρ₂ Γ ↓ᶜ (fvs e₁ ⋯ˡ ρ₁) ≡ some (C' , Γ') →
    C ≡ C' ⋯ʳᶜ invertʳ (map proj₁ sis) ρ₂ →
    dom (C [ · ]) ⊆ⁱ dom Γ →
    (C [ x₁ ∶ t₁ ]) ⊢ e₂₁ ∶[ inf ] t ⍮ u₂₁ ⍮ ϕ₂ →
    (C [ x₂ ∶ t₂ ]) ⊢ e₂₂ ∶[ inf ] t ⍮ u₂₂ ⍮ ϕ₃ →
    LocallyEqᵘ (dom Γ) (u₂₁ -ᵘ x₁) (u₂₂ -ᵘ x₂) →
    (∀ b (s : Session b) → t₁ ≡ Chan b s → u₂₁ x₁ ≡ some (b , s)) → 
    (∀ b (s : Session b) → t₂ ≡ Chan b s → u₂₂ x₂ ≡ some (b , s)) → 
    SplitsAlg' u₁ (u₂₁ -ᵘ x₁) e₁ (e₂₁ ∷ e₂₂ ∷ []) Γ Γ₁ C (x₁ ∷ x₂ ∷ []) →
    Γ ⊢ case e₁ of[ x₁ ⇒ e₂₁ ⍮ x₂ ⇒ e₂₂ ] ∶[ inf ] t ⍮ (u₁ ·ᵘ (u₂₁ -ᵘ x₁)) ⍮ (ϕ₁ ⊔ ϕ₂ ⊔ ϕ₃)
  ⊢unit :
    Γ ≲ · →
    Γ ⊢ unit ∶[ inf ] Unit ⍮ ∅ᵘ ⍮ 𝟎
  ⊢spawn :
    Γ ⊢ e ∶[ inf ] Unit ⍮ u ⍮ ϕ →
    Γ ⊢ spawn e ∶[ inf ] Unit ⍮ u ⍮ 𝟎
  ⊢new :
    Γ ≲ · →
    Γ ⊢ new s ∶[ inf ] (Chan owned s ×[ 𝟙 ] Chan owned (dual s)) ⍮ ∅ᵘ ⍮ 𝟎
  ⊢send :
    Γ₁ ≡ Γ ↓ fvs e₁ →
    Γ₁ ⊢ e₁ ∶[ inf ] t₁ ⍮ u₁ ⍮ ϕ₁ →
    Γ₂ ≡ (Γ ↓ fvs e₂) %ᶜ u₁ →
    Γ₂ ⊢ e₂ ∶[ chk ] Chan _ (op[ ‼ ] t₁ ⍮ return) ⍮ u₂ ⍮ ϕ₂ →
    SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ unordered →
    Γ ⊢ send e₁ e₂ ∶[ inf ] Unit ⍮ (u₁ ·ᵘ u₂) ⍮ 𝟏
  ⊢recv :
    Γ ⊢ e ∶[ inf ] Chan _ (op[ ⁈ ] t ⍮ return) ⍮ u ⍮ ϕ →
    Γ ⊢ recv e ∶[ inf ] t ⍮ u ⍮ 𝟏
  ⊢select : ∀ {l} →
    Γ ⊢ e ∶[ inf ] Chan _ (choice[ ‼ ] s₁ ⍮ s₂) ⍮ u ⍮ ϕ →
    Γ ⊢ select l e ∶[ inf ] Chan _ (selectₗ l s₁ s₂) ⍮ u ⍮ 𝟏
  ⊢branch :
    Γ ⊢ e ∶[ inf ] Chan _ (choice[ ⁈ ] s₁ ⍮ s₂) ⍮ u ⍮ ϕ →
    Γ ⊢ branch e ∶[ inf ] (Chan _ s₁ + Chan _ s₂) ⍮ u ⍮ 𝟏
  ⊢drop :
    Γ ⊢ e ∶[ inf ] Chan _ return ⍮ u ⍮ ϕ →
    Γ ⊢ drop e ∶[ inf ] Unit ⍮ u ⍮ 𝟏
  ⊢close : ∀ {o} →
    Γ ⊢ e ∶[ inf ] Chan _ (end o) ⍮ u ⍮ ϕ →
    Γ ⊢ close o e ∶[ inf ] Unit ⍮ u ⍮ 𝟏
  ⊢∶ :
    Γ ⊢ e ∶[ chk ] t ⍮ u ⍮ ϕ →
    Γ ⊢ (e `∶ t) ∶[ inf ] t ⍮ u ⍮ ϕ
  ⊢chk-inf :
    Γ ⊢ e ∶[ inf ] t ⍮ u ⍮ ϕ →
    Γ ⊢ e ∶[ chk ] t ⍮ u ⍮ ϕ

--------------------------------------------------------------------------------

-- split-ctx-∈⁻ : ∀ {sis ρ₁ ρ₂ Γ} → 
--   sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
--   x ∈ dom (split-ctx sis ρ₁ ρ₂ Γ) →
--   x ∈ map proj₁ sis × ∃[ x' ] x' ∈ dom Γ × (ρ₁ x' ≡ x ⊎ ρ₂ x' ≡ x) ⊎
--   x ∉ map proj₁ sis × x ∈ dom Γ
-- split-ctx-∈⁻ {sis = sis} {ρ₁} {ρ₂} {Γ = x ∶ t} sis⊧ x∈
--  with Chan? t
-- … | no _ = {!inj₂!}
-- … | yes (b , s , refl)
--  with Map.lookup x sis
-- … | none = {!!}
-- … | some s₁
--  with s % s₁
-- … | none = {!!}
-- … | some s₂ = {!!}
-- split-ctx-∈⁻ sis ρ₁ ρ₂ (Γ₁ ⸴[ o ] Γ₂) x∈ = {!!}

split-ctx-∈⁻ : ∀ sis ρ₁ ρ₂ Γ → 
  x ∈ dom (split-ctx sis ρ₁ ρ₂ Γ) →
  x ∈ dom Γ ⊎
  ∃[ x' ] x' ∈ map proj₁ sis × x' ∈ dom Γ × (ρ₁ x' ≡ x ⊎ ρ₂ x' ≡ x)
split-ctx-∈⁻ sis ρ₁ ρ₂ (x ∶ t) x∈
 with Chan? t
… | no _ = inj₁ x∈
… | yes (b , s , refl)
 with Map.lookup x sis in eq
… | none = inj₁ x∈
… | some s₁
 with s % s₁
… | none = inj₁ x∈
… | some s₂
  with x∈
… | here refl =
    inj₂ (x , ∈-map proj₁ (Map.lookup-some→∈ sis eq) , here refl , inj₁ refl)
… | there (here refl) =
    inj₂ (x , ∈-map proj₁ (Map.lookup-some→∈ sis eq) , here refl , inj₂ refl)
split-ctx-∈⁻ {x = x} sis ρ₁ ρ₂ (Γ₁ ⸴[ o ] Γ₂) x∈
  using x∈Γ₁++Γ₂ ← subst (x ∈_) (ListP.map-++ proj₁ (binds (split-ctx sis ρ₁ ρ₂ Γ₁))
                                                    (binds (split-ctx sis ρ₁ ρ₂ Γ₂))) x∈
  using eq ← ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)
  with AnyP.++⁻ (dom (split-ctx sis ρ₁ ρ₂ Γ₁)) x∈Γ₁++Γ₂
… | inj₁ x∈Γ₁ =
  case split-ctx-∈⁻ sis ρ₁ ρ₂ Γ₁ x∈Γ₁ of λ where
    (inj₁ x∈Γ₁) →
      inj₁ $ subst (x ∈_) (sym eq) (AnyP.++⁺ˡ x∈Γ₁)
    (inj₂ (x' , x'∈sis , x'∈Γ₁ , eq')) →
      inj₂ (x' , x'∈sis , subst (x' ∈_) (sym eq) (AnyP.++⁺ˡ x'∈Γ₁) , eq')
… | inj₂ x∈Γ₂ =
  case split-ctx-∈⁻ sis ρ₁ ρ₂ Γ₂ x∈Γ₂ of λ where
    (inj₁ x∈Γ₂) →
      inj₁ $ subst (x ∈_) (sym eq) (AnyP.++⁺ʳ _ x∈Γ₂)
    (inj₂ (x' , x'∈sis , x'∈Γ₂ , eq')) →
      inj₂ (x' , x'∈sis , subst (x' ∈_) (sym eq) (AnyP.++⁺ʳ _ x'∈Γ₂) , eq')

-- TODO
-- this is tricky for because ρᵢ and sis could be malformed.
-- split-ctx-dom' : ∀ C Γ' Γ ρ₁ ρ₂ sis extra (e₁ : Expr §) (e₂s : List (Expr §)) →
--   (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % map proj₁ sis ⊢ʳ ρ₁ →
--   (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % map proj₁ sis ⊢ʳ ρ₂ →
--   Disjoint (codʳ (map proj₁ sis) ρ₁)
--            (codʳ (map proj₁ sis) ρ₂) →
--   dom ((C ⋯ʳᶜ ρ₂) [ Γ' ⋯ʳ ρ₁ ]) ⊆ dom (split-ctx sis ρ₁ ρ₂ Γ) →
--   dom (C [ Γ' ]) ⊆ dom Γ
-- split-ctx-dom' C Γ' Γ ρ₁ ρ₂ sis extra e₁ e₂s ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub =
--   let open ⊆-Reasoning in
--   begin
--     dom (C [ Γ' ])
--   ≈⟨ dom-C C Γ' ⟩
--     dom (C [ · ]) ++ dom Γ'
--   ⊆⟨ ⊆-++⁺ˡ sub₁ sub₂ ⟩
--     dom Γ
--   ∎
--   where
--     sis₁ = map proj₁ sis

--     yss = dom Γ ++ extra ++ vars e₁ ++ varss e₂s

--     sub' = ⊆-++⁻ˡ (dom ((C ⋯ʳᶜ ρ₂) [ · ])) (dom (Γ' ⋯ʳ ρ₁)) $
--            ≈ˡ→⊆ $ ≈ˡ-sym $ dom-C (C ⋯ʳᶜ ρ₂) (Γ' ⋯ʳ ρ₁)

--     sub₁' : map ρ₂ (dom (C [ · ])) ⊆ dom Γ ++ map ρ₁ (dom Γ) ++ map ρ₂ (dom Γ)
--     sub₁' =
--       let open ⊆-Reasoning in
--       begin
--         map ρ₂ (dom (C [ · ]))
--       ≡⟨ sym (⋯ʳ-dom (C [ · ]) ρ₂) ⟩
--         dom ((C [ · ]) ⋯ʳ ρ₂)
--       ≡⟨ cong dom (⋯ʳ-dist-[] C · ρ₂) ⟩
--         dom ((C ⋯ʳᶜ ρ₂) [ · ])
--       ⊆⟨ proj₁ sub' ⟩
--         dom ((C ⋯ʳᶜ ρ₂) [ Γ' ⋯ʳ ρ₁ ])
--       ⊆⟨ sub ⟩
--         dom (split-ctx sis ρ₁ ρ₂ Γ)
--       ⊆⟨ {!!} ⟩
--         dom Γ ++ map ρ₁ (dom Γ) ++ map ρ₂ (dom Γ)
--       ∎

--     sub₁ : dom (C [ · ]) ⊆ dom Γ
--     sub₁ = {!!}

--     sub₂' : map ρ₁ (dom Γ') ⊆ dom Γ ++ map ρ₁ (dom Γ) ++ map ρ₂ (dom Γ)
--     sub₂' =
--       let open ⊆-Reasoning in
--       begin
--         map ρ₁ (dom Γ')
--       ≡⟨ sym (⋯ʳ-dom Γ' ρ₁) ⟩
--         dom (Γ' ⋯ʳ ρ₁)
--       ⊆⟨ proj₂ sub' ⟩
--         dom ((C ⋯ʳᶜ ρ₂) [ Γ' ⋯ʳ ρ₁ ])
--       ⊆⟨ sub ⟩
--         dom (split-ctx sis ρ₁ ρ₂ Γ)
--       ⊆⟨ {!!} ⟩
--         dom Γ ++ map ρ₁ (dom Γ) ++ map ρ₂ (dom Γ)
--       ∎

--     sub₂'' : map ρ₁ (dom Γ') ⊆ dom (split-ctx sis ρ₁ ρ₂ Γ)
--     sub₂'' =
--       let open ⊆-Reasoning in
--       begin
--         map ρ₁ (dom Γ')
--       ≡⟨ sym (⋯ʳ-dom Γ' ρ₁) ⟩
--         dom (Γ' ⋯ʳ ρ₁)
--       ⊆⟨ proj₂ sub' ⟩
--         dom ((C ⋯ʳᶜ ρ₂) [ Γ' ⋯ʳ ρ₁ ])
--       ⊆⟨ sub ⟩
--         dom (split-ctx sis ρ₁ ρ₂ Γ)
--       ∎

--     sub₂ : dom Γ' ⊆ dom Γ
--     sub₂ {x} x∈Γ' =
--       let ρ₁x∈ρ₁Γ' = ∈-map ρ₁ x∈Γ' in
--       case x ∈? sis₁ of λ where
--         (yes x∈sis₁) →
--           case AnyP.++⁻ (dom Γ) (sub₂' ρ₁x∈ρ₁Γ') of λ where
--             (inj₁ ρ₁x∈Γ) →
--               ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ₁ (ρ₁ x) (∈-map ρ₁ x∈sis₁) (AnyP.++⁺ˡ ρ₁x∈Γ) )
--             (inj₂ ρ₁x∈ρ₁Γ++ρ₂Γ) →
--               case AnyP.++⁻ (map ρ₁ (dom Γ)) ρ₁x∈ρ₁Γ++ρ₂Γ of λ where
--                 (inj₁ ρ₁x∈ρ₁Γ) →
--                   Injecitveʳ-∈ ⊆-++₁' (⊢ʳ-inj-ys-ρ ⊢ρ₁) (⊢ʳ-xs⊆ys ⊢ρ₁ x∈sis₁) ρ₁x∈ρ₁Γ
--                 (inj₂ ρ₁x∈ρ₂Γ) →
--                   let ρ₁x∈ρ₂ys : ρ₁ x ∈ map ρ₂ yss
--                       ρ₁x∈ρ₂ys = {!!} in
--                   let ρ₁x∈ys++ρ₂sis₁ = ⊢ʳ-ρys⊆ys++ρxs ⊢ρ₂ ρ₁x∈ρ₂ys in
--                   case AnyP.++⁻ yss ρ₁x∈ys++ρ₂sis₁ of λ where
--                     (inj₁ ρ₁x∈ys) →
--                       ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ₁ (ρ₁ x) (∈-map ρ₁ x∈sis₁) ρ₁x∈ys)
--                     (inj₂ ρ₁x∈ρ₂sis₁) →
--                       ⊥-elim (d-ρ₁-ρ₂ (ρ₁ x) (∈-map ρ₁ x∈sis₁) ρ₁x∈ρ₂sis₁)
--         (no ¬x∈sis₁) →
--           let ρ₁x≡x = ⊢ʳ-∉xs-id ⊢ρ₁ ¬x∈sis₁ in
--           case AnyP.++⁻ (dom Γ) (sub₂' ρ₁x∈ρ₁Γ') of λ where
--             (inj₁ ρ₁x∈Γ) →
--               subst (_∈ dom Γ) ρ₁x≡x ρ₁x∈Γ
--             (inj₂ ρ₁x∈ρ₁Γ++ρ₂Γ) →
--               case AnyP.++⁻ (map ρ₁ (dom Γ)) ρ₁x∈ρ₁Γ++ρ₂Γ of λ where
--                 (inj₁ ρ₁x∈ρ₁Γ) →
--                   let ρ₁x∈ρ₁ys : ρ₁ x ∈ map ρ₁ yss
--                       ρ₁x∈ρ₁ys = {!!} in
--                   let ρ₁x∈ys++ρ₁sis₁ = ⊢ʳ-ρys⊆ys++ρxs ⊢ρ₁ ρ₁x∈ρ₁ys in
--                   case AnyP.++⁻ yss ρ₁x∈ys++ρ₁sis₁ of λ where
--                     (inj₁ ρ₁x∈ys) →
--                       ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ₁ (ρ₁ x) {!!} ρ₁x∈ys)
--                     (inj₂ ρ₁x∈ρ₁sis₁) →
--                       {!!}
--                 (inj₂ ρ₁x∈ρ₂Γ) →
--                   {!!}

--     sub₂x : dom Γ' ⊆ dom Γ
--     sub₂x {x} x∈Γ' =
--       let
--         ρ₁x∈ρ₁Γ' = ∈-map ρ₁ x∈Γ'
--         ρ₁x∈splitΓ = sub₂'' ρ₁x∈ρ₁Γ'
--       in
--       case split-ctx-∈⁻ sis ρ₁ ρ₂ Γ ρ₁x∈splitΓ of λ where
--         (inj₁ ρ₁x∈Γ) →
--           case x ∈? sis₁ of λ where
--             (yes x∈sis₁) →
--               ⊥-elim (⊢ʳ-ρxs⊎ys ⊢ρ₁ (ρ₁ x) (∈-map ρ₁ x∈sis₁) (AnyP.++⁺ˡ ρ₁x∈Γ) )
--             (no ¬x∈sis₁) →
--               let ρ₁x≡x = ⊢ʳ-∉xs-id ⊢ρ₁ ¬x∈sis₁ in
--               subst (_∈ dom Γ) ρ₁x≡x ρ₁x∈Γ
--         (inj₂ (x' , x'∈sis₁ , x'∈Γ , inj₁ ρ₁x'≡ρ₁x)) →
--           case x ∈? sis₁ of λ where
--             (yes x∈sis₁) →
--               let
--                 x∈ys : x ∈ yss
--                 x∈ys = ⊢ʳ-xs⊆ys ⊢ρ₁ x∈sis₁
--                 x'≡x : x' ≡ x
--                 x'≡x = ⊢ʳ-inj-ys-ρ ⊢ρ₁ x' x (AnyP.++⁺ˡ x'∈Γ) x∈ys ρ₁x'≡ρ₁x
--               in
--               subst (_∈ dom Γ) x'≡x x'∈Γ
--             (no ¬x∈sis₁) →
--               let
--                 ρ₁x≡x = ⊢ʳ-∉xs-id ⊢ρ₁ ¬x∈sis₁

--                 ρ₁x'≡x = trans ρ₁x'≡ρ₁x ρ₁x≡x

--                 ρ₁x'∈ρ₁sis₁ = ∈-map ρ₁ x'∈sis₁

--                 x∈ρ₁sis₁ : x ∈ map ρ₁ sis₁
--                 x∈ρ₁sis₁ = subst (_∈ _) ρ₁x'≡x ρ₁x'∈ρ₁sis₁

--                 xx : x' ∉ map ρ₁ yss
--                 xx = ⊢ʳ-xs⊎ρys ⊢ρ₁ x' x'∈sis₁

--                 -- yy : x ∉ yss
--                 -- yy = ⊢ʳ-ρxs⊎ys ⊢ρ₁ x x∈ρ₁sis₁
--                 -- yy : ρ₁ x' ∉ map ρ₁ (map ρ₁ yss)
--                 -- yy = {!∈-map ρ₁ !}
--               in
--               {!!}
--         (inj₂ (x' , x'∈sis₁ , x'∈Γ , inj₂ ρ₂x'≡ρ₁x)) →
--           {!!}

-- split-ctx-dom'₁ : ∀ C Γ' Γ ρ₁ ρ₂ sis extra (e₁ : Expr §) (e₂s : List (Expr §)) →
--   (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % map proj₁ sis ⊢ʳ ρ₁ →
--   (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % map proj₁ sis ⊢ʳ ρ₂ →
--   Disjoint (codʳ (map proj₁ sis) ρ₁)
--            (codʳ (map proj₁ sis) ρ₂) →
--   dom ((C ⋯ʳᶜ ρ₂) [ Γ' ⋯ʳ ρ₁ ]) ⊆ dom (split-ctx sis ρ₁ ρ₂ Γ) →
--   dom (C [ · ]) ⊆ dom Γ
-- split-ctx-dom'₁ C Γ' Γ ρ₁ ρ₂ sis extra e₁ e₂s ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub =
--   let open ⊆-Reasoning in
--   begin
--     dom (C [ · ])
--   ⊆⟨ {!!} ⟩
--     dom (C [ Γ' ])
--   ⊆⟨ split-ctx-dom' C Γ' Γ ρ₁ ρ₂ sis extra e₁ e₂s ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub ⟩
--     dom Γ
--   ∎

-- -- TODO: this is deadcode
-- fvs⊆Γ : ∀ {i} →
--   Γ ⊢ e ∶[ i ] t ⍮ u ⍮ ϕ →
--   fvs e ⊆ dom Γ
-- fvs⊆Γ {Γ = Γ} (⊢`-nochan {x = x} Γ≲x∶t t≢chan) (here refl) =
--   ∈binds→∈dom Γ $
--   ≲-pres-∈' Γ≲x∶t (here refl)
-- fvs⊆Γ {Γ = Γ} (⊢`-chan Γ≲x∶t _) (here refl) =
--   ∈binds→∈dom Γ $
--   ≲-pres-∈' Γ≲x∶t (here refl)
-- fvs⊆Γ {Γ = Γ} (⊢& Γ≲x∶t _ _) (here refl) =
--   ∈binds→∈dom Γ $
--   ≲-pres-∈' Γ≲x∶t (here refl)
-- fvs⊆Γ {Γ = Γ} (⊢λ {x = y} {m = m} {t₁ = t₁} {e = e} x∉Γ ⊢e _ _ _) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e -ˡ y
--   ⊆⟨ ⊆-ˡ-both (fvs⊆Γ ⊢e) ⟩
--     dom (ext m Γ (y ∶ t₁)) -ˡ y
--   ⊆⟨ ⊆-ˡ-both (≈ˡ→⊆ (dom-ext m Γ (y ∶ t₁))) ⟩
--     (dom Γ ++ (y ∷ [])) -ˡ y
--   ≡⟨ -ˡ-dist-++ (dom Γ) _ _ ⟩
--     (dom Γ -ˡ y) ++ ((y ∷ []) -ˡ y)
--   ≡⟨ cong ((dom Γ -ˡ y) ++_) -ˡ-self ⟩
--     (dom Γ -ˡ y) ++ []
--   ≡⟨ ListP.++-identityʳ (dom Γ -ˡ y) ⟩
--     dom Γ -ˡ y
--   ≡⟨ ∉-ˡ x∉Γ ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢·≻ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁ refl ⊢e₂ _) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e₁ ++ fvs e₂
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (fvs⊆Γ ⊢e₂) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom ((Γ ↓ fvs e₂) %ᶜ u₁)
--   ≡⟨ cong (_ ++_) (%ᶜ-dom (Γ ↓ fvs e₂) u₁) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (Γ ↓ fvs e₂)
--   ⊆⟨ ⊆-++ (↓-⊆dom Γ (fvs e₁)) (↓-⊆dom Γ (fvs e₂)) ⟩
--     dom Γ ++ dom Γ
--   ⊆⟨ ≈ˡ→⊆ (≈ˡ-dup-++ (dom Γ)) ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢·≺ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁ refl ⊢e₂ _) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e₂ ++ fvs e₁
--   ≈⟨ ≈ˡ-comm (fvs e₂) (fvs e₁) ⟩
--     fvs e₁ ++ fvs e₂
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (fvs⊆Γ ⊢e₂) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom ((Γ ↓ fvs e₂) %ᶜ u₁)
--   ≡⟨ cong (_ ++_) (%ᶜ-dom (Γ ↓ fvs e₂) u₁) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (Γ ↓ fvs e₂)
--   ⊆⟨ ⊆-++ (↓-⊆dom Γ (fvs e₁)) (↓-⊆dom Γ (fvs e₂)) ⟩
--     dom Γ ++ dom Γ
--   ⊆⟨ ≈ˡ→⊆ (≈ˡ-dup-++ (dom Γ)) ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢·𝟙 {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁ refl ⊢e₂ _) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e₁ ++ fvs e₂
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (fvs⊆Γ ⊢e₂) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom ((Γ ↓ fvs e₂) %ᶜ u₁)
--   ≡⟨ cong (_ ++_) (%ᶜ-dom (Γ ↓ fvs e₂) u₁) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (Γ ↓ fvs e₂)
--   ⊆⟨ ⊆-++ (↓-⊆dom Γ (fvs e₁)) (↓-⊆dom Γ (fvs e₂)) ⟩
--     dom Γ ++ dom Γ
--   ⊆⟨ ≈ˡ→⊆ (≈ˡ-dup-++ (dom Γ)) ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢·∞ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁ refl ⊢e₂ _) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e₁ ++ fvs e₂
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (fvs⊆Γ ⊢e₂) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom ((Γ ↓ fvs e₂) %ᶜ u₁)
--   ≡⟨ cong (_ ++_) (%ᶜ-dom (Γ ↓ fvs e₂) u₁) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (Γ ↓ fvs e₂)
--   ⊆⟨ ⊆-++ (↓-⊆dom Γ (fvs e₁)) (↓-⊆dom Γ (fvs e₂)) ⟩
--     dom Γ ++ dom Γ
--   ⊆⟨ ≈ˡ→⊆ (≈ˡ-dup-++ (dom Γ)) ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢, {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁ refl ⊢e₂ x₂ x₃) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e₁ ++ fvs e₂
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (fvs⊆Γ ⊢e₂) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom ((Γ ↓ fvs e₂) %ᶜ u₁)
--   ≡⟨ cong (_ ++_) (%ᶜ-dom (Γ ↓ fvs e₂) u₁) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (Γ ↓ fvs e₂)
--   ⊆⟨ ⊆-++ (↓-⊆dom Γ (fvs e₁)) (↓-⊆dom Γ (fvs e₂)) ⟩
--     dom Γ ++ dom Γ
--   ≈⟨ ≈ˡ-dup-++ (dom Γ) ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢let {x = x} {e₁ = e₁} {t₁ = t₁} {u₁ = u₁} {C = C} {e₂ = e₂}
--                     {u₂ = u₂}
--                     x∉Γ refl ⊢e₁ x₂ sp ⊢e₂ x₄ spa) =
--   let sis = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁ in
--   let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ x ∷ vars e₁ ++ vars e₂) in
--   let (⊢ρ₁ , ⊢ρ₂ , d) = ⊢ʳ-split-rens (map proj₁ sis) (dom Γ ++ x ∷ vars e₁ ++ vars e₂) {!!} {!!} in
--   let sub-sp : dom (((C ⋯ᵘᶜ (u₂ -ᵘ x)) ⋯ʳᶜ ρ₂) [ ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ⋯ʳ ρ₁ ]) ⊆
--                dom (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ (u₂ -ᵘ x))))
--       sub-sp = ≲→⊆dom spa in
--   let open ⊆-Reasoning in
--   let sub-suffix : dom (Γ ↓ fvs e₁) ++ dom (C [ · ]) ⊆ dom Γ
--       sub-suffix =
--         begin
--           dom (Γ ↓ fvs e₁) ++ dom (C [ · ])
--         ≡⟨ cong₂ _++_ (sym (⋯ᵘ-dom (Γ ↓ fvs e₁) u₁))
--                       (trans (sym (⋯ᵘ-dom (C [ · ]) (u₂ -ᵘ x)))
--                             (cong dom (>>=ᶜ-dist-[] C · (app-rep (u₂ -ᵘ x))  ))) ⟩
--           dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ++ dom ((C ⋯ᵘᶜ u₂ -ᵘ x) [ · ])
--         ≈⟨ ≈ˡ-comm (dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁)) _ ⟩
--           dom ((C ⋯ᵘᶜ u₂ -ᵘ x) [ · ]) ++ dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁)
--         ≈⟨ ≈ˡ-sym (dom-C (C ⋯ᵘᶜ u₂ -ᵘ x) ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ) ⟩
--           dom ((C ⋯ᵘᶜ u₂ -ᵘ x) [ Γ ↓ fvs e₁ ⋯ᵘ u₁ ])
--         ⊆⟨ split-ctx-dom' (C ⋯ᵘᶜ (u₂ -ᵘ x)) ((Γ ↓ fvs e₁) ⋯ᵘ u₁) (Γ ⋯ᵘ (u₁ ·ᵘ (u₂ -ᵘ x)))
--                           ρ₁ ρ₂ sis {!⊢ρ₁!} {!⊢ρ₂!} {!d!} sub-sp ⟩
--           dom (Γ ⋯ᵘ u₁ ·ᵘ (u₂ -ᵘ x))
--         ≡⟨ ⋯ᵘ-dom Γ _ ⟩
--           dom Γ
--         ∎
--   in
--   let x∉Γ₁ , x∉C = ∉-++⁻ (dom (Γ ↓ fvs e₁)) _ (⊆-∉ sub-suffix x∉Γ) in
--   begin
--     fvs e₁ ++ (fvs e₂ -ˡ x)
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (⊆-ˡ-both (fvs⊆Γ ⊢e₂)) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ x ∶ t₁ ]) -ˡ x)
--   ⊆⟨ ⊆-++ ⊆-refl (⊆-ˡ-both (≈ˡ→⊆ (dom-C C (x ∶ t₁)))) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) ++ dom (x ∶ t₁)) -ˡ x)
--   ≡⟨ cong₂ _++_ refl (-ˡ-dist-++ (dom (C [ · ])) (dom (x ∶ t₁)) x) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) -ˡ x) ++ (dom (x ∶ t₁) -ˡ x))
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (cong₂ _++_ refl -ˡ-self) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) -ˡ x) ++ [])
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (ListP.++-identityʳ _) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ · ]) -ˡ x)
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (∉-ˡ x∉C) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (C [ · ])
--   ⊆⟨ sub-suffix ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢let× {x = x} {y = y} {e₁ = e₁} {t₁ = t₁} {p = p} {t₂ = t₂} {u₁ = u₁}
--                      {C = C} {e₂ = e₂} {u₂ = u₂} x∉Γ y∉Γ x≢y refl ⊢e₁ x₃ x₄ ⊢e₂ x₅ x₆ spa) =
--   let sis = (fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁ in
--   let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ x ∷ y ∷ vars e₁ ++ vars e₂) in
--   let sub-sp : dom (((C ⋯ᵘᶜ (u₂ -ᵘ x -ᵘ y)) ⋯ʳᶜ ρ₂) [ ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ⋯ʳ ρ₁ ]) ⊆
--            dom (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y))))
--       sub-sp = ≲→⊆dom spa in
--   let open ⊆-Reasoning in
--   let sub-suffix : dom (Γ ↓ fvs e₁) ++ dom (C [ · ]) ⊆ dom Γ
--       sub-suffix =
--         begin
--           dom (Γ ↓ fvs e₁) ++ dom (C [ · ])
--         ≡⟨ cong₂ _++_ (sym (⋯ᵘ-dom (Γ ↓ fvs e₁) u₁))
--                       (trans (sym (⋯ᵘ-dom (C [ · ]) (u₂ -ᵘ x -ᵘ y)))
--                             (cong dom (>>=ᶜ-dist-[] C · (app-rep (u₂ -ᵘ x -ᵘ y))  ))) ⟩
--           dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ++ dom ((C ⋯ᵘᶜ u₂ -ᵘ x -ᵘ y) [ · ])
--         ≈⟨ ≈ˡ-comm (dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁)) _ ⟩
--           dom ((C ⋯ᵘᶜ u₂ -ᵘ x -ᵘ y) [ · ]) ++ dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁)
--         ≈⟨ ≈ˡ-sym (dom-C (C ⋯ᵘᶜ u₂ -ᵘ x -ᵘ y) ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ) ⟩
--           dom ((C ⋯ᵘᶜ u₂ -ᵘ x -ᵘ y) [ Γ ↓ fvs e₁ ⋯ᵘ u₁ ])
--         ⊆⟨ split-ctx-dom' (C ⋯ᵘᶜ (u₂ -ᵘ x -ᵘ y)) ((Γ ↓ fvs e₁) ⋯ᵘ u₁) (Γ ⋯ᵘ (u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y)))
--                           ρ₁ ρ₂ sis {!!} {!!} {!!} sub-sp ⟩
--           dom (Γ ⋯ᵘ u₁ ·ᵘ (u₂ -ᵘ x -ᵘ y))
--         ≡⟨ ⋯ᵘ-dom Γ _ ⟩
--           dom Γ
--         ∎ in
--   let x∉Γ₁ , x∉C = ∉-++⁻ (dom (Γ ↓ fvs e₁)) _ (⊆-∉ sub-suffix x∉Γ) in
--   let y∉Γ₁ , y∉C = ∉-++⁻ (dom (Γ ↓ fvs e₁)) _ (⊆-∉ sub-suffix y∉Γ) in
--   begin
--     fvs e₁ ++ (fvs e₂ -ˡ x -ˡ y)
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (⊆-ˡ-both (⊆-ˡ-both (fvs⊆Γ ⊢e₂))) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ x ∶ t₁ ⸴[ pmult→ord p ] y ∶ t₂ ]) -ˡ x -ˡ y)
--   ⊆⟨ ⊆-++ ⊆-refl (⊆-ˡ-both (⊆-ˡ-both (≈ˡ→⊆ (dom-C C (x ∶ t₁ ⸴[ pmult→ord p ] y ∶ t₂))))) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) ++ (x ∷ y ∷ [])) -ˡ x -ˡ y)
--   ≡⟨ cong (λ ■ → dom (Γ ↓ fvs e₁) ++ (■ -ˡ y)) (-ˡ-dist-++ (dom (C [ · ])) _ x) ⟩
--     dom (Γ ↓ fvs e₁) ++ (((dom (C [ · ]) -ˡ x) ++ ((x ∷ y ∷ []) -ˡ x)) -ˡ y)
--   ≡⟨ cong₂ _++_ refl (-ˡ-dist-++ (dom (C [ · ]) -ˡ x) _ y) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) -ˡ x -ˡ y) ++ ((x ∷ y ∷ []) -ˡ x -ˡ y))
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (cong₂ _++_ refl (-ˡ-self-twice x≢y)) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) -ˡ x -ˡ y) ++ [])
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (ListP.++-identityʳ _) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ · ]) -ˡ x -ˡ y)
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (cong (_-ˡ y) (∉-ˡ x∉C)) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ · ]) -ˡ y)
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_) (∉-ˡ y∉C) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (C [ · ])
--   ⊆⟨ sub-suffix ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢inj ⊢e) = fvs⊆Γ ⊢e
-- fvs⊆Γ {Γ = Γ} (⊢case {x₁ = x} {x₂ = y} {e₁ = e₁} {t₁ = t₁} {t₂ = t₂} {u₁ = u₁}
--                      {C = C} {e₂₁ = e₂₁} {e₂₂ = e₂₂} {u₂₁ = u₂₁}
--                      x∉Γ y∉Γ x≢y refl ⊢e₁ x₃ x₄ ⊢e₂₁ ⊢e₂₂ x₅ x₆ x₇ spa) =
--   let sis = (fvs e₁ ∩ˡ (fvs e₂₁ ++ fvs e₂₂)) ↓ᵘ u₁ in
--   let ρ₁ , ρ₂ = split-rens (map proj₁ sis)
--                            (dom Γ ++ x ∷ y ∷ vars e₁ ++ vars e₂₁ ++ vars e₂₂) in
--   let sub-sp : dom (((C ⋯ᵘᶜ (u₂₁ -ᵘ x)) ⋯ʳᶜ ρ₂) [ ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ⋯ʳ ρ₁ ]) ⊆
--            dom (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ (u₂₁ -ᵘ x))))
--       sub-sp = ≲→⊆dom spa in
--   let open ⊆-Reasoning in
--   let sub-suffix : dom (Γ ↓ fvs e₁) ++ dom (C [ · ]) ⊆ dom Γ
--       sub-suffix =
--         begin
--           dom (Γ ↓ fvs e₁) ++ dom (C [ · ])
--         ≡⟨ cong₂ _++_ (sym (⋯ᵘ-dom (Γ ↓ fvs e₁) u₁))
--                       (trans (sym (⋯ᵘ-dom (C [ · ]) (u₂₁ -ᵘ x)))
--                             (cong dom (>>=ᶜ-dist-[] C · (app-rep (u₂₁ -ᵘ x))  ))) ⟩
--           dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ++ dom ((C ⋯ᵘᶜ u₂₁ -ᵘ x) [ · ])
--         ≈⟨ ≈ˡ-comm (dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁)) _ ⟩
--           dom ((C ⋯ᵘᶜ u₂₁ -ᵘ x) [ · ]) ++ dom ((Γ ↓ fvs e₁) ⋯ᵘ u₁)
--         ≈⟨ ≈ˡ-sym (dom-C (C ⋯ᵘᶜ u₂₁ -ᵘ x) ((Γ ↓ fvs e₁) ⋯ᵘ u₁) ) ⟩
--           dom ((C ⋯ᵘᶜ u₂₁ -ᵘ x) [ Γ ↓ fvs e₁ ⋯ᵘ u₁ ])
--         ⊆⟨ split-ctx-dom' (C ⋯ᵘᶜ (u₂₁ -ᵘ x)) ((Γ ↓ fvs e₁) ⋯ᵘ u₁) (Γ ⋯ᵘ (u₁ ·ᵘ (u₂₁ -ᵘ x)))
--                           ρ₁ ρ₂ sis {!!} {!!} {!!} sub-sp ⟩
--           dom (Γ ⋯ᵘ u₁ ·ᵘ (u₂₁ -ᵘ x))
--         ≡⟨ ⋯ᵘ-dom Γ _ ⟩
--           dom Γ
--         ∎
--   in
--   let x∉Γ₁ , x∉C = ∉-++⁻ (dom (Γ ↓ fvs e₁)) _ (⊆-∉ sub-suffix x∉Γ) in
--   let y∉Γ₁ , y∉C = ∉-++⁻ (dom (Γ ↓ fvs e₁)) _ (⊆-∉ sub-suffix y∉Γ) in
--   begin
--     fvs e₁ ++ (fvs e₂₁ -ˡ x) ++ (fvs e₂₂ -ˡ y)
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (⊆-++ (⊆-ˡ-both (fvs⊆Γ ⊢e₂₁)) (⊆-ˡ-both (fvs⊆Γ ⊢e₂₂))) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ x ∶ t₁ ]) -ˡ x) ++ (dom (C [ y ∶ t₂ ]) -ˡ y)
--   ⊆⟨ ⊆-++ (⊆-refl {xs = dom (Γ ↓ fvs e₁)})
--           (⊆-++ ((⊆-ˡ-both (≈ˡ→⊆ (dom-C C (x ∶ t₁)))))
--                 ((⊆-ˡ-both (≈ˡ→⊆ (dom-C C (y ∶ t₂)))))) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) ++ L.[ x ]) -ˡ x)
--                      ++ ((dom (C [ · ]) ++ L.[ y ]) -ˡ y)
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_)
--           (cong₂ _++_ (-ˡ-dist-++ (dom (C [ · ])) _ x)
--                       (-ˡ-dist-++ (dom (C [ · ])) _ y) ) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) -ˡ x) ++ (L.[ x ] -ˡ x))
--                      ++ ((dom (C [ · ]) -ˡ y) ++ (L.[ y ] -ˡ y))
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_)
--           (cong₂ _++_ (cong ((dom (C [ · ]) -ˡ x) ++_) -ˡ-self)
--                       (cong ((dom (C [ · ]) -ˡ y) ++_) -ˡ-self)) ⟩
--     dom (Γ ↓ fvs e₁) ++ ((dom (C [ · ]) -ˡ x) ++ [])
--                      ++ ((dom (C [ · ]) -ˡ y) ++ [])
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_)
--           (cong₂ _++_ (ListP.++-identityʳ (dom (C [ · ]) -ˡ x))
--                       (ListP.++-identityʳ (dom (C [ · ]) -ˡ y))) ⟩
--     dom (Γ ↓ fvs e₁) ++ (dom (C [ · ]) -ˡ x) ++ (dom (C [ · ]) -ˡ y)
--   ≡⟨ cong (dom (Γ ↓ fvs e₁) ++_)
--           (cong₂ _++_ (∉-ˡ x∉C) (∉-ˡ y∉C)) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (C [ · ]) ++ dom (C [ · ])
--   ≈⟨ ≈ˡ-++ ≈ˡ-refl (≈ˡ-dup-++ (dom (C [ · ]))) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (C [ · ])
--   ⊆⟨ sub-suffix ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} ⊢unit = []⊆ _
-- fvs⊆Γ {Γ = Γ} (⊢spawn ⊢e) = fvs⊆Γ ⊢e
-- fvs⊆Γ {Γ = Γ} ⊢new = []⊆ _
-- fvs⊆Γ {Γ = Γ} (⊢send {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} refl ⊢e₁ refl ⊢e₂ x₂ x₃) =
--   let open ⊆-Reasoning in
--   begin
--     fvs e₁ ++ fvs e₂
--   ⊆⟨ ⊆-++ (fvs⊆Γ ⊢e₁) (fvs⊆Γ ⊢e₂) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom ((Γ ↓ fvs e₂) %ᶜ u₁)
--   ≡⟨ cong (_ ++_) (%ᶜ-dom (Γ ↓ fvs e₂) u₁) ⟩
--     dom (Γ ↓ fvs e₁) ++ dom (Γ ↓ fvs e₂)
--   ⊆⟨ ⊆-++ (↓-⊆dom Γ (fvs e₁)) (↓-⊆dom Γ (fvs e₂)) ⟩
--     dom Γ ++ dom Γ
--   ⊆⟨ ≈ˡ→⊆ (≈ˡ-dup-++ (dom Γ)) ⟩
--     dom Γ
--   ∎
-- fvs⊆Γ {Γ = Γ} (⊢recv ⊢e) = fvs⊆Γ ⊢e
-- fvs⊆Γ {Γ = Γ} (⊢drop ⊢e) = fvs⊆Γ ⊢e
-- fvs⊆Γ {Γ = Γ} (⊢close ⊢e) = fvs⊆Γ ⊢e
-- fvs⊆Γ {Γ = Γ} (⊢∶ ⊢e) = fvs⊆Γ ⊢e
-- fvs⊆Γ {Γ = Γ} (⊢chk-inf ⊢e) = fvs⊆Γ ⊢e
