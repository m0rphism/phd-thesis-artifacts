module BGV.Context.Pattern where

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
open import Data.List.Membership.Propositional using (_∈_; _∉_)
import Data.List.Relation.Unary.Any.Properties as AnyP

open import BGV.Util.Decidable
open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Types
open import BGV.Util.List
open import BGV.Id
open import BGV.Util.Graph as G using (Graph)
open import BGV.Context.Semantic
open import BGV.Context.Syntactic

-- Specification

infix 5 _⸴[_]₁_ _⸴[_]₂_ _⸴₁_ _⸴₂_ _∥₁_ _∥₂_

data CtxPat : Set where
  [] : CtxPat
  _⸴[_]₁_ : CtxPat → IsOrd → Ctx → CtxPat
  _⸴[_]₂_ : Ctx → IsOrd → CtxPat → CtxPat

pattern _∥₁_ Γ₁ Γ₂ = _⸴[_]₁_ Γ₁ unordered Γ₂
pattern _∥₂_ Γ₁ Γ₂ = _⸴[_]₂_ Γ₁ unordered Γ₂
pattern _⸴₁_ Γ₁ Γ₂ = _⸴[_]₁_ Γ₁ ordered Γ₂
pattern _⸴₂_ Γ₁ Γ₂ = _⸴[_]₂_ Γ₁ ordered Γ₂

infix 6 _[_]
_[_] : CtxPat → Ctx → Ctx
[]            [ Γ' ] = Γ'
(C ⸴[ o ]₁ Γ) [ Γ' ] = C [ Γ' ] ⸴[ o ] Γ
(Γ ⸴[ o ]₂ C) [ Γ' ] = Γ ⸴[ o ] C [ Γ' ]

variable
  C C₁ C₂ C₃ C' C₁' C₂' C₃' : CtxPat
  𝒢 𝒢₁ 𝒢₂ 𝒢₃ 𝒢' 𝒢₁' 𝒢₂' 𝒢₃' : CtxPat

-- Properties

_>>=ᶜᶜ_ : CtxPat → (Id → Type → Ctx) → CtxPat
[] >>=ᶜᶜ f = []
(C ⸴[ o ]₁ Γ₂) >>=ᶜᶜ f = (C >>=ᶜᶜ f) ⸴[ o ]₁ (Γ₂ >>=ᶜ f)
(Γ₁ ⸴[ o ]₂ C) >>=ᶜᶜ f = (Γ₁ >>=ᶜ f) ⸴[ o ]₂ (C >>=ᶜᶜ f)

>>=ᶜ-dist-[] : ∀ C Γ f →
  (C [ Γ ]) >>=ᶜ f ≡ (C >>=ᶜᶜ f) [ Γ >>=ᶜ f ]
>>=ᶜ-dist-[] []            Γ' f = refl
>>=ᶜ-dist-[] (C ⸴[ o ]₁ Γ) Γ' f = cong (_⸴[ o ] _) (>>=ᶜ-dist-[] C Γ' f)
>>=ᶜ-dist-[] (Γ ⸴[ o ]₂ C) Γ' f = cong (_ ⸴[ o ]_) (>>=ᶜ-dist-[] C Γ' f)

∈binds→C : ∀ Γ →
  (x , t) ∈ binds Γ →
  ∃[ C ] Γ ≡ C [ x ∶ t ]
∈binds→C (x ∶ t) (here refl) = [] , refl
∈binds→C (Γ₁ ⸴[ o ] Γ₂) xt∈Γ 
  with AnyP.++⁻ (binds Γ₁) xt∈Γ
… | inj₁ xt∈Γ₁ = let C , eq = ∈binds→C Γ₁ xt∈Γ₁ in C ⸴[ o ]₁ Γ₂ , cong (_⸴[ o ] Γ₂) eq
… | inj₂ xt∈Γ₂ = let C , eq = ∈binds→C Γ₂ xt∈Γ₂ in Γ₁ ⸴[ o ]₂ C , cong (Γ₁ ⸴[ o ]_) eq

-- TODO: if needed derive from ∈binds→C
∈dom→C : ∀ Γ →
  x ∈ dom Γ →
  ∃[ C ] ∃[ t ] Γ ≡ C [ x ∶ t ]
∈dom→C (x ∶ t) (here refl) = [] , t , refl
∈dom→C {x = x} (Γ₁ ⸴[ o ] Γ₂) x∈dom[Γ₁,Γ₂]
  with x∈domΓ₁++domΓ₂ ← subst (x ∈_) (ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)) x∈dom[Γ₁,Γ₂]
  with AnyP.++⁻ (dom Γ₁) x∈domΓ₁++domΓ₂
… | inj₁ x∈domΓ₁ = let C , t , eq = ∈dom→C Γ₁ x∈domΓ₁ in
                   C ⸴[ o ]₁ Γ₂ , t , cong (_⸴[ o ] Γ₂) eq
… | inj₂ x∈domΓ₂ = let C , t , eq = ∈dom→C Γ₂ x∈domΓ₂ in
                   Γ₁ ⸴[ o ]₂ C , t , cong (Γ₁ ⸴[ o ]_) eq

binds-C : ∀ C Γ →
  binds (C [ Γ ]) ≈ⁱ binds (C [ · ]) ++ binds Γ
binds-C [] Γ = ≈ⁱ-refl
binds-C (C ⸴[ o ]₁ Γ') Γ =
  let open ≈ⁱ-Reasoning in
  begin
    binds (C [ Γ ]) ++ binds Γ'
  ≈⟨ ≈ⁱ-++ (binds-C C Γ) ≈ⁱ-refl ⟩
    (binds (C [ · ]) ++ binds Γ) ++ binds Γ'
  ≈⟨ ≈ⁱ-assoc (binds (C [ · ])) (binds Γ) (binds Γ') ⟩
    binds (C [ · ]) ++ (binds Γ ++ binds Γ')
  ≈⟨ ≈ⁱ-++ {xs₁ = binds (C [ · ])} ≈ⁱ-refl (≈ⁱ-comm (binds Γ) (binds Γ')) ⟩
    binds (C [ · ]) ++ (binds Γ' ++ binds Γ)
  ≈⟨ ≈ⁱ-sym (≈ⁱ-assoc (binds (C [ · ])) (binds Γ') (binds Γ)) ⟩
    (binds (C [ · ]) ++ binds Γ') ++ binds Γ
  ∎
binds-C (Γ' ⸴[ o ]₂ C) Γ =
  let open ≈ⁱ-Reasoning in
  begin
    binds Γ' ++ binds (C [ Γ ])
  ≈⟨ ≈ⁱ-++ ≈ⁱ-refl (binds-C C Γ) ⟩
    binds Γ' ++ (binds (C [ · ]) ++ binds Γ)
  ≈⟨ ≈ⁱ-sym (≈ⁱ-assoc (binds Γ') (binds (C [ · ])) (binds Γ)) ⟩
    (binds Γ' ++ binds (C [ · ])) ++ binds Γ
  ∎

dom-C : ∀ C Γ →
  dom (C [ Γ ]) ≈ⁱ dom (C [ · ]) ++ dom Γ
dom-C [] Γ = ≈ⁱ-refl
dom-C (C ⸴[ o ]₁ Γ') Γ =
  let open ≈ⁱ-Reasoning in
  begin
    dom ((C ⸴[ o ]₁ Γ') [ Γ ])
  ≡⟨ ListP.map-++ proj₁ (binds (C [ Γ ])) (binds Γ') ⟩
    dom (C [ Γ ]) ++ dom Γ'
  ≈⟨ ≈ⁱ-++ (dom-C C Γ) ≈ⁱ-refl ⟩
    (dom (C [ · ]) ++ dom Γ) ++ dom Γ'
  ≈⟨ ≈ⁱ-assoc (dom (C [ · ])) (dom Γ) (dom Γ') ⟩
    dom (C [ · ]) ++ (dom Γ ++ dom Γ')
  ≈⟨ ≈ⁱ-++ {xs₁ = dom (C [ · ])} ≈ⁱ-refl (≈ⁱ-comm (dom Γ) (dom Γ')) ⟩
    dom (C [ · ]) ++ (dom Γ' ++ dom Γ)
  ≈⟨ ≈ⁱ-sym (≈ⁱ-assoc (dom (C [ · ])) (dom Γ') (dom Γ)) ⟩
    (dom (C [ · ]) ++ dom Γ') ++ dom Γ
  ≡⟨ cong (_++ dom Γ) (sym (ListP.map-++ proj₁ (binds (C [ · ])) (binds Γ'))) ⟩
    dom ((C ⸴[ o ]₁ Γ') [ · ]) ++ dom Γ
  ∎
dom-C (Γ' ⸴[ o ]₂ C) Γ =
  let open ≈ⁱ-Reasoning in
  begin
    dom ((Γ' ⸴[ o ]₂ C) [ Γ ])
  ≡⟨ ListP.map-++ proj₁ (binds Γ') (binds (C [ Γ ])) ⟩
    dom Γ' ++ dom (C [ Γ ])
  ≈⟨ ≈ⁱ-++ ≈ⁱ-refl (dom-C C Γ) ⟩
    dom Γ' ++ (dom (C [ · ]) ++ dom Γ)
  ≈⟨ ≈ⁱ-sym (≈ⁱ-assoc (dom Γ') (dom (C [ · ])) (dom Γ)) ⟩
    (dom Γ' ++ dom (C [ · ])) ++ dom Γ
  ≡⟨ cong (_++ dom Γ) (sym (ListP.map-++ proj₁ (binds Γ') (binds (C [ · ])))) ⟩
    dom ((Γ' ⸴[ o ]₂ C) [ · ]) ++ dom Γ
  ∎

-- dom-C : ∀ C Γ →
--   dom (C [ Γ ]) ≈ˡ dom (C [ · ]) ++ dom Γ
-- dom-C C Γ =
--   let open ≈ˡ-Reasoning in
--   begin
--     L.map proj₁ (binds (C [ Γ ]))
--   ≈⟨ ≈ˡ-map proj₁ (binds-C C Γ) ⟩
--     L.map proj₁ (binds (C [ · ]) ++ binds Γ)
--   ≡⟨ ListP.map-++ proj₁ (binds (C [ · ])) (binds Γ) ⟩
--     L.map proj₁ (binds (C [ · ])) ++ L.map proj₁ (binds Γ)
--   ∎

C[]-pres-∈binds : ∀ {x t} C Γ →
  (x , t) ∈ binds Γ →
  (x , t) ∈ binds (C [ Γ ])
C[]-pres-∈binds {x = x} {t = t} C Γ xt∈Γ =
  ≈ˡ→⊆ (≈ˡ-sym (≈ⁱ→≈ˡ (binds-C C Γ))) (AnyP.++⁺ʳ _ xt∈Γ)
  
C[]-pres-∈dom : ∀ {x} C Γ →
  x ∈ dom Γ →
  x ∈ dom (C [ Γ ])
C[]-pres-∈dom {x} C Γ x∈Γ =
  let (t , x∶t∈Γ) = ∈dom→∈binds Γ x∈Γ in
  let x∶t∈C[Γ] = C[]-pres-∈binds C Γ x∶t∈Γ in
  ∈binds→∈dom (C [ Γ ]) x∶t∈C[Γ]
