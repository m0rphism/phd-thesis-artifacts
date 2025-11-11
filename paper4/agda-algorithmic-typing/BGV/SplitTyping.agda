module BGV.SplitTyping where

import Data.List.Properties as ListP
import Data.List.Relation.Unary.Any.Properties as AnyP
import Data.Nat.Properties as NatP
import Data.Product.Properties as ProdP
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_; map; _++_)
open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)
open import Data.Nat as Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
import Data.Product.Properties as ProdP
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (_∘_; _$_; case_of_) renaming (_∋_ to _by_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; subst₂; module ≡-Reasoning)

open import BGV.Context
open import BGV.Expressions
open import BGV.Id
open import BGV.Ren
open import BGV.UsageMap
open import BGV.Types
open import BGV.Util.Decidable
open import BGV.Util.List
open import BGV.Util.Map as Map using (Map)
open import BGV.Algorithmic
open import BGV.Logical
open import BGV.Translation
open import BGV.Split
open import BGV.Effect
open import BGV.Multiplicities

-- Context Modeling ------------------------------------------------------------

-- This is required for the ⊢splitₙ lemma, where we need to do induction
-- over `sis`, but still need to use the ρ₁ and ρ₂ for the entire `sis`.

record _⊧ˢ_⍮_⍮_ (sis : List (Id × SessionB)) (ρ₁ ρ₂ : Ren) (Γ : Ctx) : Set where
  field
    ⊧ˢ-binds : ∀ {x s₁} →
      (x , s₁) ∈ sis →
      ∃[ b ] Σ[ s₂ ∈ Session b ] (x , Chan _ (s₁ ++ˢ s₂)) ∈ binds Γ
    ⊧ˢ-vars-unique :
      let xs = map proj₁ sis in
      Unique (xs ++ map ρ₁ xs ++ map ρ₂ xs)
    ⊧ˢ-newvars-disjoint :
      let xs = map proj₁ sis in
      Disjoint (map ρ₁ xs ++ map ρ₂ xs) (dom Γ)

  ⊧ˢ-oldvars-unique :
    Unique (map proj₁ sis)
  ⊧ˢ-oldvars-unique = Unique-⊆ ⊆ⁱ-++₁ ⊧ˢ-vars-unique

  ⊧ˢ-newvars-unique :
    let xs = map proj₁ sis in
    Unique (map ρ₁ xs ++ map ρ₂ xs)
  ⊧ˢ-newvars-unique = Unique-⊆ (⊆ⁱ-++₂ {xs = map proj₁ sis}) ⊧ˢ-vars-unique

  ⊧ˢ-newvars₁-unique :
    let xs = map proj₁ sis in
    Unique (map ρ₁ xs)
  ⊧ˢ-newvars₁-unique = Unique-⊆ ⊆ⁱ-++₁ ⊧ˢ-newvars-unique

  ⊧ˢ-newvars₂-unique :
    let xs = map proj₁ sis in
    Unique (map ρ₂ xs)
  ⊧ˢ-newvars₂-unique = Unique-⊆ (⊆ⁱ-++₂ {xs = map ρ₁ (map proj₁ sis)}) ⊧ˢ-newvars-unique

  ⊧ˢ-ρ₁x≢ρ₂ : ∀ {x} → x ∈ map proj₁ sis → ρ₁ x ≢ ρ₂ x
  ⊧ˢ-ρ₁x≢ρ₂ {x = x} x∈
    with ρ₁ x ≟ ρ₂ x
  … | yes ρ₁x≡ρ₂x = 
    let xs = map proj₁ sis in
    let _ , _ , d = Unique-++⁻ (map ρ₁ xs) (map ρ₂ xs) ⊧ˢ-newvars-unique in
    ⊥-elim (d (ρ₁ x) (∈-map ρ₁ x∈) (subst (_∈ _) (sym ρ₁x≡ρ₂x) (∈-map ρ₂ x∈)))
  … | no p = p 

  -- ⊧ˢ-dom⊆domΓ : Map.dom sis ⊆ dom Γ
  -- ⊧ˢ-dom⊆domΓ x∈sis =
  --   let (v , eq) = Map.∈dom→lookup-some _ x∈sis in
  --   let (b , s₂ , p) = ⊧ˢ-binds eq in
  --   ∈binds→∈dom Γ p

open _⊧ˢ_⍮_⍮_ public

⊧ˢ-[] : [] ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ 
⊧ˢ-[] = record
  { ⊧ˢ-binds            = λ ()
  ; ⊧ˢ-vars-unique      = λ _ ()
  ; ⊧ˢ-newvars-disjoint = λ _ ()
  }

-- ⊧ˢ-⊆ : ∀ sis₁ sis₂ →
--   sis₁ ⊆ⁱ sis₂ →
--   sis₂ ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
--   sis₁ ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ
-- ⊧ˢ-⊆ {ρ₁ = ρ₁} {ρ₂ = ρ₂} sis₁ sis₂ sub p = record
--   { ⊧ˢ-binds = λ si∈ → ⊧ˢ-binds p (⊆ⁱ→⊆ sub si∈)
--   ; ⊧ˢ-vars-unique = Unique-⊆ eq₃ (⊧ˢ-vars-unique p)
--   ; ⊧ˢ-newvars-disjoint = Disjoint-⊆₁ (⊆ⁱ→⊆ eq₂) (⊧ˢ-newvars-disjoint p)
--   }
--   where
--     inj-proj₁-sis₂ : ∀ x y → x ∈ sis₂ → y ∈ sis₂ → proj₁ x ≡ proj₁ y → x ≡ y
--     inj-proj₁-sis₂ = Unique-cod→Injective sis₂ (⊧ˢ-oldvars-unique p)
--     inj-proj₁-sis₁ : ∀ x y → x ∈ sis₁ → y ∈ sis₁ → proj₁ x ≡ proj₁ y → x ≡ y
--     inj-proj₁-sis₁ = λ x y x∈ y∈ eq → inj-proj₁-sis₂ x y (⊆ⁱ→⊆ sub x∈) (⊆ⁱ→⊆ sub y∈) eq
--     xs₁ = map proj₁ sis₁
--     xs₂ = map proj₁ sis₂
--     eq₂ : map ρ₁ xs₁ ++ map ρ₂ xs₁ ⊆ⁱ map ρ₁ xs₂ ++ map ρ₂ xs₂
--     eq₂ = ⊆ⁱ-++ (⊆ⁱ-map ρ₁ {!!} (⊆ⁱ-map proj₁ inj-proj₁-sis₁ sub)) (⊆ⁱ-map ρ₂ {!!} (⊆ⁱ-map proj₁ inj-proj₁-sis₁ sub))
--     eq₃ : xs₁ ++ map ρ₁ xs₁ ++ map ρ₂ xs₁ ⊆ⁱ xs₂ ++ map ρ₁ xs₂ ++ map ρ₂ xs₂
--     eq₃ = ⊆ⁱ-++ (⊆ⁱ-map proj₁ {!!} sub) eq₂

⊧ˢ-++ : ∀ sis₁ sis₂ →
  (sis₁ ++ sis₂) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  sis₁ ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ ×
  sis₂ ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ
⊧ˢ-++ {ρ₁ = ρ₁} {ρ₂ = ρ₂} sis₁ sis₂ p =
  let eq' =
        let
          a = map proj₁ sis₁
          b = map proj₁ sis₂ 
          c = map ρ₁ (map proj₁ sis₁)
          d = map ρ₁ (map proj₁ sis₂)
          e = map ρ₂ (map proj₁ sis₁)
          f = map ρ₂ (map proj₁ sis₂)
        in
        let open ⊆ⁱ-Reasoning in
        begin
          (a ++ (c ++ e)) ++ (b ++ (d ++ f))
        ≡⟨ ListP.++-assoc a (c ++ e) (b ++ (d ++ f)) ⟩
          a ++ ((c ++ e) ++ (b ++ (d ++ f)))
        ≡⟨ cong (a ++_) (ListP.++-assoc c e (b ++ (d ++ f))) ⟩
          a ++ (c ++ (e ++ (b ++ (d ++ f))))
        ≡⟨ cong (a ++_) (cong (c ++_) (cong (e ++_) (sym (ListP.++-assoc b d f)))) ⟩
          a ++ (c ++ (e ++ ((b ++ d) ++ f)))
        ⊆⟨ ⊆ⁱ-++ (⊆ⁱ-refl {xs = a}) (⊆ⁱ-++ (⊆ⁱ-refl {xs = c}) (⊆ⁱ-comm e ((b ++ d) ++ f))) ⟩
          a ++ (c ++ (((b ++ d) ++ f) ++ e))
        ≡⟨ cong (a ++_) (cong (c ++_) (ListP.++-assoc (b ++ d) f e)) ⟩
          a ++ (c ++ ((b ++ d) ++ (f ++ e)))
        ⊆⟨ ⊆ⁱ-++ (⊆ⁱ-refl {xs = a}) (⊆ⁱ-++ (⊆ⁱ-refl {xs = c}) (⊆ⁱ-++ (⊆ⁱ-refl {xs = b ++ d}) (⊆ⁱ-comm f e))) ⟩
          a ++ (c ++ ((b ++ d) ++ (e ++ f)))
        ≡⟨ cong (a ++_) (sym (ListP.++-assoc c (b ++ d) (e ++ f))) ⟩
          a ++ ((c ++ (b ++ d)) ++ (e ++ f))
        ⊆⟨ ⊆ⁱ-++ (⊆ⁱ-refl {xs = a}) (⊆ⁱ-++ (⊆ⁱ-++ (⊆ⁱ-refl {xs = c}) (⊆ⁱ-comm b d)) (⊆ⁱ-refl {xs = e ++ f})) ⟩
          a ++ ((c ++ (d ++ b)) ++ (e ++ f))
        ⊆⟨ ⊆ⁱ-++ (⊆ⁱ-refl {xs = a}) (⊆ⁱ-++ (⊆ⁱ-assoc' c d b) (⊆ⁱ-refl {xs = e ++ f})) ⟩
          a ++ (((c ++ d) ++ b) ++ (e ++ f))
        ⊆⟨ ⊆ⁱ-++ (⊆ⁱ-refl {xs = a}) (⊆ⁱ-++ (⊆ⁱ-comm (c ++ d) b) (⊆ⁱ-refl {xs = e ++ f})) ⟩
          a ++ ((b ++ (c ++ d)) ++ (e ++ f))
        ≡⟨ cong (a ++_) (ListP.++-assoc b (c ++ d) (e ++ f)) ⟩
          a ++ (b ++ ((c ++ d) ++ (e ++ f)))
        ≡⟨ sym (ListP.++-assoc a b ((c ++ d) ++ (e ++ f))) ⟩
          (a ++ b) ++ ((c ++ d) ++ (e ++ f))
        ∎ in
  let eq =
        let open ⊆ⁱ-Reasoning in
        begin
          (map proj₁ sis₁ ++ map ρ₁ (map proj₁ sis₁) ++ map ρ₂ (map proj₁ sis₁)) ++
          (map proj₁ sis₂ ++ map ρ₁ (map proj₁ sis₂) ++ map ρ₂ (map proj₁ sis₂))
        ⊆⟨ eq' ⟩
          (map proj₁ sis₁ ++ map proj₁ sis₂) ++
          (map ρ₁ (map proj₁ sis₁) ++ map ρ₁ (map proj₁ sis₂)) ++
          (map ρ₂ (map proj₁ sis₁) ++ map ρ₂ (map proj₁ sis₂))
        ≡⟨ sym (cong ((map proj₁ sis₁ ++ map proj₁ sis₂) ++_)
                     (cong₂ _++_ (ListP.map-++ ρ₁ (map proj₁ sis₁) (map proj₁ sis₂))
                                 (ListP.map-++ ρ₂ (map proj₁ sis₁) (map proj₁ sis₂)))) ⟩
          (map proj₁ sis₁ ++ map proj₁ sis₂) ++
          map ρ₁ (map proj₁ sis₁ ++ map proj₁ sis₂) ++
          map ρ₂ (map proj₁ sis₁ ++ map proj₁ sis₂)
        ≡⟨ sym (cong₂ _++_ (ListP.map-++ proj₁ sis₁ sis₂)
                           (cong₂ _++_ (cong (map ρ₁) (ListP.map-++ proj₁ sis₁ sis₂))
                                       (cong (map ρ₂) (ListP.map-++ proj₁ sis₁ sis₂)))) ⟩
          map proj₁ (sis₁ ++ sis₂) ++
          map ρ₁ (map proj₁ (sis₁ ++ sis₂)) ++
          map ρ₂ (map proj₁ (sis₁ ++ sis₂))
        ∎ in
  let ux = Unique-⊆ eq (⊧ˢ-vars-unique p) in
  let uv₁ , uv₂ , d = Unique-++⁻ (map proj₁ sis₁ ++ map ρ₁ (map proj₁ sis₁) ++ map ρ₂ (map proj₁ sis₁))
                                 (map proj₁ sis₂ ++ map ρ₁ (map proj₁ sis₂) ++ map ρ₂ (map proj₁ sis₂))
                                 ux in
  let eq-d₁ : map ρ₁ (map proj₁ sis₁) ++ map ρ₂ (map proj₁ sis₁) ⊆
             map ρ₁ (map proj₁ (sis₁ ++ sis₂)) ++ map ρ₂ (map proj₁ (sis₁ ++ sis₂))
      eq-d₁ = ⊆-++ (⊆-map ρ₁ (⊆-map proj₁ (⊆-++₁' {xs₁ = sis₁}))) (⊆-map ρ₂ (⊆-map proj₁ (⊆-++₁' {xs₁ = sis₁}))) in
  let eq-d₂ : map ρ₁ (map proj₁ sis₂) ++ map ρ₂ (map proj₁ sis₂) ⊆
             map ρ₁ (map proj₁ (sis₁ ++ sis₂)) ++ map ρ₂ (map proj₁ (sis₁ ++ sis₂))
      eq-d₂ = ⊆-++ (⊆-map ρ₁ (⊆-map proj₁ (⊆-++₂' sis₁))) (⊆-map ρ₂ (⊆-map proj₁ (⊆-++₂' sis₁))) in
  let p₁ = record
             { ⊧ˢ-binds            = λ si∈ → ⊧ˢ-binds p (AnyP.++⁺ˡ si∈)
             ; ⊧ˢ-vars-unique      = uv₁
             ; ⊧ˢ-newvars-disjoint = Disjoint-⊆₁ eq-d₁ (⊧ˢ-newvars-disjoint p)
             } in
  let p₂ = record
             { ⊧ˢ-binds            = λ si∈ → ⊧ˢ-binds p (AnyP.++⁺ʳ _ si∈)
             ; ⊧ˢ-vars-unique      = uv₂
             ; ⊧ˢ-newvars-disjoint = Disjoint-⊆₁ eq-d₂ (⊧ˢ-newvars-disjoint p)
             } in
  p₁ , p₂

⊧ˢ-++₁ : ∀ sis₁ sis₂ →
  (sis₁ ++ sis₂) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  sis₁ ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ
⊧ˢ-++₁ {ρ₁ = ρ₁} {ρ₂ = ρ₂} sis₁ sis₂ p = proj₁ (⊧ˢ-++ sis₁ sis₂ p)

⊧ˢ-++₂ : ∀ sis₁ sis₂ →
  (sis₁ ++ sis₂) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  sis₂ ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ
⊧ˢ-++₂ sis₁ sis₂ p = proj₂ (⊧ˢ-++ sis₁ sis₂ p)

⊧ˢ-head : ∀ si sis →
  (si ∷ sis) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  (si ∷ []) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ
⊧ˢ-head si sis p = ⊧ˢ-++₁ (si ∷ []) sis p

⊧ˢ-tail : ∀ si sis →
  (si ∷ sis) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ
⊧ˢ-tail si sis p = ⊧ˢ-++₂ (si ∷ []) sis p

split-bind-inv-∈ : ∀ {sis ρ₁ ρ₂ x t s₁} →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ (x ∶ t) →
  (x , s₁) ∈ sis →
  ∃[ b ] Σ[ s₂ ∈ Session b ]
    t ≡ Chan b (s₁ ++ˢ s₂) ×
    Map.lookup x sis ≡ some s₁ ×
    split-bind sis ρ₁ ρ₂ x t ≡ ρ₁ x ∶ Chan _ s₁ ⸴ ρ₂ x ∶ Chan b s₂
split-bind-inv-∈ {sis} {ρ₁} {ρ₂} {x} {t} {s₁} sis⊧ xs₁∈sis
  with (b , s₂ , here refl) ← ⊧ˢ-binds sis⊧ xs₁∈sis 
  rewrite Map.lookup-∈-unique (⊧ˢ-oldvars-unique sis⊧) xs₁∈sis
  rewrite %-some s₁ s₂ =
  b , s₂ , refl , refl , refl

split-bind-inv-∈dom : ∀ sis ρ₁ ρ₂ x t →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ (x ∶ t) →
  x ∈ map proj₁ sis →
  ∃[ b ] Σ[ s₁ ∈ SessionB ] Σ[ s₂ ∈ Session b ]
    t ≡ Chan b (s₁ ++ˢ s₂) ×
    Map.lookup x sis ≡ some s₁ ×
    split-bind sis ρ₁ ρ₂ x t ≡ ρ₁ x ∶ Chan _ s₁ ⸴ ρ₂ x ∶ Chan b s₂
split-bind-inv-∈dom sis ρ₁ ρ₂ x t sis⊧ x∈sis₁
  using (s₁ , eq) ← Map.∈dom→lookup-some sis x∈sis₁
  using xs₁∈sis ← Map.lookup-some→∈ sis eq
  with (b , s₂ , here refl) ← ⊧ˢ-binds sis⊧ xs₁∈sis 
  rewrite eq
  rewrite %-some s₁ s₂
  =
  b , s₁ , s₂ , refl , refl , refl 

split-bind-inv-∉dom : ∀ sis ρ₁ ρ₂ x t →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ (x ∶ t) →
  x ∉ map proj₁ sis →
  split-bind sis ρ₁ ρ₂ x t ≡ x ∶ t
split-bind-inv-∉dom sis ρ₁ ρ₂ x t sis⊧ x∉sis₁
  with Chan? t
… | no ¬chan = refl
… | yes (b , s , refl) rewrite Map.lookup-∉ sis x∉sis₁ = refl

split-bind-inv : ∀ sis ρ₁ ρ₂ x t →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ (x ∶ t) →
  x ∉ map proj₁ sis × split-bind sis ρ₁ ρ₂ x t ≡ x ∶ t ⊎
  x ∈ map proj₁ sis × ∃[ b ] Σ[ s₁ ∈ SessionB ] Σ[ s₂ ∈ Session b ]
    t ≡ Chan b (s₁ ++ˢ s₂) ×
    Map.lookup x sis ≡ some s₁ ×
    split-bind sis ρ₁ ρ₂ x t ≡ ρ₁ x ∶ Chan _ s₁ ⸴ ρ₂ x ∶ Chan b s₂
split-bind-inv sis ρ₁ ρ₂ x t sis⊧ with x ∈? map proj₁ sis
… | no ¬x∈sis₁ = inj₁ (¬x∈sis₁ , split-bind-inv-∉dom sis ρ₁ ρ₂ x t sis⊧ ¬x∈sis₁)
… | yes x∈sis₁ = inj₂ (x∈sis₁ , split-bind-inv-∈dom sis ρ₁ ρ₂ x t sis⊧ x∈sis₁)

⊧ˢ-split₁ : ∀ si sis →
  (si ∷ sis) ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ split-ctx (si ∷ []) ρ₁ ρ₂ Γ
⊧ˢ-split₁ {ρ₁ = ρ₁} {ρ₂ = ρ₂} {Γ = Γ} si sis p = record
  { ⊧ˢ-binds = λ {x = x} si∈ →
      let b , s , q = ⊧ˢ-binds p (there si∈) in
      let x∈vars-sis = ∈-map proj₁ si∈ in
      let x∉si = Unique-∈-++₂ (proj₁ si ∷ []) (map proj₁ sis)
                              (⊧ˢ-oldvars-unique p)
                              x∈vars-sis in
      b , s , split-ctx-∈' Γ (si ∷ []) ρ₁ ρ₂ x∉si q
  ; ⊧ˢ-vars-unique = ⊧ˢ-vars-unique (⊧ˢ-tail si sis p)
  ; ⊧ˢ-newvars-disjoint =
    let eq =
          let open ≈ⁱ-Reasoning in
          begin
            (ρ₁ (proj₁ si) ∷ [] ++ ρ₂ (proj₁ si) ∷ []) ++
            (map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis))
          ≈⟨ ≈ⁱ-++ (≈ⁱ-refl {xs = ρ₁ (proj₁ si) ∷ []})
                   (≈ⁱ-++ (≈ⁱ-comm (ρ₂ (proj₁ si) ∷ []) (map ρ₁ (map proj₁ sis)))
                          ≈ⁱ-refl) ⟩
            ρ₁ (proj₁ si) ∷ (
              (map ρ₁ (map proj₁ sis) ++
              (ρ₂ (proj₁ si) ∷ [])) ++ map ρ₂ (map proj₁ sis)
            )
          ≈⟨ ≈ⁱ-++ (≈ⁱ-refl {xs = ρ₁ (proj₁ si) ∷ []})
                   (≈ⁱ-assoc (map ρ₁ (map proj₁ sis))
                             (ρ₂ (proj₁ si) ∷ [])
                             (map ρ₂ (map proj₁ sis))) ⟩
            ρ₁ (proj₁ si) ∷ (
              map ρ₁ (map proj₁ sis) ++
              ((ρ₂ (proj₁ si) ∷ []) ++ map ρ₂ (map proj₁ sis))
            )
          ≡⟨⟩
            ρ₁ (proj₁ si) ∷ map ρ₁ (map proj₁ sis) ++
            ρ₂ (proj₁ si) ∷ map ρ₂ (map proj₁ sis)
          ∎ in
    let eq' = ⊆-trans (⊆-++₂' (ρ₁ (proj₁ si) ∷ [] ++ ρ₂ (proj₁ si) ∷ []) ) (≈ⁱ→⊆ eq) in
    Disjoint-⊆₂ (split-ctx-dom (si ∷ []) ρ₁ ρ₂ Γ) $
    λ x x∈ρᵢsis x∈split → ⊧ˢ-newvars-disjoint p x (⊆-∈ eq' x∈ρᵢsis) $
      case AnyP.++⁻ (dom Γ) x∈split of λ where
        (inj₁ x∈Γ) → x∈Γ
        (inj₂ x∈ρᵢsi) → ⊥-elim $
          Unique-∈-++₁ (ρ₁ (proj₁ si) ∷ [] ++ ρ₂ (proj₁ si) ∷ [])
                       (map ρ₁ (map proj₁ sis) ++ map ρ₂ (map proj₁ sis))
                       (Unique-≈ eq (⊧ˢ-newvars-unique p))
                       x∈ρᵢsi
                       x∈ρᵢsis
  }

split-ctx-Unique : ∀ si Γ →
  let sis = si ∷ [] in
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  Unique (dom Γ) →
  Unique (dom (split-ctx sis ρ₁ ρ₂ Γ))
split-ctx-Unique {ρ₁ = ρ₁} {ρ₂ = ρ₂} si@(x , s₁) Γ sis⊧Γ U-Γ =
  let sis = si ∷ [] in
  -- let (ρ₁ , ρ₂) = split-rens (List.map proj₁ sis) ys in
  let b , s₂ , x∶s∈Γ = ⊧ˢ-binds sis⊧Γ (here refl) in
  let C , eq-Γ = ∈binds→C Γ x∶s∈Γ in
  let U-C[x] = subst (λ ■ → Unique (dom ■)) eq-Γ U-Γ in
  let C[x]≈C++x = dom-C C (x ∶ Chan _ (s₁ ++ˢ s₂)) in
  let C[x₁,x₂]≈C++x₁,x₂ = dom-C C (ρ₁ x ∶ Chan _ s₁ ⸴ ρ₂ x ∶ Chan _ s₂) in
  let U-C++x = Unique-≈ (≈ⁱ-sym C[x]≈C++x) U-C[x] in
  let U-C = Unique-++₁ {xs = dom (C [ · ])} U-C++x in
  -- let D-x₁++x₂-ys : Disjoint (ρ₁ x ∷ ρ₂ x ∷ []) ys
  --     D-x₁++x₂-ys = split-rens-disjoint (List.map proj₁ sis) ys (Unique-single x)  in
  -- let D-x₁++x₂-Γ = Disjoint-⊆₂ Γ⊆ys D-x₁++x₂-ys in
  let D-x₁++x₂-Γ = ⊧ˢ-newvars-disjoint sis⊧Γ in
  let D-x₁++x₂-C[x] = Disjoint-≈₂ (≈ˡ-sym (≈ⁱ→≈ˡ C[x]≈C++x))
                      (subst (λ ■ → Disjoint _ (dom ■)) eq-Γ D-x₁++x₂-Γ)  in
  let D-x₁++x₂-C = Disjoint-⊆₂ ⊆-++₁' D-x₁++x₂-C[x] in
  -- let U-C++x₁,x₂ = Unique-++ U-C (split-rens-unique (List.map proj₁ sis) ys (Unique-single x))
  --                                (Disjoint-sym D-x₁++x₂-C) in
  let U-C++x₁,x₂ = Unique-++ U-C (⊧ˢ-newvars-unique sis⊧Γ) (Disjoint-sym D-x₁++x₂-C) in
  let U-C[x₁,x₂] = Unique-≈ C[x₁,x₂]≈C++x₁,x₂ U-C++x₁,x₂ in
  let eq-sΓ = split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ Γ C U-Γ eq-Γ in
  subst (λ ■ → Unique (dom ■))
        (sym eq-sΓ)
        U-C[x₁,x₂] 

--------------------------------------------------------------------------------

data Prefixˢ : ∀ {b₁ b₂} → Session b₁ → Session b₂ → Set where
  prefix-owned    : ∀ {s : Session owned} → Prefixˢ s s
  prefix-borrowed : ∀ {b} ({s} s₂ : Session b) → s ≡ s₁ ++ˢ s₂ → Prefixˢ s₁ s

++ˢ-neutralʳ : ∀ (s : SessionB) → s ++ˢ return ≡ s
++ˢ-neutralʳ return = refl
++ˢ-neutralʳ (op[ o ] s₁ ⍮ s₂) = cong (op[ o ] s₁ ⍮_) (++ˢ-neutralʳ s₂)
++ˢ-neutralʳ (choice[ o ] s₁ ⍮ s₂) = cong₂ (choice[ o ]_⍮_) (++ˢ-neutralʳ s₁) (++ˢ-neutralʳ s₂)

prefix-whole : ∀ {b} {s : Session b} → Prefixˢ s s
prefix-whole {borrowed} {s} = prefix-borrowed return (sym (++ˢ-neutralʳ s))
prefix-whole {owned} {s} = prefix-owned

∈-ext-inv : ∀ {b} m Γ₁ Γ₂ →
  b ∈ binds (ext m Γ₁ Γ₂) →
  b ∈ binds Γ₁ ⊎ b ∈ binds Γ₂
∈-ext-inv ∞ Γ₁ Γ₂ b∈ = AnyP.++⁻ (binds Γ₁) b∈
∈-ext-inv 𝟙 Γ₁ Γ₂ b∈ = AnyP.++⁻ (binds Γ₁) b∈
∈-ext-inv ≻ Γ₁ Γ₂ b∈ = AnyP.++⁻ (binds Γ₁) b∈
∈-ext-inv ≺ Γ₁ Γ₂ b∈ = Sum.swap (AnyP.++⁻ (binds Γ₂) b∈)

%-∈-none/someᵒ : ∀ {x t} Γ u →
  u x ≡ none ⊎ ∃[ s ] u x ≡ some (owned , s) →
  (x , t) ∈ binds (Γ %ᶜ u) →
  (x , t) ∈ binds Γ
%-∈-none/someᵒ (x ∶ t) u eq xt∈Γ%u
  with Chan? t
… | no ¬chan = xt∈Γ%u
… | yes (b , s , refl)
  with u x in eq'
… | none             = xt∈Γ%u
… | (some (owned , s₁)) = xt∈Γ%u
… | (some (borrowed , s₁))
  with s % s₁
… | none             = xt∈Γ%u
… | some s₂
  with here refl ← xt∈Γ%u
  with eq
… | inj₁ eq with () ← trans (sym eq) (eq')
… | inj₂ (s , eq) with () ← trans (sym eq) (eq')
%-∈-none/someᵒ (Γ₁ ⸴[ o ] Γ₂) u eq xt∈Γ%u
  with AnyP.++⁻ (binds (Γ₁ %ᶜ u)) xt∈Γ%u
… | inj₁ b∈₁ = AnyP.++⁺ˡ $ %-∈-none/someᵒ Γ₁ u eq b∈₁
… | inj₂ b∈₂ = AnyP.++⁺ʳ _ $ %-∈-none/someᵒ Γ₂ u eq b∈₂

%-∈-none : ∀ {x t} Γ u →
  u x ≡ none →
  (x , t) ∈ binds (Γ %ᶜ u) →
  (x , t) ∈ binds Γ
%-∈-none Γ u eq = %-∈-none/someᵒ Γ u (inj₁ eq)

%-∈-someᵒ : ∀ {x t} Γ u →
  u x ≡ some (owned , s₁) →
  (x , t) ∈ binds (Γ %ᶜ u) →
  (x , t) ∈ binds Γ
%-∈-someᵒ Γ u eq = %-∈-none/someᵒ Γ u (inj₂ (_ , eq))

--------------------------------------------------------------------------------

⋯ᵘ-∈binds : ∀ {x b} {s : Session b} Γ u →
  (x , Chan b s) ∈ binds Γ →
  ∃[ b' ] Σ[ s' ∈ Session b' ] (x , Chan b' s') ∈ binds (Γ ⋯ᵘ u)
⋯ᵘ-∈binds (x ∶ t) u (here refl)
  with Chan? t
… | no ¬chan = ⊥-elim (¬chan (_ , _ , refl))
… | yes xx
  with u x
… | none = _ , _ , here refl
… | some s₁ = _ , _ , here refl
⋯ᵘ-∈binds (Γ₁ ⸴[ o ] Γ₂) u x,c∈Γ
  with AnyP.++⁻ (binds Γ₁) x,c∈Γ
… | inj₁ x,c∈Γ₁ =
  let b' , s' , x,c∈Γ₁⋯u = ⋯ᵘ-∈binds Γ₁ u x,c∈Γ₁ in
  b' , s' , AnyP.++⁺ˡ x,c∈Γ₁⋯u
… | inj₂ x,c∈Γ₂ =
  let b' , s' , x,c∈Γ₂⋯u = ⋯ᵘ-∈binds Γ₂ u x,c∈Γ₂ in
  b' , s' , AnyP.++⁺ʳ _ x,c∈Γ₂⋯u

split-ctx-ρ₂-contra : ∀ Γ ys sis ρ₁ ρ₂ →
    ys % map proj₁ sis ⊢ʳ ρ₁ →
    ys % map proj₁ sis ⊢ʳ ρ₂ →
    Disjoint (map ρ₁ (map proj₁ sis)) (map ρ₂ (map proj₁ sis)) →
    dom Γ ⊆ ys →
    (ρ₂ x , Chan b s) ∈ binds (split-ctx sis ρ₁ ρ₂ Γ) →
    x ∈ ys →
    x ∉ dom Γ →
    ⊥
split-ctx-ρ₂-contra {x = x} {b = b} {s = s}
                    (y ∶ t) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ domΓ⊆ys ρ₂x∈sΓ x∈ys x∉Γ
  with Chan? t in eq-t
… | no ¬chan rewrite eq-t with here refl ← ρ₂x∈sΓ = ⊥-elim (¬chan (_ , _ , refl))
… | yes (b' , s' , refl)
  using x≢ρ₂x ← λ x≡ρ₂x → x∉Γ (here x≡ρ₂x)
  with Map.lookup x sis in eq-sis-x
split-ctx-ρ₂-contra {x = x} {b = b} {s = s}
                    (y ∶ t) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ domΓ⊆ys ρ₂x∈sΓ x∈ys x∉Γ
                  | yes (b' , s' , refl) | none
  using x∉sis₁ ← Map.lookup-none→∉dom sis eq-sis-x
  using ρ₂x≡x ← ⊢ʳ-∉xs-id ⊢ρ₂ x∉sis₁
  with Map.lookup y sis in eq-sis
… | none rewrite eq-t with here refl ← ρ₂x∈sΓ =
    ⊥-elim (x∉Γ (here (sym ρ₂x≡x))) 
… | some s₁
  with s' % s₁
… | none rewrite eq-t with here refl ← ρ₂x∈sΓ =
    ⊥-elim (x∉Γ (here (sym ρ₂x≡x))) 
… | some s₂
  with ρ₂x∈sΓ
… | here eq
  with ρ₂x≡ρ₁y , refl ← ProdP.,-injective eq
  using y∈sis₁ ← Map.∈→∈dom (Map.lookup-some→∈ sis eq-sis)
  using ρ₁y∈ρ₁sis ← ∈-map ρ₁ y∈sis₁
  using ρ₂x∈ρ₁sis ← subst (_∈ map ρ₁ (map proj₁ sis)) (sym ρ₂x≡ρ₁y) ρ₁y∈ρ₁sis
  using ρ₁y∉ys ← ⊢ʳ-ρxs⊎ys ⊢ρ₁ (ρ₁ y) ρ₁y∈ρ₁sis
  using x∉ys ← subst (_∉ ys) (trans (sym ρ₂x≡ρ₁y) ρ₂x≡x) ρ₁y∉ys
  = x∉ys x∈ys
… | there (here eq)
  with ρ₂x≡ρ₂y , refl ← ProdP.,-injective eq
  using y∈sis₁ ← Map.∈→∈dom (Map.lookup-some→∈ sis eq-sis)
  using ρ₂y∈ρ₂sis₁ ← ∈-map ρ₂ y∈sis₁
  using x≢y ← λ p → x∉Γ (here p)
  using x∈ρ₂sis₁ ← subst (_∈ _) (trans (sym ρ₂x≡ρ₂y) ρ₂x≡x) ρ₂y∈ρ₂sis₁
  = ⊢ʳ-ρxs⊎ys ⊢ρ₂ x x∈ρ₂sis₁ x∈ys
split-ctx-ρ₂-contra {x = x} {b = b} {s = s}
                    (y ∶ t) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ domΓ⊆ys ρ₂x∈sΓ x∈ys x∉Γ
                  | yes (b' , s' , refl) | some s₁x
  using x∈sis₁ ← Map.∈→∈dom (Map.lookup-some→∈ sis eq-sis-x)
  using ρ₂x∈ρ₂sis₁ ← ∈-map ρ₂ x∈sis₁
  using ρ₂x∉ys ← (⊢ʳ-ρxs⊎ys ⊢ρ₂) (ρ₂ x) ρ₂x∈ρ₂sis₁
  using ρ₂x∉sis₁ ← ⊆-∉ (⊢ʳ-xs⊆ys ⊢ρ₂) ρ₂x∉ys
  using eq-ρ₂x-sis-none ← Map.∉dom→lookup-none sis ρ₂x∉sis₁
  with Map.lookup y sis in eq-sis
… | none rewrite eq-t with here refl ← ρ₂x∈sΓ =
    ⊥-elim (ρ₂x∉ys (domΓ⊆ys (here refl)))
… | some s₁
  with s' % s₁
… | none rewrite eq-t with here refl ← ρ₂x∈sΓ with () ← trans (sym eq-sis) eq-ρ₂x-sis-none
… | some s₂
  with ρ₂x∈sΓ
… | here eq
  with ρ₂x≡ρ₁y , refl ← ProdP.,-injective eq
  using y∈sis₁ ← Map.∈→∈dom (Map.lookup-some→∈ sis eq-sis)
  using ρ₁y∈ρ₁sis ← ∈-map ρ₁ y∈sis₁
  using ρ₂x∈ρ₁sis ← subst (_∈ _) (sym ρ₂x≡ρ₁y) ρ₁y∈ρ₁sis
  = d-ρ₁-ρ₂ (ρ₂ x) ρ₂x∈ρ₁sis (∈-map ρ₂ x∈sis₁)
… | there (here eq)
  with ρ₂x≡ρ₂y , refl ← ProdP.,-injective eq
  with x≡y@refl ← ⊢ʳ-inj-ys-ρ ⊢ρ₂ x y (⊢ʳ-xs⊆ys ⊢ρ₂ x∈sis₁) (domΓ⊆ys (here refl)) ρ₂x≡ρ₂y
  = ⊥-elim (x∉Γ (here refl))
split-ctx-ρ₂-contra {x = x} {b = b} {s = s}
                    (Γ₁ ⸴[ o ] Γ₂) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ domΓ⊆ys ρ₂x∈sΓ x∈ys x∉Γ
  using eq ← ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)
  using x∉Γ₁ , x∉Γ₂ ← ∉-++⁻ (dom Γ₁) (dom Γ₂) (subst (x ∉_) eq x∉Γ)
  with AnyP.++⁻ (binds (split-ctx sis ρ₁ ρ₂ Γ₁)) ρ₂x∈sΓ
… | inj₁ ρ₂x∈sΓ₁ =
    let sub₁ : dom Γ₁ ⊆ ys
        sub₁ = let open ⊆-Reasoning in
               begin
                 dom Γ₁
               ⊆⟨ ⊆-++₁' ⟩
                 dom Γ₁ ++ dom Γ₂
               ≡⟨ sym eq ⟩
                 dom (Γ₁ ⸴[ o ] Γ₂)
               ⊆⟨ domΓ⊆ys ⟩
                 ys
               ∎ in
    split-ctx-ρ₂-contra Γ₁ ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub₁ ρ₂x∈sΓ₁ x∈ys x∉Γ₁
… | inj₂ ρ₂x∈sΓ₂ =
    let sub₂ : dom Γ₂ ⊆ ys
        sub₂ = let open ⊆-Reasoning in
               begin
                 dom Γ₂
               ⊆⟨ ⊆-++₂' _ ⟩
                 dom Γ₁ ++ dom Γ₂
               ≡⟨ sym eq ⟩
                 dom (Γ₁ ⸴[ o ] Γ₂)
               ⊆⟨ domΓ⊆ys ⟩
                 ys
               ∎ in
    split-ctx-ρ₂-contra Γ₂ ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub₂ ρ₂x∈sΓ₂ x∈ys x∉Γ₂

split-ctx-∈binds : ∀ u₁ u₂ Γ ys sis ρ₁ ρ₂ →
    ys % map proj₁ sis ⊢ʳ ρ₁ →
    ys % map proj₁ sis ⊢ʳ ρ₂ →
    Disjoint (map ρ₁ (map proj₁ sis)) (map ρ₂ (map proj₁ sis)) →
    dom Γ ⊆ ys →
    x ∈ dom Γ →
    (ρ₂ x , Chan b s) ∈ binds (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂))) →
    ∃[ b' ] Σ[ s' ∈ Session b' ] (x , Chan b' s') ∈ binds Γ
split-ctx-∈binds {x = x} {b = b} {s = s}
                 u₁ u₂ (.x ∶ t) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ domΓ⊆ys (here refl) ρ₂x,c∈sΓ
  with Chan? t in eq-t
… | no _ rewrite eq-t with here eq ← ρ₂x,c∈sΓ =
  let c≡t = ProdP.,-injectiveʳ ((ρ₂ x , Chan b s) ≡ (x , t) by eq) in
  _ , _ , here (cong (x ,_) c≡t)
… | yes (b , s , refl)
  with Map.lookup x sis
… | none =
  _ , _ , here refl
… | some s₁
  with s % s₁
… | none =
  _ , _ , here refl
… | some s₂ = _ , _ , here refl
split-ctx-∈binds {x = x} {b = b} {s = s}
                 u₁ u₂ (Γ₁ ⸴[ o ] Γ₂) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ domΓ⊆ys x∈domΓ ρ₂x,c∈sΓ
  using eq ← ListP.map-++ proj₁ (binds Γ₁) (binds Γ₂)
  with AnyP.++⁻ (binds (split-ctx sis ρ₁ ρ₂ (Γ₁ ⋯ᵘ u₁ ·ᵘ u₂))) ρ₂x,c∈sΓ
… | inj₁ ρ₂x,c∈sΓ₁ =
    let
      sub₁ : dom Γ₁ ⊆ ys
      sub₁ = let open ⊆-Reasoning in
            begin
              dom Γ₁
            ⊆⟨ ⊆-++₁' ⟩
              dom Γ₁ ++ dom Γ₂
            ≡⟨ sym eq ⟩
              dom (Γ₁ ⸴[ o ] Γ₂)
            ⊆⟨ domΓ⊆ys ⟩
              ys
            ∎
      sub₁' = dom (Γ₁ ⋯ᵘ u₁ ·ᵘ u₂) ⊆ ys
      sub₁' = subst (_⊆ ys) (sym (⋯ᵘ-dom Γ₁ (u₁ ·ᵘ u₂))) sub₁
    in
    case x ∈? dom Γ₁ of λ where
      (yes x∈domΓ₁) →
        let
          b' , s' , x,c∈Γ₁ =
            split-ctx-∈binds u₁ u₂ Γ₁ ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub₁ x∈domΓ₁ ρ₂x,c∈sΓ₁
        in
          b' , s' , AnyP.++⁺ˡ x,c∈Γ₁
      (no ¬x∈domΓ₁) →
        let ¬x∈domΓ₁⋯ = subst (x ∉_) (sym (⋯ᵘ-dom Γ₁ (u₁ ·ᵘ u₂))) (¬x∈domΓ₁) in
        ⊥-elim $ split-ctx-ρ₂-contra
          (Γ₁ ⋯ᵘ u₁ ·ᵘ u₂) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂
          sub₁' ρ₂x,c∈sΓ₁ (domΓ⊆ys x∈domΓ) ¬x∈domΓ₁⋯
… | inj₂ ρ₂x,c∈sΓ₂ =
    let
      sub₂ : dom Γ₂ ⊆ ys
      sub₂ = let open ⊆-Reasoning in
             begin
               dom Γ₂
             ⊆⟨ ⊆-++₂' _ ⟩
               dom Γ₁ ++ dom Γ₂
             ≡⟨ sym eq ⟩
               dom (Γ₁ ⸴[ o ] Γ₂)
             ⊆⟨ domΓ⊆ys ⟩
               ys
             ∎
      sub₂' = dom (Γ₂ ⋯ᵘ u₁ ·ᵘ u₂) ⊆ ys
      sub₂' = subst (_⊆ ys) (sym (⋯ᵘ-dom Γ₂ (u₁ ·ᵘ u₂))) sub₂
    in
    case x ∈? dom Γ₂ of λ where
      (yes x∈domΓ₂) →
        let
          b' , s' , x,c∈Γ₂ =
            split-ctx-∈binds u₁ u₂ Γ₂ ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ sub₂ x∈domΓ₂ ρ₂x,c∈sΓ₂
        in
          b' , s' , AnyP.++⁺ʳ _ x,c∈Γ₂
      (no ¬x∈domΓ₂) →
        let ¬x∈domΓ₂⋯ = subst (x ∉_) (sym (⋯ᵘ-dom Γ₂ (u₁ ·ᵘ u₂))) (¬x∈domΓ₂) in
        ⊥-elim $ split-ctx-ρ₂-contra
          (Γ₂ ⋯ᵘ u₁ ·ᵘ u₂) ys sis ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂
          sub₂' ρ₂x,c∈sΓ₂ (domΓ⊆ys x∈domΓ) ¬x∈domΓ₂⋯

foo : ∀ u₁ u₂ (e₁ : Expr §) (e₂s : List (Expr §)) Γ Γ₁ C extra →
  dom (C [ · ]) ⊆ⁱ dom Γ →
  SplitsAlg' u₁ u₂ e₁ e₂s Γ Γ₁ C extra →
  (x , Chan b s) ∈ binds (C [ · ]) →
  ∃[ b' ] Σ[ s' ∈ Session b' ] (x , Chan b' s') ∈ binds Γ
foo {x = x} {b = b} {s = s} u₁ u₂ e₁ e₂s Γ Γ₁ C extra C⊆ⁱΓ salg x,c∈C =
  let
    sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁
    ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
    U-sis = ↓ᵘ-pres-Unique (fvs e₁ ∩ˡ fvss e₂s) u₁ $ ∩ˡ-unique (fvs e₁) (fvss e₂s)
    ys = dom Γ ++ extra ++ vars e₁ ++ varss e₂s
    sub : map proj₁ sis ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
    sub = let open ⊆-Reasoning in
          begin
            map proj₁ sis
          ⊆⟨ sis⊆ Γ e₁ e₂s u₁ ⟩
            dom Γ ++ vars e₁ ++ varss e₂s
          ⊆⟨ ⊆-++ (⊆-refl {xs = dom Γ}) (⊆-++₂' extra) ⟩
            ys
          ∎
    ⊢ρ₁ , ⊢ρ₂ , _ =
      ⊢ʳ-split-rens (map proj₁ sis) ys sub U-sis
    U-cod-ρᵢ = split-rens-unique (map proj₁ sis) ys U-sis
    _ , _ , d-ρ₁-ρ₂ = Unique-++⁻ (map ρ₁ (map proj₁ sis)) (map ρ₂ (map proj₁ sis)) U-cod-ρᵢ

    _ : split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ≲ ((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ (Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁ ]
    _ = salg

    b' , s' , x,c'∈C⋯u₂ = ⋯ᵘ-∈binds (C [ · ]) u₂ x,c∈C

    ρ₂x,c'∈C⋯u₂⋯ρ₂ = ⋯ʳ-binds (C [ · ] ⋯ᵘ u₂) ρ₂ x,c'∈C⋯u₂

    salg' : binds (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ (Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁ ]) ⊆
            binds (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)))
    salg' = ≲→⊆binds salg

    salg' : binds (((C [ · ]) ⋯ᵘ u₂) ⋯ʳ ρ₂) ⊆ binds (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)))
    salg' =
      let open ⊆-Reasoning in
      begin
        binds (((C [ · ]) ⋯ᵘ u₂) ⋯ʳ ρ₂)
      ≡⟨ cong (λ ■ → binds (■ ⋯ʳ ρ₂)) (⋯ᵘ-dist-[] C · u₂) ⟩
        binds (((C ⋯ᵘᶜ u₂) [ · ]) ⋯ʳ ρ₂)
      ≡⟨ cong binds (⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂) · ρ₂) ⟩
        binds (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ · ])
      ⊆⟨ ⊆-++₁' ⟩
        binds (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ · ]) ++ binds ((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁)
      ≈⟨ ≈ˡ-sym (≈ⁱ→≈ˡ (binds-C ((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) ((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁))) ⟩
        binds (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ (Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁ ])
      ⊆⟨ salg' ⟩
        binds (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)))
      ∎

    ρ₂x,c'∈sΓ : (ρ₂ x , Chan b' s') ∈ binds (split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ (u₁ ·ᵘ u₂)))
    ρ₂x,c'∈sΓ = salg' ρ₂x,c'∈C⋯u₂⋯ρ₂

    x∈C : x ∈ dom (C [ · ])
    x∈C = ∈binds→∈dom (C [ · ]) x,c∈C

    x∈Γ : x ∈ dom Γ
    x∈Γ = ⊆ⁱ→⊆ C⊆ⁱΓ x∈C

    t , x,t∈Γ = ∈dom→∈binds Γ x∈Γ
    -- x,t'∈Γ⋯u₁·u₂ = ...
  in
  split-ctx-∈binds u₁ u₂ Γ (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) sis
                   ρ₁ ρ₂ ⊢ρ₁ ⊢ρ₂ d-ρ₁-ρ₂ ⊆-++₁' x∈Γ ρ₂x,c'∈sΓ

dom-ext-∈⁺ˡ : ∀ m Γ₁ Γ₂ →
  x ∈ dom Γ₁ →
  x ∈ dom (ext m Γ₁ Γ₂)
dom-ext-∈⁺ˡ m Γ₁ Γ₂ x∈Γ₁ = ≈ⁱ→⊆ (≈ⁱ-sym (dom-ext m Γ₁ Γ₂)) (AnyP.++⁺ˡ x∈Γ₁) 

domΓ₁⊆domΓ : ∀ Γ (e₁ : Expr alg) → dom (Γ ↓ fvs e₁) ⊆ⁱ dom Γ
domΓ₁⊆domΓ Γ e₁ =
  ↓-⊆ⁱdom Γ (fvs e₁)

domΓ₂⊆domΓ : ∀ Γ (e₂ : Expr alg) u → dom ((Γ ↓ fvs e₂) %ᶜ u) ⊆ⁱ dom Γ
domΓ₂⊆domΓ Γ e₂ u =
  subst (λ ■ → ■ ⊆ⁱ dom Γ) (sym (%ᶜ-dom (Γ ↓ fvs e₂) u)) $
  ↓-⊆ⁱdom Γ (fvs e₂)

lem' : ∀ {i} →
  (⊢e : Γ ⊢ e ∶[ i ] t ⍮ u ⍮ ϕ) →
  ∀ x {s} →
  x ∉ bvs e →
  u x ≡ some s →
  ∃[ b ] Σ[ s ∈ Session b ] (x , Chan b s) ∈ binds Γ
lem' (⊢`-chan {x = x} Γ≲x∶s refl) y y∉bvs eq
  with x ≟ y
… | no ¬x≡y with () ← eq
… | yes refl with refl ← eq = _ , _ , ≲-pres-∈' Γ≲x∶s (here refl)
lem' (⊢& {x = x} Γ≲x∶s₁++s₂ refl refl) y y∉bvs eq
  with x ≟ y
… | no ¬x≡y with () ← eq
… | yes refl with refl ← eq = _ , _ , ≲-pres-∈' Γ≲x∶s₁++s₂ (here refl)
lem' (⊢λ {x = x} {Γ = Γ} {m = m} {t₁ = t₁} x∉Γ ⊢e m≡∞→UnrΓ t₁≡Chan→ux ϕ₁⊑ϕ₂) y y∉bvs eq
  with x ≟ y
… | yes refl with () ← eq
… | no ¬x≡y 
  using b' , s' , y,s'∈[Γ,x∶t] ← lem' ⊢e y (∉-tail y∉bvs) eq
  with ∈-ext-inv m Γ (x ∶ t₁) y,s'∈[Γ,x∶t]
… | inj₁ y,s'∈Γ = b' , s' , y,s'∈Γ
… | inj₂ (here px) = ⊥-elim (¬x≡y (sym (ProdP.,-injectiveˡ px)))
lem' {Γ = Γ} (⊢·≻ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ splitsalg)
             y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | none with () ← eq
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  b' , s' , (↓-⊆ Γ (fvs e₂) $ %-∈-none (Γ ↓ fvs e₂) u₁ eq₁ y,s'∈)
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
lem' {Γ = Γ} (⊢·≺ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ splitsalg) y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | none with () ← eq
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  b' , s' , (↓-⊆ Γ (fvs e₂) $ %-∈-none (Γ ↓ fvs e₂) u₁ eq₁ y,s'∈)
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
lem' {Γ = Γ} (⊢·𝟙 {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ splitsalg) y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | none with () ← eq
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  b' , s' , (↓-⊆ Γ (fvs e₂) $ %-∈-none (Γ ↓ fvs e₂) u₁ eq₁ y,s'∈)
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
lem' {Γ = Γ} (⊢·∞ {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ splitsalg) y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | none with () ← eq
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  b' , s' , (↓-⊆ Γ (fvs e₂) $ %-∈-none (Γ ↓ fvs e₂) u₁ eq₁ y,s'∈)
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
lem' {Γ = Γ} (⊢, {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ splitsalg _) y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | none with () ← eq
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  b' , s' , (↓-⊆ Γ (fvs e₂) $ %-∈-none (Γ ↓ fvs e₂) u₁ eq₁ y,s'∈)
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
lem' {Γ = Γ} (⊢let {x = x} {e₁ = e₁} {t₁ = t₁} {u₁ = u₁} {e₂ = e₂} {C' = C'} {C = C} {u₂ = u₂}
                   x∉Γ refl ⊢e₁ Γ↓ refl ¬left→ϕ₁≡0 domC⊆domΓ ⊢e₂ t₁≡Chan→used salg)
             y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) $ ∉-tail y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  let y,s'∈C++x = ≈ⁱ→⊆ (binds-C C (x ∶ t₁)) y,s'∈ in
  case AnyP.++⁻ (binds (C [ · ])) y,s'∈C++x of λ where
    (inj₁ y,s'∈C) →
      let (b'' , s'' , y,s''∈) =
            foo u₁ (u₂ -ᵘ x) e₁ (e₂ ∷ []) Γ (Γ ↓ fvs e₁) C (x ∷ []) domC⊆domΓ salg y,s'∈C in
      b'' , s'' ,  y,s''∈ 
    (inj₂ y,s'∈x@(here eq)) →
      let y≡x , chanb's'≡t₁ = ProdP.,-injective eq in
      ⊥-elim (y∉bvs (here y≡x))
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
… | none | none
  with x ≟ y
… | yes refl with () ← eq
… | no ¬x≡y with () ← trans (sym eq) eq₂ 
lem' {Γ = Γ} (⊢let× {x = x₁} {y = x₂} {e₁ = e₁} {t₁ = t₁} {p = p} {t₂ = t₂} {u₁ = u₁}
                    {C = C} {e₂ = e₂} {C' = C'} {u₂ = u₂}
                   x₁∉Γ x₂∉Γ x₁≢x₂ refl ⊢e₁ ¬left→ϕ₁≡0 Γ↓ refl domC⊆domΓ ⊢e₂
                   t₁≡Chan→used t₂≡Chan→used salg)
             y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) $ ∉-tail $ ∉-tail y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  let y,s'∈C++xy = ≈ⁱ→⊆ (binds-C C (x₁ ∶ t₁ ⸴[ pmult→ord p ] x₂ ∶ t₂)) y,s'∈ in
  case AnyP.++⁻ (binds (C [ · ])) y,s'∈C++xy of λ where
    (inj₁ y,s'∈C) →
      let (b'' , s'' , y,s''∈) =
            foo u₁ (u₂ -ᵘ x₁ -ᵘ x₂) e₁ (e₂ ∷ []) Γ (Γ ↓ fvs e₁) C (x₁ ∷ x₂ ∷ [])
                domC⊆domΓ salg y,s'∈C in
      b'' , s'' ,  y,s''∈ 
    (inj₂ y,s'∈x@(here eq)) →
      let y≡x , chanb's'≡t₁ = ProdP.,-injective eq in
      ⊥-elim (y∉bvs (here y≡x))
    (inj₂ y,s'∈x@(there (here eq))) →
      let y≡x , chanb's'≡t₁ = ProdP.,-injective eq in
      ⊥-elim (y∉bvs (there (here y≡x)))
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
… | none | none
  with x₂ ≟ y
… | yes refl with () ← eq
… | no ¬x₂≡y
  with x₁ ≟ y
… | yes refl with () ← eq
… | no ¬x₁≡y with () ← trans (sym eq) eq₂ 
lem' (⊢inj ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' {Γ = Γ} (⊢case {x₁ = x₁} {x₂ = x₂} {e₁ = e₁} {t₁ = t₁} {t₂ = t₂} {u₁ = u₁}
                    {C = C} {e₂₁ = e₂₁} {e₂₂ = e₂₂} {C' = C'} {u₂₁ = u₂₁} {u₂₂ = u₂₂}
                    x₁∉Γ x₂∉Γ x₁≢x₂ refl ⊢e₁ ¬left→ϕ₁≡0 Γ↓ refl domC⊆domΓ ⊢e₂₁ ⊢e₂₂
                    u₂₁-x₁≡u₂₂-x₂ t₁≡Chan→used t₂≡Chan→used salg)
             y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂₁ ++ bvs e₂₂) $ ∉-tail $ ∉-tail y∉bvs
  using y∉bvs₂₁ , y∉bvs₂₂ ← ∉-++⁻ (bvs e₂₁) (bvs e₂₂) y∉bvs₂
  with u₁ y in eq₁ | u₂₁ y in eq₂
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂₁ y y∉bvs₂₁ eq₂ in
  let y,s'∈C++x = ≈ⁱ→⊆ (binds-C C (x₁ ∶ t₁)) y,s'∈ in
  case AnyP.++⁻ (binds (C [ · ])) y,s'∈C++x of λ where
    (inj₁ y,s'∈C) →
      let (b'' , s'' , y,s''∈) =
            foo u₁ (u₂₁ -ᵘ x₁) e₁ (e₂₁ ∷ e₂₂ ∷ []) Γ (Γ ↓ fvs e₁) C (x₁ ∷ x₂ ∷ [])
                domC⊆domΓ salg y,s'∈C in
      b'' , s'' ,  y,s''∈ 
    (inj₂ y,s'∈x@(here eq)) →
      let y≡x , chanb's'≡t₁ = ProdP.,-injective eq in
      ⊥-elim (y∉bvs (here y≡x))
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
… | none | none
  with x₁ ≟ y
… | yes refl with () ← eq
… | no ¬x₁≡y with () ← trans (sym eq) eq₂
lem' (⊢spawn ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' {Γ = Γ} (⊢send {e₁ = e₁} {u₁ = u₁} {e₂ = e₂} {u₂ = u₂} refl ⊢e₁ refl ⊢e₂ splitsalg) y y∉bvs eq
  using y∉bvs₁ , y∉bvs₂ ← ∉-++⁻ (bvs e₁) (bvs e₂) y∉bvs
  with u₁ y in eq₁ | u₂ y in eq₂
… | none | none with () ← eq
… | none | some s₁₂ rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₂ y y∉bvs₂ eq₂ in
  b' , s' , (↓-⊆ Γ (fvs e₂) $ %-∈-none (Γ ↓ fvs e₂) u₁ eq₁ y,s'∈)
… | some s₁₁ | none rewrite eq =
  let b' , s' , y,s'∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  b' , s' , ↓-⊆ Γ (fvs e₁) y,s'∈
… | some s₁₁ | some s₁₂ rewrite eq =
  let b'₁ , s'₁ , y,s'₁∈ = lem' ⊢e₁ y y∉bvs₁ eq₁ in
  let y,s'₁∈Γ = ↓-⊆ Γ (fvs e₁) y,s'₁∈ in
  b'₁ , s'₁ , y,s'₁∈Γ
lem' (⊢recv ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' (⊢select ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' (⊢branch ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' (⊢drop ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' (⊢close ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' (⊢∶ ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq
lem' (⊢chk-inf ⊢e) y y∉bvs eq = lem' ⊢e y y∉bvs eq

∈dom→∈⋯ : ∀ {b'} {s' : Session b'} Γ u →
  (x , Chan b' s') ∈ binds Γ →
  u x ≡ some (b , s) →
  (x , Chan b s) ∈ binds (Γ ⋯ᵘ u)
∈dom→∈⋯ {x = x} (.x ∶ t) u (here refl) eq
  with Chan? t
… | no ¬chan = ⊥-elim (¬chan (_ , _ , refl))
… | yes _ rewrite eq = here refl
∈dom→∈⋯ {x = x} (Γ₁ ⸴[ o ] Γ₂) u x∈Γ eq
  with AnyP.++⁻ (binds Γ₁) x∈Γ
… | inj₁ x∈Γ₁ = AnyP.++⁺ˡ (∈dom→∈⋯ Γ₁ u x∈Γ₁ eq)
… | inj₂ x∈Γ₂ = AnyP.++⁺ʳ _ (∈dom→∈⋯ Γ₂ u x∈Γ₂ eq)

⊧ˢ-splitₐ-binds⋯ : ∀ {x s₁ i} {u₁} Γ (e₁ : Expr alg) (e₂s : List (Expr alg)) →
  let sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ varss e₂s) in
  Disjoint (bvs e₁) (fvs e₁) →
  binds Γ₁ ⊆ binds Γ →
  (Γ₁ ⊢ e₁ ∶[ i ] t₁ ⍮ u₁ ⍮ ϕ) →
  (x , s₁) ∈ sis →
  ∃[ b ] Σ[ s₂ ∈ Session b ] (x , Chan _ (s₁ ++ˢ s₂)) ∈ binds (Γ ⋯ᵘ u₁ ·ᵘ u₂)
⊧ˢ-splitₐ-binds⋯ {Γ₁ = Γ₁} {u₂ = u₂} {x = x} {s₁ = s₁} {u₁ = u₁}
                 Γ e₁ e₂s bvs⊎fvs Γ₁⊆Γ ⊢e₁ x,s₁∈sisₐ
  using sis ← (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁
  using ρ₁ , ρ₂ ← split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ varss e₂s)
  using (x∈fvs , eq) ← ↓ᵘ-∈⁻ (fvs e₁ ∩ˡ fvss e₂s) u₁ x,s₁∈sisₐ
  using x∈fvs₁ , _ ← ∩ˡ-∈⁻ (fvs e₁) (fvss e₂s) x∈fvs
  using b' , s' , x∈Γ₁ ← lem' ⊢e₁ x (Disjoint-sym bvs⊎fvs x x∈fvs₁) eq
  using x∈Γ ← Γ₁⊆Γ x∈Γ₁
  with ·ᵘ-some₁ u₁ u₂ x eq
… | inj₁ eq₁₂ =
    let x,s₁∈Γ⋯ = ∈dom→∈⋯ Γ (u₁ ·ᵘ u₂) x∈Γ eq₁₂ in
    let x,s₁++return∈Γ⋯ = subst (λ ■ → (x , ■) ∈ binds (Γ ⋯ᵘ u₁ ·ᵘ u₂))
                                (cong (Chan borrowed) (sym (++ˢ-neutralʳ s₁)))
                                x,s₁∈Γ⋯ in
    _ , return , x,s₁++return∈Γ⋯
… | inj₂ (b₂ , s₂ , eq₂ , eq₁₂) =
    let x,s₁∈Γ⋯ = ∈dom→∈⋯ Γ (u₁ ·ᵘ u₂) x∈Γ eq₁₂ in
    b₂ , s₂ , x,s₁∈Γ⋯

⊧ˢ-splitₐ : ∀ {i ϕ Γ₁} Γ (e₁ : Expr alg) (e₂s : List (Expr alg)) u₁ u₂ →
  let sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) (dom Γ ++ vars e₁ ++ varss e₂s) in
  Disjoint (bvs e₁) (fvs e₁) →
  binds Γ₁ ⊆ binds Γ →
  (Γ₁ ⊢ e₁ ∶[ i ] t₁ ⍮ u₁ ⍮ ϕ) →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ (Γ ⋯ᵘ u₁ ·ᵘ u₂)
⊧ˢ-splitₐ Γ e₁ e₂s u₁ u₂ bvs⊎fvs Γ₁⊆Γ ⊢e₁ = record
  { ⊧ˢ-binds = ⊧ˢ-splitₐ-binds⋯ Γ e₁ e₂s bvs⊎fvs Γ₁⊆Γ ⊢e₁
  ; ⊧ˢ-vars-unique =
      let
        sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁
        vs = dom Γ ++ vars e₁ ++ varss e₂s
        ρ₁ , ρ₂ = split-rens (map proj₁ sis) vs
        xs = map proj₁ sis
        U-xs : Unique xs
        U-xs = Unique-sisₐ e₁ e₂s u₁
        U-ρ₁xs++ρ₂xs = split-rens-unique xs vs U-xs
        d₁ : Disjoint xs (map ρ₁ xs ++ map ρ₂ xs)
        d₁ = Disjoint-⊆₁ (sis⊆ Γ e₁ e₂s u₁) (Disjoint-sym (split-rens-disjoint xs vs U-xs))
      in
      Unique (xs ++ map ρ₁ xs ++ map ρ₂ xs) by
      Unique-++ U-xs U-ρ₁xs++ρ₂xs d₁ 
  ; ⊧ˢ-newvars-disjoint =
      let
        sis = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁
        vs = dom Γ ++ vars e₁ ++ varss e₂s
        ρ₁ , ρ₂ = split-rens (map proj₁ sis) vs
        xs = map proj₁ sis
        U-xs : Unique xs
        U-xs = Unique-sisₐ e₁ e₂s u₁
        d₁ : Disjoint (map ρ₁ xs ++ map ρ₂ xs) vs
        d₁ = split-rens-disjoint xs vs U-xs
        sub : dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ⊆ vs
        sub =
          let open ⊆-Reasoning in
          begin
            dom (Γ ⋯ᵘ u₁ ·ᵘ u₂)
          ≡⟨ ⋯ᵘ-dom Γ (u₁ ·ᵘ u₂) ⟩
            dom Γ
          ⊆⟨ ⊆-++₁' ⟩
            dom Γ ++ vars e₁ ++ varss e₂s
          ∎
      in
      Disjoint (map ρ₁ xs ++ map ρ₂ xs) (dom (Γ ⋯ᵘ u₁ ·ᵘ u₂)) by
      Disjoint-⊆₂ sub d₁
  }

⊧ˢ-split : ∀ {dom-ρ ρ i} Γ (e₁ : Expr alg) (e₂s : List (Expr alg)) u₁ u₂ extra →
  Disjoint (bvs e₁) (fvs e₁) →
  (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  let sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ in
  let ρ₁ , ρ₂ = split-rens (map proj₁ sis) ((dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ) in
  binds Γ₁ ⊆ binds Γ →
  (Γ₁ ⊢ e₁ ∶[ i ] t₁ ⍮ u₁ ⍮ ϕ) →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ)
⊧ˢ-split {dom-ρ = dom-ρ} {ρ = ρ} Γ e₁ e₂s u₁ u₂ extra bvs⊎fvs ⊢ρ Γ₁⊆Γ ⊢e₁ = record
  { ⊧ˢ-binds            = λ {x} {s₁} x,s₁∈sis →
      let (x' , s') , x'∈sisₐ , ρx's'≡x,s₁ =
            map-∈-inv (map₁ ρ) ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) x,s₁∈sis  in
      let b₂ , s₂ , x',s'++s₂∈Γ⋯ = ⊧ˢ-splitₐ-binds⋯ {u₂ = u₂} Γ e₁ e₂s bvs⊎fvs Γ₁⊆Γ ⊢e₁ x'∈sisₐ in
      let ρx'≡x = ProdP.,-injectiveˡ ρx's'≡x,s₁ in
      let s'≡s₁ = ProdP.,-injectiveʳ ρx's'≡x,s₁ in
      let ∈₁ : (ρ x' , Chan b₂ (s' ++ˢ s₂)) ∈ map (map₁ ρ) (binds (Γ ⋯ᵘ u₁ ·ᵘ u₂))
          ∈₁ = ∈-map (map₁ ρ) x',s'++s₂∈Γ⋯ in
      let ∈₂ : (x , Chan b₂ (s₁ ++ˢ s₂)) ∈ map (map₁ ρ) (binds (Γ ⋯ᵘ u₁ ·ᵘ u₂))
          ∈₂ = subst₂ (λ ■₁ ■₂ → (■₁ , Chan b₂ (■₂ ++ˢ s₂)) ∈
                                 map (map₁ ρ) (binds (Γ ⋯ᵘ u₁ ·ᵘ u₂)))
                      ρx'≡x s'≡s₁ ∈₁ in
      let ∈₃ : (x , Chan b₂ (s₁ ++ˢ s₂)) ∈ binds (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ)
          ∈₃ = subst ((x , Chan b₂ (s₁ ++ˢ s₂)) ∈_)
                     (sym (⋯ʳ-binds-eq (Γ ⋯ᵘ u₁ ·ᵘ u₂) ρ))
                     ∈₂ in
      b₂ , s₂ , ∈₃
  ; ⊧ˢ-vars-unique      =
      let
        sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ
        vs = (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
        ρ₁ , ρ₂ = split-rens (map proj₁ sis) vs
        xs = map proj₁ sis
        U-xs : Unique xs
        U-xs = Unique-sis-extra Γ e₁ e₂s u₁ extra ⊢ρ
        U-ρ₁xs++ρ₂xs = split-rens-unique xs vs U-xs
        d₁ : Disjoint xs (map ρ₁ xs ++ map ρ₂ xs)
        d₁ = Disjoint-⊆₁ (sis⊆ρ-extra Γ e₁ e₂s u₁ extra ⊢ρ) (Disjoint-sym (split-rens-disjoint xs vs U-xs))
      in
      Unique (xs ++ map ρ₁ xs ++ map ρ₂ xs) by
      Unique-++ U-xs U-ρ₁xs++ρ₂xs d₁ 
  ; ⊧ˢ-newvars-disjoint =
      let
        sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ
        vs = (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
        ρ₁ , ρ₂ = split-rens (map proj₁ sis) vs
        xs = map proj₁ sis
        U-xs : Unique xs
        U-xs = Unique-sis-extra Γ e₁ e₂s u₁ extra ⊢ρ
        d₁ : Disjoint (map ρ₁ xs ++ map ρ₂ xs) vs
        d₁ = split-rens-disjoint xs vs U-xs
        sub : dom (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ) ⊆ vs
        sub =
          let open ⊆-Reasoning in
          begin
            dom (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ)
          ≡⟨ ⋯ʳ-dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ρ ⟩
            map ρ (dom (Γ ⋯ᵘ u₁ ·ᵘ u₂))
          ≡⟨ cong (map ρ) (⋯ᵘ-dom Γ (u₁ ·ᵘ u₂)) ⟩
            map ρ (dom Γ)
          ⊆⟨ ⊆-++₁' ⟩
            map ρ (dom Γ) ++ map ρ (extra ++ vars e₁ ++ varss e₂s)
          ≡⟨ sym (ListP.map-++ ρ (dom Γ) (extra ++ vars e₁ ++ varss e₂s)) ⟩
            map ρ (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
          ⊆⟨ ⊢ʳ-ρys⊆ys++ρxs ⊢ρ ⟩
            (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ
          ∎
      in
      Disjoint (map ρ₁ xs ++ map ρ₂ xs) (dom (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ)) by
      Disjoint-⊆₂ sub d₁
  }

⊢split₁ : ∀ {o} {s₂ : Session o} {e : Expr log} →
  x₁ ∉ dom (C [ x ∶ Chan o (s₁ ++ˢ s₂) ]) →
  x₂ ∉ dom (C [ x ∶ Chan o (s₁ ++ˢ s₂) ]) →
  x₁ ≢ x₂ →
  (C [ (x₁ ∶ Chan borrowed s₁) ⸴ (x₂ ∶ Chan o s₂) ]) ⊢ e ∶ t ⍮ ϕ →
  (C [ x ∶ Chan o (s₁ ++ˢ s₂) ]) ⊢ let[ x₁ `, x₂ ≔ split[ s₁ ] (` x) ]in e ∶ t ⍮ ϕ
⊢split₁ x₁∉ x₂∉ x₁≢x₂ ⊢e = ⊢let× refl x₁∉ x₂∉ x₁≢x₂ (⊢split refl (⊢` ≲-refl)) (λ _ → refl) ⊢e

⊢splitₙ : ∀ {e : Expr log} (sis : List (Id × SessionB)) →
  Unique (dom Γ) →
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γ →
  split-ctx sis ρ₁ ρ₂ Γ ⊢ e ∶ t ⍮ ϕ →
  Γ ⊢ splitsₙ sis ρ₁ ρ₂ e ∶ t ⍮ ϕ
⊢splitₙ []       U-Γ sis⊧Γ ⊢e =
  subst (_⊢ _ ∶ _ ⍮ _) (split-ctx-[] _) ⊢e
⊢splitₙ {Γ = Γ} {ρ₁ = ρ₁} {ρ₂ = ρ₂} ((x , s₁) ∷ sis) U-Γ sis⊧Γ ⊢e =
  let b , s₂ , x∶s∈Γ = ⊧ˢ-binds sis⊧Γ (here refl) in
  let C , eq-Γ = ∈binds→C Γ x∶s∈Γ in
  let eq-sΓ = split-ctx-∈ ρ₁ ρ₂ x s₁ s₂ Γ C U-Γ eq-Γ in
  let si = (x , s₁) in
  let ⊢e₁ = subst (_⊢ _ ∶ _ ⍮ _)
                  (split-ctx-++ (si ∷ []) sis ρ₁ ρ₂ Γ (⊧ˢ-vars-unique sis⊧Γ))
                  ⊢e in
  let ⊢e₂ = ⊢splitₙ {Γ = split-ctx ((x , s₁) ∷ []) ρ₁ ρ₂ Γ}
                    sis
                    (split-ctx-Unique si Γ ((⊧ˢ-head si sis sis⊧Γ)) U-Γ)
                    (⊧ˢ-split₁ si sis sis⊧Γ) ⊢e₁ in
  let ⊢e₃ = subst (_⊢ _ ∶ _ ⍮ _) eq-sΓ ⊢e₂ in
  let x₁∉domC[x] = subst (λ ■ → ρ₁ x ∉ dom ■)
                         eq-Γ
                         (⊧ˢ-newvars-disjoint sis⊧Γ (ρ₁ x) (here refl)) in
  let x₂∉domC[x] = subst (λ ■ → ρ₂ x ∉ dom ■)
                         eq-Γ
                         (Disjoint-⊆₁ (⊆-++₂' (map ρ₁ (map proj₁ (si ∷ sis))))
                                      (⊧ˢ-newvars-disjoint sis⊧Γ) (ρ₂ x) (here refl)) in
  let ⊢e₄ = ⊢split₁ x₁∉domC[x] x₂∉domC[x] (⊧ˢ-ρ₁x≢ρ₂ sis⊧Γ (here refl)) ⊢e₃ in
  let ⊢e₅ = subst (_⊢ _ ∶ _ ⍮ _) (sym eq-Γ) ⊢e₄ in
  ⊢e₅

⊢splits' : ∀ {Γ Γ₁ C u₁ u₂ t₁ ϕ₁ ϕ dom-ρ ρ i₁ e} e₂s extra →
             (⊢e₁ : Γ₁ ⊢ e₁ ∶[ i₁ ] t₁ ⍮ u₁ ⍮ ϕ₁) →
  Disjoint (bvs e₁) (fvs e₁) →
  binds Γ₁ ⊆ binds Γ →
  dom (C [ · ]) ⊆ dom Γ →
  let Γx = (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ in
  Unique (dom Γ) →
  (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) % dom-ρ ⊢ʳ ρ →
  let vs = (dom Γ ++ extra ++ vars e₁ ++ varss e₂s) ++ codʳ dom-ρ ρ in
  let sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ in
  let (ρ₁ , ρ₂) = split-rens (map proj₁ sis) vs in
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γx →
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvss e₂s) u₁ (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
               dom-ρ ρ Γ₁ (C [ · ]) in
  SplitsAlg' u₁ u₂ e₁ e₂s Γ Γ₁ C extra →
  (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ρ₂) [ (Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁ ]) ⊢ e ∶ t ⍮ ϕ →
  ((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E e ∶ t ⍮ ϕ
⊢splits' {e₁ = e₁} {Γ = Γ} {Γ₁ = Γ₁} {C = C} {u₁ = u₁}
         {u₂ = u₂} {dom-ρ = dom-ρ} {ρ = ρ} {e = e}
         e₂s extra ⊢e₁ bvs⊎fvs Γ₁⊆Γ dΓ₂⊆dΓ U-Γ ⊢ρ sis⊧ˢΓx Γ≲ ⊢F =
  let sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ in
  let (ρ₁ , ρ₂) = split-rens (map proj₁ sis) vs in
  let ρ₁ = ρ₁ ↓ʳ fvs e₁ in
  let ρ₂ = ρ₂ ↓ʳ fvss e₂s in
  let E = splitsₙ sis ρ₁ ρ₂ in
  -- This is a different E... (because of vs)
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvss e₂s) u₁ (dom Γ ++ extra ++ (vars e₁ ++ varss e₂s))
               dom-ρ ρ Γ₁ (C [ · ]) in
  ⊢splitₙ sis U-Γx sis⊧ˢΓx $ ⊢wk q₂ ⊑-refl ⊢F
  where
    vs = (dom Γ ++ extra ++ (vars e₁ ++ varss e₂s)) ++ codʳ dom-ρ ρ
    Γx = (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ
    U-Γ⋯ : Unique (dom (Γ ⋯ᵘ u₁ ·ᵘ u₂))
    U-Γ⋯ = subst Unique (sym (⋯ᵘ-dom Γ (u₁ ·ᵘ u₂))) U-Γ
    sub : dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
    sub =
      let open ⊆-Reasoning in
      begin
        dom (Γ ⋯ᵘ u₁ ·ᵘ u₂)
      ≡⟨ ⋯ᵘ-dom Γ (u₁ ·ᵘ u₂) ⟩
        dom Γ
      ⊆⟨ ⊆-++₁' ⟩
        dom Γ ++ extra ++ vars e₁ ++ varss e₂s
      ∎
    U-Γx : Unique (dom (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ))
    U-Γx = ⋯ʳ-unique-dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ρ (Injectiveʳ-⊆ sub (⊢ʳ-inj-ys-ρ ⊢ρ)) U-Γ⋯
    q₂ : let sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ in
         let ρ₁ , ρ₂ = split-rens (map proj₁ sis) vs in
         split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ) ≲
         (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ((ρ ·ʳ ρ₂) ↓ʳ dom (C [ · ]))) [
           (Γ₁ ⋯ᵘ u₁) ⋯ʳ ((ρ ·ʳ ρ₁) ↓ʳ dom Γ₁)
         ])
    q₂ = let
           dΓ₁⊆dΓ : dom Γ₁ ⊆ dom Γ
           dΓ₁⊆dΓ = ⊆binds→⊆dom Γ₁ Γ Γ₁⊆Γ
           sis = ((fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁) ⋯ˢⁱ ρ
           ρ₁ , ρ₂ = split-rens (map proj₁ sis) vs
           sisₐ = (fvs e₁ ∩ˡ fvss e₂s) ↓ᵘ u₁
           ρ₁ₐ , ρ₂ₐ = split-rens (map proj₁ sisₐ) (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
           ρ' = split-replaceʳ (map proj₁ sisₐ) (map proj₁ sisₐ) ρ₁ₐ ρ₂ₐ ρ₁ ρ₂ ρ
           sisₐ⊧ = ⊧ˢ-splitₐ Γ e₁ e₂s u₁ u₂ bvs⊎fvs Γ₁⊆Γ ⊢e₁
           U-fvse₁∩fvse₂ = ∩ˡ-unique (fvs e₁) (fvss e₂s)
           U-sisₐ₁ = ↓ᵘ-pres-Unique (fvs e₁ ∩ˡ fvss e₂s) u₁ U-fvse₁∩fvse₂
           ρ-⊆ : dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ++ map proj₁ sisₐ ⊆
                 dom Γ ++ extra ++ vars e₁ ++ varss e₂s
           ρ-⊆ =
             let open ⊆-Reasoning in
             begin
               dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ++ map proj₁ sisₐ
             ≡⟨ cong (_++ _) (⋯ᵘ-dom Γ (u₁ ·ᵘ u₂)) ⟩
               dom Γ ++ map proj₁ sisₐ
             ⊆⟨ ⊆-++ (⊆-refl {xs = dom Γ}) (↓ᵘ-⊆ (fvs e₁ ∩ˡ fvss e₂s) u₁) ⟩
               dom Γ ++ (fvs e₁ ∩ˡ fvss e₂s)
             ⊆⟨ ⊆-++ (⊆-refl {xs = dom Γ}) (∩ˡ-⊆₁ (fvs e₁) (fvss e₂s)) ⟩
               dom Γ ++ fvs e₁
             ⊆⟨ ⊆-++ (⊆-refl {xs = dom Γ}) (fvs⊆vars e₁) ⟩
               dom Γ ++ vars e₁
             ⊆⟨ ⊆-++ (⊆-++₁' {xs₁ = dom Γ}) ⊆-++₁' ⟩
               (dom Γ ++ extra) ++ vars e₁ ++ varss e₂s
             ≈⟨ ≈ˡ-assoc (dom Γ) extra (vars e₁ ++ varss e₂s) ⟩
               dom Γ ++ extra ++ vars e₁ ++ varss e₂s
             ∎
           inj-ρ = Injectiveʳ-⊆ ρ-⊆ (⊢ʳ-inj-ys-ρ ⊢ρ)
           lemx : ∀ x t (s₁ : SessionB) →
                  (x , t) ∈ binds (Γ ⋯ᵘ u₁ ·ᵘ u₂) →
                  (x , s₁) ∈ sisₐ →
                  ∃[ b ] Σ[ s₂ ∈ Session b ] t ≡ Chan b (s₁ ++ˢ s₂)
           lemx = λ x t s₁ x,t∈Γ⋯ᵘ x,s₁∈sisₐ →
                    -- let b , s₂ , x,chan∈ = ⊧ˢ-binds sis⊧ˢΓx {!x,s₁∈sisₐ!} in
                    let b , s₂ , x,chan∈ = ⊧ˢ-binds sisₐ⊧ x,s₁∈sisₐ in
                    let t≡s₁++s₂ = ∈binds-Unique (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) U-Γ⋯ x,t∈Γ⋯ᵘ x,chan∈ in
                    b , s₂ , t≡s₁++s₂
           sis⊆' : map proj₁ sisₐ ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
           sis⊆' = ⊆-trans (sis⊆ Γ e₁ e₂s u₁)
                           (⊆-++ (⊆-refl {xs = dom Γ}) (⊆-++₂' extra))
           (⊢ρ₁' , ⊢ρ₂' , d-ρᵢ'-ys) =
             ⊢ʳ-split-rens (map proj₁ sisₐ) (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
                           sis⊆' U-sisₐ₁
           (⊢ρ₁ , ⊢ρ₂ , d-ρᵢ-ys) =
             ⊢ʳ-split-rens (map proj₁ sis) vs
                           (sis⊆ρ-extra Γ e₁ e₂s u₁ extra ⊢ρ)
                           (Unique-sis-extra Γ e₁ e₂s u₁ extra ⊢ρ)
           u-ρᵢ' = split-rens-unique (map proj₁ sisₐ) (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
                                     U-sisₐ₁
           u-ρ₁' , u-ρ₂' , d-ρ₁'-ρ₂' =
             Unique-++⁻ (map ρ₁ₐ (map proj₁ sisₐ)) (map ρ₂ₐ (map proj₁ sisₐ)) u-ρᵢ'
           sub₁ : dom (Γ ⋯ᵘ u₁ ·ᵘ u₂) ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
           sub₁ =
             let open ⊆-Reasoning in
             begin
               dom (Γ ⋯ᵘ u₁ ·ᵘ u₂)
             ≡⟨ ⋯ᵘ-dom Γ (u₁ ·ᵘ u₂)  ⟩
               dom Γ
             ⊆⟨ ⊆-++₁' ⟩
               dom Γ ++ extra ++ vars e₁ ++ varss e₂s
             ∎
           sub₂ : dom (Γ₁ ⋯ᵘ u₁) ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
           sub₂ =
             let open ⊆-Reasoning in
             begin
               dom (Γ₁ ⋯ᵘ u₁)
             ≡⟨ ⋯ᵘ-dom Γ₁ u₁  ⟩
               dom Γ₁
             ⊆⟨ dΓ₁⊆dΓ ⟩
               dom Γ
             ⊆⟨ ⊆-++₁' ⟩
               dom Γ ++ extra ++ vars e₁ ++ varss e₂s
             ∎
           sub₃ : dom ((C ⋯ᵘᶜ u₂) [ · ]) ⊆ dom Γ ++ extra ++ vars e₁ ++ varss e₂s
           sub₃ =
             let open ⊆-Reasoning in
             begin
               dom ((C ⋯ᵘᶜ u₂) [ · ])
             ≡⟨ cong dom (sym (⋯ᵘ-dist-[] C · u₂)) ⟩
               dom ((C [ · ]) ⋯ᵘ u₂)
             ≡⟨ ⋯ᵘ-dom (C [ · ]) u₂  ⟩
               dom (C [ · ])
             ⊆⟨ dΓ₂⊆dΓ ⟩
               dom Γ
             ⊆⟨ ⊆-++₁' ⟩
               dom Γ ++ extra ++ vars e₁ ++ varss e₂s
             ∎
         in
         let open ≲-Reasoning in
         begin
           split-ctx sis ρ₁ ρ₂ (Γ ⋯ᵘ u₁ ·ᵘ u₂ ⋯ʳ ρ)
         ≡⟨ split-ctx-ren ρ (fvs e₁ ∩ˡ fvss e₂s) u₁ vs
                          (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
                          (Γ ⋯ᵘ u₁ ·ᵘ u₂) U-sisₐ₁ inj-ρ
                          (Disjoint-⊆₁ sub₁ (Disjoint-sym d-ρᵢ'-ys)) lemx
          ⟩
           split-ctx sisₐ ρ₁ₐ ρ₂ₐ (Γ ⋯ᵘ u₁ ·ᵘ u₂) ⋯ʳ ρ'
         ≲⟨ ≲-⋯ʳ ρ' Γ≲ ⟩
           ((C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂ₐ) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ₐ ]) ⋯ʳ ρ'
         ≡⟨ ⋯ʳ-dist-[] (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂ₐ) (Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ₐ) ρ'  ⟩
           (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂ₐ ⋯ʳᶜ ρ') [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ₐ ⋯ʳ ρ' ]
         ≡⟨ cong₂ _[_] (sym (⋯ʳᶜ-·ʳ (C ⋯ᵘᶜ u₂) ρ₂ₐ ρ')) (sym (⋯ʳ-·ʳ (Γ₁ ⋯ᵘ u₁) ρ₁ₐ ρ')) ⟩
           (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ₂ₐ ·ʳ ρ') [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ₁ₐ ·ʳ ρ' ]
         ≡⟨ cong₂ _[_] (⋯ʳᶜ-locally-eq (C ⋯ᵘᶜ u₂) (ρ₂ₐ ·ʳ ρ') (ρ ·ʳ ρ₂)
                         (LocallyEq-⊆ sub₃
                           (split-replaceʳ-lem₂x
                             (map proj₁ sisₐ)
                             (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
                             dom-ρ ρ₁ₐ ρ₂ₐ ρ₁ ρ₂ ρ ⊢ρ₁' ⊢ρ₂' ⊢ρ
                             (subst (vs %_⊢ʳ ρ₂) (map-proj₁ ρ sisₐ) ⊢ρ₂)
                             d-ρ₁'-ρ₂')))
                       (⋯ʳ-locally-eq (Γ₁ ⋯ᵘ u₁) (ρ₁ₐ ·ʳ ρ') (ρ ·ʳ ρ₁)
                         (LocallyEq-⊆ sub₂
                           (split-replaceʳ-lem₁x
                             (map proj₁ sisₐ)
                             (dom Γ ++ extra ++ vars e₁ ++ varss e₂s)
                             dom-ρ ρ₁ₐ ρ₂ₐ ρ₁ ρ₂ ρ ⊢ρ₁' ⊢ρ₂' ⊢ρ
                             (subst (vs %_⊢ʳ ρ₁) (map-proj₁ ρ sisₐ) ⊢ρ₁)))) ⟩
           (C ⋯ᵘᶜ u₂ ⋯ʳᶜ ρ ·ʳ ρ₂) [ Γ₁ ⋯ᵘ u₁ ⋯ʳ ρ ·ʳ ρ₁ ]
         ≡⟨ cong₂ _[_] (⋯ʳᶜ-locally-eq (C ⋯ᵘᶜ u₂) (ρ ·ʳ ρ₂) ((ρ ·ʳ ρ₂) ↓ʳ dom (C [ · ]))
                    (subst (λ ■ → LocallyEq ■ (ρ ·ʳ ρ₂) ((ρ ·ʳ ρ₂) ↓ʳ dom (C [ · ])))
                           (trans (sym (⋯ᵘ-dom (C [ · ]) u₂))
                                  (cong dom (⋯ᵘ-dist-[] C · u₂)))
                           (↓ʳ-eq (ρ ·ʳ ρ₂) (dom (C [ · ])))))
                       (⋯ʳ-locally-eq (Γ₁ ⋯ᵘ u₁) (ρ ·ʳ ρ₁) ((ρ ·ʳ ρ₁) ↓ʳ dom Γ₁)
                         (subst (λ ■ → LocallyEq ■ (ρ ·ʳ ρ₁) ((ρ ·ʳ ρ₁) ↓ʳ dom Γ₁))
                           (sym (⋯ᵘ-dom Γ₁ u₁))
                           (↓ʳ-eq (ρ ·ʳ ρ₁) (dom Γ₁)))) ⟩
           (((C ⋯ᵘᶜ u₂) ⋯ʳᶜ ((ρ ·ʳ ρ₂) ↓ʳ dom (C [ · ]))) [
             (Γ₁ ⋯ᵘ u₁) ⋯ʳ ((ρ ·ʳ ρ₁) ↓ʳ dom Γ₁)
           ])
         ∎

⊢splits : ∀ {Γ Γ₁ u₁ Γ₂ u₂ t₁ t₂ ϕ₁ ϕ dom-ρ ρ i₁ i₂} →
            (F : Expr log → Expr log → Expr log) →
            (⊢e₁ : Γ₁ ⊢ e₁ ∶[ i₁ ] t₁ ⍮ u₁ ⍮ ϕ₁) →
            (⊢e₂ : Γ₂ ⊢ e₂ ∶[ i₂ ] t₂ ⍮ u₂ ⍮ ϕ₂) →
  Disjoint (bvs e₁) (fvs e₁) →
  binds Γ₁ ⊆ binds Γ →
  dom Γ₂ ⊆ dom Γ →
  let Γx = (Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ in
  Unique (dom Γ) →
  (dom Γ ++ (vars e₁ ++ vars e₂)) % dom-ρ ⊢ʳ ρ →
  let vs = (dom Γ ++ (vars e₁ ++ vars e₂)) ++ codʳ dom-ρ ρ in
  let sis = ((fvs e₁ ∩ˡ fvs e₂) ↓ᵘ u₁) ⋯ˢⁱ ρ in
  let (ρ₁ , ρ₂) = split-rens (map proj₁ sis) vs in
  sis ⊧ˢ ρ₁ ⍮ ρ₂ ⍮ Γx →
  let (dom-ρ₁ , ρ₁ , dom-ρ₂ , ρ₂ , E) =
        splits (fvs e₁) (fvs e₂) u₁ (dom Γ ++ (vars e₁ ++ vars e₂)) dom-ρ ρ Γ₁ Γ₂ in
  SplitsAlg u₁ u₂ e₁ e₂ Γ Γ₁ Γ₂ o →
  (((Γ₁ ⋯ᵘ u₁) ⋯ʳ ρ₁) ⸴[ o ] ((Γ₂ ⋯ᵘ u₂) ⋯ʳ ρ₂)) ⊢ F (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂) ∶ t ⍮ ϕ →
  ((Γ ⋯ᵘ (u₁ ·ᵘ u₂)) ⋯ʳ ρ) ⊢ E (F (⟪ ⊢e₁ ⟫ dom-ρ₁ ρ₁) (⟪ ⊢e₂ ⟫ dom-ρ₂ ρ₂)) ∶ t ⍮ ϕ
⊢splits {e₁ = e₁} {e₂ = e₂} {o = o} {Γ = Γ} {Γ₁ = Γ₁} {u₁ = u₁} {Γ₂ = Γ₂}
        {u₂ = u₂} {dom-ρ = dom-ρ} {ρ = ρ} F ⊢e₁ ⊢e₂ bvs⊎fvs Γ₁⊆Γ dΓ₂⊆dΓ U-Γ ⊢ρ sis⊧ˢΓx Γ≲ ⊢F =
  ⊢splits' {e₁ = e₁} {Γ = Γ} {Γ₁ = Γ₁} {C = [] ⸴[ o ]₁ Γ₂} {u₁ = u₁}
           {u₂ = u₂} {dom-ρ = dom-ρ} {ρ = ρ}
           (e₂ ∷ []) [] ⊢e₁ bvs⊎fvs Γ₁⊆Γ dΓ₂⊆dΓ U-Γ ⊢ρ sis⊧ˢΓx Γ≲ ⊢F  


