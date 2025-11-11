{-# OPTIONS --allow-unsolved-metas #-}

module LawAndOrder.Util.Graph where

open import Data.Nat as ℕ using (ℕ; suc; zero)
import Data.Nat.Properties as ℕP
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as FinP
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Level using (Level; _⊔_; 0ℓ) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst; subst₂; module ≡-Reasoning)
open import Relation.Binary.HeterogeneousEquality as H using (_≅_; refl; module ≅-Reasoning)
open import Function using (_$_)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Data.List using (List; []; _∷_)

cong₃ : ∀ {a b c d} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d} {x y u v q p}
        (f : (x : A) (y : B x) (z : C x y) → D x y z) → x ≅ y → u ≅ v → p ≅ q → f x u p ≅ f y v q
cong₃ f refl refl refl = refl

cong₄ : ∀ {a b c d e}
          {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c} {D : ∀ x → (y : B x) → C x y → Set d}
          {E : ∀ x → (y : B x) → (z : C x y) → D x y z → Set e}
          {x y u v q p r s}
        (f : (x : A) (y : B x) (z : C x y) (w : D x y z) → E x y z w) → x ≅ y → u ≅ v → p ≅ q → r ≅ s → f x u p r ≅ f y v q s
cong₄ f refl refl refl refl = refl

variable
  ℓ ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ' : Level
  A B C D A' B' C' D' : Set ℓ

variable
  L L₁ L₂ : Set ℓ
  N N₁ N₂ : Set ℓ

record Graph (Label : Set ℓ) : Set (ℓ ⊔ lsuc 0ℓ) where
  constructor graph
  field
    Node  : Set
    Edge  : Node → Node → Set
    label : Node → Label

open Graph public

∅ : Graph L
∅ = graph ⊥ (λ ()) (λ ())

[_] : L → Graph L
[ l ] = graph ⊤ (λ _ _ → ⊥) λ _ → l

_∪ₑ_ : (N₁ → N₁ → Set) → (N₂ → N₂ → Set) → (N₁ ⊎ N₂ → N₁ ⊎ N₂ → Set)
(e₁ ∪ₑ e₂) (inj₁ n₁) (inj₁ n₁') = e₁ n₁ n₁'
(e₁ ∪ₑ e₂) (inj₁ n₁) (inj₂ n₂') = ⊥
(e₁ ∪ₑ e₂) (inj₂ n₂) (inj₁ n₁') = ⊥
(e₁ ∪ₑ e₂) (inj₂ n₂) (inj₂ n₂') = e₂ n₂ n₂'

_+ₑ_ : (N₁ → N₁ → Set) → (N₂ → N₂ → Set) → (N₁ ⊎ N₂ → N₁ ⊎ N₂ → Set)
(e₁ +ₑ e₂) (inj₁ n₁) (inj₁ n₁') = e₁ n₁ n₁'
(e₁ +ₑ e₂) (inj₁ n₁) (inj₂ n₂') = ⊤
(e₁ +ₑ e₂) (inj₂ n₂) (inj₁ n₁') = ⊥
(e₁ +ₑ e₂) (inj₂ n₂) (inj₂ n₂') = e₂ n₂ n₂'

_∪ₗ_ : (N₁ → L) → (N₂ → L) → (N₁ ⊎ N₂ → L)
(l₁ ∪ₗ l₂) (inj₁ n₁) = l₁ n₁
(l₁ ∪ₗ l₂) (inj₂ n₂) = l₂ n₂

_∪_ : Graph L → Graph L → Graph L
g₁ ∪ g₂ = graph (Node g₁ ⊎ Node g₂) (Edge g₁ ∪ₑ Edge g₂) (label g₁ ∪ₗ label g₂)

_+_ : Graph L → Graph L → Graph L
g₁ + g₂ = graph (Node g₁ ⊎ Node g₂) (Edge g₁ +ₑ Edge g₂) (label g₁ ∪ₗ label g₂)

module Type where
  infix 4 _≃_
  record _≃_ (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
    field
      to : A → B
      from : B → A
      from∘to : ∀ x → from (to x) ≡ x
      to∘from : ∀ x → to (from x) ≡ x

  module ≃ = _≃_

  ≃-refl : A ≃ A
  ≃-refl = record
    { to      = λ x → x
    ; from    = λ x → x
    ; from∘to = λ x → refl
    ; to∘from = λ x → refl
    }

  ≃-sym : A ≃ B → B ≃ A
  ≃-sym A≃B = record
    { to      = from
    ; from    = to
    ; from∘to = to∘from
    ; to∘from = from∘to
    } where open ≃ A≃B

  ≃-trans : A ≃ B → B ≃ C → A ≃ C
  ≃-trans A≃B B≃C = record
    { to      = λ x → I₂.to (I₁.to x)
    ; from    = λ x → I₁.from (I₂.from x)
    ; from∘to = λ x → trans (cong I₁.from (I₂.from∘to _)) (I₁.from∘to _)
    ; to∘from = λ x → trans (cong I₂.to (I₁.to∘from _)) (I₂.to∘from _)
    } where module I₁ = ≃ A≃B
            module I₂ = ≃ B≃C

  module ≃-Reasoning where
    infix 1 begin_
    infixr 2 _≃⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
    infix 3 _∎

    begin_ : ∀ {A : Set ℓ₁} {B : Set ℓ₂} → A ≃ B → A ≃ B
    begin p = p

    _≃⟨_⟩_ : ∀ (A : Set ℓ₁) {B : Set ℓ₂} {C : Set ℓ₃} → A ≃ B → B ≃ C → A ≃ C
    _ ≃⟨ p ⟩ q = ≃-trans p q

    _≡⟨_⟩_ : ∀ (A : Set ℓ₁) {B : Set ℓ₁} {C : Set ℓ₂} → A ≡ B → B ≃ C → A ≃ C
    _ ≡⟨ refl ⟩ q = q

    _≡⟨⟩_ : ∀ (A : Set ℓ₁) {C : Set ℓ₂} → A ≃ C → A ≃ C
    _ ≡⟨⟩ q = q

    _∎ : ∀ (A : Set ℓ) → A ≃ A
    _ ∎ = ≃-refl

  ⊥-⊎ : (⊥ ⊎ A) ≃ A
  ⊥-⊎ = record
    { to      = λ { (inj₂ x) → x }
    ; from    = inj₂
    ; from∘to = λ { (inj₂ y) → refl }
    ; to∘from = λ x → refl
    }

  ⊎-⊥ : (A ⊎ ⊥) ≃ A
  ⊎-⊥ = record
    { to      = λ { (inj₁ x) → x }
    ; from    = inj₁
    ; from∘to = λ { (inj₁ y) → refl }
    ; to∘from = λ x → refl
    }

  ⊎-comm : (A ⊎ B) ≃ (B ⊎ A)
  ⊎-comm = record
    { to      = λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
    ; from    = λ { (inj₁ x) → inj₂ x ; (inj₂ x) → inj₁ x }
    ; from∘to = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
    }

  ⊎-assoc : ((A ⊎ B) ⊎ C) ≃ (A ⊎ (B ⊎ C))
  ⊎-assoc = record
    { to      = λ { (inj₁ (inj₁ x)) → inj₁ x ; (inj₁ (inj₂ y)) → inj₂ (inj₁ y) ; (inj₂ y) → inj₂ (inj₂ y) }
    ; from    = λ { (inj₁ x) → inj₁ (inj₁ x) ; (inj₂ (inj₁ x)) → inj₁ (inj₂ x) ; (inj₂ (inj₂ y)) → inj₂ y }
    ; from∘to = λ { (inj₁ (inj₁ x)) → refl ; (inj₁ (inj₂ y)) → refl ; (inj₂ y) → refl }
    ; to∘from = λ { (inj₁ x) → refl ; (inj₂ (inj₁ x)) → refl ; (inj₂ (inj₂ y)) → refl }
    }

  -- ≃-cong₂ : ∀ {A A' : Set ℓ₁} {B B' : Set ℓ₂} (C : Set ℓ₁ → Set ℓ₂ → Set ℓ₃) → A ≃ A' → B ≃ B' → C A B ≃ C A' B'
  -- ≃-cong₂ C A≃A' B≃B' = record
  --   { to      = ?
  --   ; from    = ?
  --   ; from∘to = ?
  --   ; to∘from = ?
  --   }

  ≃-⊎ : A ≃ A' → B ≃ B' → (A ⊎ B) ≃ (A' ⊎ B')
  ≃-⊎ A≃A' B≃B' = record
    { to      = λ where (inj₁ x) → inj₁ (A.to x)
                        (inj₂ x) → inj₂ (B.to x)
    ; from    = λ where (inj₁ x) → inj₁ (A.from x)
                        (inj₂ x) → inj₂ (B.from x)
    ; from∘to = λ where (inj₁ x) → cong inj₁ (A.from∘to x)
                        (inj₂ x) → cong inj₂ (B.from∘to x)
    ; to∘from = λ where (inj₁ x) → cong inj₁ (A.to∘from x)
                        (inj₂ x) → cong inj₂ (B.to∘from x)
    } where module A = ≃ A≃A'
            module B = ≃ B≃B'


  Σ-⊎-≡₁ : ∀ (n : A) →
    (Σ[ x ∈ A ⊎ B ] ¬ x ≡ inj₁ n) ≃ ((Σ[ x ∈ A ] ¬ x ≡ n) ⊎ B)
  Σ-⊎-≡₁ n = record
    { to      = λ where (inj₁ x , p)   → inj₁ (x , (λ eq   → p (cong inj₁ eq)))
                        (inj₂ x , p)   → inj₂ x
    ; from    = λ where (inj₁ (x , p)) → inj₁ x , λ { refl → p refl }
                        (inj₂ y)       → inj₂ y , λ()
    ; from∘to = λ where (inj₁ x , p)   → refl
                        (inj₂ x , p)   → refl
    ; to∘from = λ where (inj₁ (x , p)) → refl
                        (inj₂ y)       → refl
    }

  Σ-⊎-≡₂ : ∀ (n : B) →
    (Σ[ x ∈ A ⊎ B ] ¬ x ≡ inj₂ n) ≃ (A ⊎ (Σ[ x ∈ B ] ¬ x ≡ n))
  Σ-⊎-≡₂ n = record
    { to      = λ where (inj₁ x , p)   → inj₁ x
                        (inj₂ x , p)   → inj₂ (x , (λ eq   → p (cong inj₂ eq)))
    ; from    = λ where (inj₂ (x , p)) → inj₂ x , λ { refl → p refl }
                        (inj₁ y)       → inj₁ y , λ()
    ; from∘to = λ where (inj₁ x , p)   → refl
                        (inj₂ x , p)   → refl
    ; to∘from = λ where (inj₂ (x , p)) → refl
                        (inj₁ y)       → refl
    }

  Σ-⊎ : ∀ (P : (A ⊎ B) → Set ℓ) →
    (Σ (A ⊎ B) P) ≃ (Σ A (λ x → P (inj₁ x)) ⊎ Σ B (λ x → P (inj₂ x)))
  Σ-⊎ P = record
    { to      = λ where
      (inj₁ x , p) → inj₁ (x , p)
      (inj₂ x , p) → inj₂ (x , p)
    ; from    = λ where
      (inj₁ (x , p)) → inj₁ x , p
      (inj₂ (x , p)) → inj₂ x , p
    ; from∘to = λ where
      (inj₁ x , p) → refl
      (inj₂ x , p) → refl
    ; to∘from = λ where
      (inj₁ (x , p)) → refl
      (inj₂ (x , p)) → refl
    }

  Σ-≃ : (F : A → Set ℓ₁) (f : ∀ a → F a → Set ℓ₂) (a b : A) →
    (iso : F a ≃ F b) →
    (∀ x → f a x ≡ f b (≃.to iso x)) →
    Σ (F a) (f a) ≃ Σ (F b) (f b)
  Σ-≃ F f a b Fa≃Fb f-pres = record
    { to      = λ (x , y) → to x , subst (λ x → x) (f-pres x) y 
    ; from    = λ (x , y) → from x , subst (λ x → x) (sym (f-pres' x)) y
    ; from∘to = λ (x , y) → H.≅-to-≡ $
       H.cong₂ _,_ (H.≡-to-≅ (from∘to x))
                   (H.trans (H.≡-subst-removable (λ x → x) (sym (f-pres' (to x))) _)
                            (H.≡-subst-removable (λ x → x) (f-pres x) _))
    ; to∘from = λ (x , y) → H.≅-to-≡ $
       H.cong₂ _,_ (H.≡-to-≅ (to∘from x))
                   (H.trans (H.≡-subst-removable (λ x → x) (f-pres (from x)) _)
                            (H.≡-subst-removable (λ x → x) (sym (f-pres' x)) _))
    } where open ≃ Fa≃Fb
            f-pres' : ∀ x → f a (≃.from Fa≃Fb x) ≡ f b x
            f-pres' x = let open ≡-Reasoning in
                        begin
                          f a (from x)
                        ≡⟨ f-pres (from x) ⟩
                          f b (to (from x))
                        ≡⟨ cong (f b) (to∘from x) ⟩
                          f b x
                        ∎

  ≃-⊎-lem : ((A ⊎ B) ⊎ (C ⊎ D)) ≃ ((A ⊎ C) ⊎ (B ⊎ D))
  ≃-⊎-lem {A = A} {B = B} {C = C} {D = D} =
    let open ≃-Reasoning in
    begin
      ((A ⊎ B) ⊎ (C ⊎ D))
    ≃⟨ ⊎-assoc ⟩
      (A ⊎ (B ⊎ (C ⊎ D)))
    ≃⟨ ≃-⊎ ≃-refl (≃-⊎ ≃-refl ⊎-comm) ⟩
      (A ⊎ (B ⊎ (D ⊎ C)))
    ≃⟨ ≃-⊎ ≃-refl (≃-sym ⊎-assoc) ⟩
      (A ⊎ ((B ⊎ D) ⊎ C))
    ≃⟨ ≃-⊎ ≃-refl ⊎-comm ⟩
      (A ⊎ (C ⊎ (B ⊎ D)))
    ≃⟨ ≃-sym ⊎-assoc ⟩
      ((A ⊎ C) ⊎ (B ⊎ D))
    ∎

  ⊥≃Fin0 : ⊥ ≃ Fin 0
  ⊥≃Fin0 = record
    { to      = λ()
    ; from    = λ()
    ; from∘to = λ()
    ; to∘from = λ()
    }

  ⊤≃Fin1 : ⊤ ≃ Fin 1
  ⊤≃Fin1 = record
    { to      = λ x → zero
    ; from    = λ x → tt
    ; from∘to = λ x → refl
    ; to∘from = λ where zero → refl
    }

  Fin⊎Fin≃Fin : ∀ {n₁ n₂} → (Fin n₁ ⊎ Fin n₂) ≃ Fin (n₁ ℕ.+ n₂)
  Fin⊎Fin≃Fin {n₁} {n₂} = record
    { to      = to
    ; from    = from
    ; from∘to = from∘to
    ; to∘from = to∘from {n₁}
    } where
    to : ∀ {n₁} {n₂} → Fin n₁ ⊎ Fin n₂ → Fin (n₁ ℕ.+ n₂)
    to {n₁} {n₂} (inj₁ x) = Fin.inject≤ x (ℕP.m≤m+n n₁ n₂)
    to {n₁} {n₂} (inj₂ x) = n₁ Fin.↑ʳ x
    from : ∀ {n₁} {n₂} → Fin (n₁ ℕ.+ n₂) → Fin n₁ ⊎ Fin n₂
    from {n₁ = zero} x = inj₂ x
    from {n₁ = suc n₁} zero = inj₁ zero
    from {n₁ = suc n₁} (suc x) with from x
    ... | inj₁ x = inj₁ (suc x)
    ... | inj₂ x = inj₂ x
    from∘to : ∀ {n₁} {n₂} (x : Fin n₁ ⊎ Fin n₂) → from (to x) ≡ x
    from∘to (inj₁ x) = {!!}
    from∘to (inj₂ y) = {!!}
    to∘from : ∀ {n₁} {n₂} (x : Fin (n₁ ℕ.+ n₂)) → to {n₁} {n₂} (from x) ≡ x
    to∘from {n₁ = zero} x = refl
    to∘from {n₁ = suc n₁} zero = refl
    to∘from {n₁ = suc n₁} (suc x) with from {n₁ = n₁} x in eq
    ... | inj₁ y = {!to∘from {n₁ = n₁} x!}
    ... | inj₂ y = {!!}

infix 4 _≃_
record _≃_ {L : Set ℓ} (g₁ g₂ : Graph L) : Set ℓ where
  field
    iso    : Node g₁ Type.≃ Node g₂

  open Type.≃ iso public

  field
    edges₁ : ∀ x y → Edge g₁ x y → Edge g₂ (to x) (to y)
    edges₂ : ∀ x y → Edge g₂ x y → Edge g₁ (from x) (from y)
    labels : ∀ x → label g₁ x ≡ label g₂ (to x)

module ≃ = _≃_

infix 4 _≲_
record _≲_ {L : Set ℓ} (g₁ g₂ : Graph L) : Set ℓ where
  field
    iso    : Node g₁ Type.≃ Node g₂

  open Type.≃ iso public

  field
    edges : ∀ x y → Edge g₁ x y → Edge g₂ (to x) (to y)
    labels : ∀ x → label g₁ x ≡ label g₂ (to x)

module ≲ = _≲_

record TopOrd {L : Set ℓ} (g : Graph L) : Set ℓ where
  constructor top-ord
  field
    order  : ℕ
    iso    : Node g Type.≃ Fin order

  open Type.≃ iso public

  field
    ordered : ∀ x y → Edge g x y → to x Fin.< to y

-- Lemma A.4

∪-identityˡ : ∀ (g : Graph L) → (∅ ∪ g) ≃ g
∪-identityˡ g = record
  { iso    = Type.⊥-⊎
  ; edges₁  = λ { (inj₂ y) (inj₂ y₁) x→y → x→y }
  ; edges₂  = λ x y x→y → x→y
  ; labels = λ { (inj₂ y) → refl }
  }

∪-identityʳ : ∀ (g : Graph L) → (g ∪ ∅) ≃ g
∪-identityʳ g = record
  { iso    = Type.⊎-⊥
  ; edges₁ = λ { (inj₁ x) (inj₁ x₁) x→y → x→y }
  ; edges₂ = λ x y x→y → x→y
  ; labels = λ { (inj₁ x) → refl }
  }

∪-comm : ∀ (g₁ g₂ : Graph L) → (g₁ ∪ g₂) ≃ (g₂ ∪ g₁)
∪-comm g₁ g₂ = record
  { iso    = Type.⊎-comm
  ; edges₁ = λ { (inj₁ x) (inj₁ y) x→y → x→y ; (inj₂ x) (inj₂ y) x→y → x→y }
  ; edges₂ = λ { (inj₁ x) (inj₁ y) x→y → x→y ; (inj₂ x) (inj₂ y) x→y → x→y }
  ; labels = λ { (inj₁ x) → refl ; (inj₂ x) → refl }
  }

∪-assoc : ∀ (g₁ g₂ g₃ : Graph L) → ((g₁ ∪ g₂) ∪ g₃) ≃ (g₁ ∪ (g₂ ∪ g₃))
∪-assoc g₁ g₂ g₃ = record
  { iso    = Type.⊎-assoc
  ; edges₁ = λ where (inj₁ (inj₁ x)) (inj₁ (inj₁ x₁)) x→y → x→y
                     (inj₁ (inj₂ y)) (inj₁ (inj₂ y₁)) x→y → x→y
                     (inj₂ y)        (inj₂ y₁)        x→y → x→y
  ; edges₂ = λ where (inj₁ x)        (inj₁ x₁)        x→y → x→y
                     (inj₂ (inj₁ x)) (inj₂ (inj₁ x₁)) x→y → x→y
                     (inj₂ (inj₂ y)) (inj₂ (inj₂ y₁)) x→y → x→y
  ; labels = λ where (inj₁ (inj₁ x)) → refl
                     (inj₁ (inj₂ y)) → refl
                     (inj₂ y)        → refl
  }

+-identityˡ : ∀ (g : Graph L) → (∅ + g) ≃ g
+-identityˡ g = record
  { iso    = Type.⊥-⊎
  ; edges₁ = λ { (inj₂ y) (inj₂ y₁) x→y → x→y }
  ; edges₂ = λ x y x→y → x→y
  ; labels = λ { (inj₂ y) → refl }
  }

+-identityʳ : ∀ (g : Graph L) → (g + ∅) ≃ g
+-identityʳ g = record
  { iso    = Type.⊎-⊥
  ; edges₁ = λ { (inj₁ x) (inj₁ x₁) x→y → x→y }
  ; edges₂ = λ x y x→y → x→y
  ; labels = λ { (inj₁ x) → refl }
  }

+-assoc : ∀ (g₁ g₂ g₃ : Graph L) → ((g₁ + g₂) + g₃) ≃ (g₁ + (g₂ + g₃))
+-assoc g₁ g₂ g₃ = record
  { iso    = Type.⊎-assoc
  ; edges₁ = λ where (inj₁ (inj₁ x)) (inj₁ (inj₁ x₁)) x→y → x→y
                     (inj₁ (inj₁ x)) (inj₁ (inj₂ y))  x→y → x→y
                     (inj₁ (inj₂ y)) (inj₁ (inj₂ y₁)) x→y → x→y
                     (inj₁ (inj₁ x)) (inj₂ y)         x→y → x→y
                     (inj₁ (inj₂ x)) (inj₂ y)         x→y → x→y
                     (inj₂ y)        (inj₂ y₁)        x→y → x→y
  ; edges₂ = λ where (inj₁ x)        (inj₁ x₁)        x→y → x→y
                     (inj₁ x)        (inj₂ (inj₁ x₁)) x→y → x→y
                     (inj₁ x)        (inj₂ (inj₂ y))  x→y → x→y
                     (inj₂ (inj₁ x)) (inj₂ (inj₁ x₁)) x→y → x→y
                     (inj₂ (inj₁ x)) (inj₂ (inj₂ y))  x→y → x→y
                     (inj₂ (inj₂ y)) (inj₂ (inj₂ y₁)) x→y → x→y
  ; labels = λ where (inj₁ (inj₁ x)) → refl
                     (inj₁ (inj₂ y)) → refl
                     (inj₂ y)        → refl
  }

-- Lemma A.5

∪≲+ : ∀ (g₁ g₂ : Graph L) → (g₁ ∪ g₂) ≲ (g₁ + g₂)
∪≲+ g₁ g₂ = record
  { iso    = Type.≃-refl
  ; edges  = λ where (inj₁ x) (inj₁ y) x→y → x→y
                     (inj₂ x) (inj₂ y) x→y → x→y
  ; labels = λ where (inj₁ x) → refl
                     (inj₂ x) → refl
  }

∪≲+' : ∀ (g₁ g₂ g₃ : Graph L) → (g₁ ∪ (g₂ + g₃)) ≲ ((g₁ ∪ g₂) + g₃)
∪≲+' g₁ g₂ g₃ = record
  { iso    = Type.≃-sym Type.⊎-assoc
  ; edges  = λ where (inj₁ x)        (inj₁ y)        x→y → x→y
                     (inj₂ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
                     (inj₂ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
                     (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) x→y → x→y
  ; labels = λ where (inj₁ x)        → refl
                     (inj₂ (inj₁ x)) → refl
                     (inj₂ (inj₂ x)) → refl
  }

∪≲+'' : ∀ (g₁ g₂ g₃ : Graph L) → ((g₁ + g₂) ∪ g₃) ≲ (g₁ + (g₂ ∪ g₃))
∪≲+'' g₁ g₂ g₃ = record
  { iso    = Type.⊎-assoc
  ; edges  = λ where (inj₁ (inj₁ x)) (inj₁ (inj₁ y)) x→y → x→y
                     (inj₁ (inj₁ x)) (inj₁ (inj₂ y)) x→y → x→y
                     (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) x→y → x→y
                     (inj₂ x)        (inj₂ y)        x→y → x→y
  ; labels = λ where (inj₁ (inj₁ x)) → refl
                     (inj₁ (inj₂ x)) → refl
                     (inj₂ x)        → refl
  }

≲-dist-∪-+ : (g₁₁ g₁₂ g₂₁ g₂₂ : Graph L) → (g₁₁ + g₁₂) ∪ (g₂₁ + g₂₂) ≲ (g₁₁ ∪ g₂₁) + (g₁₂ ∪ g₂₂)
≲-dist-∪-+ g₁₁ g₁₂ g₂₁ g₂₂ = record
  { iso    = Type.≃-⊎-lem
  ; edges  = λ where
      (inj₁ (inj₁ x)) (inj₁ (inj₁ y)) x→y → x→y
      (inj₁ (inj₁ x)) (inj₁ (inj₂ y)) x→y → tt
      (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) x→y → x→y
      (inj₂ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
      (inj₂ (inj₁ x)) (inj₂ (inj₂ y)) x→y → tt
      (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) x→y → x→y
  ; labels = λ where
      (inj₁ (inj₁ x)) → refl
      (inj₁ (inj₂ x)) → refl
      (inj₂ (inj₁ x)) → refl
      (inj₂ (inj₂ x)) → refl
  }

-- Lemma A.6

≃-refl : ∀ {g : Graph L} → g ≃ g
≃-refl = record
  { iso    = Type.≃-refl
  ; edges₁ = λ x y x→y → x→y
  ; edges₂ = λ x y x→y → x→y
  ; labels = λ x → refl
  }

-- Lemma A.9

≲-refl : ∀ {g : Graph L} → g ≲ g
≲-refl = record
  { iso    = Type.≃-refl
  ; edges = λ x y x→y → x→y
  ; labels = λ x → refl
  }

-- TODO: Lemma missing

≃-trans : ∀ {g₁ g₂ g₃ : Graph L} → g₁ ≃ g₂ → g₂ ≃ g₃ → g₁ ≃ g₃
≃-trans g₁≃g₂ g₂≃g₃ = record
  { iso    = Type.≃-trans I₁.iso I₂.iso
  ; edges₁ = λ x y x→y → I₂.edges₁ _ _ (I₁.edges₁ _ _ x→y)
  ; edges₂ = λ x y x→y → I₁.edges₂ _ _ (I₂.edges₂ _ _ x→y)
  ; labels = λ x → trans (I₁.labels x) (I₂.labels _)
  } where module I₁ = ≃ g₁≃g₂
          module I₂ = ≃ g₂≃g₃

≃-sym : ∀ {g₁ g₂ : Graph L} → g₁ ≃ g₂ → g₂ ≃ g₁
≃-sym {g₂ = g₂} g₁≃g₂ = record
  { iso    = Type.≃-sym I.iso
  ; edges₁ = λ x y x→y → I.edges₂ _ _ x→y
  ; edges₂ = λ x y x→y → I.edges₁ _ _ x→y
  ; labels = λ x → trans (cong (label g₂) (sym (I.to∘from x))) (sym (I.labels (I.from x)))
  } where module I = ≃ g₁≃g₂

≃→≲ : ∀ {g₁ g₂ : Graph L} → g₁ ≃ g₂ → g₁ ≲ g₂
≃→≲ p = record
  { iso    = iso
  ; edges  = edges₁
  ; labels = labels
  } where open ≃ p

≲-trans : ∀ {g₁ g₂ g₃ : Graph L} → g₁ ≲ g₂ → g₂ ≲ g₃ → g₁ ≲ g₃
≲-trans g₁≃g₂ g₂≃g₃ = record
  { iso    = Type.≃-trans I₁.iso I₂.iso
  ; edges = λ x y x→y → I₂.edges _ _ (I₁.edges _ _ x→y)
  ; labels = λ x → trans (I₁.labels x) (I₂.labels _)
  } where module I₁ = ≲ g₁≃g₂
          module I₂ = ≲ g₂≃g₃

≃-≲-trans : ∀ {g₁ g₂ g₃ g₄ : Graph L} → g₁ ≃ g₂ → g₂ ≲ g₃ → g₃ ≃ g₄ → g₁ ≲ g₄
≃-≲-trans g₁≃g₂ g₂≲g₃ g₃≃g₄ = record
  { iso    = Type.≃-trans I₁.iso (Type.≃-trans I₂.iso I₃.iso)
  ; edges  = λ x y x→y → I₃.edges₁ _ _ (I₂.edges _ _ (I₁.edges₁ _ _ x→y))
  ; labels = λ x → trans (I₁.labels x) (trans (I₂.labels _) (I₃.labels _))
  } where module I₁ = ≃ g₁≃g₂
          module I₂ = ≲ g₂≲g₃
          module I₃ = ≃ g₃≃g₄

module ≃-Reasoning where
  infix 1 begin_
  infixr 2 _≃⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {g₁ g₂ : Graph L} → g₁ ≃ g₂ → g₁ ≃ g₂
  begin p = p

  _≃⟨_⟩_ : ∀ (g₁ {g₂ g₃} : Graph L) → g₁ ≃ g₂ → g₂ ≃ g₃ → g₁ ≃ g₃
  _ ≃⟨ p ⟩ q = ≃-trans p q

  _≡⟨_⟩_ : ∀ (g₁ {g₂ g₃} : Graph L) → g₁ ≡ g₂ → g₂ ≃ g₃ → g₁ ≃ g₃
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (g₁ {g₂} : Graph L) → g₁ ≃ g₂ → g₁ ≃ g₂
  _ ≡⟨⟩ q = q

  _∎ : ∀ (g : Graph L) → g ≃ g
  _ ∎ = ≃-refl

module ≲-Reasoning where
  infix 1 begin_
  infixr 2 _≲⟨_⟩_ _≃⟨_⟩_ _≡⟨_⟩_ _≡⟨⟩_
  infix 3 _∎

  begin_ : ∀ {g₁ g₂ : Graph L} → g₁ ≲ g₂ → g₁ ≲ g₂
  begin p = p

  _≲⟨_⟩_ : ∀ (g₁ {g₂ g₃} : Graph L) → g₁ ≲ g₂ → g₂ ≲ g₃ → g₁ ≲ g₃
  _ ≲⟨ p ⟩ q = ≲-trans p q

  _≃⟨_⟩_ : ∀ (g₁ {g₂ g₃} : Graph L) → g₁ ≃ g₂ → g₂ ≲ g₃ → g₁ ≲ g₃
  _ ≃⟨ p ⟩ q = ≲-trans (≃→≲ p) q

  _≡⟨_⟩_ : ∀ (g₁ {g₂ g₃} : Graph L) → g₁ ≡ g₂ → g₂ ≲ g₃ → g₁ ≲ g₃
  _ ≡⟨ refl ⟩ q = q

  _≡⟨⟩_ : ∀ (g₁ {g₂} : Graph L) → g₁ ≲ g₂ → g₁ ≲ g₂
  _ ≡⟨⟩ q = q

  _∎ : ∀ (g : Graph L) → g ≲ g
  _ ∎ = ≲-refl

-- Lemma A.7

≃-+ : ∀ {g₁ g₁' g₂ g₂' : Graph L} → g₁ ≃ g₁' → g₂ ≃ g₂' → (g₁ + g₂) ≃ (g₁' + g₂')
≃-+ g₁≃g₁' g₂≃g₂' = record
  { iso    = Type.≃-⊎ (≃.iso g₁≃g₁') (≃.iso g₂≃g₂')
  ; edges₁ = λ where (inj₁ x) (inj₁ y) x→y → I₁.edges₁ x y x→y
                     (inj₁ x) (inj₂ y) x→y → tt
                     (inj₂ x) (inj₂ y) x→y → I₂.edges₁ x y x→y
  ; edges₂ = λ where (inj₁ x) (inj₁ y) x→y → I₁.edges₂ x y x→y
                     (inj₁ x) (inj₂ y) x→y → tt
                     (inj₂ x) (inj₂ y) x→y → I₂.edges₂ x y x→y
  ; labels = λ where (inj₁ x) → I₁.labels x
                     (inj₂ x) → I₂.labels x
  } where module I₁ = ≃ g₁≃g₁'
          module I₂ = ≃ g₂≃g₂'

-- Lemma A.8

≃-∪ : ∀ {g₁ g₁' g₂ g₂' : Graph L} → g₁ ≃ g₁' → g₂ ≃ g₂' → (g₁ ∪ g₂) ≃ (g₁' ∪ g₂')
≃-∪ g₁≃g₁' g₂≃g₂' = record
  { iso    = Type.≃-⊎ (≃.iso g₁≃g₁') (≃.iso g₂≃g₂')
  ; edges₁ = λ where (inj₁ x) (inj₁ y) x→y → I₁.edges₁ x y x→y
                     (inj₂ x) (inj₂ y) x→y → I₂.edges₁ x y x→y
  ; edges₂ = λ where (inj₁ x) (inj₁ y) x→y → I₁.edges₂ x y x→y
                     (inj₂ x) (inj₂ y) x→y → I₂.edges₂ x y x→y
  ; labels = λ where (inj₁ x) → I₁.labels x
                     (inj₂ x) → I₂.labels x
  } where module I₁ = ≃ g₁≃g₁'
          module I₂ = ≃ g₂≃g₂'

-- Lemma A.10

≲-+ : ∀ {g₁ g₁' g₂ g₂' : Graph L} → g₁ ≲ g₁' → g₂ ≲ g₂' → (g₁ + g₂) ≲ (g₁' + g₂')
≲-+ g₁≲g₁' g₂≲g₂' = record
  { iso    = Type.≃-⊎ (≲.iso g₁≲g₁') (≲.iso g₂≲g₂')
  ; edges  = λ where (inj₁ x) (inj₁ y) x→y → I₁.edges x y x→y
                     (inj₁ x) (inj₂ y) x→y → tt
                     (inj₂ x) (inj₂ y) x→y → I₂.edges x y x→y
  ; labels = λ where (inj₁ x) → I₁.labels x
                     (inj₂ x) → I₂.labels x
  } where module I₁ = ≲ g₁≲g₁'
          module I₂ = ≲ g₂≲g₂'

-- Lemma A.11

≲-∪ : ∀ {g₁ g₁' g₂ g₂' : Graph L} → g₁ ≲ g₁' → g₂ ≲ g₂' → (g₁ ∪ g₂) ≲ (g₁' ∪ g₂')
≲-∪ g₁≲g₁' g₂≲g₂' = record
  { iso    = Type.≃-⊎ (≲.iso g₁≲g₁') (≲.iso g₂≲g₂')
  ; edges  = λ where (inj₁ x) (inj₁ y) x→y → I₁.edges x y x→y
                     (inj₂ x) (inj₂ y) x→y → I₂.edges x y x→y
  ; labels = λ where (inj₁ x) → I₁.labels x
                     (inj₂ x) → I₂.labels x
  } where module I₁ = ≲ g₁≲g₁'
          module I₂ = ≲ g₂≲g₂'

-- Definition A.12

_[_/_] : ∀ (g₁ g₂ : Graph L) → Node g₁ → Graph L
g₁ [ g₂ / n ] = graph N' E' L' where
  N' = (Σ[ n' ∈ Node g₁ ] ¬ n' ≡ n ) ⊎ Node g₂
  E' = λ where
        (inj₁ (x , x≢n)) (inj₁ (y , y≢n)) → Edge g₁ x y
        (inj₁ (x , x≢n)) (inj₂ y)         → Edge g₁ x n
        (inj₂ x)         (inj₁ (y , y≢n)) → Edge g₁ n y
        (inj₂ x)         (inj₂ y)         → Edge g₂ x y
  L' = λ where
        (inj₁ (x , x≢n)) → label g₁ x
        (inj₂ x)         → label g₂ x

-- Definition A.13

_[_/_]ˡ : ∀ {L : Set} (g₁ g₂ : Graph L) → L → Graph L
g₁ [ g₂ / l ]ˡ = graph N' E' L' where
  N' = (Σ[ n' ∈ Node g₁ ] label g₁ n' ≢ l) ⊎
       (Σ[ n' ∈ Node g₁ ] label g₁ n' ≡ l × Node g₂)
  E' = λ where
        (inj₁ (x , x≢l))      (inj₁ (y , y≢l))      → Edge g₁ x y
        (inj₁ (x , x≢l))      (inj₂ (y , y≡l , y')) → Edge g₁ x y
        (inj₂ (x , x≡l , x')) (inj₁ (y , y≢l))      → Edge g₁ x y
        (inj₂ (x , x≡l , x')) (inj₂ (y , y≡l , y')) → Edge g₁ x y ⊎ (x ≡ y × Edge g₂ x' y')
  L' = λ where
        (inj₁ (x , x≢l))    → label g₁ x
        (inj₂ (x , p , x')) → label g₂ x'

-- Lemma A.14

+-[]₁ : ∀ (g₁ g₂ g : Graph L) (n : Node g₁) →
  ((g₁ + g₂) [ g / inj₁ n ]) ≃ ((g₁ [ g / n ]) + g₂)
+-[]₁ g₁ g₂ g n = record
  { iso    = let open Type.≃-Reasoning in
              begin
                Node ((g₁ + g₂) [ g / inj₁ n ])
              ≡⟨⟩
                (Σ (Node g₁ ⊎ Node g₂) (_≢ inj₁ n) ⊎ Node g)
              ≃⟨ Type.≃-⊎ (Type.Σ-⊎-≡₁ n) Type.≃-refl ⟩
                ((Σ (Node g₁) (_≢ n) ⊎ Node g₂) ⊎ Node g)
              ≃⟨ Type.⊎-assoc ⟩
                (Σ (Node g₁) (_≢ n) ⊎ (Node g₂ ⊎ Node g))
              ≃⟨ Type.≃-⊎ Type.≃-refl Type.⊎-comm ⟩
                (Σ (Node g₁) (_≢ n) ⊎ (Node g ⊎ Node g₂))
              ≃⟨ Type.≃-sym Type.⊎-assoc ⟩
                ((Σ (Node g₁) (_≢ n) ⊎ Node g) ⊎ Node g₂)
              ≡⟨⟩
                Node ((g₁ [ g / n ]) + g₂)
              ∎
  ; edges₁ = λ where
    (inj₁ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ y)            x→y → x→y
    (inj₂ x)            (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₂ x)            (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ x)            (inj₂ y)            x→y → x→y
  ; edges₂ = λ where
    (inj₁ (inj₁ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₁ (inj₂ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₂ y)        x→y → x→y
    (inj₁ (inj₂ x)) (inj₂ y)        x→y → x→y
    (inj₂ x)        (inj₂ y)        x→y → x→y
  ; labels = λ where
    (inj₁ (inj₁ x , p)) → refl
    (inj₁ (inj₂ x , p)) → refl
    (inj₂ y)            → refl
  }

+-[]₂ : ∀ (g₁ g₂ g : Graph L) (n : Node g₂) →
  ((g₁ + g₂) [ g / inj₂ n ]) ≃ (g₁ + (g₂ [ g / n ]))
+-[]₂ g₁ g₂ g n = record
  { iso    = let open Type.≃-Reasoning in
             begin
               Node ((g₁ + g₂) [ g / inj₂ n ])
             ≡⟨⟩
               (Σ (Node g₁ ⊎ Node g₂) (λ n' → n' ≡ inj₂ n → ⊥) ⊎ Node g)
             ≃⟨ Type.≃-⊎ (Type.Σ-⊎-≡₂ n) Type.≃-refl ⟩
               ((Node g₁ ⊎ Σ (Node g₂) (λ n' → n' ≡ n → ⊥)) ⊎ Node g)
             ≃⟨ Type.⊎-assoc ⟩
               (Node g₁ ⊎ (Σ (Node g₂) (λ n' → n' ≡ n → ⊥) ⊎ Node g))
             ≡⟨⟩
               Node (g₁ + (g₂ [ g / n ]))
             ∎
  ; edges₁ = λ where
    (inj₁ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ y)            x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₂ y)            x→y → x→y
    (inj₂ x)            (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₂ x)            (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ x)            (inj₂ y)            x→y → x→y
  ; edges₂ = λ where
    (inj₁ x)        (inj₁ y)        x→y → x→y
    (inj₁ x)        (inj₂ (inj₁ y)) x→y → x→y
    (inj₁ x)        (inj₂ (inj₂ y)) x→y → x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) x→y → x→y
  ; labels = λ where
    (inj₁ (inj₁ x , p)) → refl
    (inj₁ (inj₂ x , p)) → refl
    (inj₂ x)            → refl
  }

-- Lemma A.15

∪-[]₁ : ∀ (g₁ g₂ g : Graph L) (n : Node g₁) →
  ((g₁ ∪ g₂) [ g / inj₁ n ]) ≃ ((g₁ [ g / n ]) ∪ g₂)
∪-[]₁ g₁ g₂ g n = record
  { iso    = let open Type.≃-Reasoning in
              begin
                Node ((g₁ ∪ g₂) [ g / inj₁ n ])
              ≡⟨⟩
                (Σ (Node g₁ ⊎ Node g₂) (_≢ inj₁ n) ⊎ Node g)
              ≃⟨ Type.≃-⊎ (Type.Σ-⊎-≡₁ n) Type.≃-refl ⟩
                ((Σ (Node g₁) (_≢ n) ⊎ Node g₂) ⊎ Node g)
              ≃⟨ Type.⊎-assoc ⟩
                (Σ (Node g₁) (_≢ n) ⊎ (Node g₂ ⊎ Node g))
              ≃⟨ Type.≃-⊎ Type.≃-refl Type.⊎-comm ⟩
                (Σ (Node g₁) (_≢ n) ⊎ (Node g ⊎ Node g₂))
              ≃⟨ Type.≃-sym Type.⊎-assoc ⟩
                ((Σ (Node g₁) (_≢ n) ⊎ Node g) ⊎ Node g₂)
              ≡⟨⟩
                Node ((g₁ [ g / n ]) ∪ g₂)
              ∎
  ; edges₁ = λ where
    (inj₁ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ y)            x→y → x→y
    (inj₂ x)            (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₂ x)            (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ x)            (inj₂ y)            x→y → x→y
  ; edges₂ = λ where
    (inj₁ (inj₁ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₁ (inj₂ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₂ y)        x→y → x→y
    (inj₁ (inj₂ x)) (inj₂ y)        x→y → x→y
    (inj₂ x)        (inj₂ y)        x→y → x→y
  ; labels = λ where
    (inj₁ (inj₁ x , p)) → refl
    (inj₁ (inj₂ x , p)) → refl
    (inj₂ y)            → refl
  }

∪-[]₂ : ∀ (g₁ g₂ g : Graph L) (n : Node g₂) →
  ((g₁ ∪ g₂) [ g / inj₂ n ]) ≃ (g₁ ∪ (g₂ [ g / n ]))
∪-[]₂ g₁ g₂ g n = record
  { iso    = let open Type.≃-Reasoning in
             begin
               Node ((g₁ ∪ g₂) [ g / inj₂ n ])
             ≡⟨⟩
               (Σ (Node g₁ ⊎ Node g₂) (λ n' → n' ≡ inj₂ n → ⊥) ⊎ Node g)
             ≃⟨ Type.≃-⊎ (Type.Σ-⊎-≡₂ n) Type.≃-refl ⟩
               ((Node g₁ ⊎ Σ (Node g₂) (λ n' → n' ≡ n → ⊥)) ⊎ Node g)
             ≃⟨ Type.⊎-assoc ⟩
               (Node g₁ ⊎ (Σ (Node g₂) (λ n' → n' ≡ n → ⊥) ⊎ Node g))
             ≡⟨⟩
               Node (g₁ ∪ (g₂ [ g / n ]))
             ∎
  ; edges₁ = λ where
    (inj₁ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ y)            x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₂ y)            x→y → x→y
    (inj₂ x)            (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₂ x)            (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ x)            (inj₂ y)            x→y → x→y
  ; edges₂ = λ where
    (inj₁ x)        (inj₁ y)        x→y → x→y
    (inj₁ x)        (inj₂ (inj₁ y)) x→y → x→y
    (inj₁ x)        (inj₂ (inj₂ y)) x→y → x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) x→y → x→y
  ; labels = λ where
    (inj₁ (inj₁ x , p)) → refl
    (inj₁ (inj₂ x , p)) → refl
    (inj₂ x)            → refl
  }

-- Lemma A.16

+-[]ˡ : ∀ (g₁ g₂ g : Graph L) (l : L) →
  ((g₁ + g₂) [ g / l ]ˡ) ≃ ((g₁ [ g / l ]ˡ) + (g₂ [ g / l ]ˡ))
+-[]ˡ g₁ g₂ g n = record
  { iso    = let open Type.≃-Reasoning in
             begin
               Node ((g₁ + g₂) [ g / n ]ˡ)
             ≡⟨⟩
               (Σ (Node g₁ ⊎ Node g₂) (λ n' → label (g₁ ∪ g₂) n' ≢ n) ⊎
                Σ (Node g₁ ⊎ Node g₂) (λ n' → label (g₁ ∪ g₂) n' ≡ n × Node g))
             ≃⟨ Type.≃-⊎ (Type.Σ-⊎ _) (Type.Σ-⊎ _) ⟩
               ((Σ (Node g₁) (λ n' → label g₁ n' ≢ n) ⊎
                 Σ (Node g₂) (λ n' → label g₂ n' ≢ n))
                ⊎
                (Σ (Node g₁) (λ n' → label g₁ n' ≡ n × Node g) ⊎
                 Σ (Node g₂) (λ n' → label g₂ n' ≡ n × Node g)))
             ≃⟨ Type.≃-⊎-lem ⟩
               ((Σ (Node g₁) (λ n' → label g₁ n' ≢ n) ⊎
                 Σ (Node g₁) (λ n' → label g₁ n' ≡ n × Node g))
                ⊎
                (Σ (Node g₂) (λ n' → label g₂ n' ≢ n) ⊎
                 Σ (Node g₂) (λ n' → label g₂ n' ≡ n × Node g)))
             ≡⟨⟩
               Node ((g₁ [ g / n ]ˡ) + (g₂ [ g / n ]ˡ))
             ∎
  ; edges₁ = λ where
    (inj₁ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₂ (inj₂ y , q)) x→y → x→y
    (inj₂ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₂ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ (inj₁ x , p)) (inj₂ (inj₁ y , q)) (inj₁ x→y) → inj₁ x→y
    (inj₂ (inj₁ x , p)) (inj₂ (inj₁ y , q)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
    (inj₂ (inj₁ x , p)) (inj₂ (inj₂ y , q)) x→y → tt
    (inj₂ (inj₂ x , p)) (inj₂ (inj₁ y , q)) (inj₁ ())
    (inj₂ (inj₂ x , p)) (inj₂ (inj₁ y , q)) (inj₂ (() , x→y))
    (inj₂ (inj₂ x , p)) (inj₂ (inj₂ y , q)) (inj₁ x→y) → inj₁ x→y
    (inj₂ (inj₂ x , p)) (inj₂ (inj₂ y , q)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
  ; edges₂ = λ where
    (inj₁ (inj₁ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₁ (inj₂ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) (inj₁ x→y) → inj₁ x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
    (inj₁ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₂ (inj₂ y)) x→y → inj₁ x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) (inj₁ x→y) → inj₁ x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
  ; labels = λ where
    (inj₁ (inj₁ x , p)) → refl
    (inj₁ (inj₂ x , p)) → refl
    (inj₂ (inj₁ x , p)) → refl
    (inj₂ (inj₂ x , p)) → refl
  }

-- Lemma A.17

∪-[]ˡ : ∀ (g₁ g₂ g : Graph L) (l : L) →
  ((g₁ ∪ g₂) [ g / l ]ˡ) ≃ ((g₁ [ g / l ]ˡ) ∪ (g₂ [ g / l ]ˡ))
∪-[]ˡ g₁ g₂ g n = record
  { iso    = let open Type.≃-Reasoning in
             begin
               Node ((g₁ ∪ g₂) [ g / n ]ˡ)
             ≡⟨⟩
               (Σ (Node g₁ ⊎ Node g₂) (λ n' → label (g₁ ∪ g₂) n' ≢ n) ⊎
                Σ (Node g₁ ⊎ Node g₂) (λ n' → label (g₁ ∪ g₂) n' ≡ n × Node g))
             ≃⟨ Type.≃-⊎ (Type.Σ-⊎ _) (Type.Σ-⊎ _) ⟩
               ((Σ (Node g₁) (λ n' → label g₁ n' ≢ n) ⊎
                 Σ (Node g₂) (λ n' → label g₂ n' ≢ n))
                ⊎
                (Σ (Node g₁) (λ n' → label g₁ n' ≡ n × Node g) ⊎
                 Σ (Node g₂) (λ n' → label g₂ n' ≡ n × Node g)))
             ≃⟨ Type.≃-⊎-lem ⟩
               ((Σ (Node g₁) (λ n' → label g₁ n' ≢ n) ⊎
                 Σ (Node g₁) (λ n' → label g₁ n' ≡ n × Node g))
                ⊎
                (Σ (Node g₂) (λ n' → label g₂ n' ≢ n) ⊎
                 Σ (Node g₂) (λ n' → label g₂ n' ≡ n × Node g)))
             ≡⟨⟩
               Node ((g₁ [ g / n ]ˡ) ∪ (g₂ [ g / n ]ˡ))
             ∎
  ; edges₁ = λ where
    (inj₁ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ (inj₁ y , q)) x→y → x→y
    (inj₁ (inj₁ x , p)) (inj₂ (inj₂ y , q)) x→y → x→y
    (inj₁ (inj₂ x , p)) (inj₂ (inj₂ y , q)) x→y → x→y
    (inj₂ (inj₁ x , p)) (inj₁ (inj₁ y , q)) x→y → x→y
    (inj₂ (inj₁ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ (inj₂ x , p)) (inj₁ (inj₂ y , q)) x→y → x→y
    (inj₂ (inj₁ x , p)) (inj₂ (inj₁ y , q)) (inj₁ x→y) → inj₁ x→y
    (inj₂ (inj₁ x , p)) (inj₂ (inj₁ y , q)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
    (inj₂ (inj₂ x , p)) (inj₂ (inj₁ y , q)) (inj₁ ())
    (inj₂ (inj₂ x , p)) (inj₂ (inj₁ y , q)) (inj₂ (() , x→y))
    (inj₂ (inj₂ x , p)) (inj₂ (inj₂ y , q)) (inj₁ x→y) → inj₁ x→y
    (inj₂ (inj₂ x , p)) (inj₂ (inj₂ y , q)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
  ; edges₂ = λ where
    (inj₁ (inj₁ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₁ (inj₂ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₁ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) (inj₁ x→y) → inj₁ x→y
    (inj₁ (inj₂ x)) (inj₁ (inj₂ y)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
    (inj₁ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₁ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₁ (inj₂ x)) (inj₂ (inj₂ y)) x→y → inj₁ x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₁ x)) (inj₂ (inj₂ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₁ y)) x→y → x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) (inj₁ x→y) → inj₁ x→y
    (inj₂ (inj₂ x)) (inj₂ (inj₂ y)) (inj₂ (refl , x→y)) → inj₂ (refl , x→y)
  ; labels = λ where
    (inj₁ (inj₁ x , p)) → refl
    (inj₁ (inj₂ x , p)) → refl
    (inj₂ (inj₁ x , p)) → refl
    (inj₂ (inj₂ x , p)) → refl
  }

-- Lemma A.18

≃-[]ˡ : ∀ (g₁ g₂ g : Graph L) (l : L) →
  g₁ ≃ g₂ →
  (g₁ [ g / l ]ˡ) ≃ (g₂ [ g / l ]ˡ)
≃-[]ˡ g₁ g₂ g l g₁≃g₂ = record
  { iso    = let open Type.≃-Reasoning in
             begin
               Node (g₁ [ g / l ]ˡ)
             ≡⟨⟩
               (Σ (Node g₁) (λ n' → label g₁ n' ≢ l) ⊎
                Σ (Node g₁) (λ n' → label g₁ n' ≡ l × Node g))
             ≃⟨ Type.≃-⊎ (Type.Σ-≃ Node (λ g' n' → label g' n' ≢ l) g₁ g₂ (≃.iso g₁≃g₂)
                                   λ x → cong (λ ■ → ■ ≢ l) (labels x))
                         (Type.Σ-≃ Node (λ g' n' → label g' n' ≡ l × Node g) g₁ g₂ (≃.iso g₁≃g₂)
                                   λ x → cong (λ ■ → ■ ≡ l × Node g) (labels x)) ⟩
               (Σ (Node g₂) (λ n' → label g₂ n' ≢ l) ⊎
                Σ (Node g₂) (λ n' → label g₂ n' ≡ l × Node g))
             ≡⟨⟩
               Node (g₂ [ g / l ]ˡ)
             ∎
  ; edges₁ = λ where
    (inj₁ (x , p)) (inj₁ (y , q)) x→y → edges₁ x y x→y
    (inj₁ (x , p)) (inj₂ (y , q)) x→y → edges₁ x y x→y
    (inj₂ (x , p)) (inj₁ (y , q)) x→y → edges₁ x y x→y
    (inj₂ (x , p , x')) (inj₂ (y , q , y')) (inj₁ x→y) → inj₁ (edges₁ x y x→y)
    (inj₂ (x , p , x')) (inj₂ (y , q , y')) (inj₂ (refl , x→y)) →
      inj₂ (refl , subst₂ (Edge g) ? {!!} x→y)
  ; edges₂ = λ where
    (inj₁ (x , p)) (inj₁ (y , q)) x→y → edges₂ x y x→y
    (inj₁ (x , p)) (inj₂ (y , q)) x→y → edges₂ x y x→y
    (inj₂ (x , p)) (inj₁ (y , q)) x→y → edges₂ x y x→y
    (inj₂ (x , p)) (inj₂ (y , q)) (inj₁ x→y) → inj₁ (edges₂ x y x→y)
    (inj₂ (x , p)) (inj₂ (y , q)) (inj₂ (refl , x→y)) →
      inj₂ (refl , subst₂ (Edge g) {!!} {!!} x→y)
  ; labels = λ where
    (inj₁ (x , p)) → labels x
    (inj₂ (x , p , x')) → {!!}
  } where open ≃ g₁≃g₂

-- Lemma A.19

≲-[]ˡ : ∀ (g₁ g₂ g : Graph L) (l : L) →
  g₁ ≲ g₂ →
  (g₁ [ g / l ]ˡ) ≲ (g₂ [ g / l ]ˡ)
≲-[]ˡ = {!!}

-- Lemma A.20

-- For any graph representation, a topological order exists.

-- TODO

-- FIXME: MISSING LEMMA

top-∅ : TopOrd (∅ {L = L})
top-∅ = top-ord 0 Type.⊥≃Fin0 λ()

top-[] : ∀ (l : L) → TopOrd [ l ]
top-[] l = top-ord 1 Type.⊤≃Fin1 λ x y ()

-- Definition A.21 & Lemma A.22

top-+ : ∀ {g₁ g₂ : Graph L} →
  TopOrd g₁ →
  TopOrd g₂ →
  TopOrd (g₁ + g₂)
top-+ {g₁ = g₁} {g₂ = g₂} o₁ o₂ = record
  { order   = TopOrd.order o₁ ℕ.+ TopOrd.order o₂
  ; iso     = let open Type.≃-Reasoning in
              begin
                (Node g₁ ⊎ Node g₂)
              ≃⟨ Type.≃-⊎ (TopOrd.iso o₁) (TopOrd.iso o₂) ⟩
                (Fin (TopOrd.order o₁) ⊎ Fin (TopOrd.order o₂))
              ≃⟨ Type.Fin⊎Fin≃Fin ⟩
                Fin (TopOrd.order o₁ ℕ.+ TopOrd.order o₂)
              ∎
  ; ordered = λ where
    (inj₁ x) (inj₁ y) x→y →
      let open ℕP.≤-Reasoning in
      begin
        suc (Fin.toℕ (Fin.inject≤ (TopOrd.to o₁ x) _))
      ≡⟨ cong suc (FinP.toℕ-inject≤ _ _) ⟩
        suc (Fin.toℕ (TopOrd.to o₁ x))
      ≤⟨ TopOrd.ordered o₁ x y x→y ⟩
        Fin.toℕ (TopOrd.to o₁ y)
      ≡⟨ sym (FinP.toℕ-inject≤ _ _) ⟩
        Fin.toℕ (Fin.inject≤ (TopOrd.to o₁ y) _)
      ∎
    (inj₁ x) (inj₂ y) x→y →
      let open ℕP.≤-Reasoning in
      begin
        suc (Fin.toℕ (Fin.inject≤ (TopOrd.to o₁ x) _))
      ≡⟨ cong suc (FinP.toℕ-inject≤ _ _) ⟩
        suc (Fin.toℕ (TopOrd.to o₁ x))
      ≤⟨ FinP.toℕ<n _ ⟩
        TopOrd.order o₁
      ≤⟨ ℕP.m≤m+n _ _ ⟩
        TopOrd.order o₁ ℕ.+ Fin.toℕ (TopOrd.to o₂ y)
      ≡⟨ sym (FinP.toℕ-↑ʳ _ (TopOrd.to o₂ y)) ⟩
        Fin.toℕ (TopOrd.order o₁ Fin.↑ʳ TopOrd.to o₂ y)
      ∎
    (inj₂ x) (inj₂ y) x→y →
      let open ℕP.≤-Reasoning in
      begin
        suc (Fin.toℕ (TopOrd.order o₁ Fin.↑ʳ TopOrd.to o₂ x))
      ≡⟨ cong suc (FinP.toℕ-↑ʳ _ (TopOrd.to o₂ x)) ⟩
        suc (TopOrd.order o₁ ℕ.+ Fin.toℕ (TopOrd.to o₂ x))
      ≡⟨ sym (ℕP.+-suc _ _) ⟩
        TopOrd.order o₁ ℕ.+ suc (Fin.toℕ (TopOrd.to o₂ x))
      ≤⟨ ℕP.+-monoʳ-≤ (TopOrd.order o₁) (TopOrd.ordered o₂ x y x→y) ⟩
        TopOrd.order o₁ ℕ.+ Fin.toℕ (TopOrd.to o₂ y)
      ≡⟨ sym (FinP.toℕ-↑ʳ _ (TopOrd.to o₂ y)) ⟩
        Fin.toℕ (TopOrd.order o₁ Fin.↑ʳ TopOrd.to o₂ y)
      ∎
  }

-- Lemma A.23

-- TODO

-- Lemma A.24

top-∪₁ : ∀ {g₁ g₂ : Graph L} →
  TopOrd g₁ →
  TopOrd g₂ →
  TopOrd (g₁ ∪ g₂)
top-∪₁ {g₁ = g₁} {g₂ = g₂} o₁ o₂ = record
  { order   = TopOrd.order o₁ ℕ.+ TopOrd.order o₂
  ; iso     = let open Type.≃-Reasoning in
              begin
                (Node g₁ ⊎ Node g₂)
              ≃⟨ Type.≃-⊎ (TopOrd.iso o₁) (TopOrd.iso o₂) ⟩
                (Fin (TopOrd.order o₁) ⊎ Fin (TopOrd.order o₂))
              ≃⟨ Type.Fin⊎Fin≃Fin ⟩
                Fin (TopOrd.order o₁ ℕ.+ TopOrd.order o₂)
              ∎
  ; ordered = λ where
    (inj₁ x) (inj₁ y) x→y →
      let open ℕP.≤-Reasoning in
      begin
        suc (Fin.toℕ (Fin.inject≤ (TopOrd.to o₁ x) _))
      ≡⟨ cong suc (FinP.toℕ-inject≤ _ _) ⟩
        suc (Fin.toℕ (TopOrd.to o₁ x))
      ≤⟨ TopOrd.ordered o₁ x y x→y ⟩
        Fin.toℕ (TopOrd.to o₁ y)
      ≡⟨ sym (FinP.toℕ-inject≤ _ _) ⟩
        Fin.toℕ (Fin.inject≤ (TopOrd.to o₁ y) _)
      ∎
    (inj₂ x) (inj₂ y) x→y →
      let open ℕP.≤-Reasoning in
      begin
        suc (Fin.toℕ (TopOrd.order o₁ Fin.↑ʳ TopOrd.to o₂ x))
      ≡⟨ cong suc (FinP.toℕ-↑ʳ _ (TopOrd.to o₂ x)) ⟩
        suc (TopOrd.order o₁ ℕ.+ Fin.toℕ (TopOrd.to o₂ x))
      ≡⟨ sym (ℕP.+-suc _ _) ⟩
        TopOrd.order o₁ ℕ.+ suc (Fin.toℕ (TopOrd.to o₂ x))
      ≤⟨ ℕP.+-monoʳ-≤ (TopOrd.order o₁) (TopOrd.ordered o₂ x y x→y) ⟩
        TopOrd.order o₁ ℕ.+ Fin.toℕ (TopOrd.to o₂ y)
      ≡⟨ sym (FinP.toℕ-↑ʳ _ (TopOrd.to o₂ y)) ⟩
        Fin.toℕ (TopOrd.order o₁ Fin.↑ʳ TopOrd.to o₂ y)
      ∎
  }

-- TODO: second ordering (if needed)

-- Lemma A.25

≃-top : ∀ {g₁ g₂ : Graph L} →
  g₁ ≃ g₂ →
  TopOrd g₁ →
  TopOrd g₂
≃-top g₁≃g₂ o₁ = record
  { order   = o₁.order
  ; iso     = Type.≃-trans (Type.≃-sym g₁≃g₂.iso) o₁.iso
  ; ordered = λ x y x→y → o₁.ordered (g₁≃g₂.from x) (g₁≃g₂.from y) (g₁≃g₂.edges₂ _ _ x→y) 
  } where module o₁    = TopOrd o₁
          module g₁≃g₂ = ≃ g₁≃g₂

-- Lemma A.26

≲-top : ∀ {g₁ g₂ : Graph L} →
  g₁ ≲ g₂ →
  TopOrd g₂ →
  TopOrd g₁
≲-top g₁≲g₂ o₂ = record
  { order   = o₂.order
  ; iso     = Type.≃-trans (g₁≲g₂.iso) o₂.iso
  ; ordered = λ x y x→y → o₂.ordered (g₁≲g₂.to x) (g₁≲g₂.to y) (g₁≲g₂.edges _ _ x→y) 
  } where module o₂    = TopOrd o₂
          module g₁≲g₂ = ≲ g₁≲g₂

-- Lemma A.27

Traceable : ∀ (g : Graph L) → Set _
Traceable g = Σ[ o ∈ TopOrd g ] ∀ (o' : TopOrd g) → o ≡ o'

traceable-+ : ∀ (g₁ g₂ : Graph L) →
  Traceable g₁ →
  Traceable g₂ →
  Traceable (g₁ + g₂)
traceable-+ g₁ g₂ (o₁ , t₁) (o₂ , t₂) =
  top-+ o₁ o₂ ,
  λ where
    (top-ord order iso ordered) → H.≅-to-≡ $ cong₃ top-ord {!!} {!!} {!!}

traceable-+' : ∀ (g₁ g₂ : Graph L) →
  Traceable (g₁ + g₂) →
  Traceable g₁ × Traceable g₂
traceable-+' g₁ g₂ (o , t) = t₁ , t₂ where
  t₁ = {!!}
  t₂ = {!!}

-- TODO

-- Lemma A.28

≃-top-many : ∀ (g₁ g₂ : Graph L) →
  g₁ ≃ g₂ →
  (o₁ o₁' : Traceable g₁) →
  o₁ ≢ o₁' →
  Σ[ o₂ ∈ Traceable g₂ ] Σ[ o₂' ∈ Traceable g₂ ] o₂ ≢ o₂'
≃-top-many = {!!}

-- own

filter : (L → Set) → Graph L → Graph L
filter P g = graph (Σ[ n ∈ Node g ] P (label g n))
                   (λ (n₁ , p₁) (n₂ , p₂) → Edge g n₁ n₂)
                   (λ (n , p) → label g n)
