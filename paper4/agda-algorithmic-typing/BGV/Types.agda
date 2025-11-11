module BGV.Types where

open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Data.Empty using (⊥; ⊥-elim)

open import BGV.Multiplicities
open import BGV.Effect
open import BGV.Util.Decidable

data Ownership : Set where
  borrowed owned : Ownership

variable
  b b₁ b₂ : Ownership

data Op : Set where
  ‼ ⁈ : Op

variable
  Ω Ω₁ Ω₂ : Op

mutual
  data Session : Ownership → Set where
    return       : Session borrowed
    end          : Op → Session owned
    op[_]_⍮_     : Op → Type → Session b → Session b
    choice[_]_⍮_ : Op → Session b → Session b → Session b

  SessionO = Session owned
  SessionB = Session borrowed

  data Type : Set where
    Chan      : ∀ b → Session b → Type
    _+_       : Type → Type → Type
    _×[_]_    : Type → PMult → Type → Type
    _–[_⍮_]→_ : Type → Mult → Effect → Type → Type
    Unit      : Type

dual-op : Op → Op
dual-op ‼ = ⁈
dual-op ⁈ = ‼

dual : Session b → Session b
dual return = return
dual (end o) = end (dual-op o)
dual (op[ o ] t ⍮ s) = op[ dual-op o ] t ⍮ dual s
dual (choice[ o ] s₁ ⍮ s₂) = choice[ dual-op o ] dual s₁ ⍮ dual s₂

variable
  t t₁ t₂ t₃ t' t₁' t₂' t₃' t₁₁ t₁₂ t₂₁ t₂₂ : Type
  s s₁ s₂ s₃ s' s₁' s₂' s₃' : Session b
  s₁₁ s₁₂ s₂₁ s₂₂ : Session b

data Unr : Type → Set where
  unr-Unit : Unr Unit
  unr-→    : Unr (t₁ –[ ∞ ⍮ ϕ ]→ t₂)
  unr-×    : Unr t₁ → Unr t₂ → Unr (t₁ ×[ p ] t₂)
  unr-+    : Unr t₁ → Unr t₂ → Unr (t₁ + t₂)
  
Ord : Type → Set
Ord t = ¬ Unr t

-- Properties

Unr? : ∀ t → Dec (Unr t)
Unr? Unit = yes unr-Unit
Unr? (Chan o s) = no λ()
Unr? (t₁ –[ m ⍮ ϕ ]→ t₂) with m
…                           | ∞ = yes unr-→
…                           | 𝟙 = no λ ()
…                           | ≻ = no λ ()
…                           | ≺ = no λ ()
Unr? (t₁ + t₂) with Unr? t₁ | Unr? t₂
…                      | yes u₁  | yes u₂ = yes (unr-+ u₁ u₂)
…                      | no ¬u₁  | _      = no λ { (unr-+ u₁ u₂) → ¬u₁ u₁ }
…                      | _       | no ¬u₂ = no λ { (unr-+ u₁ u₂) → ¬u₂ u₂ }
Unr? (t₁ ×[ m ] t₂) with Unr? t₁ | Unr? t₂
…                      | yes u₁  | yes u₂ = yes (unr-× u₁ u₂)
…                      | no ¬u₁  | _      = no λ { (unr-× u₁ u₂) → ¬u₁ u₁ }
…                      | _       | no ¬u₂ = no λ { (unr-× u₁ u₂) → ¬u₂ u₂ }

_++ˢ_ : SessionB → Session b → Session b
return                  ++ˢ s₂ = s₂
(op[ o ] x ⍮ s₁)        ++ˢ s₂ = op[ o ] x ⍮ (s₁ ++ˢ s₂)
(choice[ o ] s₁₁ ⍮ s₁₂) ++ˢ s₂ = choice[ o ] (s₁₁ ++ˢ s₂) ⍮ (s₁₂ ++ˢ s₂)

_≟ᵒ'_ : ∀ (x y : Ownership) → Dec (x ≡ y)
borrowed ≟ᵒ' borrowed = yes refl
borrowed ≟ᵒ' owned    = no λ()
owned    ≟ᵒ' borrowed = no λ()
owned    ≟ᵒ' owned    = yes refl

_≟ᵒ_ : ∀ (x y : Op) → Dec (x ≡ y)
‼ ≟ᵒ ‼ = yes refl
‼ ≟ᵒ ⁈ = no λ()
⁈ ≟ᵒ ‼ = no λ()
⁈ ≟ᵒ ⁈ = yes refl

instance
  DecEq-Ownership : DecEq Ownership
  DecEq-Ownership = _ ≟ᵒ' _

  DecEq-Op : DecEq Op
  DecEq-Op = _ ≟ᵒ _

mutual
  _≟ᵗ_ : ∀ (x y : Type) → Dec (x ≡ y)
  Chan b x ≟ᵗ Chan b₁ x₁
    with b ≟ b₁
  … | no q = no λ { refl → q refl }
  … | yes refl
    with x ≟ x₁
  … | no q = no λ { refl → q refl }
  … | yes refl = yes refl
  (x + x₁) ≟ᵗ (y + y₁)
    with x ≟ y | x₁ ≟ y₁
  … | yes refl | yes refl = yes refl
  … | no q | _ = no λ { refl → q refl }
  … | _ | no q = no λ { refl → q refl }
  (x ×[ x₁ ] x₂) ≟ᵗ (y ×[ x₃ ] y₁)
    with x ≟ y | x₁ ≟ x₃ | x₂ ≟ y₁
  … | yes refl | yes refl | yes refl = yes refl
  … | no q | _ | _ = no λ { refl → q refl }
  … | _ | no q | _ = no λ { refl → q refl }
  … | _ | _ | no q = no λ { refl → q refl }
  (x –[ x₁ ⍮ x₂ ]→ x₃) ≟ᵗ (y –[ x₄ ⍮ x₅ ]→ y₁)
    with x ≟ y | x₁ ≟ x₄ | x₂ ≟ x₅ | x₃ ≟ y₁
  … | yes refl | yes refl | yes refl | yes refl = yes refl
  … | no q | _ | _ | _ = no λ { refl → q refl }
  … | _ | no q | _ | _ = no λ { refl → q refl }
  … | _ | _ | no q | _ = no λ { refl → q refl }
  … | _ | _ | _ | no q = no λ { refl → q refl }
  Unit ≟ᵗ Unit                                 = yes refl
  Chan b x ≟ᵗ (y + y₁)                   = no λ()
  Chan b x ≟ᵗ (y ×[ x₁ ] y₁)             = no λ()
  Chan b x ≟ᵗ (y –[ x₁ ⍮ x₂ ]→ y₁)       = no λ()
  Chan b x ≟ᵗ Unit                       = no λ()
  (x + x₁) ≟ᵗ Chan b x₂                  = no λ()
  (x + x₁) ≟ᵗ (y ×[ x₂ ] y₁)             = no λ()
  (x + x₁) ≟ᵗ (y –[ x₂ ⍮ x₃ ]→ y₁)       = no λ()
  (x + x₁) ≟ᵗ Unit                       = no λ()
  (x ×[ x₁ ] x₂) ≟ᵗ Chan b x₃            = no λ()
  (x ×[ x₁ ] x₂) ≟ᵗ (y + y₁)             = no λ()
  (x ×[ x₁ ] x₂) ≟ᵗ (y –[ x₃ ⍮ x₄ ]→ y₁) = no λ()
  (x ×[ x₁ ] x₂) ≟ᵗ Unit                 = no λ()
  (x –[ x₁ ⍮ x₂ ]→ x₃) ≟ᵗ Chan b x₄      = no λ()
  (x –[ x₁ ⍮ x₂ ]→ x₃) ≟ᵗ (y + y₁)       = no λ()
  (x –[ x₁ ⍮ x₂ ]→ x₃) ≟ᵗ (y ×[ x₄ ] y₁) = no λ()
  (x –[ x₁ ⍮ x₂ ]→ x₃) ≟ᵗ Unit           = no λ()
  Unit ≟ᵗ Chan b x                       = no λ()
  Unit ≟ᵗ (y + y₁)                       = no λ()
  Unit ≟ᵗ (y ×[ x ] y₁)                  = no λ()
  Unit ≟ᵗ (y –[ x ⍮ x₁ ]→ y₁)            = no λ()

  _≟ˢ_ : ∀ {b} (x y : Session b) → Dec (x ≡ y)
  return ≟ˢ return = yes refl
  return ≟ˢ (op[ x ] x₁ ⍮ y) = no λ ()
  end x ≟ˢ end x₁
    with x ≟ x₁
  … | yes refl = yes refl
  … | no q = no λ { refl → q refl }
  end x ≟ˢ (op[ x₁ ] x₂ ⍮ y) = no λ ()
  (op[ x ] x₁ ⍮ x₂) ≟ˢ return = no λ ()
  (op[ x ] x₁ ⍮ x₂) ≟ˢ end x₃ = no λ ()
  (op[ x ] x₁ ⍮ x₂) ≟ˢ (op[ x₃ ] x₄ ⍮ y)
    with x ≟ x₃ | x₁ ≟ x₄ | x₂ ≟ y
  … | yes refl | yes refl | yes refl = yes refl
  … | no q | _ | _ = no λ { refl → q refl }
  … | _ | no q | _ = no λ { refl → q refl }
  … | _ | _ | no q = no λ { refl → q refl }
  return ≟ˢ (choice[ x ] s₂ ⍮ s₃) = no λ ()
  end x ≟ˢ (choice[ x₁ ] s₂ ⍮ s₃) = no λ ()
  (op[ x ] x₁ ⍮ s₁) ≟ˢ (choice[ x₂ ] s₂ ⍮ s₃) = no λ ()
  (choice[ x ] s₁ ⍮ s₂) ≟ˢ return = no λ ()
  (choice[ x ] s₁ ⍮ s₂) ≟ˢ end x₁ = no λ ()
  (choice[ x ] s₁ ⍮ s₂) ≟ˢ (op[ x₁ ] x₂ ⍮ s₃) = no λ ()
  (choice[ x ] s₁ ⍮ s₂) ≟ˢ (choice[ x₁ ] s₃ ⍮ s₄)
    with x ≟ x₁ | s₁ ≟ s₃ | s₂ ≟ s₄
  … | yes refl | yes refl | yes refl = yes refl
  … | no q | _ | _ = no λ { refl → q refl }
  … | _ | no q | _ = no λ { refl → q refl }
  … | _ | _ | no q = no λ { refl → q refl }

  instance
    DecEq-Type : DecEq Type
    DecEq-Type = _ ≟ᵗ _

    DecEq-Session : ∀ {o} → DecEq (Session o)
    DecEq-Session = _ ≟ˢ _

open import Data.Maybe using (Maybe) renaming (just to some; nothing to none)

-- _%ˢ_ : SessionO → SessionB → Maybe SessionO
-- s₁ %ˢ return     = some s₁
-- (op[ o₁ ] x₁ ⍮ s₁) %ˢ (op[ o₂ ] x₂ ⍮ s₂) with o₁ ≟ o₂ | x₁ ≟ x₂
-- … | yes _ | yes _ = s₁ %ˢ s₂
-- … | _     | _     = none
-- _ %ˢ (op[ o ] x ⍮ s₂) = none

open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax; Σ)

op-injective : (op[ Ω₁ ] t₁ ⍮ s₁) ≡ (op[ Ω₂ ] t₂ ⍮ s₂) → Ω₁ ≡ Ω₂ × t₁ ≡ t₂ × s₁ ≡ s₂
op-injective refl = refl , refl , refl

op-injective₁ : (op[ Ω₁ ] t₁ ⍮ s₁) ≡ (op[ Ω₂ ] t₂ ⍮ s₂) → Ω₁ ≡ Ω₂
op-injective₁ refl = refl

op-injective₂ : (op[ Ω₁ ] t₁ ⍮ s₁) ≡ (op[ Ω₂ ] t₂ ⍮ s₂) → t₁ ≡ t₂
op-injective₂ refl = refl

op-injective₃ : (op[ Ω₁ ] t₁ ⍮ s₁) ≡ (op[ Ω₂ ] t₂ ⍮ s₂) → s₁ ≡ s₂
op-injective₃ refl = refl

choice-injective₂ : (choice[ Ω₁ ] s₁₁ ⍮ s₂₁) ≡ (choice[ Ω₂ ] s₁₂ ⍮ s₂₂) → s₁₁ ≡ s₁₂
choice-injective₂ refl = refl

choice-injective₃ : (choice[ Ω₁ ] s₁₁ ⍮ s₂₁) ≡ (choice[ Ω₂ ] s₁₂ ⍮ s₂₂) → s₂₁ ≡ s₂₂
choice-injective₃ refl = refl

++ˢ-injective₂ : ∀ s →
  s ++ˢ s₁ ≡ s ++ˢ s₂ →
  s₁ ≡ s₂
++ˢ-injective₂ return eq = eq
++ˢ-injective₂ (op[ x ] x₁ ⍮ s) eq = ++ˢ-injective₂ _ (op-injective₃ eq)
++ˢ-injective₂ (choice[ x ] s₁₁ ⍮ s₁₂) eq = ++ˢ-injective₂ _ (choice-injective₂ eq)

Chan-injective : ∀ {b₁ b₂ s₁ s₂} → Chan b₁ s₁ ≡ Chan b₂ s₂ → Σ (b₁ ≡ b₂) (λ { refl → s₁ ≡ s₂ })
Chan-injective refl = refl , refl

infixl 5 _%?_

_%?_ : (s : Session b) → (s₁ : SessionB) → Dec (Σ[ s₂ ∈ Session b ] s ≡ s₁ ++ˢ s₂)  
s %? return = yes (s , refl)
end o %? (op[ o₁ ] x₁ ⍮ s₁) = no λ()
return %? (op[ o₁ ] x₁ ⍮ s₁) = no λ()
(op[ o ] x ⍮ s) %? (op[ o₁ ] x₁ ⍮ s₁)
 with o ≟ o₁ | x ≟ x₁ | s %? s₁
…   | yes refl | yes refl | yes (s₂ , refl)  = yes (s₂ , refl)
…   | yes refl | yes refl | no  ¬s≟s₁ = no (λ (s₂ , eq) → ¬s≟s₁ (_ , op-injective₃ eq))
…   | no ¬o≡o₁ | _        | _ = no λ (s₂ , eq) → ¬o≡o₁ (op-injective₁ eq)
…   | _        | no ¬x≡x₁ | _ = no λ (s₂ , eq) → ¬x≡x₁ (op-injective₂ eq)
return %? (choice[ x ] s₂ ⍮ s₃) = no λ ()
end x %? (choice[ x₁ ] s₂ ⍮ s₃) = no λ ()
(op[ x ] x₁ ⍮ s₁) %? (choice[ x₂ ] s₂ ⍮ s₃) = no λ ()
(choice[ x ] s₁ ⍮ s₂) %? (op[ x₁ ] x₂ ⍮ s₃) = no λ ()
(choice[ Ω₁ ] s₁₁ ⍮ s₁₂) %? (choice[ Ω₂ ] s₂₁ ⍮ s₂₂)
 with Ω₁ ≟ Ω₂ | s₁₁ %? s₂₁ | s₁₂ %? s₂₂
… | no q | _ | _ = no λ { (s , refl) → q refl }
… | _ | no q | _ = no λ { (s , refl) → q (_ , refl) }
… | _ | _ | no q = no λ { (s , refl) → q (_ , refl) }
… | yes refl | yes (s₁ , refl) | yes (s₂ , refl)
 with s₁ ≟ s₂
… | no q = no (λ { (s , eq) → q (trans (++ˢ-injective₂ s₂₁ (choice-injective₂ eq))
                                       (sym (++ˢ-injective₂ s₂₂ (choice-injective₃ eq)))) })
… | yes refl = yes (_ , refl)

infixl 5 _%_

_%_ : Session b → SessionB → Maybe (Session b)
s % s₁ with s %? s₁
… | yes (s₂ , _) = some s₂
… | no _ = none

%-some : ∀ s₁ (s₂ : Session b) →
  (s₁ ++ˢ s₂) % s₁ ≡ some s₂
%-some s₁ s₂ with (s₁ ++ˢ s₂) %? s₁
… | no ¬p = ⊥-elim (¬p (s₂ , refl))
… | yes (s₂' , eq) = cong some (++ˢ-injective₂ s₁ (sym eq))

AnySession = ∃[ b ] Session b

_+++ˢ_ : AnySession → AnySession → AnySession
(borrowed , s₁) +++ˢ (b₂ , s₂) = (b₂ , (s₁ ++ˢ s₂))
(owned ,    s₁) +++ˢ (b₂ , s₂) = (owned , s₁)

Chan? : (t : Type) → Dec (∃[ b ] Σ[ s ∈ Session b ] t ≡ Chan b s)
Chan? (Chan b s)          = yes (b , s , refl)
Chan? (t₁ + t₂)           = no λ { (b , s , ()) }
Chan? (t₁ ×[ p ] t₂)      = no λ { (b , s , ()) }
Chan? (t₁ –[ m ⍮ ϕ ]→ t₂) = no λ { (b , s , ()) }
Chan? Unit                = no λ { (b , s , ()) }

