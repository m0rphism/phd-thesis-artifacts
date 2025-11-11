module VGR.Lemmas where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.List using (List; []; _∷_)
open import Data.Product
open import Data.Sum

open import Function

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning -- using (begin_; _≡⟨⟩_; _∎)

open import Relation.Nullary using (Dec; yes; no; ¬_)

open import Identifier
open import Extensionality
open import VGR.Syntax

private
  variable
    α β α′ α₁ α₂ : Alpha
    σ σ′ σ₁ σ₂ σ₃ σ₁′ : Store
    S S′ S₁ S₂ : Session
    α#σ : α # σ
    α₁#σ : α₁ # σ
    α#σ₁ : α # σ₁
    α#σ₂ : α # σ₂
    α′#σ′ : α′ # σ′
    α₂#σ₂ : α₂ # σ₂

-- remove one binding from a store

mutual
  _/-_ : Store → Alpha → Store
  `emp /- α = `emp
  (σ , α₁ ⦂ S [ α₁#σ ]) /- α with α₁ α=? α
  ... | no ¬p = (σ /- α) , α₁ ⦂ S [ #-/- σ α₁#σ ]
  ... | yes refl = σ

  #-/- : ∀ {α₁} {α} σ → α₁ # σ → α₁ # (σ /- α)
  #-/- `emp α₁#σ = #emp
  #-/- {α₁} {α} (σ , α₂ ⦂ S [ α₂#σ ]) (#cons α₁#σ α₁≢α₂) with α₂ α=? α
  ... | no ¬p = #cons (#-/- σ α₁#σ) α₁≢α₂
  ... | yes refl = α₁#σ

-- difference of stores

_\\_ : Store → Store → Store
σ₁ \\ `emp = σ₁
σ₁ \\ (σ₂ , α ⦂ S [ α#σ ]) = (σ₁ /- α) \\ σ₂

\\-emp : ∀ σ → σ \\ `emp ≡ σ
\\-emp σ = refl

emp-\\ : ∀ σ → `emp \\ σ ≡ `emp
emp-\\ `emp = refl
emp-\\ (σ , α ⦂ S [ α#σ ]) = emp-\\ σ

-- projection of store to a list of alphas
-- store-dom (store-project σ₁ (store-dom σ₂)) ≡ store-dom (σ₁ ∩ σ₂)

store-dom : Store → List Alpha
store-dom `emp = []
store-dom (σ , α ⦂ _ [ _ ]) = α ∷ store-dom σ

open import Data.List.Membership.DecPropositional _α=?_

mutual
  store-project : Store → List Alpha → Store
  store-project `emp αs = `emp
  store-project (σ , α ⦂ S [ α#σ ]) αs
    with α ∈? αs
  ... | no ¬p = store-project σ αs
  ... | yes p = (store-project σ αs) , α ⦂ S [ #-store-project σ α αs α#σ ]

  #-store-project : ∀ σ α (αs : List Alpha) → α # σ → α # store-project σ αs
  #-store-project `emp α αs α#σ = #emp
  #-store-project (σ , α₁ ⦂ S [ α#σ₁ ]) α αs α#σ
    with α₁ ∈? αs
  ... | no ¬p = #-store-project σ α αs (#-weak α#σ)
  ... | yes p
    with #-store-project σ α αs (#-weak α#σ)
  ... | rec = #cons rec (#-≢ α#σ)

store-project-[] : ∀ σ → store-project σ [] ≡ `emp
store-project-[] `emp = refl
store-project-[] (σ , α ⦂ S [ α#σ ]) = store-project-[] σ

_∩′_ : Store → Store → Store
σ₁ ∩′ σ₂ = store-project σ₁ (store-dom σ₂)

∩′-emp : ∀ σ → σ ∩′ `emp ≡ `emp
∩′-emp σ rewrite store-project-[] σ = refl

σ\\σ : ∀ σ → σ \\ σ ≡ `emp
σ\\σ `emp = refl
σ\\σ (σ , α ⦂ S [ α#σ ]) with α α=? α
... | no ¬p = ⊥-elim (¬p refl)
... | yes refl = σ\\σ σ

#-irrelevant : (p q : α # σ) → p ≡ q 
#-irrelevant {α} {`emp} #emp #emp = refl
#-irrelevant {α} {σ , α₁ ⦂ S [ α#σ ]} (#cons p α≡α₁) (#cons q α≡α₁′) =
  cong₂ #cons (#-irrelevant p q) (fun-ext α≡α₁ α≡α₁′ (λ x → ⊥-elim (α≡α₁ x)))

cong-store : (#₁ : α # σ₁) (#₂ : α # σ₂) → σ₁ ≡ σ₂ → (σ₁ , α ⦂ S [ #₁ ]) ≡ (σ₂ , α ⦂ S [ #₂ ]) 
cong-store #₁ #₂ refl rewrite #-irrelevant #₁ #₂ = refl

#++irrelevant : (p q : all# σ σ′) → p ≡ q
#++irrelevant {σ′ = `emp} p q = refl
#++irrelevant {σ′ = σ′ , α ⦂ S [ α#σ ]} (all#₁ , #₁) (all#₂ , #₂) 
  rewrite #++irrelevant all#₁ all#₂ | #-irrelevant #₁ #₂ = refl

cong++store : (#₁ : all# σ₁ σ₂) (#₂ : all# σ₁ σ₃) → σ₂ ≡ σ₃ → (σ₁ ++ σ₂ [ #₁ ]) ≡ (σ₁ ++ σ₃ [ #₂ ])
cong++store all#₁ all#₂ refl rewrite #++irrelevant all#₁ all#₂ = refl

σ/-α=σ : ∀ α σ → (α#σ : α # σ) → (σ /- α) ≡ σ
σ/-α=σ α `emp α#σ = refl
σ/-α=σ α (σ , α₁ ⦂ S [ α₁#σ ]) α#σ with α₁ α=? α
σ/-α=σ α (σ , .α ⦂ S [ α₁#σ ]) (#cons α#σ x) | yes refl = ⊥-elim (x refl)
σ/-α=σ α (σ , α₁ ⦂ S [ α₁#σ ]) (#cons α#σ x) | no ¬p = cong-store (#-/- σ α₁#σ) α₁#σ (σ/-α=σ α σ α#σ)

\\-++-emp : ∀ σ₁ σ₂ σ₁#σ₂ → σ₁ \\ (σ₁ ++ σ₂ [ σ₁#σ₂ ]) ≡ `emp
\\-++-emp σ₁ `emp σ₁#σ₂ = σ\\σ σ₁
\\-++-emp σ₁ (σ₂ , α ⦂ S [ α#σ ]) (σ₁#σ₂ , α#σ₁) rewrite σ/-α=σ α σ₁ α#σ₁ = \\-++-emp σ₁ σ₂ σ₁#σ₂

all#-α-left : ∀ σ₁ σ₂ α → all# σ₁ σ₂ → all# (σ₁ /- α) σ₂
all#-α-left σ₁ `emp α σ₁#σ₂ = tt
all#-α-left σ₁ (σ₂ , α₁ ⦂ S [ α#σ ]) α (σ₁#σ₂ , α₁#σ₁) = all#-α-left σ₁ σ₂ α σ₁#σ₂ , #-/- σ₁ α₁#σ₁

all#-α : ∀ σ₁ σ₂ α → all# σ₁ σ₂ → all# (σ₁ /- α) (σ₂ /- α)
all#-α σ₁ `emp α σ₁#σ₂ = tt
all#-α σ₁ (σ₂ , α₁ ⦂ S [ α#σ ]) α (σ₁#σ₂ , α₁#σ₁) with α₁ α=? α
... | no ¬p = (all#-α σ₁ σ₂ α σ₁#σ₂) , #-/- σ₁ α₁#σ₁
... | yes refl = all#-α-left σ₁ σ₂ α σ₁#σ₂

all#-σ : ∀ σ₁ σ₂ σ →
  all# σ₁ σ₂ → all# (σ₁ \\ σ) (σ₂ \\ σ)
all#-σ σ₁ σ₂ `emp σ₁#σ₂ = σ₁#σ₂
all#-σ σ₁ σ₂ (σ , α ⦂ S [ α#σ ]) σ₁#σ₂ = all#-σ (σ₁ /- α) (σ₂ /- α) σ (all#-α σ₁ σ₂ α σ₁#σ₂)

-- #-/- : ∀ {α₁} {α} σ → α₁ # σ → α₁ # (σ /- α)

++-/α : ∀ σ₁ σ₂ α σ₁#σ₂ →
  (σ₁ ++ σ₂ [ σ₁#σ₂ ]) /- α ≡ (σ₁ /- α) ++ (σ₂ /- α) [ all#-α σ₁ σ₂ α σ₁#σ₂ ]
++-/α σ₁ `emp α σ₁#σ₂ = refl
++-/α σ₁ (σ₂ , α₁ ⦂ S [ α₁#σ₂ ]) α (σ₁#σ₂ , α₁#σ₁) with α₁ α=? α
... | yes refl =
  (σ₁ ++ σ₂ [ σ₁#σ₂ ])
  ≡⟨ sym (σ/-α=σ α₁ (σ₁ ++ σ₂ [ σ₁#σ₂ ]) (#-++ α₁#σ₁ α₁#σ₂)) ⟩
  ((σ₁ ++ σ₂ [ σ₁#σ₂ ]) /- α₁)
  ≡⟨ ++-/α σ₁ σ₂ α σ₁#σ₂ ⟩ 
  ((σ₁ /- α₁) ++ σ₂ /- α₁ [ all#-α σ₁ σ₂ α₁ σ₁#σ₂ ])
  ≡⟨ cong++store (all#-α σ₁ σ₂ α₁ σ₁#σ₂) (all#-α-left σ₁ σ₂ α₁ σ₁#σ₂) (σ/-α=σ α₁ σ₂ α₁#σ₂) ⟩
  ((σ₁ /- α₁) ++ σ₂ [ all#-α-left σ₁ σ₂ α₁ σ₁#σ₂ ]) 
  ∎
... | no ¬p =
  let ## = #-++ {σ₁#σ₂ = σ₁#σ₂} α₁#σ₁ α₁#σ₂ in
  cong-store
    (#-/- {α = α} (σ₁ ++ σ₂ [ σ₁#σ₂ ]) ##)
    (#-++ (#-/- σ₁ α₁#σ₁) (#-/- σ₂ α₁#σ₂))
    (++-/α σ₁ σ₂ α σ₁#σ₂)

++-\\ : ∀ σ₁ σ₂ σ σ₁#σ₂ →
  (σ₁ ++ σ₂ [ σ₁#σ₂ ]) \\ σ ≡ (σ₁ \\ σ) ++ (σ₂ \\ σ) [ all#-σ σ₁ σ₂ σ σ₁#σ₂ ]
++-\\ σ₁ σ₂ `emp σ₁#σ₂ = refl
++-\\ σ₁ σ₂ (σ , α ⦂ S [ α#σ ]) σ₁#σ₂ = 
  begin ((σ₁ ++ σ₂ [ σ₁#σ₂ ]) \\ (σ , α ⦂ S [ α#σ ]) 
    ≡⟨ cong (λ x → x \\ σ) (++-/α σ₁ σ₂ α σ₁#σ₂) ⟩
  ((σ₁ /- α) ++ σ₂ /- α [ all#-α σ₁ σ₂ α σ₁#σ₂ ]) \\ σ
    ≡⟨ ++-\\ (σ₁ /- α) (σ₂ /- α) σ (all#-α σ₁ σ₂ α σ₁#σ₂) ⟩
  refl)

emp+σ=σ : ∀ σ → `emp ++ σ [ all#-emp σ ] ≡ σ
emp+σ=σ `emp = refl
emp+σ=σ (σ , α ⦂ S [ α#σ ]) = cong-store (#-++ #emp α#σ) α#σ (emp+σ=σ σ)

⊆-mon : (σ , α ⦂ S [ α#σ ]) ⊆ σ′ → σ ⊆ σ′
⊆-mon (⊆-elem α∈ sub) = sub

⊆-in : α ⦂ S `in σ → σ ⊆ σ′ → α ⦂ S `in σ′
⊆-in `Z (⊆-elem α∈ σ⊆σ′) = α∈
⊆-in (`S x α∈) σ⊆σ′ = ⊆-in α∈ (⊆-mon σ⊆σ′)

#-⊆ : (α#σ   : α # σ) → (s1<s2 : σ ⊆ (σ₁ , α ⦂ S [ α#σ₁ ])) → σ ⊆ σ₁
#-⊆ α#σ ⊆-emp = ⊆-emp
#-⊆ {α = α} (#cons α#σ α≢α′) (⊆-elem `Z s1<s2) = ⊥-elim (α≢α′ refl)
#-⊆ {α = α} (#cons α#σ α≢α′) (⊆-elem (`S α≢β α∈) s1<s2) = ⊆-elem α∈ (#-⊆ α#σ s1<s2)

cancel-⊆ : σ₁ , α ⦂ S [ α#σ₁ ] ⊆ σ₂ , α ⦂ S [ α#σ₂ ] → σ₁ ⊆ σ₂
cancel-⊆ {α#σ₁ = α#σ₁} (⊆-elem α∈ σ₁α⊆σ₂α) = #-⊆ α#σ₁ σ₁α⊆σ₂α

-- transitivity

⊆-trans : σ₁ ⊆ σ₂ → σ₂ ⊆ σ₃ → σ₁ ⊆ σ₃
⊆-trans ⊆-emp ⊆-emp = ⊆-emp
⊆-trans ⊆-emp (⊆-elem α∈ s2<s3) = ⊆-emp
⊆-trans {σ₁ , α₁ ⦂ S₁ [ α₁#σ₁ ]} {σ₂ , α₂ ⦂ S₂ [ α₂#σ₂ ]} (⊆-elem α₁∈ s1<s2) (⊆-elem α∈₁ s2<s3) with α₁ α=? α₂
⊆-trans {σ , α ⦂ S [ α#σ ]} {σ₁ , .α ⦂ .S [ α#σ₁ ]} (⊆-elem `Z s1<s2) (⊆-elem α∈₁ s2<s3) | yes refl = ⊆-elem α∈₁ (⊆-trans (#-⊆ α#σ s1<s2) s2<s3)
⊆-trans {σ , α ⦂ S [ α#σ ]} {σ₂ , .α ⦂ S₁ [ α#σ₁ ]} (⊆-elem (`S x α∈) s1<s2) (⊆-elem α∈₁ s2<s3) | yes refl = ⊥-elim (x refl)
... | no α≢α₁ with α₁∈
... | `Z = ⊥-elim (α≢α₁ refl)
... | `S α≢α₁′ α∈₂ = ⊆-elem (⊆-in α∈₂ s2<s3) (⊆-trans s1<s2 (⊆-elem α∈₁ s2<s3))


#-in-contradiction : α # σ → α ⦂ S `in σ → ⊥
#-in-contradiction (#cons α#σ α≢α) `Z = α≢α refl
#-in-contradiction (#cons α#σ α≢α′) (`S α≢β α∈) = #-in-contradiction α#σ α∈

⊆-ext : σ ⊆ σ′ → σ ⊆ (σ′ , α′ ⦂ S′ [ α′#σ′ ]) -- requires α′ to be different
⊆-ext ⊆-emp = ⊆-emp
⊆-ext {α′ = α′} {α′#σ′ = α′#σ′} (⊆-elem {α} α∈ s<s') with α α=? α′
... | no ¬p = ⊆-elem (`S ¬p α∈) (⊆-ext s<s')
... | yes refl = ⊥-elim (#-in-contradiction α′#σ′ α∈)


⊆-refl : σ ⊆ σ
⊆-refl {`emp} = ⊆-emp
⊆-refl {σ , α ⦂ S [ α#σ ]} = ⊆-elem `Z (⊆-ext ⊆-refl)

expand-⊆ : σ₁ ⊆ σ₂ → σ₁ , α ⦂ S [ α#σ₁ ] ⊆ σ₂ , α ⦂ S [ α#σ₂ ]
expand-⊆ σ₁⊆σ₂ = ⊆-elem `Z (⊆-ext σ₁⊆σ₂)

-- swap the two top entries
⊆-swap : ∀ {α α₁} {σ} {α#σ} {α₁#σ} {α₁#σα} {α#σα₁} →
  σ , α ⦂ S [ α#σ ] , α₁ ⦂ S₁ [ α₁#σα ] ⊆ σ , α₁ ⦂ S₁ [ α₁#σ ] , α ⦂ S [ α#σα₁ ]
⊆-swap {α₁#σα = #cons α₁#σ α₁≢α} = ⊆-elem (`S α₁≢α `Z) (⊆-elem `Z (⊆-trans (⊆-ext ⊆-refl) (⊆-ext ⊆-refl)))

++-pull : ∀ σ′ {σ#σ′} {σα#σ′} {α#σσ′} →
  ((σ , α ⦂ S [ α#σ ]) ++ σ′ [ σα#σ′ ]) ⊆ ((σ ++ σ′ [ σ#σ′ ]) , α ⦂ S [ α#σσ′ ])
++-pull {α#σ = α#σ} `emp {α#σσ′ = α#σσ′} rewrite #-irrelevant α#σ α#σσ′ = ⊆-refl
++-pull {σ} {α} {S} {α#σ} (σ′ , α₁ ⦂ S₁ [ α₁#σ′ ]) {σ#σ′ = σ#σ′ , α₁#σ} {σα#σ′ = fst , #cons xx α₁≢α} {α#σσ′ = #cons α#σσ′ x2} =
  let ih = ++-pull {σ}{α}{S}{α#σ} σ′ {σ#σ′} {σα#σ′ = fst} in
  ⊆-trans (expand-⊆ {α#σ₂ = foo} ih) ⊆-swap
  where foo : α₁ # ((σ ++ σ′ [ σ#σ′ ]) , α ⦂ S [ α#σσ′ ])
        foo = #cons (#-++ α₁#σ α₁#σ′) α₁≢α

++-pull-back : ∀ σ′ {σ#σ′} {σα#σ′} {α#σσ′} →
  ((σ ++ σ′ [ σ#σ′ ]) , α ⦂ S [ α#σσ′ ]) ⊆  ((σ , α ⦂ S [ α#σ ]) ++ σ′ [ σα#σ′ ])
++-pull-back {α#σ = α#σ} `emp {α#σσ′ = α#σσ′} rewrite #-irrelevant α#σ α#σσ′ = ⊆-refl
++-pull-back {σ} {α} {S} {α#σ} (σ′ , α₁ ⦂ S₁ [ α₁#σ′ ])  {σ#σ′ = σ#σ′ , α₁#σ} {σα#σ′ = fst , snd} {α#σσ′ = #cons α#σσ′ a≢a₁} =
  let ih = ++-pull-back {σ}{α}{S}{α#σ} σ′ {σ#σ′} {σα#σ′ = fst} in
  ⊆-trans (⊆-swap {α₁#σ = α#σσ′} {α#σα₁ = foo}) (expand-⊆ ih)
  where foo : α₁ # ((σ ++ σ′ [ σ#σ′ ]) , α ⦂ S [ α#σσ′ ])
        foo = #cons (#-++ α₁#σ α₁#σ′) (a≢a₁ ∘ sym)

++-comm : ∀ σ₁ σ₂ {σ₁#σ₂} {σ₂#σ₁} → σ₁ ++ σ₂ [ σ₁#σ₂ ] ⊆ σ₂ ++ σ₁ [ σ₂#σ₁ ]
++-comm σ₁ `emp {σ₁#σ₂}{σ₂#σ₁} rewrite #++irrelevant σ₂#σ₁ (all#-emp σ₁) | emp+σ=σ σ₁ = ⊆-refl
++-comm σ₁ (σ₂ , α ⦂ S [ α#σ ]) {σ₁#σ₂ , α#σ₁} {σ₂#σ₁}
  with ++-comm σ₁ σ₂ {σ₁#σ₂}{all#-weak σ₂#σ₁}
... | ih = let ext-ih = expand-⊆ {α#σ₂ = α#σ₂σ₁} ih in ⊆-trans ext-ih (++-pull-back σ₁) 
  where α#σ₂σ₁ : α # (σ₂ ++ σ₁ [ all#-weak σ₂#σ₁ ])
        α#σ₂σ₁ = #-++ α#σ α#σ₁

_≈_ : Store → Store → Set
σ₁ ≈ σ₂ = ∃ λ f → ∃ λ g → f ∘ g ≡ id × g ∘ f ≡ id × σ₁ ≡ f σ₂

α-in-++ : ∀ {σ₁#σ₁′} → α ⦂ S `in (σ₁ ++ σ₁′ [ σ₁#σ₁′ ]) → α ⦂ S `in σ₁ ⊎ α ⦂ S `in σ₁′
α-in-++ {σ₁ = σ₁} {`emp} {σ₁#σ₁′} α∈ = inj₁ α∈
α-in-++ {α = .α₁} {σ₁ = σ₁} {σ₁′ , α₁ ⦂ S₁ [ α₁#σ₁′ ]} {σ₁#σ₁′ , α₁#σ₁} `Z = inj₂ `Z
α-in-++ {α = α} {σ₁ = σ₁} {σ₁′ , α₁ ⦂ S₁ [ α₁#σ₁′ ]} {σ₁#σ₁′ , α₁#σ₁} (`S α≢β α∈)
  with α-in-++ {α} {σ₁ = σ₁} {σ₁′} α∈
... | inj₁ x = inj₁ x
... | inj₂ y = inj₂ (`S α≢β y)

all#-in-contradiction : ∀ {S₁ S₂} → α ⦂ S₁ `in σ₁ → α ⦂ S₂ `in σ₂ → all# σ₁ σ₂ → ⊥
all#-in-contradiction α∈σ₁ `Z (fst , α#σ₁) = #-in-contradiction α#σ₁ α∈σ₁
all#-in-contradiction α∈σ₁ (`S α≢β α∈σ₂) (σ₁#σ₂ , snd) = all#-in-contradiction α∈σ₁ α∈σ₂ σ₁#σ₂

¬-⊎ : ∀ {A B : Set} → ¬ A → ¬ B → ¬ (A ⊎ B)
¬-⊎ ¬A ¬B (inj₁ x) = ¬A x
¬-⊎ ¬A ¬B (inj₂ y) = ¬B y

store-sub :
  {σ₁#σ₁′ : all# σ₁ σ₁′} {σ₁₂#σ₁′₂ : all# (σ₁ ∩ σ₂) (σ₁′ ∩ σ₂)} →
  σ₂ ⊆ (σ₁ ++ σ₁′ [ σ₁#σ₁′ ]) →
  (σ₁ ∩ σ₂) ++ (σ₁′ ∩ σ₂) [ σ₁₂#σ₁′₂ ] ⊆⊇ σ₂
store-sub {σ₂ = `emp} s2<s1+s1' = ⊆-emp , ⊆-emp
store-sub {σ₁ = σ₁} {σ₁′ = σ₁′} {σ₂ = σ₂ , α ⦂ S [ α#σ ]}  {σ₁#σ₁′ = σ₁#σ₁′} {σ₁₂#σ₁′₂} (⊆-elem α∈ s2<s1+s1') with α ∈′ σ₁ | α ∈′ σ₁′
... | no ¬p | no ¬p₁ = ⊥-elim (¬-⊎ ¬p ¬p₁ (Data.Sum.map (λ x → _ , x) (λ x → _ , x) (α-in-++ α∈)))
... | yes p | yes p₁ = ⊥-elim (all#-in-contradiction (proj₂ p) (proj₂ p₁) σ₁#σ₁′)
... | yes p | no ¬p
  with store-sub {σ₁}{σ₁′}{σ₂}{σ₁#σ₁′}{σ₁₂#σ₁′₂ = all#-weak σ₁₂#σ₁′₂} s2<s1+s1'
... | ih-⊆σ₂ , ih-σ₂⊆ = ⊆-trans (++-pull (σ₁′ ∩ σ₂) {α#σσ′ = #-++ (#-∩ σ₁ σ₂ α#σ) (#-∩ σ₁′ σ₂ α#σ)}) (⊆-elem `Z (⊆-ext ih-⊆σ₂))
                      , ⊆-trans (expand-⊆ {α#σ₂ = #-++ (#-∩ σ₁ σ₂ α#σ) (#-∩ σ₁′ σ₂ α#σ)} ih-σ₂⊆) (++-pull-back (σ₁′ ∩ σ₂))
store-sub {σ₁ = σ₁} {σ₁′ = σ₁′} {σ₂ , α ⦂ S [ α#σ ]} {σ₁#σ₁′ = σ₁#σ₁′} {σ₁∩σ₂#σ₁′∩σ₂ , α#σ₁∩σ₂} (⊆-elem α∈ s2<s1+s1') | no ¬p | yes p
  with store-sub {σ₁}{σ₁′}{σ₂}{σ₁#σ₁′}{σ₁∩σ₂#σ₁′∩σ₂} s2<s1+s1'
... | ih-⊆σ₂ , ih-σ₂⊆ = expand-⊆ ih-⊆σ₂ , expand-⊆ ih-σ₂⊆

store-in-functional : ∀ {S₁ S₂} →
  α ⦂ S₁ `in σ → α ⦂ S₂ `in σ → S₁ ≡ S₂
store-in-functional `Z `Z = refl
store-in-functional `Z (`S α≢β ∈σ2) = ⊥-elim (α≢β refl)
store-in-functional (`S α≢β ∈σ1) `Z = ⊥-elim (α≢β refl)
store-in-functional (`S α≢β ∈σ1) (`S α≢β₁ ∈σ2) = store-in-functional ∈σ1 ∈σ2

#-in :
  α ⦂ S `in σ → β # σ → β ≢ α
#-in {σ = σ , α ⦂ S [ α#σ ]} `Z (#cons β#σ β≢α) = β≢α
#-in {σ = σ , α ⦂ S [ α#σ ]} (`S α≢β α∈) (#cons β#σ β≢α) = #-in {σ = σ} α∈ β#σ

store-in-++ : ∀ {S₀} σ₁′ {σ₁#σ₁′} → 
  α ⦂ S₀ `in σ₁ → α ⦂ S `in (σ₁ ++ σ₁′ [ σ₁#σ₁′ ]) → S₀ ≡ S
store-in-++ `emp ∈σ₁ ∈σ₁++σ₁′ = store-in-functional ∈σ₁ ∈σ₁++σ₁′
store-in-++ (σ₁′ , α₁ ⦂ S [ α₁#σ₁′ ]) {σ₁#σ₁′} ∈σ₁ ∈σ₁++σ₁′
  with #-in ∈σ₁ (proj₂ σ₁#σ₁′)
... | α₁≢α
  with ∈σ₁++σ₁′
... | `Z = ⊥-elim (α₁≢α refl)
... | `S α≢β ∈++σ₁′ = store-in-++ σ₁′ ∈σ₁ ∈++σ₁′


⊆-++ : ∀ σ₁ σ₂ (σ₂#σ₁ : all# σ₂ σ₁) → σ₁ ⊆ (σ₂ ++ σ₁ [ σ₂#σ₁ ])
⊆-++ `emp σ₂ σ₂#σ₁ = ⊆-emp
⊆-++ (σ₁ , α ⦂ S [ α#σ ]) σ₂ σ₂#σ₁ = ⊆-elem `Z (⊆-ext (⊆-++ σ₁ σ₂ (proj₁ σ₂#σ₁)))

⊆-∩ : ∀ σ₁ σ₂ σ₁#σ₁′ → σ₂ ⊆ σ₁ ++ σ₁′ [ σ₁#σ₁′ ] → σ₁ ∩ σ₂ ⊆ σ₁
⊆-∩ σ₁ `emp σ₁#σ₁′ σ₂⊆ = ⊆-emp
⊆-∩ σ₁ (σ₂ , α ⦂ S [ α#σ ])  σ₁#σ₁′  σ₂⊆
  with α ∈′ σ₁
⊆-∩ σ₁ (σ₂ , α ⦂ S [ α#σ ]) σ₁#σ₁′ (⊆-elem α∈ σ₂⊆) | no ¬p = ⊆-∩ σ₁ σ₂ σ₁#σ₁′ σ₂⊆
⊆-∩ σ₁ (σ₂ , α ⦂ S [ α#σ ]) σ₁#σ₁′ (⊆-elem α∈ σ₂⊆) | yes (fst , snd)
  with store-in-++ _ snd α∈
... | refl
  = ⊆-elem snd (⊆-∩ σ₁ σ₂ σ₁#σ₁′ σ₂⊆)

module _ where
  open import VGR.Typing

  private
    variable
      Γ : TEnv
      T T′ T₁ T₂ U : Type
      e : Expr

  ~[]~⇒⊆ : ∀ σ α σ′ T α#σ′ → (σ ~[ α ]~ (σ′ , α ⦂ T [ α#σ′ ])) → σ′ ⊆ σ
  ~[]~⇒⊆ .(σ′ , α ⦂ T [ α#σ′ ]) α σ′ T α#σ′ `Z = ⊆-ext ⊆-refl
  ~[]~⇒⊆ .(_ , _ ⦂ _ [ _ ]) α .(_ , _ ⦂ _ [ _ ]) T .(#cons _ α≢β) (`S α≢β ~[]~) = expand-⊆ (~[]~⇒⊆ _ _ _ _ _ ~[]~)

  -- unused store σ₁ returned by typing is always a subset of the incoming store σ

  ⊢e⇒σ₁⊆σ : (Γ ፤ σ ፤ e ↦ σ₁ ፤ T ፤ σ₂) → σ₁ ⊆ σ
  ⊢e⇒σ₁⊆σ (C-ReceiveD ⊢v sp) = ~[]~⇒⊆ _ _ _ _ _ sp
  ⊢e⇒σ₁⊆σ (C-ReceiveS ⊢v α≢β sp) = ~[]~⇒⊆ _ _ _ _ _ sp
  ⊢e⇒σ₁⊆σ (C-SendD ⊢v ⊢v′ sp) = ~[]~⇒⊆ _ _ _ _ _ sp
  ⊢e⇒σ₁⊆σ (C-SendDS ⊢v ⊢v′ sp sp′) = ⊆-trans (~[]~⇒⊆ _ _ _ _ _ sp′) (~[]~⇒⊆ _ _ _ _ _ sp)
  ⊢e⇒σ₁⊆σ (C-Close ⊢v sp) = ~[]~⇒⊆ _ _ _ _ _ sp
  ⊢e⇒σ₁⊆σ (C-Accept ⊢v) = ⊆-refl
  ⊢e⇒σ₁⊆σ (C-Request ⊢v) = ⊆-refl
  ⊢e⇒σ₁⊆σ (C-Val ⊢v) = ⊆-refl
  ⊢e⇒σ₁⊆σ {σ = σ} {σ₁ = σ₁} (C-App {σ₁ = σ₂} {σ₁#σ = σ₂#σ₁} ⊢v ⊢v′) = ⊆-++ σ₁ σ₂ σ₂#σ₁
  ⊢e⇒σ₁⊆σ C-New = ⊆-refl
  ⊢e⇒σ₁⊆σ (C-Let {σ₁ = σ₂} {σ₁#σ₁′ = σ₁#σ₁′} {σ₂ = σ₄} ⊢e ⊢e₁ refl x₁) = ⊆-trans (⊆-∩ σ₂ σ₄ σ₁#σ₁′ (⊢e⇒σ₁⊆σ ⊢e₁)) (⊢e⇒σ₁⊆σ ⊢e)
  ⊢e⇒σ₁⊆σ (C-LetV ⊢v ⊢e) = ⊢e⇒σ₁⊆σ ⊢e
  ⊢e⇒σ₁⊆σ (C-Fork {σ₁ = σ₃} {σ₂ = σ₂} {σ₁#σ₂ = σ₃#σ₂} ⊢e ⊢e₁) = ⊆-trans (⊢e⇒σ₁⊆σ ⊢e₁) (⊆-++ σ₂ σ₃ σ₃#σ₂)
