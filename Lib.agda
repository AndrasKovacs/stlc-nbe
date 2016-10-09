{-# OPTIONS --without-K #-}

module Lib where

open import Level

data _≡_ {i}{A : Set i} (x : A) : A → Set i where
  refl : x ≡ x
infix 4 _≡_

{-# BUILTIN EQUALITY _≡_ #-}
{-# BUILTIN REFL refl #-}

_◾_ : ∀{i}{A : Set i}{x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl ◾ refl = refl
infixl 4 _◾_

_⁻¹ : ∀{i}{A : Set i}{x y : A} → x ≡ y → y ≡ x
refl ⁻¹ = refl
infix 5 _⁻¹

_≡⟨_⟩_ : ∀{i}{A : Set i}(x : A){y z : A} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ x≡y ⟩ y≡z = x≡y ◾ y≡z
infixr 2 _≡⟨_⟩_

_∎ : ∀{i}{A : Set i}(x : A) → x ≡ x
x ∎ = refl
infix  3 _∎

coe : ∀{i}{A B : Set i} → A ≡ B → A → B
coe refl a = a

_≡[_]≡_ : ∀{i}{A B : Set i} → A → A ≡ B → B → Set i
x ≡[ α ]≡ y = coe α x ≡ y
infix 4 _≡[_]≡_

_&_ :
  ∀{i j}{A : Set i}{B : Set j}(f : A → B){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
  → f a₀ ≡ f a₁
f & refl = refl
infixl 9 _&_

_⊗_ :
  ∀ {α β}{A : Set α}{B : Set β}
    {f g : A → B}(p : f ≡ g){a a' : A}(q : a ≡ a')
  → f a ≡ g a'
refl ⊗ refl = refl
infixl 8 _⊗_

apd : ∀{i j}{A : Set i}{B : A → Set j}(f : (x : A) → B x){a₀ a₁ : A}(a₂ : a₀ ≡ a₁)
    → f a₀ ≡[ B & a₂ ]≡ f a₁
apd f refl = refl

J : {A : Set} {x : A} (P : {y : A} → x ≡ y → Set) → P refl → {y : A} → (w : x ≡ y) → P w
J P pr refl = pr

record Σ {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁
infixl 5 _,_

open Σ public

_×_ : ∀{i j} → Set i → Set j → Set (i ⊔ j)
A × B = Σ A λ _ → B
infix 4 _×_

record ⊤ : Set where
  constructor tt

data ⊥ : Set where

⊥-elim : ∀{i}{A : Set i} → ⊥ → A
⊥-elim ()

data _⊎_ (A B : Set) : Set where
  inl : A → A ⊎ B
  inr : B → A ⊎ B
infixr 1 _⊎_

ind⊎ : {A B : Set}(P : A ⊎ B → Set) → ((a : A) → P (inl a)) → ((b : B) → P (inr b))
     → (w : A ⊎ B) → P w
ind⊎ P ca cb (inl a) = ca a
ind⊎ P ca cb (inr b) = cb b

record Reveal_·_is_ {a b} {A : Set a} {B : A → Set b}
                    (f : (x : A) → B x) (x : A) (y : B x) :
                    Set (a ⊔ b) where
  constructor pack
  field eq : f x ≡ y

inspect : ∀ {a b} {A : Set a} {B : A → Set b}
          (f : (x : A) → B x) (x : A) → Reveal f · x is f x
inspect f x = pack refl

