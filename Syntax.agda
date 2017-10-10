{-# OPTIONS --without-K #-}

module Syntax where

infixr 4 _⇒_
infixr 5 _+_
infixr 6 _*_

data Ty : Set where
  ⊤   : Ty
  ⊥   : Ty
  _⇒_ : Ty → Ty → Ty
  _*_ : Ty → Ty → Ty
  _+_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → (v : A ∈ Γ) → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var   : ∀ {A} → A ∈ Γ → Tm Γ A
  lam   : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  tt    : Tm Γ ⊤
  π₁    : ∀ {A B} → Tm Γ (A * B) → Tm Γ A
  π₂    : ∀ {A B} → Tm Γ (A * B) → Tm Γ B
  _,_   : ∀ {A B} → Tm Γ A → Tm Γ B → Tm Γ (A * B)
  inj₁  : ∀ {A B} → Tm Γ A → Tm Γ (A + B)
  inj₂  : ∀ {A B} → Tm Γ B → Tm Γ (A + B)
  case  : ∀ {A B C} → Tm (Γ , A) C → Tm (Γ , B) C → Tm Γ (A + B) → Tm Γ C
  app   : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B
  ⊥-rec : ∀ {A} → Tm Γ ⊥ → Tm Γ A
