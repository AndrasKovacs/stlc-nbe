{-# OPTIONS --without-K #-}

module Syntax where

infixr 4 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → (v : A ∈ Γ) → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → (v : A ∈ Γ) → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → (f : Tm Γ (A ⇒ B)) → (a : Tm Γ A) → Tm Γ B
