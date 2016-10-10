{-# OPTIONS --without-K #-}

module Nf where

open import Syntax
open import Renaming

infixl 7 _$ₙ_
infixl 8 _[_]ₙᵣ _[_]ₙₑᵣ

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  _[_]ₙᵣ : ∀ {Γ Δ A} → Nf Δ A → Ren Γ Δ → Nf Γ A
  ne  n [ σ ]ₙᵣ = ne (n [ σ ]ₙₑᵣ)
  lam n [ σ ]ₙᵣ = lam (n [ keep σ ]ₙᵣ)

  _[_]ₙₑᵣ : ∀ {Γ Δ A} → Ne Δ A → Ren Γ Δ → Ne Γ A
  var v    [ σ ]ₙₑᵣ = var (v [ σ ]∈ᵣ)
  (f $ₙ a) [ σ ]ₙₑᵣ = f [ σ ]ₙₑᵣ $ₙ a [ σ ]ₙᵣ

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v  ⌝Ne = var v
  ⌜ n $ₙ t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝
