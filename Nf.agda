{-# OPTIONS --without-K #-}

module Nf where

open import Lib
open import Syntax
open import Renaming

infixl 8 _[_]ₙᵣ _[_]ₙₑᵣ

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var : ∀ {A} → A ∈ Γ → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  _[_]ₙᵣ : ∀ {Γ Δ A} → Nf Δ A → Ren Γ Δ → Nf Γ A
  ne  n [ σ ]ₙᵣ = ne (n [ σ ]ₙₑᵣ)
  lam n [ σ ]ₙᵣ = lam (n [ keep σ ]ₙᵣ)

  _[_]ₙₑᵣ : ∀ {Γ Δ A} → Ne Δ A → Ren Γ Δ → Ne Γ A
  var v     [ σ ]ₙₑᵣ = var (v [ σ ]∈ᵣ)
  (app f a) [ σ ]ₙₑᵣ = app (f [ σ ]ₙₑᵣ) (a [ σ ]ₙᵣ)

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v   ⌝Ne = var v
  ⌜ app n t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

mutual
  ⌜⌝Neᵣ : ∀ {Γ Δ A}(n : Ne Γ A)(σ : Ren Δ Γ) → ⌜ n [ σ ]ₙₑᵣ ⌝Ne ≡ ⌜ n ⌝Ne [ σ ]ᵣ
  ⌜⌝Neᵣ (var v)   σ = refl
  ⌜⌝Neᵣ (app f a) σ = app & ⌜⌝Neᵣ f σ ⊗ ⌜⌝ᵣ a σ

  ⌜⌝ᵣ : ∀ {Γ Δ A}(n : Nf Γ A)(σ : Ren Δ Γ) → ⌜ n [ σ ]ₙᵣ ⌝ ≡ ⌜ n ⌝ [ σ ]ᵣ
  ⌜⌝ᵣ (ne n)  σ = ⌜⌝Neᵣ n σ
  ⌜⌝ᵣ (lam n) σ = lam & ⌜⌝ᵣ n (keep σ)

mutual
  ∘ᵣNf :
    ∀ {Γ Δ Σ A}(t : Nf Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
    → t [ σ ]ₙᵣ [ δ ]ₙᵣ ≡ t [ σ ∘ᵣ δ ]ₙᵣ
  ∘ᵣNf (ne n)  σ δ = ne & ∘ᵣNe n σ δ
  ∘ᵣNf (lam t) σ δ = lam & ∘ᵣNf t (keep σ) (keep δ)  
    
  ∘ᵣNe :
    ∀ {Γ Δ Σ A}(t : Ne Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
    → t [ σ ]ₙₑᵣ [ δ ]ₙₑᵣ ≡ t [ σ ∘ᵣ δ ]ₙₑᵣ
  ∘ᵣNe (var v)   σ δ = var & ∘ᵣ∈ v σ δ
  ∘ᵣNe (app f a) σ δ = app & ∘ᵣNe f σ δ ⊗ ∘ᵣNf a σ δ

mutual
  idᵣNf : ∀ {Γ A}(n : Nf Γ A) → n [ idᵣ ]ₙᵣ ≡ n
  idᵣNf (ne n)  = ne & idᵣNe n
  idᵣNf (lam n) = lam & idᵣNf n

  idᵣNe : ∀ {Γ A}(n : Ne Γ A) → n [ idᵣ ]ₙₑᵣ ≡ n
  idᵣNe (var v)   = var & idᵣ∈ v
  idᵣNe (app f a) = app & idᵣNe f ⊗ idᵣNf a

