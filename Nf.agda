-- {-# OPTIONS --without-K #-}

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

app-≡-elim :
  ∀ {Γ A A' B}{f : Tm Γ (A ⇒ B)}{f' : Tm Γ (A' ⇒ B)}{a a'}
  → (Tm Γ B ∋ app f a) ≡ app f' a'
  → Σ (A ≡ A') λ p → (coe ((Tm Γ ∘ (_⇒ B)) & p) f ≡ f') × (coe (Tm Γ & p) a ≡ a')
app-≡-elim refl = refl , refl , refl

lam-inj : ∀ {Γ A B}{t t' : Tm (Γ , A) B} → (Tm Γ (A ⇒ B) ∋ lam t) ≡ lam t' → t ≡ t'
lam-inj refl = refl

mutual
  ⌜⌝-inj : ∀ {Γ A}{n n' : Nf Γ A} → ⌜ n ⌝ ≡ ⌜ n' ⌝ → n ≡ n'
  ⌜⌝-inj {n = ne n}   {ne n'} p = ne & ⌜⌝Ne-inj p
  ⌜⌝-inj {n = lam n} {lam n'} p = lam & ⌜⌝-inj (lam-inj p)

  ⌜⌝Ne-inj : ∀ {Γ A}{n n' : Ne Γ A} → ⌜ n ⌝Ne ≡ ⌜ n' ⌝Ne → n ≡ n'
  ⌜⌝Ne-inj {n = var v} {var .v} refl = refl
  ⌜⌝Ne-inj {n = app f a} {app f' a'} p with app-≡-elim p
  ... | refl , p2 , p3 = app & ⌜⌝Ne-inj p2 ⊗ ⌜⌝-inj p3
  ⌜⌝Ne-inj {n = var _} {app _ _} ()
  ⌜⌝Ne-inj {n = app _ _} {var _} ()

