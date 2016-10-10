{-# OPTIONS --without-K #-}

module Renaming where

open import Lib
open import Syntax

infixr 9 _∘ᵣ_
infixl 8 _[_]∈ᵣ _[_]ᵣ

data Ren : Con → Con → Set where
  ∙    : Ren ∙ ∙
  drop : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) Δ
  keep : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) (Δ , A)

-- Ren is a category

idᵣ : ∀ {Γ} → Ren Γ Γ
idᵣ {∙}     = ∙
idᵣ {Γ , A} = keep (idᵣ {Γ})

wk : ∀ {A Γ} → Ren (Γ , A) Γ
wk = drop idᵣ

_∘ᵣ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
σ      ∘ᵣ ∙      = σ
σ      ∘ᵣ drop δ = drop (σ ∘ᵣ δ)
drop σ ∘ᵣ keep δ = drop (σ ∘ᵣ δ)
keep σ ∘ᵣ keep δ = keep (σ ∘ᵣ δ)

idlᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → idᵣ ∘ᵣ σ ≡ σ
idlᵣ ∙        = refl
idlᵣ (drop σ) = drop & idlᵣ σ
idlᵣ (keep σ) = keep & idlᵣ σ

idrᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → σ ∘ᵣ idᵣ ≡ σ
idrᵣ ∙        = refl
idrᵣ (drop σ) = drop & idrᵣ σ
idrᵣ (keep σ) = keep & idrᵣ σ

assᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ∘ᵣ δ) ∘ᵣ ν ≡ σ ∘ᵣ (δ ∘ᵣ ν)
assᵣ σ        δ        ∙        = refl
assᵣ σ        δ        (drop ν) = drop & assᵣ σ δ ν
assᵣ σ        (drop δ) (keep ν) = drop & assᵣ σ δ ν
assᵣ (drop σ) (keep δ) (keep ν) = drop & assᵣ σ δ ν
assᵣ (keep σ) (keep δ) (keep ν) = keep & assᵣ σ δ ν

-- (A ∈_) : is a presheaf on Ren

_[_]∈ᵣ : ∀ {Γ Δ A} → A ∈ Δ → Ren Γ Δ → A ∈ Γ
v    [ ∙      ]∈ᵣ = v
v    [ drop σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)
vz   [ keep σ ]∈ᵣ = vz
vs v [ keep σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)

idᵣ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idᵣ ]∈ᵣ ≡ v
idᵣ∈ vz     = refl
idᵣ∈ (vs v) = vs & idᵣ∈ v

∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  →  v [ σ ]∈ᵣ [ δ ]∈ᵣ ≡ v [ σ ∘ᵣ δ ]∈ᵣ
∘ᵣ∈ ()     ∙        ∙
∘ᵣ∈ v      σ        (drop δ)  = vs & ∘ᵣ∈ v σ δ
∘ᵣ∈ v      (drop σ) (keep δ)  = vs & ∘ᵣ∈ v σ δ
∘ᵣ∈ vz     (keep σ) (keep δ)  = refl
∘ᵣ∈ (vs v) (keep σ) (keep δ)  = vs & ∘ᵣ∈ v σ δ

-- (Tm _ A) is a presheaf on Ren

_[_]ᵣ : ∀ {Γ Δ A} → Tm Δ A → Ren Γ Δ → Tm Γ A
var v   [ σ ]ᵣ = var (v [ σ ]∈ᵣ)
lam t   [ σ ]ᵣ = lam (t [ keep σ ]ᵣ)
app f a [ σ ]ᵣ = app (f [ σ ]ᵣ) (a [ σ ]ᵣ)

idᵣTm : ∀ {Γ A}(t : Tm Γ A) → t [ idᵣ ]ᵣ ≡ t
idᵣTm (var v)   = var & idᵣ∈ v
idᵣTm (lam t)   = lam & idᵣTm t
idᵣTm (app f a) = app & idᵣTm f ⊗ idᵣTm a

∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ]ᵣ [ δ ]ᵣ ≡ t [ σ ∘ᵣ δ ]ᵣ
∘ᵣTm (var v)   σ δ = var & ∘ᵣ∈ v σ δ
∘ᵣTm (lam t)   σ δ = lam & ∘ᵣTm t (keep σ) (keep δ)
∘ᵣTm (app f a) σ δ = app & ∘ᵣTm f σ δ ⊗ ∘ᵣTm a σ δ
