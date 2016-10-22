{-# OPTIONS --without-K #-}

module Substitution where

open import Lib
open import Syntax
open import Renaming

-- (Satisfies the category-with-families equations except the β and η conversions)

infixr  6 _ᵣ∘ₛ_ _ₛ∘ᵣ_
infixl 8 _[_] _[_]∈

data Tms (Γ : Con) : Con → Set where
  ∙   : Tms Γ ∙
  _,_ : ∀ {A Δ} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ , A)

_ₛ∘ᵣ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Ren Γ Δ → Tms Γ Σ
∙       ₛ∘ᵣ δ = ∙
(σ , t) ₛ∘ᵣ δ = σ ₛ∘ᵣ δ , t [ δ ]ᵣ

_ᵣ∘ₛ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Tms Γ Δ → Tms Γ Σ
∙      ᵣ∘ₛ δ       = δ
drop σ ᵣ∘ₛ (δ , t) = σ ᵣ∘ₛ δ
keep σ ᵣ∘ₛ (δ , t) = σ ᵣ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) Δ
dropₛ σ = σ ₛ∘ᵣ wk

keepₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

idₛ : ∀ {Γ} → Tms Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = keepₛ {A} idₛ

_[_]∈ : ∀ {Γ Δ A} → A ∈ Δ → Tms Γ Δ → Tm Γ A
vz   [ σ , t ]∈ = t
vs v [ σ , _ ]∈ = v [ σ ]∈

_[_] : ∀ {Γ Δ A} → Tm Δ A → Tms Γ Δ → Tm Γ A
var v   [ σ ] = v [ σ ]∈
lam t   [ σ ] = lam (t [ keepₛ σ ])
app f a [ σ ] = app (f [ σ ]) (a [ σ ])

_∘ₛ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , t [ δ ]

assₛᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ₛ∘ᵣ δ) ₛ∘ᵣ ν ≡ σ ₛ∘ᵣ (δ ∘ᵣ ν)
assₛᵣᵣ ∙       δ ν = refl
assₛᵣᵣ (σ , t) δ ν = _,_ & assₛᵣᵣ σ δ ν ⊗ ∘ᵣTm t δ ν

assᵣₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Tms Δ Σ)(ν : Ren Γ Δ)
  → (σ ᵣ∘ₛ δ) ₛ∘ᵣ ν ≡ σ ᵣ∘ₛ (δ ₛ∘ᵣ ν)
assᵣₛᵣ ∙        δ       ν = refl
assᵣₛᵣ (drop σ) (δ , t) ν = assᵣₛᵣ σ δ ν
assᵣₛᵣ (keep σ) (δ , t) ν = (_, t [ ν ]ᵣ) & assᵣₛᵣ σ δ ν

⌜_⌝ʳ : ∀ {Γ Δ} → Ren Γ Δ → Tms Γ Δ
⌜ ∙      ⌝ʳ = ∙
⌜ drop σ ⌝ʳ = dropₛ ⌜ σ ⌝ʳ
⌜ keep σ ⌝ʳ = keepₛ ⌜ σ ⌝ʳ

idlᵣₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → idᵣ ᵣ∘ₛ σ ≡ σ
idlᵣₛ ∙       = refl
idlᵣₛ (σ , t) = (_, t) & idlᵣₛ σ

idlₛᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → idₛ ₛ∘ᵣ σ ≡ ⌜ σ ⌝ʳ
idlₛᵣ ∙        = refl
idlₛᵣ (drop σ) =
      ((idₛ ₛ∘ᵣ_) ∘ drop) & idrᵣ σ ⁻¹
    ◾ assₛᵣᵣ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛᵣ σ
idlₛᵣ (keep σ) =
  (_, var vz) &
      (assₛᵣᵣ idₛ wk (keep σ)
    ◾ ((idₛ ₛ∘ᵣ_) ∘ drop) & (idlᵣ σ ◾ idrᵣ σ ⁻¹)
    ◾ assₛᵣᵣ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ᵣ wk) & idlₛᵣ σ )

idrᵣₛ : ∀ {Γ Δ}(σ : Ren Γ Δ) → σ ᵣ∘ₛ idₛ ≡ ⌜ σ ⌝ʳ
idrᵣₛ ∙        = refl
idrᵣₛ (drop σ) = assᵣₛᵣ σ idₛ wk ⁻¹ ◾ dropₛ & idrᵣₛ σ
idrᵣₛ (keep σ) = (_, var vz) & (assᵣₛᵣ σ idₛ wk ⁻¹ ◾ (_ₛ∘ᵣ wk) & idrᵣₛ σ)

ᵣ∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Ren Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ᵣ [ δ ]∈ ≡ v [ σ ᵣ∘ₛ δ ]∈
ᵣ∘ₛ∈ v      ∙        δ       = refl
ᵣ∘ₛ∈ v      (drop σ) (δ , t) = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛ∈ vz     (keep σ) (δ , t) = refl
ᵣ∘ₛ∈ (vs v) (keep σ) (δ , t) = ᵣ∘ₛ∈ v σ δ

ᵣ∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ]ᵣ [ δ ] ≡ t [ σ ᵣ∘ₛ δ ]
ᵣ∘ₛTm (var v)   σ δ = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛTm (lam t)   σ δ =
  lam &
      (ᵣ∘ₛTm t (keep σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) & (assᵣₛᵣ σ δ wk ⁻¹))
ᵣ∘ₛTm (app f a) σ δ = app & ᵣ∘ₛTm f σ δ ⊗ ᵣ∘ₛTm a σ δ

ₛ∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → v [ σ ]∈ [ δ ]ᵣ ≡ v [ σ ₛ∘ᵣ δ ]∈
ₛ∘ᵣ∈ vz     (σ , _) δ = refl
ₛ∘ᵣ∈ (vs v) (σ , _) δ = ₛ∘ᵣ∈ v σ δ

ₛ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ] [ δ ]ᵣ ≡ t [ σ ₛ∘ᵣ δ ]
ₛ∘ᵣTm (var v)   σ δ = ₛ∘ᵣ∈ v σ δ
ₛ∘ᵣTm (lam t)   σ δ =
  lam & (
      ₛ∘ᵣTm t (keepₛ σ) (keep δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣᵣ σ wk (keep δ)
      ◾ ((λ δ → σ ₛ∘ᵣ (drop δ)) &
          idlᵣ δ
        ◾ (λ δ → σ ₛ∘ᵣ drop δ) & (idrᵣ δ ⁻¹)
        ◾ assₛᵣᵣ σ δ wk ⁻¹)))
ₛ∘ᵣTm (app f a) σ δ = app & ₛ∘ᵣTm f σ δ ⊗ ₛ∘ᵣTm a σ δ

assₛᵣₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Tms Γ Δ)
  → (σ ₛ∘ᵣ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ᵣ∘ₛ ν)
assₛᵣₛ ∙       δ ν = refl
assₛᵣₛ (σ , t) δ ν = _,_ & assₛᵣₛ σ δ ν ⊗ ᵣ∘ₛTm t δ ν

assₛₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tms Δ Σ)(ν : Ren Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ᵣ ν ≡ σ ∘ₛ (δ ₛ∘ᵣ ν)
assₛₛᵣ ∙       δ ν = refl
assₛₛᵣ (σ , t) δ ν = _,_ & assₛₛᵣ σ δ ν ⊗ ₛ∘ᵣTm t δ ν

∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ [ δ ] ≡ v [ σ ∘ₛ δ ]∈
∘ₛ∈ vz     (σ , _) δ = refl
∘ₛ∈ (vs v) (σ , t) δ = ∘ₛ∈ v σ δ

∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ] [ δ ] ≡ t [ σ ∘ₛ δ ]
∘ₛTm (var v)   σ δ = ∘ₛ∈ v σ δ
∘ₛTm (lam t)   σ δ =
  lam & (
      ∘ₛTm t (keepₛ σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣₛ σ wk (keepₛ δ)
      ◾ (σ ∘ₛ_) & idlᵣₛ (δ ₛ∘ᵣ wk) ◾ assₛₛᵣ σ δ wk ⁻¹))
∘ₛTm (app f a) σ δ = app & ∘ₛTm f σ δ ⊗ ∘ₛTm a σ δ

idₛ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idₛ ]∈ ≡ var v
idₛ∈ vz     = refl
idₛ∈ (vs v) = ₛ∘ᵣ∈ v idₛ wk ⁻¹ ◾ (_[ wk ]ᵣ) & idₛ∈ v ◾ (var ∘ vs) & idᵣ∈ v

idₛTm : ∀ {Γ A}(t : Tm Γ A) → t [ idₛ ] ≡ t
idₛTm (var v)   = idₛ∈ v
idₛTm (lam t)   = lam & idₛTm t
idₛTm (app f x) = app & idₛTm f ⊗ idₛTm x

idrₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ idₛTm t

βᵣ :
  ∀ {Γ Δ Σ A B}(σ : Tms Δ Γ)(ν : Ren Σ Δ) (t : Tm (Γ , A) B) (a : Tm Σ A)
  → t [ keepₛ σ ] [ keep ν ]ᵣ [ idₛ , a ] ≡ t [ (σ ₛ∘ᵣ ν) , a ]
βᵣ σ ν t a =
    ᵣ∘ₛTm (t [ keepₛ σ ]) (keep ν) (idₛ , a)
  ◾ ∘ₛTm t (keepₛ σ) ((ν ᵣ∘ₛ idₛ) , a)
  ◾ ((t [_]) ∘ (_, a)) & (
      assₛᵣₛ σ wk ((ν ᵣ∘ₛ idₛ) , a)
    ◾ (σ ∘ₛ_) & idlᵣₛ (ν ᵣ∘ₛ idₛ)
    ◾ assₛᵣₛ σ ν idₛ ⁻¹
    ◾ idrₛ (σ ₛ∘ᵣ ν))

