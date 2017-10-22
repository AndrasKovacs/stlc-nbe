{-# OPTIONS --without-K #-}

module Embedding where

open import Lib
open import Syntax

infixr 9 _∘ₑ_

-- order-preserving embedding
data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

-- 𝒪PE is a category
idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ , A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

-- (A ∈_) : PSh 𝒪PE
∈ₑ : ∀ {A Γ Δ} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ ∙        v      = v
∈ₑ (drop σ) v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs v) = vs (∈ₑ σ v)

∈-idₑ : ∀ {A Γ}(v : A ∈ Γ) → ∈ₑ idₑ v ≡ v
∈-idₑ vz     = refl
∈-idₑ (vs v) = vs & ∈-idₑ v

∈-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₑ (σ ∘ₑ δ) v ≡ ∈ₑ δ (∈ₑ σ v)
∈-∘ₑ ∙        ∙        v      = refl
∈-∘ₑ σ        (drop δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (drop σ) (keep δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (keep σ) (keep δ) vz     = refl
∈-∘ₑ (keep σ) (keep δ) (vs v) = vs & ∈-∘ₑ σ δ v

-- (Tm _ A) : PSh 𝒪PE
Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (var v)      = var (∈ₑ σ v)
Tmₑ σ (lam t)      = lam (Tmₑ (keep σ) t)
Tmₑ σ (app t u)    = app (Tmₑ σ t) (Tmₑ σ u)
Tmₑ σ tt           = tt
Tmₑ σ (π₁ t)       = π₁ (Tmₑ σ t)
Tmₑ σ (π₂ t)       = π₂ (Tmₑ σ t)
Tmₑ σ (t , u)      = Tmₑ σ t , Tmₑ σ u
Tmₑ σ (inj₁ t)     = inj₁ (Tmₑ σ t)
Tmₑ σ (inj₂ t)     = inj₂ (Tmₑ σ t)
Tmₑ σ (case l r t) = case (Tmₑ σ l) (Tmₑ σ r) (Tmₑ σ t)
Tmₑ σ (⊥-rec t)    = ⊥-rec (Tmₑ σ t)
Tmₑ σ (con t)      = con (Tmₑ σ t)
Tmₑ σ (rec t u)    = rec (Tmₑ σ t) (Tmₑ σ u)

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ (var v)      = var & ∈-idₑ v
Tm-idₑ (lam t)      = lam & Tm-idₑ t
Tm-idₑ (app f a)    = app & Tm-idₑ f ⊗ Tm-idₑ a
Tm-idₑ tt           = refl
Tm-idₑ (π₁ t)       = π₁ & Tm-idₑ t
Tm-idₑ (π₂ t)       = π₂ & Tm-idₑ t
Tm-idₑ (t , u)      = _,_ & Tm-idₑ t ⊗ Tm-idₑ u
Tm-idₑ (inj₁ t)     = inj₁ & Tm-idₑ t
Tm-idₑ (inj₂ t)     = inj₂ & Tm-idₑ t
Tm-idₑ (case l r t) = case & Tm-idₑ l ⊗ Tm-idₑ r ⊗ Tm-idₑ t
Tm-idₑ (⊥-rec t)    = ⊥-rec & Tm-idₑ t
Tm-idₑ (con t)      = con & Tm-idₑ t
Tm-idₑ (rec t u)    = rec & Tm-idₑ t ⊗ Tm-idₑ u

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ (var v)      = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)      = lam & Tm-∘ₑ (keep σ) (keep δ) t
Tm-∘ₑ σ δ (app f a)    = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a
Tm-∘ₑ σ δ tt           = refl
Tm-∘ₑ σ δ (π₁ t)       = π₁ & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (π₂ t)       = π₂ & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (t , u)      = _,_ & Tm-∘ₑ σ δ t ⊗ Tm-∘ₑ σ δ u
Tm-∘ₑ σ δ (inj₁ t)     = inj₁ & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (inj₂ t)     = inj₂ & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (case l r t) = case & Tm-∘ₑ σ δ l ⊗ Tm-∘ₑ σ δ r ⊗ Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (⊥-rec t)    = ⊥-rec & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (con t)      = con & Tm-∘ₑ σ δ t
Tm-∘ₑ σ δ (rec t u)    = rec & Tm-∘ₑ σ δ t ⊗ Tm-∘ₑ σ δ u
