
module Embedding where

open import Lib
open import Syntax

infixr 9 _∘ₑ_

-- order-preserving embedding
data OPE : Con → Con → Set where
  idₑ  : ∀ {Γ} → OPE Γ Γ
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

-- 𝒪PE is a category
wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ idₑ    = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
idₑ    ∘ₑ keep δ = keep δ
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ idₑ      = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = refl

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        idₑ      = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        idₑ      (keep ν) = refl
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ idₑ      (keep δ) (keep ν) = refl
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

-- (A ∈_) : PSh 𝒪PE
∈ₑ : ∀ {A Γ Δ} → OPE Γ Δ → A ∈ Δ → A ∈ Γ
∈ₑ idₑ      v      = v
∈ₑ (drop σ) v      = vs (∈ₑ σ v)
∈ₑ (keep σ) vz     = vz
∈ₑ (keep σ) (vs v) = vs (∈ₑ σ v)

∈-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(v : A ∈ Σ) → ∈ₑ (σ ∘ₑ δ) v ≡ ∈ₑ δ (∈ₑ σ v)
∈-∘ₑ σ        idₑ      v      = refl
∈-∘ₑ σ        (drop δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ idₑ      (keep δ) v      = refl
∈-∘ₑ (drop σ) (keep δ) v      = vs & ∈-∘ₑ σ δ v
∈-∘ₑ (keep σ) (keep δ) vz     = refl
∈-∘ₑ (keep σ) (keep δ) (vs v) = vs & ∈-∘ₑ σ δ v

-- (Tm _ A) : PSh 𝒪PE
Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (var v)   = var (∈ₑ σ v)
Tmₑ σ (lam t)   = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a) = app (Tmₑ σ f) (Tmₑ σ a)

Idish : ∀ {Γ} → OPE Γ Γ → Set
Idish idₑ      = ⊤
Idish (drop σ) = ⊥
Idish (keep σ) = Idish σ

∈-idₑ : ∀ {A Γ}(v : A ∈ Γ){σ : OPE Γ Γ}{p : Idish σ} → ∈ₑ σ v ≡ v
∈-idₑ v      {idₑ}       = refl
∈-idₑ v      {drop σ} {()}
∈-idₑ vz     {keep σ}    = refl
∈-idₑ (vs v) {keep σ}{p} = vs & ∈-idₑ v {σ}{p}

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A){σ : OPE Γ Γ}{p : Idish σ} → Tmₑ σ t ≡ t
Tm-idₑ (var v)   {σ}{p} = var & ∈-idₑ v {σ}{p}
Tm-idₑ (lam t)   {σ}{p} = lam & Tm-idₑ t {keep σ}{p}
Tm-idₑ (app f a) {σ}{p} = app & Tm-idₑ f {σ}{p} ⊗ Tm-idₑ a {σ}{p}

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ (var v)   = var & ∈-∘ₑ σ δ v
Tm-∘ₑ σ δ (lam t)   = lam & Tm-∘ₑ (keep σ) (keep δ) t
Tm-∘ₑ σ δ (app f a) = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a

