{-# OPTIONS --without-K #-}

module Nf where

open import Lib hiding (⊤; ⊥)
import Lib as L
open import Syntax
open import Embedding

mutual
  data Nf (Γ : Con) : Ty → Set where
    tt   : Nf Γ ⊤
    _,_  : ∀ {A B} → Nf Γ A → Nf Γ B → Nf Γ (A * B)
    lam  : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

    ne⊥  : Ne Γ ⊥ → Nf Γ ⊥

    ne+  : ∀ {A B} → Ne Γ (A + B) → Nf Γ (A + B)
    inj₁ : ∀ {A B} → Nf Γ A → Nf Γ (A + B)
    inj₂ : ∀ {A B} → Nf Γ B → Nf Γ (A + B)

    neμ  : ∀ {F} → Ne Γ (μ F) → Nf Γ (μ F)
    con  : ∀ {F} → Nf Γ (apF F (μ F)) → Nf Γ (μ F)

  data Ne (Γ : Con) : Ty → Set where
    var   : ∀ {A} → A ∈ Γ → Ne Γ A
    app   : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B
    π₁    : ∀ {A B} → Ne Γ (A * B) → Ne Γ A
    π₂    : ∀ {A B} → Ne Γ (A * B) → Ne Γ B
    case  : ∀ {A B C} → Nf Γ (A ⇒ C) → Nf Γ (B ⇒ C) → Ne Γ (A + B) → Ne Γ C
    ⊥-rec : ∀ {A} → Ne Γ ⊥ → Ne Γ A
    rec   : ∀ {F A} → Nf Γ (apF F A ⇒ A) → Ne Γ (μ F) → Ne Γ A

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ (ne+ n)  = ne+ (Neₑ σ n)
  Nfₑ σ (ne⊥ n)  = ne⊥ (Neₑ σ n)
  Nfₑ σ (lam n)  = lam (Nfₑ (keep σ) n)
  Nfₑ σ (t , u)  = Nfₑ σ t , Nfₑ σ u
  Nfₑ σ tt       = tt
  Nfₑ σ (inj₁ t) = inj₁ (Nfₑ σ t)
  Nfₑ σ (inj₂ t) = inj₂ (Nfₑ σ t)
  Nfₑ σ (neμ t)  = neμ (Neₑ σ t)
  Nfₑ σ (con t)  = con (Nfₑ σ t)

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var v)      = var (∈ₑ σ v)
  Neₑ σ (app f a)    = app (Neₑ σ f) (Nfₑ σ a)
  Neₑ σ (π₁ t)       = π₁ (Neₑ σ t)
  Neₑ σ (π₂ t)       = π₂ (Neₑ σ t)
  Neₑ σ (case l r t) = case (Nfₑ σ l) (Nfₑ σ r) (Neₑ σ t)
  Neₑ σ (⊥-rec t)    = ⊥-rec (Neₑ σ t)
  Neₑ σ (rec t u)    = rec (Nfₑ σ t) (Neₑ σ u)

-- Natural embedding into Tm
mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ tt      ⌝ = tt
  ⌜ (t , u) ⌝ = ⌜ t ⌝ , ⌜ u ⌝
  ⌜ lam t   ⌝ = lam ⌜ t ⌝
  ⌜ ne+ n   ⌝ = ⌜ n ⌝Ne
  ⌜ ne⊥ n   ⌝ = ⌜ n ⌝Ne
  ⌜ inj₁ t  ⌝ = inj₁ ⌜ t ⌝
  ⌜ inj₂ t  ⌝ = inj₂ ⌜ t ⌝
  ⌜ neμ t   ⌝ = ⌜ t ⌝Ne
  ⌜ con t   ⌝ = con ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v      ⌝Ne = var v
  ⌜ app n t    ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝
  ⌜ π₁ t       ⌝Ne = π₁ ⌜ t ⌝Ne
  ⌜ π₂ t       ⌝Ne = π₂ ⌜ t ⌝Ne
  ⌜ case l r t ⌝Ne = case ⌜ l ⌝ ⌜ r ⌝ ⌜ t ⌝Ne
  ⌜ ⊥-rec t    ⌝Ne = ⊥-rec ⌜ t ⌝Ne
  ⌜ rec t u    ⌝Ne = rec ⌜ t ⌝ ⌜ u ⌝Ne

mutual
  ⌜⌝Ne-nat : ∀ {Γ Δ A}(σ : OPE Δ Γ)(n : Ne Γ A) → ⌜ Neₑ σ n ⌝Ne ≡ Tmₑ σ ⌜ n ⌝Ne
  ⌜⌝Ne-nat σ (var v)      = refl
  ⌜⌝Ne-nat σ (app f a)    = app & ⌜⌝Ne-nat σ f ⊗ ⌜⌝Nf-nat σ a
  ⌜⌝Ne-nat σ (π₁ t)       = π₁ & ⌜⌝Ne-nat σ t
  ⌜⌝Ne-nat σ (π₂ t)       = π₂ & ⌜⌝Ne-nat σ t
  ⌜⌝Ne-nat σ (case l r t) = case & ⌜⌝Nf-nat σ l ⊗ ⌜⌝Nf-nat σ r ⊗ ⌜⌝Ne-nat σ t
  ⌜⌝Ne-nat σ (⊥-rec t)    = ⊥-rec & ⌜⌝Ne-nat σ t
  ⌜⌝Ne-nat σ (rec t u)    = rec & ⌜⌝Nf-nat σ t ⊗ ⌜⌝Ne-nat σ u

  ⌜⌝Nf-nat : ∀ {Γ Δ A}(σ : OPE Δ Γ)(n : Nf Γ A) → ⌜ Nfₑ σ n ⌝ ≡ Tmₑ σ ⌜ n ⌝
  ⌜⌝Nf-nat σ (ne+ n)  = ⌜⌝Ne-nat σ n
  ⌜⌝Nf-nat σ (ne⊥ n)  = ⌜⌝Ne-nat σ n
  ⌜⌝Nf-nat σ (lam n)  = lam & ⌜⌝Nf-nat (keep σ) n
  ⌜⌝Nf-nat σ (t , u)  = _,_ & ⌜⌝Nf-nat σ t ⊗ ⌜⌝Nf-nat σ u
  ⌜⌝Nf-nat σ tt       = refl
  ⌜⌝Nf-nat σ (inj₁ t) = inj₁ & ⌜⌝Nf-nat σ t
  ⌜⌝Nf-nat σ (inj₂ t) = inj₂ & ⌜⌝Nf-nat σ t
  ⌜⌝Nf-nat σ (neμ t)  = ⌜⌝Ne-nat σ t
  ⌜⌝Nf-nat σ (con t)  = con & ⌜⌝Nf-nat σ t

-- (Ne _ A) and (Nf _ A) are presheaves on OPE
mutual
  Nf-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Nf Σ A)
    → Nfₑ (σ ∘ₑ δ) t ≡ Nfₑ δ (Nfₑ σ t)
  Nf-∘ₑ σ δ (ne+ n)  = ne+ & Ne-∘ₑ σ δ n
  Nf-∘ₑ σ δ (ne⊥ n)  = ne⊥ & Ne-∘ₑ σ δ n
  Nf-∘ₑ σ δ (lam t)  = lam & Nf-∘ₑ (keep σ) (keep δ) t
  Nf-∘ₑ σ δ (t , u)  = _,_ & Nf-∘ₑ σ δ t ⊗ Nf-∘ₑ σ δ u
  Nf-∘ₑ σ δ tt       = refl
  Nf-∘ₑ σ δ (inj₁ t) = inj₁ & Nf-∘ₑ σ δ t
  Nf-∘ₑ σ δ (inj₂ t) = inj₂ & Nf-∘ₑ σ δ t
  Nf-∘ₑ σ δ (neμ t)  = neμ & Ne-∘ₑ σ δ t
  Nf-∘ₑ σ δ (con t)  = con & Nf-∘ₑ σ δ t

  Ne-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Ne Σ A)
    → Neₑ (σ ∘ₑ δ) t ≡ Neₑ δ (Neₑ σ t)
  Ne-∘ₑ σ δ (var v)      = var & ∈-∘ₑ σ δ v
  Ne-∘ₑ σ δ (app f a)    = app & Ne-∘ₑ σ δ f ⊗ Nf-∘ₑ σ δ a
  Ne-∘ₑ σ δ (π₁ t)       = π₁ & Ne-∘ₑ σ δ t
  Ne-∘ₑ σ δ (π₂ t)       = π₂ & Ne-∘ₑ σ δ t
  Ne-∘ₑ σ δ (case l r t) = case & Nf-∘ₑ σ δ l ⊗ Nf-∘ₑ σ δ r ⊗ Ne-∘ₑ σ δ t
  Ne-∘ₑ σ δ (⊥-rec t)    = ⊥-rec & Ne-∘ₑ σ δ t
  Ne-∘ₑ σ δ (rec t u)    = rec & Nf-∘ₑ σ δ t ⊗ Ne-∘ₑ σ δ u

mutual
  Nf-idₑ : ∀ {Γ A}(t : Nf Γ A) → Nfₑ idₑ t ≡ t
  Nf-idₑ (ne+ n)  = ne+ & Ne-idₑ n
  Nf-idₑ (ne⊥ n)  = ne⊥ & Ne-idₑ n
  Nf-idₑ (lam t)  = lam & Nf-idₑ t
  Nf-idₑ (t , u)  = _,_ & Nf-idₑ t ⊗ Nf-idₑ u
  Nf-idₑ tt       = refl
  Nf-idₑ (inj₁ t) = inj₁ & Nf-idₑ t
  Nf-idₑ (inj₂ t) = inj₂ & Nf-idₑ t
  Nf-idₑ (neμ t)  = neμ & Ne-idₑ t
  Nf-idₑ (con t)  = con & Nf-idₑ t

  Ne-idₑ : ∀ {Γ A}(t : Ne Γ A) → Neₑ idₑ t ≡ t
  Ne-idₑ (var v)      = var & ∈-idₑ v
  Ne-idₑ (app f a)    = app & Ne-idₑ f ⊗ Nf-idₑ a
  Ne-idₑ (π₁ t)       = π₁ & Ne-idₑ t
  Ne-idₑ (π₂ t)       = π₂ & Ne-idₑ t
  Ne-idₑ (case l r t) = case & Nf-idₑ l ⊗ Nf-idₑ r ⊗ Ne-idₑ t
  Ne-idₑ (⊥-rec t)    = ⊥-rec & Ne-idₑ t
  Ne-idₑ (rec t u)    = rec & Nf-idₑ t ⊗ Ne-idₑ u
