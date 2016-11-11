{-# OPTIONS --without-K #-}

module Nf where

open import Lib
open import Syntax
open import Embedding

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var : ∀ {A} → A ∈ Γ → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ (ne n)  = ne (Neₑ σ n)
  Nfₑ σ (lam n) = lam (Nfₑ (keep σ) n)

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var v)   = var (∈ₑ σ v)
  Neₑ σ (app f a) = app (Neₑ σ f) (Nfₑ σ a)

-- Natural embedding into Tm
mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v   ⌝Ne = var v
  ⌜ app n t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

mutual
  ⌜⌝Neₑ-nat : ∀ {Γ Δ A}(n : Ne Γ A)(σ : OPE Δ Γ) → ⌜ Neₑ σ n ⌝Ne ≡ Tmₑ σ ⌜ n ⌝Ne
  ⌜⌝Neₑ-nat (var v)   σ = refl
  ⌜⌝Neₑ-nat (app f a) σ = app & ⌜⌝Neₑ-nat f σ ⊗ ⌜⌝Nfₑ-nat a σ

  ⌜⌝Nfₑ-nat : ∀ {Γ Δ A}(n : Nf Γ A)(σ : OPE Δ Γ) → ⌜ Nfₑ σ n ⌝ ≡ Tmₑ σ ⌜ n ⌝
  ⌜⌝Nfₑ-nat (ne n)  σ = ⌜⌝Neₑ-nat n σ
  ⌜⌝Nfₑ-nat (lam n) σ = lam & ⌜⌝Nfₑ-nat n (keep σ)

-- (Ne _ A) and (Nf _ A) are presheaves on OPE
mutual
  Nf-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Nf Σ A)
    → Nfₑ (σ ∘ₑ δ) t ≡ Nfₑ δ (Nfₑ σ t)
  Nf-∘ₑ  σ δ (ne n)  = ne & Ne-∘ₑ σ δ n
  Nf-∘ₑ  σ δ (lam t) = lam & Nf-∘ₑ (keep σ) (keep δ) t
    
  Ne-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Ne Σ A)
    → Neₑ (σ ∘ₑ δ) t ≡ Neₑ δ (Neₑ σ t)
  Ne-∘ₑ σ δ (var v)   = var & ∈-∘ₑ σ δ v
  Ne-∘ₑ σ δ (app f a) = app & Ne-∘ₑ σ δ f ⊗ Nf-∘ₑ σ δ a

mutual
  Nf-idₑ : ∀ {Γ A}(t : Nf Γ A) → Nfₑ idₑ t ≡ t
  Nf-idₑ (ne n)  = ne & Ne-idₑ n
  Nf-idₑ (lam t) = lam & Nf-idₑ t

  Ne-idₑ : ∀ {Γ A}(t : Ne Γ A) → Neₑ idₑ t ≡ t
  Ne-idₑ (var v)   = var & ∈-idₑ v
  Ne-idₑ (app f a) = app & Ne-idₑ f ⊗ Nf-idₑ a

