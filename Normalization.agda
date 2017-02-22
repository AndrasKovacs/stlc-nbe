{-# OPTIONS --without-K #-}

module Normalization where

open import Syntax
open import Embedding
open import Substitution
open import Nf

Tyᴺ : Ty → Con → Set
Tyᴺ ι       Γ = Nf Γ ι
Tyᴺ (A ⇒ B) Γ = ∀ {Δ} → OPE Δ Γ → Tyᴺ A Δ → Tyᴺ B Δ

Tyᴺₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴺ A Γ → Tyᴺ A Δ
Tyᴺₑ {ι}     σ tᴺ = Nfₑ σ tᴺ
Tyᴺₑ {A ⇒ B} σ tᴺ = λ δ → tᴺ (σ ∘ₑ δ)

data Conᴺ : Con → Con → Set where
  ∙   : ∀ {Δ} → Conᴺ ∙ Δ
  _,_ : ∀ {A Γ Δ} → Conᴺ Γ Δ → Tyᴺ A Δ → Conᴺ (Γ , A) Δ

Conᴺₑ : ∀ {Γ Δ Σ} → OPE Σ Δ → Conᴺ Γ Δ → Conᴺ Γ Σ
Conᴺₑ σ ∙         = ∙
Conᴺₑ σ (Γᴺ , tᴺ) = Conᴺₑ σ Γᴺ , Tyᴺₑ σ tᴺ

∈ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (Γᴺ , tᴺ) = tᴺ
∈ᴺ (vs v) (Γᴺ , _ ) = ∈ᴺ v Γᴺ

Tmᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
Tmᴺ (var v)   Γᴺ = ∈ᴺ v Γᴺ
Tmᴺ (lam t)   Γᴺ = λ σ aᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ , aᴺ)
Tmᴺ (app f x) Γᴺ = Tmᴺ f Γᴺ idₑ (Tmᴺ x Γᴺ)

mutual
  qᴺ : ∀ {A Γ} → Tyᴺ A Γ → Nf Γ A
  qᴺ {ι}     tᴺ = tᴺ
  qᴺ {A ⇒ B} tᴺ = lam (qᴺ (tᴺ wk (uᴺ (var vz))))

  uᴺ : ∀ {A Γ} → Ne Γ A → Tyᴺ A Γ
  uᴺ {ι}     n = ne n
  uᴺ {A ⇒ B} n = λ σ aᴺ → uᴺ (app (Neₑ σ n) (qᴺ aᴺ))

uᶜᴺ : ∀ {Γ} → Conᴺ Γ Γ
uᶜᴺ {∙}      = ∙
uᶜᴺ {Γ , tᴺ} = Conᴺₑ wk uᶜᴺ , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tmᴺ t uᶜᴺ)

