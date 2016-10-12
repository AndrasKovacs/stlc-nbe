{-# OPTIONS --without-K #-}

module Normalization where

open import Lib
open import Syntax
open import Renaming
open import Nf

infixr 6 _ᴺ∘ᵣ_
infixl 8 _ᴺ[_]ᵣ

Tmᴺ : Con → Ty → Set
Tmᴺ Γ ι       = Nf Γ ι
Tmᴺ Γ (A ⇒ B) = ∀ Δ → Ren Δ Γ → Tmᴺ Δ A → Tmᴺ Δ B

data Tmsᴺ (Γ : Con) : Con → Set where
  ∙   : Tmsᴺ Γ ∙
  _,_ : ∀ {A Δ} (σ : Tmsᴺ Γ Δ)(t : Tmᴺ Γ A) → Tmsᴺ Γ (Δ , A)
infixr 5 _,_

_ᴺ[_]ᵣ : ∀ {A Γ Δ} → Tmᴺ Γ A → Ren Δ Γ → Tmᴺ Δ A
_ᴺ[_]ᵣ {ι}     = _[_]ₙᵣ
_ᴺ[_]ᵣ {A ⇒ B} = λ f* σ Σ δ → f* Σ (σ ∘ᵣ δ)

_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ} → Tmsᴺ Δ Σ → Ren Γ Δ → Tmsᴺ Γ Σ
∙       ᴺ∘ᵣ δ = ∙
(σ , t) ᴺ∘ᵣ δ = (σ ᴺ∘ᵣ δ) , (t ᴺ[ δ ]ᵣ)

∈↑ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Tmsᴺ Δ Γ → Tmᴺ Δ A
∈↑ᴺ vz     (σ , t) = t
∈↑ᴺ (vs v) (σ , t) = ∈↑ᴺ v σ

Tm↑ᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Tmsᴺ Δ Γ → Tmᴺ Δ A
Tm↑ᴺ (var v)   σ = ∈↑ᴺ v σ
Tm↑ᴺ (lam t)   σ = λ Σ δ a → Tm↑ᴺ t (σ ᴺ∘ᵣ δ , a)
Tm↑ᴺ (app f a) σ = Tm↑ᴺ f σ _ idᵣ (Tm↑ᴺ a σ)

mutual
  qᴺ : ∀ A {Γ} → Tmᴺ Γ A → Nf Γ A
  qᴺ ι       t = t
  qᴺ (A ⇒ B) t = lam (qᴺ B (t _ wk (uᴺ A (var vz))))

  uᴺ : ∀ A {Γ} → Ne Γ A → Tmᴺ Γ A
  uᴺ ι       n = ne n
  uᴺ (A ⇒ B) n = λ Δ σ a → uᴺ B (app (n [ σ ]ₙₑᵣ) (qᴺ A a))

idᴺₛ : ∀ {Γ} → Tmsᴺ Γ Γ
idᴺₛ {∙}     = ∙
idᴺₛ {Γ , t} = idᴺₛ {Γ} ᴺ∘ᵣ wk , uᴺ _ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ _ (Tm↑ᴺ t idᴺₛ)

