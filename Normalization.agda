{-# OPTIONS --without-K #-}

module Normalization where

open import Lib
open import Syntax
open import Renaming
open import Nf

infixr 6 _*∘ᵣ_
infixl 8 _*[_]ᵣ

Tm* : Con → Ty → Set
Tm* Γ ι       = Nf Γ ι
Tm* Γ (A ⇒ B) = ∀ Δ → Ren Δ Γ → Tm* Δ A → Tm* Δ B

data Tms* (Γ : Con) : Con → Set where
  ∙   : Tms* Γ ∙
  _,_ : ∀ {A Δ} (σ : Tms* Γ Δ)(t : Tm* Γ A) → Tms* Γ (Δ , A)
infixr 5 _,_

_*[_]ᵣ : ∀ {A Γ Δ} → Tm* Γ A → Ren Δ Γ → Tm* Δ A
_*[_]ᵣ {ι}     = _[_]ₙᵣ
_*[_]ᵣ {A ⇒ B} = λ f* σ Σ δ → f* Σ (σ ∘ᵣ δ)

_*∘ᵣ_ : ∀ {Γ Δ Σ} → Tms* Δ Σ → Ren Γ Δ → Tms* Γ Σ
∙       *∘ᵣ δ = ∙
(σ , t) *∘ᵣ δ = (σ *∘ᵣ δ) , (t *[ δ ]ᵣ)

∈↑ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Tms* Δ Γ → Tm* Δ A
∈↑ vz     (σ , t) = t
∈↑ (vs v) (σ , t) = ∈↑ v σ

Tm↑ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Tms* Δ Γ → Tm* Δ A
Tm↑ (var v)   σ = ∈↑ v σ
Tm↑ (lam t)   σ = λ Σ δ a → Tm↑ t (σ *∘ᵣ δ , a)
Tm↑ (app f a) σ = Tm↑ f σ _ idᵣ (Tm↑ a σ)

mutual
  q : ∀ A {Γ} → Tm* Γ A → Nf Γ A
  q ι       t = t
  q (A ⇒ B) t = lam (q B (t _ wk (u A (var vz))))

  u : ∀ A {Γ} → Ne Γ A → Tm* Γ A
  u ι       n = ne n
  u (A ⇒ B) n = λ Δ σ a → u B (n [ σ ]ₙₑᵣ $ₙ q A a)

uCon : ∀ Γ → Tms* Γ Γ
uCon ∙       = ∙
uCon (Γ , t) = uCon Γ *∘ᵣ wk , u _ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = q _ (Tm↑ t (uCon _))

