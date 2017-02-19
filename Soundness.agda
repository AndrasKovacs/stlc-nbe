{-# OPTIONS --without-K #-}

module Soundness where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Nf
open import Presheaf
open import Normalization

⟦~⟧ : ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → (σ : Conᴺ Γ Δ) → Tmᴺ t σ ≡ Tmᴺ t' σ
⟦~⟧ (η t) σ = ⇒ᴺ≡ λ {Σ} ν aᴺ →
    (λ x → proj₁ (Tmᴺ t σ) x aᴺ) & (idrₑ ν ⁻¹)
  ◾ (λ x → proj₁ x idₑ aᴺ) &
        (Tmₑᴺ wk t (Conᴺₑ ν σ , aᴺ)
      ◾ Tmᴺ t & OPEᴺ-idₑ (Conᴺₑ ν σ)
      ◾ Tmᴺ-nat t ν σ) ⁻¹                                 
⟦~⟧ (β t t')            σ = (λ x → Tmᴺ t (x , Tmᴺ t' σ)) & (Conᴺ-idₑ σ ◾ Subᴺ-idₛ σ ⁻¹) ◾ Tmₛᴺ (idₛ , t') t σ ⁻¹
⟦~⟧ (lam t~t')          σ = ⇒ᴺ≡ λ {Σ} ν aᴺ → ⟦~⟧ t~t' (Conᴺₑ ν σ , aᴺ)
⟦~⟧ (app₁ {x = x} t~t') σ = (λ f → proj₁ f idₑ (Tmᴺ x σ)) & ⟦~⟧ t~t' σ
⟦~⟧ (app₂ {f = f} t~t') σ = (λ x → proj₁ (Tmᴺ f σ) idₑ x ) & ⟦~⟧ t~t' σ
⟦~⟧ ~refl               σ = refl
⟦~⟧ (t'~t ~⁻¹)          σ = ⟦~⟧ t'~t σ ⁻¹
⟦~⟧ (t~t' ~◾ t'~t'')    σ = ⟦~⟧ t~t' σ ◾ ⟦~⟧ t'~t'' σ

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = qᴺ & ⟦~⟧ t~t' uConᴺ

