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

⟦~⟧ : ∀ {A Γ Δ}{t t' : Tm Γ A} → t ~ t' → (σ : Conᴺ Γ Δ) → Tmᴺ t σ ≡ Tmᴺ t' σ
⟦~⟧ (⇒η {A} {B} t) σᴺ =
  ⇒ᴺ≡ {A}{B} λ {Σ} ν aᴺ →
    (λ x → proj₁ (Tmᴺ t σᴺ) x aᴺ) & (idrₑ ν ⁻¹)
  ◾ (λ x → proj₁ x idₑ aᴺ) &
        (Tmₑᴺ wk t (Conᴺₑ ν σᴺ , aᴺ)
      ◾ Tmᴺ t & OPEᴺ-idₑ (Conᴺₑ ν σᴺ)
      ◾ Tmᴺ-nat t ν σᴺ) ⁻¹
⟦~⟧ (⇒β t t')         σᴺ =
  (λ x → Tmᴺ t (x , Tmᴺ t' σᴺ)) & (Conᴺ-idₑ σᴺ ◾ Subᴺ-idₛ σᴺ ⁻¹) ◾ Tmₛᴺ (idₛ , t') t σᴺ ⁻¹
⟦~⟧ (lam {A} {B} t~t') σ =
  ⇒ᴺ≡ {A}{B} λ {Σ} ν aᴺ → ⟦~⟧ t~t' (Conᴺₑ ν σ , aᴺ)
⟦~⟧ (app t~t' a~a')  σᴺ = (λ f a → proj₁ f idₑ a) & ⟦~⟧ t~t' σᴺ ⊗ ⟦~⟧ a~a' σᴺ
⟦~⟧ ~refl            σᴺ = refl
⟦~⟧ (t'~t ~⁻¹)       σᴺ = ⟦~⟧ t'~t σᴺ ⁻¹
⟦~⟧ (t~t' ~◾ t'~t'') σᴺ = ⟦~⟧ t~t' σᴺ ◾ ⟦~⟧ t'~t'' σᴺ
⟦~⟧ (π₁β t u) σᴺ = refl
⟦~⟧ (π₂β t u) σᴺ = refl
⟦~⟧ (π₁ t) σᴺ = proj₁ & ⟦~⟧ t σᴺ
⟦~⟧ (π₂ t) σᴺ = proj₂ & ⟦~⟧ t σᴺ
⟦~⟧ (πη t) σᴺ = refl
⟦~⟧ (t , u) σᴺ = _,_ & ⟦~⟧ t σᴺ ⊗ ⟦~⟧ u σᴺ
⟦~⟧ (inj₁ t) σᴺ = inj₁ & ⟦~⟧ t σᴺ
⟦~⟧ (inj₂ t) σᴺ = inj₂ & ⟦~⟧ t σᴺ
⟦~⟧ (case₁β l r t) σᴺ = (λ x → Tmᴺ l (x , Tmᴺ t σᴺ)) & (Subᴺ-idₛ σᴺ ⁻¹) ◾ Tmₛᴺ (idₛ , t) l σᴺ ⁻¹
⟦~⟧ (case₂β l r t) σᴺ = (λ x → Tmᴺ r (x , Tmᴺ t σᴺ)) & (Subᴺ-idₛ σᴺ ⁻¹) ◾ Tmₛᴺ (idₛ , t) r σᴺ ⁻¹
⟦~⟧ {C} (case {A} {B} {l = l} {l'} {r} {r'} {t} {t'} l~l' r~r' t~t') σᴺ
  rewrite ⟦~⟧ t~t' σᴺ with Tmᴺ t' σᴺ
... | ne+ n rewrite
        ⟦~⟧ l~l' (Conᴺₑ (wk {A}) σᴺ , uᴺ {A} (var vz))
      | ⟦~⟧ r~r' (Conᴺₑ (wk {B}) σᴺ , uᴺ {B} (var vz)) = refl
... | inj₁ tᴺ rewrite ⟦~⟧ l~l' (σᴺ , tᴺ) = refl
... | inj₂ tᴺ rewrite ⟦~⟧ r~r' (σᴺ , tᴺ) = refl
⟦~⟧ (⊥-rec {A} t) σᴺ = (uᴺ {A} ∘ ⊥-rec) & ⟦~⟧ t σᴺ
⟦~⟧ (⊤η t) σᴺ with Tmᴺ t σᴺ
... | tt = refl

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = qᴺ & ⟦~⟧ t~t' uConᴺ
