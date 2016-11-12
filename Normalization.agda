{-# OPTIONS --without-K #-}

module Normalization where

open import Lib
open import Syntax
open import Embedding
open import Nf
open import Presheaf

mutual
  qᴺ : ∀ {A Γ} → Tyᴺ A Γ → Nf Γ A
  qᴺ {ι}     tᴺ       = tᴺ
  qᴺ {A ⇒ B} (tᴺ , _) = lam (qᴺ (tᴺ wk (uᴺ (var vz))))

  qᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(tᴺ : Tyᴺ A Γ) → Nfₑ σ (qᴺ tᴺ) ≡ qᴺ (Tyᴺₑ σ tᴺ)
  qᴺ-nat {ι}     σ tᴺ            = refl
  qᴺ-nat {A ⇒ B} σ (tᴺ , tᴺ-nat) =
    lam & (qᴺ-nat (keep σ) (tᴺ wk (uᴺ (var vz)))
         ◾ qᴺ & (tᴺ-nat wk (keep σ) (uᴺ (var vz)) ⁻¹
                ◾ tᴺ & (drop & (idlₑ σ ◾ idrₑ σ ⁻¹)) ⊗ uᴺ-nat (keep σ) (var vz)))

  uᴺ : ∀ {A Γ} → Ne Γ A → Tyᴺ A Γ
  uᴺ {ι}     n = ne n
  uᴺ {A ⇒ B} n =
    (λ δ aᴺ → uᴺ (app (Neₑ δ n) (qᴺ aᴺ))) ,
    (λ σ δ aᴺ → (λ x y → uᴺ (app x y)) & (Ne-∘ₑ σ δ n ⁻¹) ⊗ qᴺ-nat δ aᴺ ⁻¹
              ◾ uᴺ-nat δ (app (Neₑ σ n) (qᴺ aᴺ)) ⁻¹)

  uᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(n : Ne Γ A) → Tyᴺₑ σ (uᴺ n) ≡ uᴺ (Neₑ σ n)
  uᴺ-nat {ι}     σ n = refl
  uᴺ-nat {A ⇒ B} σ n = ⇒ᴺ≡ λ δ aᴺ → (λ x → uᴺ (app x (qᴺ aᴺ))) & Ne-∘ₑ σ δ n

uConᴺ : ∀ {Γ} → Conᴺ Γ Γ
uConᴺ {∙}     = ∙
uConᴺ {Γ , A} = Conᴺₑ wk uConᴺ , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tmᴺ t uConᴺ)

