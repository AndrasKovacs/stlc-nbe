{-# OPTIONS --without-K #-}

module Naturality where

open import Lib
open import Syntax
open import Nf
open import Renaming
open import Substitution
open import Normalization

u-nat : ∀ {A Γ Δ} → (n : Ne Γ A) → (σ : Ren Δ Γ) → uᴺ A n ᴺ[ σ ]ᵣ ≡ uᴺ A (n [ σ ]ₙₑᵣ)
u-nat {ι}     n σ = refl
u-nat {A ⇒ B} n σ = funext λ Σ → funext λ δ →
  (λ x a → uᴺ B (app x (qᴺ A a))) &
    ⌜⌝Ne-inj
      (⌜⌝Neᵣ n (σ ∘ᵣ δ)
    ◾ ∘ᵣTm ⌜ n ⌝Ne σ δ ⁻¹
    ◾ (_[ δ ]ᵣ) & (⌜⌝Neᵣ n σ ⁻¹)
    ◾ ⌜⌝Neᵣ (n [ σ ]ₙₑᵣ) δ ⁻¹)
  
∈↑-nat : ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tmsᴺ Δ Σ)(δ : Ren Γ Δ) → ∈↑ᴺ v (σ ᴺ∘ᵣ δ) ≡ ∈↑ᴺ v σ ᴺ[ δ ]ᵣ
∈↑-nat vz     (σ , t) δ = refl
∈↑-nat (vs v) (σ , t) δ = ∈↑-nat v σ δ

-- ⌜ Tm↑ t (uCon .Γ) [ σ ]ₙᵣ ⌝ ≡ ⌜ Tm↑ (t [ σ ]ᵣ) (uCon .Δ) ⌝

-- σ  : Ren .Δ .Γ
-- tᶜ : t ~ ⌜ Tm↑ t (uCon .Γ) ⌝
-- t  : Tm .Γ ι
-- .Δ : Con
-- .Γ : Con

-- Tm↑-nat : ∀ {Γ Δ A}(t : Tm Γ A)(δ : Ren Δ Γ) → Tm↑ t (uCon _) ᴺ[ δ ]ᵣ ≡ Tm↑ (t [ δ ]ᵣ) (uCon _)
-- Tm↑-nat = {!!}



-- Tm↑-nat₂ : ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tmsᴺ Δ Σ)(δ : Ren Γ Δ) → Tm↑ t (σ ᴺ∘ᵣ δ) ≡ Tm↑ t σ ᴺ[ δ ]ᵣ
-- Tm↑-nat₂ (var v)   σ δ = ∈↑-nat v σ δ
-- Tm↑-nat₂ (lam t)   σ δ = funext λ Σ → funext λ ν → {!Tm↑-nat₂ t!}
-- Tm↑-nat₂ (app f a) σ δ = 
--     (λ x → x _ idᵣ (Tm↑ a (σ ᴺ∘ᵣ δ))) & Tm↑-nat₂ f σ δ
--   ◾ (Tm↑ f σ _ (δ ∘ᵣ idᵣ)) & Tm↑-nat₂ a σ δ
--   ◾ (λ x → Tm↑ f σ _ x (Tm↑ a σ ᴺ[ δ ]ᵣ)) & idrᵣ δ
--   ◾ {!!}


