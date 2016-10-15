{-# OPTIONS --without-K #-}

module Functoriality where

open import Lib
open import Syntax
open import Nf
open import Renaming
open import Substitution
open import Normalization

uᴺ-nat : ∀ {A Γ Δ} → (n : Ne Γ A) → (σ : Ren Δ Γ) → uᴺ A n ᴺ[ σ ]ᵣ ≡ uᴺ A (n [ σ ]ₙₑᵣ)
uᴺ-nat {ι}     n σ = refl
uᴺ-nat {A ⇒ B} n σ =
  funext λ Σ → funext λ δ → (λ x a → uᴺ B (app x (qᴺ A a))) & ∘ᵣNe n σ δ ⁻¹

∈↑ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tmsᴺ Δ Σ)(δ : Ren Γ Δ) → ∈↑ᴺ v (σ ᴺ∘ᵣ δ) ≡ ∈↑ᴺ v σ ᴺ[ δ ]ᵣ
∈↑ᴺ-nat vz     (σ , t) δ = refl
∈↑ᴺ-nat (vs v) (σ , t) δ = ∈↑ᴺ-nat v σ δ

ᴺ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tmᴺ Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t ᴺ[ σ ]ᵣ ᴺ[ δ ]ᵣ ≡ t ᴺ[ σ ∘ᵣ δ ]ᵣ
ᴺ∘ᵣTm {A = ι}     t σ δ = ∘ᵣNf t σ δ
ᴺ∘ᵣTm {A = A ⇒ B} t σ δ = funext λ Ξ → funext λ ν → t Ξ & (assᵣ σ δ ν ⁻¹)

assₙᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tmsᴺ Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ᴺ∘ᵣ δ) ᴺ∘ᵣ ν ≡ σ ᴺ∘ᵣ (δ ∘ᵣ ν)
assₙᵣᵣ ∙       δ ν = refl
assₙᵣᵣ (σ , t) δ ν = _,_ & assₙᵣᵣ σ δ ν ⊗ ᴺ∘ᵣTm t δ ν

mutual
  appᴺ-nat :
    ∀ {Γ Δ Σ A B}(f : Tm Γ (A ⇒ B))(a : Tm Γ A)(σ : Tmsᴺ Δ Γ)(δ : Ren Σ Δ)
    → Tm↑ᴺ f σ _ δ (Tm↑ᴺ a σ ᴺ[ δ ]ᵣ) ≡ Tm↑ᴺ f σ _ idᵣ (Tm↑ᴺ a σ) ᴺ[ δ ]ᵣ
  appᴺ-nat t a σ δ = {!!}

-- for lambda
-- Tm↑ᴺ f (σ ᴺ∘ᵣ δ , Tm↑ᴺ a σ ᴺ[ δ ]ᵣ)   -- by definition
-- Tm↑ᴺ f ((σ , Tm↑ᴺ a σ) ᴺ∘ᵣ δ)         -- Tm↑ᴺ-nat f (σ , Tm↑ᴺ a σ) δ
-- Tm↑ᴺ f (σ , Tm↑ᴺ a σ) ᴺ[ δ ]ᵣ         -- idrᴺᵣ σ ⁻¹
-- Tm↑ᴺ f (σ ᴺ∘ᵣ idᵣ , Tm↑ᴺ a σ) ᴺ[ δ ]ᵣ -- ∎


  Tm↑ᴺ-nat :
    ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : Tmsᴺ Σ Γ)(δ : Ren Δ Σ)
    → Tm↑ᴺ t (σ ᴺ∘ᵣ δ) ≡ Tm↑ᴺ t σ ᴺ[ δ ]ᵣ
  Tm↑ᴺ-nat (var v)   σ δ = ∈↑ᴺ-nat v σ δ
  Tm↑ᴺ-nat (lam t)   σ δ =
    funext λ Ξ → funext λ ν → funext λ a → (λ x → Tm↑ᴺ t (x , a)) & assₙᵣᵣ σ δ ν
  Tm↑ᴺ-nat (app f a) σ δ =
       (λ x → x _ idᵣ (Tm↑ᴺ a (σ ᴺ∘ᵣ δ)) ) & Tm↑ᴺ-nat f σ δ
     ◾ Tm↑ᴺ f σ _ (δ ∘ᵣ idᵣ) & Tm↑ᴺ-nat a σ δ
     ◾ (λ x → Tm↑ᴺ f σ _ x (Tm↑ᴺ a σ ᴺ[ δ ]ᵣ)) & idrᵣ δ
     ◾ appᴺ-nat f a σ δ

