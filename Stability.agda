{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Renaming
open import Nf
open import Normalization

stab∈ : ∀ {Γ A}(v : A ∈ Γ) → ∈↑ᴺ v idᴺₛ ≡ uᴺ (var v)
stab∈ vz     = refl
stab∈ (vs v) =
    ∈↑ᴺ-nat v idᴺₛ wk
  ◾ (_ᴺ[ wk ]ᵣ) & stab∈ v
  ◾ uᴺ-nat (var v) wk
  ◾ (λ x → uᴺ (var (vs x))) & idᵣ∈ v

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne n)  = stabNe n
  stab (lam n) = lam & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → Tm↑ᴺ ⌜ n ⌝Ne idᴺₛ ≡ uᴺ n
  stabNe (var v)   = stab∈ v
  stabNe (app f a) =
      (λ x → proj₁ x idᵣ (Tm↑ᴺ ⌜ a ⌝ idᴺₛ)) & stabNe f
    ◾ (λ x → uᴺ (app (f [ idᵣ ]ₙₑᵣ) x)) & stab a
    ◾ (λ x → uᴺ (app x a)) & idᵣNe f

