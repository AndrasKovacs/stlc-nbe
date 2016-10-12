{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Renaming
open import Substitution
open import Conversion
open import Nf
open import Normalization
open import Naturality

stab∈ : ∀ {Γ A}(v : A ∈ Γ) → ∈↑ᴺ v idᴺₛ ≡ uᴺ A (var v)
stab∈ vz     = refl
stab∈ (vs v) =
    ∈↑-nat v idᴺₛ wk
  ◾ (_ᴺ[ wk ]ᵣ) & stab∈ v
  ◾ u-nat (var v) wk
  ◾ (λ x → uᴺ _ (var (vs x))) & idᵣ∈ v

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne n)  = stabNe n
  stab (lam n) = lam & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → Tm↑ᴺ ⌜ n ⌝Ne idᴺₛ ≡ uᴺ A n
  stabNe (var v)   = stab∈ v
  stabNe (app f a) =
      (λ x → x _ idᵣ (Tm↑ᴺ ⌜ a ⌝ idᴺₛ)) & stabNe f
    ◾ (λ x → uᴺ _ (app (f [ idᵣ ]ₙₑᵣ) x)) & stab a
    ◾ (λ x → uᴺ _ (app x a)) & ⌜⌝Ne-inj (⌜⌝Neᵣ f idᵣ ◾ idᵣTm ⌜ f ⌝Ne)

