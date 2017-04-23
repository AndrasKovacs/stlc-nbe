{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Embedding
open import NormalForm

open import Normalization
open import PresheafRefinement

stab∈ : ∀ {Γ A}(v : A ∈ Γ) → ∈ᴺ v uᶜᴺ ≡ uᴺ (var v)
stab∈ vz     = refl
stab∈ (vs v) =
    ∈ᴺ-nat v wk uᶜᴺ
  ◾ Tyᴺₑ wk & stab∈ v
  ◾ uᴺ-nat wk (var v)

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne n)  = stabNe n
  stab (lam n) = lam & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → Tmᴺ ⌜ n ⌝Ne uᶜᴺ ≡ uᴺ n
  stabNe (var v)   = stab∈ v
  stabNe (app f a) = 
      (λ x → x idₑ (Tmᴺ ⌜ a ⌝ uᶜᴺ)) & stabNe f
    ◾ (λ x → uᴺ (app (Neₑ idₑ f) x)) & stab a
    ◾ (λ x → uᴺ (app x a)) & Ne-idₑ f

