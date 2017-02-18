{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Embedding
open import Nf
open import Normalization

stab∈ : ∀ {Γ A}(v : A ∈ Γ) → ∈ᴺ v uConᴺ ≡ uᴺ (var v)
stab∈ vz     = refl
stab∈ (vs v) =
    ∈ᴺ-nat v wk uConᴺ
  ◾ Tyᴺₑ wk & stab∈ v
  ◾ uᴺ-nat wk (var v)
  ◾ (λ x → uᴺ (var (vs x))) & ∈-idₑ v

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne n)  = stabNe n
  stab (lam n) = lam & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → Tmᴺ ⌜ n ⌝Ne uConᴺ ≡ uᴺ n
  stabNe (var v)   = stab∈ v
  stabNe (app f a) = 
      (λ x → x idₑ (Tmᴺ ⌜ a ⌝ uConᴺ)) & stabNe f
    ◾ (λ x → uᴺ (app (Neₑ idₑ f) x)) & stab a
    ◾ (λ x → uᴺ (app x a)) & Ne-idₑ f

