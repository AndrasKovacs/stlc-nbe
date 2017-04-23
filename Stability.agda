{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Embedding
open import NormalForm

open import Normalization
open import PresheafRefinement

stable∈ : ∀ {Γ A}(v : A ∈ Γ) → ∈ᴺ v uᶜᴺ ≡ uᴺ (var v)
stable∈ vz     = refl
stable∈ (vs v) =
    ∈ᴺ-nat v wk uᶜᴺ
  ◾ Tyᴺₑ wk & stable∈ v
  ◾ uᴺ-nat wk (var v)
  ◾ (λ x → uᴺ (var (vs x))) & ∈-idₑ v

mutual
  stable : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝Nf ≡ n
  stable (ne n)  = stableNe n
  stable (lam n) = lam & stable n

  stableNe : ∀ {Γ A}(n : Ne Γ A) → Tmᴺ ⌜ n ⌝Ne uᶜᴺ ≡ uᴺ n
  stableNe (var v)   = stable∈ v
  stableNe (app f a) =
      (λ x → x idₑ (Tmᴺ ⌜ a ⌝Nf uᶜᴺ)) & stableNe f
    ◾ (λ x → uᴺ (app (Neₑ idₑ f) x)) & stable a
    ◾ (λ x → uᴺ (app x a)) & Ne-idₑ f

