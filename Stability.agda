{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Renaming
open import Substitution
open import Nf
open import Normalization

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne n)  = {!!}
  stab (lam n) = lam & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → nf ⌜ n ⌝Ne ≡ {!!}
  stabNe n = {!!}

