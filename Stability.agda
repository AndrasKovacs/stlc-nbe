{-# OPTIONS --without-K #-}

module Stability where

open import Lib
open import Syntax
open import Embedding
open import Nf
open import Presheaf
open import Normalization

stab∈ : ∀ {A Γ}(v : A ∈ Γ) → ∈ᴺ v uConᴺ ≡ uᴺ (var v)
stab∈ vz     = refl
stab∈ {A}{Γ} (vs {B} v) =
    ∈ᴺ-nat v (wk {B}) uConᴺ
  ◾ Tyᴺₑ {A} (wk {B}) & stab∈ v
  ◾ uᴺ-nat {A} (wk {B}) (var v)
  ◾ (λ x → uᴺ {A} (var (vs x))) & ∈-idₑ {A} v

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne+ n)  = qᴺ & stabNe n
  stab (ne⊥ n)  = ne⊥ & stabNe n
  stab (lam n)  = lam & stab n
  stab tt       = refl
  stab (t , u)  = _,_ & stab t ⊗ stab u
  stab (inj₁ n) = inj₁ & stab n
  stab (inj₂ n) = inj₂ & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → Tmᴺ ⌜ n ⌝Ne uConᴺ ≡ uᴺ n
  stabNe (var v)   = stab∈ v
  stabNe (app f a) =
      (λ x → proj₁ x idₑ (Tmᴺ ⌜ a ⌝ uConᴺ)) & stabNe f
    ◾ (λ x → uᴺ (app (Neₑ idₑ f) x)) & stab a
    ◾ (λ x → uᴺ (app x a)) & Ne-idₑ f
  stabNe (π₁ n) = proj₁ & stabNe n
  stabNe (π₂ n) = proj₂ & stabNe n
  stabNe (case l r n) rewrite stabNe n | stab l | stab r = refl
  stabNe (⊥-rec {A} n) = (uᴺ {A} ∘ ⊥-rec) & stabNe n
