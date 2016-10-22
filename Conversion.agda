{-#  OPTIONS --without-K #-}

module Conversion where

open import Lib
open import Syntax
open import Renaming
open import Substitution
open import Nf

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))     →  t ~ lam (app (t [ wk ]ᵣ) (var vz))
  β     : ∀ {A B}(t : Tm (Γ , A) B) t'  →  app (lam t) t' ~ t [ idₛ , t' ]

  lam   : ∀ {A B}{t t' : Tm (Γ , A) B}      → t ~ t' →  lam t   ~ lam t'
  app₁  : ∀ {A B}{f f' : Tm Γ (A ⇒ B)}{x}   → f ~ f' →  app f x ~ app f' x
  app₂  : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x x'}  → x ~ x' →  app f x ~ app f x'
  ~refl : ∀ {A}{t : Tm Γ A}                 → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A}              → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A}          → t ~ t' → t' ~ t'' → t ~ t''

infix 3 _~_
infixl 4 _~◾_
infix 6 _~⁻¹

~ᵣ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : Ren Δ Γ) → t ~ t' → t [ σ ]ᵣ ~ t' [ σ ]ᵣ
~ᵣ σ (η t)    =
  coe ((λ t' → t [ σ ]ᵣ ~ lam (app t' (var vz))) &
      (∘ᵣTm t σ wk
    ◾ ((t [_]ᵣ) ∘ drop) & (idrᵣ σ ◾ idlᵣ σ ⁻¹)
    ◾ ∘ᵣTm t wk (keep σ) ⁻¹))
  (η (t [ σ ]ᵣ))

~ᵣ σ (β t t') =
  coe ((app (lam (t [ keep σ ]ᵣ)) (t' [ σ ]ᵣ) ~_) &
      (ᵣ∘ₛTm t (keep σ) (idₛ , (t' [ σ ]ᵣ))
    ◾ (λ δ → t [ δ , (t' [ σ ]ᵣ)]) & (idrᵣₛ σ ◾ idlₛᵣ σ ⁻¹)
    ◾ ₛ∘ᵣTm t (idₛ , t') σ ⁻¹))
  (β (t [ keep σ ]ᵣ) (t' [ σ ]ᵣ))

~ᵣ σ (lam t~t')       = lam (~ᵣ (keep σ) t~t')
~ᵣ σ (app₁ t~t')      = app₁ (~ᵣ σ t~t')
~ᵣ σ (app₂ t~t')      = app₂ (~ᵣ σ t~t')
~ᵣ σ ~refl            = ~refl
~ᵣ σ (t~t' ~⁻¹)       = ~ᵣ σ t~t' ~⁻¹
~ᵣ σ (t~t' ~◾ t'~t'') = ~ᵣ σ t~t' ~◾ ~ᵣ σ t'~t''
