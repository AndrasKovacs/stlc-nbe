{-#  OPTIONS --without-K #-}

module Conversion where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Nf

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))     →  t ~ lam (app (t [ wk ]ₑ) (var vz))
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

~ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~ t' → t [ σ ]ₑ ~ t' [ σ ]ₑ
~ₑ σ (η t)    =
  coe ((λ t' → t [ σ ]ₑ ~ lam (app t' (var vz))) &
      (∘ₑTm t σ wk
    ◾ ((t [_]ₑ) ∘ drop) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ ∘ₑTm t wk (keep σ) ⁻¹))
  (η (t [ σ ]ₑ))

~ₑ σ (β t t') =
  coe ((app (lam (t [ keep σ ]ₑ)) (t' [ σ ]ₑ) ~_) &
      (ₑ∘ₛTm t (keep σ) (idₛ , (t' [ σ ]ₑ))
    ◾ (λ δ → t [ δ , (t' [ σ ]ₑ)]) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
    ◾ ₛ∘ₑTm t (idₛ , t') σ ⁻¹))
  (β (t [ keep σ ]ₑ) (t' [ σ ]ₑ))

~ₑ σ (lam t~t')       = lam (~ₑ (keep σ) t~t')
~ₑ σ (app₁ t~t')      = app₁ (~ₑ σ t~t')
~ₑ σ (app₂ t~t')      = app₂ (~ₑ σ t~t')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''
