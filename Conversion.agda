{-#  OPTIONS --without-K #-}

module Conversion where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import NormalForm

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))     →  t ~ lam (app (Tmₑ wk t) (var vz))
  β     : ∀ {A B}(t : Tm (Γ , A) B) t'  →  app (lam t) t' ~ Tmₛ (idₛ , t') t

  lam   : ∀ {A B}{t t' : Tm (Γ , A) B}      → t ~ t' →  lam t   ~ lam t'
  app₁  : ∀ {A B}{f f' : Tm Γ (A ⇒ B)}{x}   → f ~ f' →  app f x ~ app f' x
  app₂  : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x x'}  → x ~ x' →  app f x ~ app f x'
  ~refl : ∀ {A}{t : Tm Γ A}                 → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A}              → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A}          → t ~ t' → t' ~ t'' → t ~ t''

infix 3 _~_
infixl 4 _~◾_
infix 6 _~⁻¹

~ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~ t' → Tmₑ σ t ~ Tmₑ σ t'
~ₑ σ (η t) =
  coe ((λ t' → Tmₑ σ t ~ lam (app t' (var vz)))
    & (Tm-∘ₑ σ wk t ⁻¹
    ◾ (λ x → Tmₑ (drop x) t) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ Tm-∘ₑ wk  (keep σ) t))
  (η (Tmₑ σ t))
  
~ₑ σ (β t t') =
  coe ((app (lam (Tmₑ (keep σ) t)) (Tmₑ σ t') ~_) &
    (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₑ σ t') t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
    ◾ Tm-ₛ∘ₑ (idₛ , t') σ t))
  (β (Tmₑ (keep σ) t) (Tmₑ σ t'))

~ₑ σ (lam t~t')       = lam (~ₑ (keep σ) t~t')
~ₑ σ (app₁ t~t')      = app₁ (~ₑ σ t~t')
~ₑ σ (app₂ t~t')      = app₂ (~ₑ σ t~t')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''
