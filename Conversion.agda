{-#  OPTIONS --without-K #-}

module Conversion where

open import Lib hiding (⊥; ⊤)
open import Syntax
open import Embedding
open import Substitution
open import Nf

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  ⇒η    : ∀ {A B}(t : Tm Γ (A ⇒ B))     →  t ~ lam (app (Tmₑ wk t) (var vz))
  ⇒β    : ∀ {A B}(t : Tm (Γ , A) B) t'  →  app (lam t) t' ~ Tmₛ (idₛ , t') t
  lam   : ∀ {A B}{t t' : Tm (Γ , A) B}       → t ~ t' →  lam t   ~ lam t'
  app   : ∀ {A B}{f f' : Tm Γ (A ⇒ B)}{a a'} → f ~ f' →  a ~ a' → app f a ~ app f' a'

  π₁β   : ∀ {A B}(t : Tm Γ A)(u : Tm Γ B) → π₁ (t , u) ~ t
  π₂β   : ∀ {A B}(t : Tm Γ A)(u : Tm Γ B) → π₂ (t , u) ~ u
  π₁    : ∀ {A B}{t t' : Tm Γ (A * B)} → t ~ t' → π₁ t ~ π₁ t'
  π₂    : ∀ {A B}{t t' : Tm Γ (A * B)} → t ~ t' → π₂ t ~ π₂ t'
  πη    : ∀ {A B}(t : Tm Γ (A * B)) → (π₁ t , π₂ t) ~ t
  _,_   : ∀ {A B}{t t' : Tm Γ A}{u u' : Tm Γ B} → t ~ t' → u ~ u' → (t , u) ~ (t' , u')

  inj₁   : ∀ {A B}{t t' : Tm Γ A} → t ~ t' → inj₁ {B = B} t ~ inj₁ t'
  inj₂   : ∀ {A B}{t t' : Tm Γ B} → t ~ t' → inj₂ {A = A} t ~ inj₂ t'
  case₁β :
    ∀ {A B C}(l : Tm Γ (A ⇒ C))(r : Tm Γ (B ⇒ C))(t : Tm Γ A)
    → case l r (inj₁ t) ~ app l t
  case₂β :
    ∀ {A B C}(l : Tm Γ (A ⇒ C))(r : Tm Γ (B ⇒ C))(t : Tm Γ B)
    → case l r (inj₂ t) ~ app r t
  case :
    ∀ {A B C}{l l' : Tm Γ (A ⇒ C)}{r r' : Tm Γ (B ⇒ C)}{t t' : Tm Γ (A + B)}
    → l ~ l' → r ~ r' → t ~ t'
    → case l r t ~ case l' r' t'

  ⊥-rec : ∀ {A}{t t' : Tm Γ ⊥} → t ~ t' → ⊥-rec {A = A} t ~ ⊥-rec t'

  ⊤η : (t : Tm Γ ⊤) → t ~ tt

  ~refl : ∀ {A}{t : Tm Γ A}        → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A}     → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A} → t ~ t' → t' ~ t'' → t ~ t''

  con   : ∀ {F}{t t' : Tm Γ (apF F (μ F))} → t ~ t' → con {_}{F} t ~ con t'
  rec   : ∀ {F A}{t t' : Tm Γ (apF F A ⇒ A)}{u u' : Tm Γ (μ F)}
          → t ~ t' → u ~ u' → rec t u ~ rec t' u'
  recβ  : ∀ {F A}(t : Tm Γ (apF F A ⇒ A))(u : Tm Γ (apF F (μ F)))
          → rec t (con {_}{F} u) ~ {!!}

infix 3 _~_
infixl 4 _~◾_
infix 6 _~⁻¹

~ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~ t' → Tmₑ σ t ~ Tmₑ σ t'
~ₑ σ (⇒η t) =
  coe ((λ t' → Tmₑ σ t ~ lam (app t' (var vz)))
    & (Tm-∘ₑ σ wk t ⁻¹
    ◾ (λ x → Tmₑ (drop x) t) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ Tm-∘ₑ wk  (keep σ) t))
  (⇒η (Tmₑ σ t))

~ₑ σ (⇒β t t') =
  coe ((app (lam (Tmₑ (keep σ) t)) (Tmₑ σ t') ~_) &
    (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₑ σ t') t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
    ◾ Tm-ₛ∘ₑ (idₛ , t') σ t))
  (⇒β (Tmₑ (keep σ) t) (Tmₑ σ t'))

~ₑ σ (lam t~t')       = lam (~ₑ (keep σ) t~t')
~ₑ σ (app t~t' a~a')  = app (~ₑ σ t~t') (~ₑ σ a~a')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''

~ₑ σ (π₁β t u) = π₁β (Tmₑ σ t) (Tmₑ σ u)
~ₑ σ (π₂β t u) = π₂β (Tmₑ σ t) (Tmₑ σ u)
~ₑ σ (π₁ t) = π₁ (~ₑ σ t)
~ₑ σ (π₂ t) = π₂ (~ₑ σ t)
~ₑ σ (inj₁ t) = inj₁ (~ₑ σ t)
~ₑ σ (inj₂ t) = inj₂ (~ₑ σ t)
~ₑ σ (case₁β l r t) = case₁β (Tmₑ σ l) (Tmₑ σ r) (Tmₑ σ t)
~ₑ σ (case₂β l r t) = case₂β (Tmₑ σ l) (Tmₑ σ r) (Tmₑ σ t)
~ₑ σ (πη t) = πη (Tmₑ σ t)
~ₑ σ (case l r t) = case (~ₑ σ l) (~ₑ σ r) (~ₑ σ t)
~ₑ σ (⊥-rec t) = ⊥-rec (~ₑ σ t)
~ₑ σ (⊤η t)    = ⊤η (Tmₑ σ t)
~ₑ σ (t , u)   = ~ₑ σ t , ~ₑ σ u
~ₑ σ (con t)    = con (~ₑ σ t)
~ₑ σ (rec t u)  = rec (~ₑ σ t) (~ₑ σ u)
~ₑ σ (recβ t u) = {!!}
