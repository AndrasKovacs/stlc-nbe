{-# OPTIONS --without-K #-}

module Completeness where

open import Lib
open import Syntax
open import Nf
open import Normalization
open import Renaming
open import Substitution
open import Conversion

_≈_ : ∀ {Γ A} → Tm Γ A → Tmᴺ Γ A → Set
_≈_ {Γ}{ι}     t tᴺ = t ~ ⌜ qᴺ tᴺ ⌝
_≈_ {Γ}{A ⇒ B} t tᴺ =
  ∀ {Δ}(σ : Ren Δ Γ){a aᴺ} → a ≈ aᴺ → app (t [ σ ]ᵣ) a ≈ appᴺ (tᴺ ᴺ[ σ ]ᵣ) aᴺ

infix 3 _≈_ _≈ₛ_

data _≈ₛ_ {Γ} : ∀ {Δ} → Tms Γ Δ → Tmsᴺ Γ Δ → Set where
  ∙   : _≈ₛ_ ∙ ∙
  _,_ : ∀ {A Δ σ δ}{t : Tm Γ A}{t' : Tmᴺ Γ A} → _≈ₛ_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈ₛ (δ , t')

≈ᵣ : ∀ {Γ Δ A}(σ : Ren Δ Γ){t}{t' : Tmᴺ Γ A} → t ≈ t' → t [ σ ]ᵣ ≈ t' ᴺ[ σ ]ᵣ
≈ᵣ {A = ι}     σ {t}{t'} t≈t' = coe ((_ ~_) & (⌜⌝ᵣ t' σ ⁻¹)) (~ᵣ σ t≈t')
≈ᵣ {A = A ⇒ B} σ {t}{t'} t≈t' = λ δ {a}{aᴺ} a≈aᴺ
  → coe ((λ x y → (app x a ≈ proj₁ t' y aᴺ)) & (∘ᵣTm t σ δ ⁻¹) ⊗ assᵣ σ δ idᵣ)
        (t≈t' (σ ∘ᵣ δ) a≈aᴺ)

≈ₛᵣ : ∀ {Γ Δ Σ}(σ : Ren Σ Γ){δ}{ν : Tmsᴺ Γ Δ} → δ ≈ₛ ν → (δ ₛ∘ᵣ σ) ≈ₛ (ν ᴺ∘ᵣ σ)
≈ₛᵣ σ ∙          = ∙
≈ₛᵣ σ (p , t≈t') = (≈ₛᵣ σ p) , ≈ᵣ σ t≈t'

_~≈◾_ : ∀ {Γ A}{t t'}{tᴺ : Tmᴺ Γ A} → t ~ t' → t' ≈ tᴺ → t ≈ tᴺ
_~≈◾_ {A = ι}     p q = p ~◾ q
_~≈◾_ {A = A ⇒ B} p q = λ σ a≈aᴺ → app₁ (~ᵣ σ p) ~≈◾ q σ a≈aᴺ

⟦∈⟧ : ∀ {Γ Δ A}(v : A ∈ Γ){σ}{δ : Tmsᴺ Δ Γ} → σ ≈ₛ δ → v [ σ ]∈ ≈ ∈↑ᴺ v δ
⟦∈⟧ vz     (σ≈δ , t≈t') = t≈t'
⟦∈⟧ (vs v) (σ≈δ , _   ) = ⟦∈⟧ v σ≈δ

⟦Tm⟧ : ∀ {Γ Δ A}(t : Tm Γ A){σ}{δ : Tmsᴺ Δ Γ} → σ ≈ₛ δ → t [ σ ] ≈ Tm↑ᴺ t δ
⟦Tm⟧ (var v)   σ≈δ = ⟦∈⟧ v σ≈δ

⟦Tm⟧ (lam t) {σ} {δ} σ≈δ ν {a} {aᴺ} a≈aᴺ
  rewrite idrᵣ ν
  = coe ((app (lam (t [ keepₛ σ ] [ keep ν ]ᵣ)) a ~_) & βᵣ σ ν t a)
        (β (t [ (σ ₛ∘ᵣ drop idᵣ) , var vz ] [ keep ν ]ᵣ) a)
  ~≈◾ ⟦Tm⟧ t (≈ₛᵣ ν σ≈δ , a≈aᴺ)

⟦Tm⟧ (app f a) {σ} {δ} σ≈δ =
  coe ((λ x y → app x (a [ σ ]) ≈ proj₁ (Tm↑ᴺ f δ) y (Tm↑ᴺ a δ))
    & idᵣTm (f [ σ ]) ⊗ idrᵣ idᵣ)
  (⟦Tm⟧ f σ≈δ idᵣ (⟦Tm⟧ a σ≈δ))

mutual
  qᶜ : ∀ {Γ A}{t}{tᴺ : Tmᴺ Γ A} → t ≈ tᴺ → t ~ ⌜ qᴺ tᴺ ⌝
  qᶜ {Γ}{ι}     t≈tᴺ = t≈tᴺ
  qᶜ {Γ}{A ⇒ B} t≈tᴺ rewrite (idrᵣ (idᵣ{Γ}) ⁻¹) =
    η _ ~◾ lam (qᶜ (t≈tᴺ wk (uᶜ (var vz))))

  uᶜ : ∀ {Γ A}(n : Ne Γ A) → ⌜ n ⌝Ne ≈ uᴺ n
  uᶜ {A = ι}     n = ~refl
  uᶜ {A = A ⇒ B} n σ {a} {aᴺ} a≈aᴺ rewrite idrᵣ σ | ⌜⌝Neᵣ n σ ⁻¹
    = app₂ (qᶜ a≈aᴺ) ~≈◾ uᶜ (app (n [ σ ]ₙₑᵣ) (qᴺ aᴺ))

id≈ₛ : ∀ {Γ} → idₛ {Γ} ≈ₛ idᴺₛ
id≈ₛ {∙}     = ∙
id≈ₛ {Γ , A} = ≈ₛᵣ wk id≈ₛ , uᶜ (var vz)

complete : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝
complete t = coe ((_~ ⌜ qᴺ (Tm↑ᴺ t idᴺₛ) ⌝) & idₛTm t) (qᶜ (⟦Tm⟧ t id≈ₛ))

