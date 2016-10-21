{-# OPTIONS --without-K #-}

module Soundness where

open import Lib
open import Syntax
open import Renaming
open import Substitution
open import Conversion
open import Nf
open import Normalization

infix 3 _≈_ _≈ₛ_

_≈_ : ∀ {Γ A} → Tmᴺ Γ A → Tmᴺ Γ A → Set
_≈_ {Γ}{ι}     t t' = t ≡ t'
_≈_ {Γ}{A ⇒ B} t t' =
  ∀ {Δ}(σ : Ren Δ Γ){a a'} → a ≈ a' → appᴺ (t ᴺ[ σ ]ᵣ) a ≈ appᴺ (t' ᴺ[ σ ]ᵣ) a'

data _≈ₛ_ {Γ} : ∀ {Δ} → Tmsᴺ Γ Δ → Tmsᴺ Γ Δ → Set where
  ∙   : _≈ₛ_ ∙ ∙
  _,_ : ∀ {A Δ σ δ}{t t' : Tmᴺ Γ A} → _≈ₛ_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈ₛ (δ , t')

_≈⁻¹ : ∀ {Γ A}{t t' : Tmᴺ Γ A} → t ≈ t' → t' ≈ t
_≈⁻¹ {A = ι}     t≈t' = t≈t' ⁻¹
_≈⁻¹ {A = A ⇒ B} t≈t' = λ σ a≈a' → t≈t' σ (a≈a' ≈⁻¹) ≈⁻¹

_≈ₛ⁻¹ : ∀ {Γ Δ}{σ δ : Tmsᴺ Γ Δ} → σ ≈ₛ δ → δ ≈ₛ σ
∙            ≈ₛ⁻¹ = ∙
(σ≈δ , t≈t') ≈ₛ⁻¹ = (σ≈δ ≈ₛ⁻¹) , (t≈t' ≈⁻¹)

_≈◾_ : ∀ {Γ A}{t t' t'' : Tmᴺ Γ A} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {A = ι}     p q = p ◾ q
_≈◾_ {A = A ⇒ B} p q = λ σ a≈a' → p σ (a≈a' ≈◾ (a≈a' ≈⁻¹)) ≈◾ q σ a≈a'

_≈ₛ◾_ : ∀ {Γ Δ}{σ δ ν : Tmsᴺ Γ Δ} → σ ≈ₛ δ → δ ≈ₛ ν → σ ≈ₛ ν
∙          ≈ₛ◾ q            = q
(p , t≈t') ≈ₛ◾ (q , t'≈t'') = (p ≈ₛ◾ q) , (t≈t' ≈◾ t'≈t'')

≈ᵣ : ∀ {Γ Δ A}(σ : Ren Δ Γ){t t' : Tmᴺ Γ A} → t ≈ t' → t ᴺ[ σ ]ᵣ ≈ t' ᴺ[ σ ]ᵣ
≈ᵣ {A = ι}     σ t≈t' = (_[ σ ]ₙᵣ) & t≈t'
≈ᵣ {A = A ⇒ B} σ t≈t' δ rewrite idrᵣ δ | idrᵣ (σ ∘ᵣ δ) ⁻¹ = t≈t' (σ ∘ᵣ δ)

≈ₛᵣ : ∀ {Γ Δ Σ}(σ : Ren Σ Γ){δ ν : Tmsᴺ Γ Δ} → δ ≈ₛ ν → (δ ᴺ∘ᵣ σ) ≈ₛ (ν ᴺ∘ᵣ σ)
≈ₛᵣ σ ∙          = ∙
≈ₛᵣ σ (p , t≈t') = (≈ₛᵣ σ p) , ≈ᵣ σ t≈t'

⟦∈⟧ : ∀ {Γ Δ A}(v : A ∈ Γ){σ δ : Tmsᴺ Δ Γ} → σ ≈ₛ δ → ∈↑ᴺ v σ ≈ ∈↑ᴺ v δ
⟦∈⟧ vz     (σ≈δ , t≈t') = t≈t'
⟦∈⟧ (vs v) (σ≈δ , _   ) = ⟦∈⟧ v σ≈δ

⟦Tm⟧ : ∀ {Γ Δ A}(t : Tm Γ A){σ δ : Tmsᴺ Δ Γ} → σ ≈ₛ δ → Tm↑ᴺ t σ ≈ Tm↑ᴺ t δ
⟦Tm⟧ (var v)   σ≈δ = ⟦∈⟧ v σ≈δ
⟦Tm⟧ (lam t)   σ≈δ ν a≈a'
  rewrite idrᵣ ν = ⟦Tm⟧ t (≈ₛᵣ ν σ≈δ , a≈a')
⟦Tm⟧ {Δ = Δ} (app f a) σ≈δ
  rewrite idrᵣ (idᵣ {Δ}) ⁻¹ = ⟦Tm⟧ f σ≈δ idᵣ (⟦Tm⟧ a σ≈δ)

⟦~⟧ : ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → ∀ {σ δ : Tmsᴺ Δ Γ} → σ ≈ₛ δ → Tm↑ᴺ t σ ≈ Tm↑ᴺ t' δ
⟦~⟧ (η t) {σ} {δ} σ≈δ {Σ} ν {a} {a'} a≈a'
    rewrite Tm↑ᴺ-nat₁ t wk (δ ᴺ∘ᵣ ν ∘ᵣ idᵣ , a')
  | idlᴺᵣ (δ ᴺ∘ᵣ ν ∘ᵣ idᵣ)
  | proj₁ & Tm↑ᴺ-nat t δ (ν ∘ᵣ idᵣ)
  | idrᵣ (ν ∘ᵣ idᵣ)
  = ⟦Tm⟧ t σ≈δ ν a≈a'

⟦~⟧ (β t t') {σ} {δ} σ≈δ
  rewrite ₛ∘ᴺ↑ t (idₛ , t') δ
  = ⟦Tm⟧ t (coe (_≈ₛ_ & (idrᴺᵣ σ ⁻¹) ⊗ idlᴺₛ δ) σ≈δ , ⟦Tm⟧ t' σ≈δ)

⟦~⟧ (lam {t = t} {t'} t~t') {σ} {δ} σ≈δ ν {a} {a'} a≈a'
  rewrite idrᵣ ν = ⟦~⟧ t~t' (≈ₛᵣ ν σ≈δ , a≈a')

⟦~⟧ {Δ = Δ} (app₁ {f = f} {f'} {x} t~t') σ≈δ
  rewrite idrᵣ (idᵣ {Δ}) ⁻¹ = ⟦~⟧ t~t' σ≈δ idᵣ (⟦Tm⟧ x σ≈δ)

⟦~⟧ {Δ = Δ} (app₂ {f = f} t~t') σ≈δ
  rewrite idrᵣ (idᵣ {Δ}) ⁻¹ = ⟦Tm⟧ f σ≈δ idᵣ (⟦~⟧ t~t' σ≈δ)

⟦~⟧ {t = t} ~refl σ≈δ = ⟦Tm⟧ t σ≈δ
⟦~⟧ (t'~t ~⁻¹) σ≈δ = ⟦~⟧ t'~t (σ≈δ ≈ₛ⁻¹) ≈⁻¹
⟦~⟧ (t~t' ~◾ t'~t'') σ≈δ = ⟦~⟧ t~t' (σ≈δ ≈ₛ◾ (σ≈δ ≈ₛ⁻¹)) ≈◾ ⟦~⟧ t'~t'' σ≈δ

mutual
  q≈ : ∀ {Γ A}{t t' : Tmᴺ Γ A} → t ≈ t' → qᴺ t ≡ qᴺ t'
  q≈ {Γ} {ι}     t≈t' = t≈t'
  q≈ {Γ} {A ⇒ B} t≈t' rewrite idrᵣ (idᵣ {Γ}) ⁻¹ =
    lam & q≈ (t≈t' (wk {A}) (u≈ {n = var vz} refl))

  u≈ : ∀ {Γ A}{n n' : Ne Γ A} → n ≡ n' → uᴺ n ≈ uᴺ n'
  u≈ {A = ι}     p = ne & p
  u≈ {A = A ⇒ B} p = λ σ a≈a' → u≈ (app & ((_[ σ ∘ᵣ idᵣ ]ₙₑᵣ) & p) ⊗ q≈ a≈a')

idₛTmsᴺ : ∀ {Γ} → idᴺₛ {Γ} ≈ₛ idᴺₛ
idₛTmsᴺ {∙}     = ∙
idₛTmsᴺ {Γ , A} = ≈ₛᵣ wk idₛTmsᴺ , u≈ refl

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = q≈ (⟦~⟧ t~t' idₛTmsᴺ)

