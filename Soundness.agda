{-# OPTIONS --without-K #-}

module Soundness where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Nf
open import Presheaf
open import Normalization

infix 3 _≈_ _≈*_

_≈_ : ∀ {A Γ} → Tyᴺ A Γ → Tyᴺ A Γ → Set
_≈_ {ι}    {Γ} t t' = t ≡ t'
_≈_ {A ⇒ B}{Γ} t t' = ∀ {Δ}(σ : OPE Δ Γ){a a'} → a ≈ a' → proj₁ t σ a ≈ proj₁ t' σ a'

data _≈*_ : ∀ {Γ Δ} → Conᴺ Γ Δ → Conᴺ Γ Δ → Set where
  ∙   : ∀ {Γ} → _≈*_ {∙}{Γ} ∙ ∙
  _,_ : ∀ {A Γ Δ σ δ}{t t' : Tyᴺ A Δ} → _≈*_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈* (δ , t')

_≈⁻¹ : ∀ {Γ A}{t t' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t
_≈⁻¹ {A = ι}     t≈t' = t≈t' ⁻¹
_≈⁻¹ {A = A ⇒ B} t≈t' = λ σ a≈a' → t≈t' σ (a≈a' ≈⁻¹) ≈⁻¹

_≈*⁻¹ : ∀ {Γ Δ}{σ δ : Conᴺ Γ Δ} → σ ≈* δ → δ ≈* σ
∙            ≈*⁻¹ = ∙
(σ≈δ , t≈t') ≈*⁻¹ = (σ≈δ ≈*⁻¹) , (t≈t' ≈⁻¹)

_≈◾_ : ∀ {Γ A}{t t' t'' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {A = ι}     p q = p ◾ q
_≈◾_ {A = A ⇒ B} p q = λ σ a≈a' → p σ (a≈a' ≈◾ (a≈a' ≈⁻¹)) ≈◾ q σ a≈a'

_≈*◾_ : ∀ {Γ Δ}{σ δ ν : Conᴺ Γ Δ} → σ ≈* δ → δ ≈* ν → σ ≈* ν
∙          ≈*◾ q            = q
(p , t≈t') ≈*◾ (q , t'≈t'') = (p ≈*◾ q) , (t≈t' ≈◾ t'≈t'')

≈ₑ : ∀ {Γ Δ A}(σ : OPE Δ Γ){t t' : Tyᴺ A Γ} → t ≈ t' → Tyᴺₑ σ t ≈ Tyᴺₑ σ t'
≈ₑ {A = ι}     σ t≈t' = Nfₑ σ & t≈t'
≈ₑ {A = A ⇒ B} σ t≈t' = λ δ → t≈t' (σ ∘ₑ δ)

≈*ₑ : ∀ {Γ Δ Σ}(σ : OPE Σ Γ){δ ν : Conᴺ Δ Γ} → δ ≈* ν → Conᴺₑ σ δ ≈* Conᴺₑ σ ν
≈*ₑ σ ∙          = ∙
≈*ₑ σ (p , t≈t') = ≈*ₑ σ p , ≈ₑ σ t≈t'

⟦∈⟧ : ∀ {Γ Δ A}(v : A ∈ Γ){σ δ : Conᴺ Γ Δ} → σ ≈* δ → ∈ᴺ v σ ≈ ∈ᴺ v δ
⟦∈⟧ vz     (σ≈δ , t≈t') = t≈t'
⟦∈⟧ (vs v) (σ≈δ , _   ) = ⟦∈⟧ v σ≈δ

⟦Tm⟧ : ∀ {Γ Δ A}(t : Tm Γ A){σ δ : Conᴺ Γ Δ} → σ ≈* δ → Tmᴺ t σ ≈ Tmᴺ t δ
⟦Tm⟧ (var v)   σ≈δ = ⟦∈⟧ v σ≈δ
⟦Tm⟧ (lam t)   σ≈δ = λ ν a≈a' → ⟦Tm⟧ t (≈*ₑ ν σ≈δ , a≈a')
⟦Tm⟧ (app f a) σ≈δ = ⟦Tm⟧ f σ≈δ idₑ (⟦Tm⟧ a σ≈δ)

⟦~⟧ : ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → ∀ {σ δ : Conᴺ Γ Δ} → σ ≈* δ → Tmᴺ t σ ≈ Tmᴺ t' δ
⟦~⟧ (η t) {σ} {δ} σ≈δ ν {a} {a'} a≈a'
  rewrite
    Tmₑᴺ wk t (Conᴺₑ ν δ , a')
  | OPEᴺ-idₑ (Conᴺₑ ν δ)
  | Tmᴺ-nat t ν δ
  | idrₑ ν
  = ⟦Tm⟧ t σ≈δ ν a≈a'

⟦~⟧ (β t t') {σ} {δ} σ≈δ
  rewrite Tmₛᴺ (idₛ , t') t δ
  = ⟦Tm⟧ t (coe (_≈*_ & (Conᴺ-idₑ σ ⁻¹) ⊗ (Subᴺ-idₛ δ ⁻¹)) σ≈δ , ⟦Tm⟧ t' σ≈δ)

⟦~⟧ (lam t~t')          σ≈δ = λ ν a≈a' → ⟦~⟧ t~t' (≈*ₑ ν σ≈δ , a≈a')
⟦~⟧ (app₁ {x = x} t~t') σ≈δ = ⟦~⟧ t~t' σ≈δ idₑ (⟦Tm⟧ x σ≈δ)
⟦~⟧ (app₂ {f = f} t~t') σ≈δ = ⟦Tm⟧ f σ≈δ idₑ (⟦~⟧ t~t' σ≈δ)
⟦~⟧ {t = t} ~refl       σ≈δ = ⟦Tm⟧ t σ≈δ
⟦~⟧ (t'~t ~⁻¹)          σ≈δ = ⟦~⟧ t'~t (σ≈δ ≈*⁻¹) ≈⁻¹
⟦~⟧ (t~t' ~◾ t'~t'')    σ≈δ = ⟦~⟧ t~t' (σ≈δ ≈*◾ (σ≈δ ≈*⁻¹)) ≈◾ ⟦~⟧ t'~t'' σ≈δ

mutual
  q≈ : ∀ {Γ A}{t t' : Tyᴺ A Γ} → t ≈ t' → qᴺ t ≡ qᴺ t'
  q≈ {A = ι}     t≈t' = t≈t'
  q≈ {A = A ⇒ B} t≈t' = lam & q≈ (t≈t' (wk {A}) (u≈ {n = var vz} refl))

  u≈ : ∀ {Γ A}{n n' : Ne Γ A} → n ≡ n' → uᴺ n ≈ uᴺ n'
  u≈ {A = ι}     p = ne & p
  u≈ {A = A ⇒ B} p = λ σ a≈a' → u≈ (app & (Neₑ σ & p) ⊗ q≈ a≈a')

u≈* : ∀ {Γ} → uConᴺ {Γ} ≈* uConᴺ
u≈* {∙}     = ∙
u≈* {Γ , A} = ≈*ₑ wk u≈* , u≈ refl

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = q≈ (⟦~⟧ t~t' u≈*)

