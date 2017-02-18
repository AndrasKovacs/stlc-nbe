{-# OPTIONS --without-K #-}

module Soundness where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import Nf
open import Normalization

infix 3 _≈_ _≈*_

_≈_ : ∀ {A Γ} → Tyᴺ A Γ → Tyᴺ A Γ → Set
_≈_ {ι}    {Γ} t t' = t ≡ t'
_≈_ {A ⇒ B}{Γ} t t' = ∀ {Δ}(σ : OPE Δ Γ){a a'} → Tyᴾ a → Tyᴾ a' → a ≈ a' → t σ a ≈ t' σ a'

data _≈*_ : ∀ {Γ Δ} → Conᴺ Γ Δ → Conᴺ Γ Δ → Set where
  ∙   : ∀ {Γ} → _≈*_ {∙}{Γ} ∙ ∙
  _,_ : ∀ {A Γ Δ σ δ}{t t' : Tyᴺ A Δ} → _≈*_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈* (δ , t')

_≈⁻¹ : ∀ {Γ A}{t t' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t
_≈⁻¹ {A = ι}     t≈t' = t≈t' ⁻¹
_≈⁻¹ {A = A ⇒ B} t≈t' = λ σ aᴾ a'ᴾ a≈a' → t≈t' σ a'ᴾ aᴾ (a≈a' ≈⁻¹) ≈⁻¹

_≈*⁻¹ : ∀ {Γ Δ}{σ δ : Conᴺ Γ Δ} → σ ≈* δ → δ ≈* σ
∙            ≈*⁻¹ = ∙
(σ≈δ , t≈t') ≈*⁻¹ = (σ≈δ ≈*⁻¹) , (t≈t' ≈⁻¹)

_≈◾_ : ∀ {Γ A}{t t' t'' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {A = ι}     p q = p ◾ q
_≈◾_ {A = A ⇒ B} p q = λ σ aᴾ a'ᴾ a≈a' → p σ aᴾ aᴾ (a≈a' ≈◾ (a≈a' ≈⁻¹)) ≈◾ q σ aᴾ a'ᴾ a≈a'

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

⟦Tm⟧ : ∀ {Γ Δ A}(t : Tm Γ A){Γᴺ Γᴺ' : Conᴺ Γ Δ} → Conᴾ Γᴺ → Conᴾ Γᴺ' →  Γᴺ ≈* Γᴺ' → Tmᴺ t Γᴺ ≈ Tmᴺ t Γᴺ'
⟦Tm⟧ (var v)   Γᴾ Γᴾ' σ≈δ = ⟦∈⟧ v σ≈δ
⟦Tm⟧ (lam t)   Γᴾ Γᴾ' σ≈δ = λ ν aᴾ aᴾ' a≈a' → ⟦Tm⟧ t (Conᴾₑ ν Γᴾ , aᴾ) (Conᴾₑ ν Γᴾ' , aᴾ') (≈*ₑ ν σ≈δ , a≈a')
⟦Tm⟧ (app f a) Γᴾ Γᴾ' σ≈δ = ⟦Tm⟧ f Γᴾ Γᴾ' σ≈δ idₑ (Tmᴾ a Γᴾ) (Tmᴾ a Γᴾ') (⟦Tm⟧ a Γᴾ Γᴾ' σ≈δ)

∈ₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(v : A ∈ Γ)(δᴺ : Conᴺ Δ Σ)
 → Tmᴺ (∈ₛ σ v) δᴺ ≈ ∈ᴺ v (Subᴺ σ δᴺ)
∈ₛᴺ (σ , t) vz     δᴺ = {!!}
∈ₛᴺ (σ , _) (vs v) δᴺ = ∈ₛᴺ σ v δᴺ

Tmₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ) → Conᴾ δᴺ
 → Tmᴺ (Tmₛ σ t) δᴺ ≈ Tmᴺ t (Subᴺ σ δᴺ)
Tmₛᴺ σ (var v)   δᴺ δᴾ = {!!}
Tmₛᴺ σ (lam t)   δᴺ δᴾ = {!!}
Tmₛᴺ σ (app f x) δᴺ δᴾ = {!!} 

⟦~⟧ :
  ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → ∀ {Γᴺ Γᴺ' : Conᴺ Γ Δ}
  → Conᴾ Γᴺ → Conᴾ Γᴺ' → Γᴺ ≈* Γᴺ' → Tmᴺ t Γᴺ ≈ Tmᴺ t' Γᴺ'
⟦~⟧ (η t) {Γᴺ} {Γᴺ'} Γᴾ Γᴾ' σ≈δ ν {a} {a'} a≈a'
  rewrite
    Tmₑᴺ wk t (Conᴺₑ ν Γᴺ' , a')
  | OPEᴺ-idₑ (Conᴺₑ ν Γᴺ')
  | Tmᴺ-nat t ν {Γᴺ'} Γᴾ'
  | idrₑ ν
  = ⟦Tm⟧ t Γᴾ Γᴾ' σ≈δ ν a≈a'

⟦~⟧ (β t t') {σ} {δ} Γᴾ Γᴾ' σ≈δ = {!!}
  -- rewrite Tmₛᴺ (idₛ , t') t δ
  -- = ⟦Tm⟧ t (coe (_≈*_ & (Conᴺ-idₑ σ ⁻¹) ⊗ (Subᴺ-idₛ δ ⁻¹)) σ≈δ , ⟦Tm⟧ t' σ≈δ)

⟦~⟧ (lam t~t')                  Γᴾ Γᴾ' σ≈δ = λ ν aᴾ aᴾ' a≈a' → ⟦~⟧ t~t' (Conᴾₑ ν Γᴾ , aᴾ) (Conᴾₑ ν Γᴾ' , aᴾ') (≈*ₑ ν σ≈δ , a≈a')
⟦~⟧ (app₁ {x = x} t~t')         Γᴾ Γᴾ' σ≈δ = ⟦~⟧ t~t' Γᴾ Γᴾ' σ≈δ idₑ (Tmᴾ x Γᴾ) (Tmᴾ x Γᴾ') (⟦Tm⟧ x Γᴾ Γᴾ' σ≈δ)
⟦~⟧ (app₂ {f = f}{x} {x'} t~t') Γᴾ Γᴾ' σ≈δ = ⟦Tm⟧ f Γᴾ Γᴾ' σ≈δ idₑ (Tmᴾ x Γᴾ) (Tmᴾ x' Γᴾ') (⟦~⟧ t~t' Γᴾ Γᴾ' σ≈δ)
⟦~⟧ {t = t} ~refl               Γᴾ Γᴾ' σ≈δ = ⟦Tm⟧ t Γᴾ Γᴾ' σ≈δ
⟦~⟧ (t'~t ~⁻¹)                  Γᴾ Γᴾ' σ≈δ = ⟦~⟧ t'~t Γᴾ' Γᴾ (σ≈δ ≈*⁻¹) ≈⁻¹
⟦~⟧ (t~t' ~◾ t'~t'')            Γᴾ Γᴾ' σ≈δ = ⟦~⟧ t~t' Γᴾ Γᴾ (σ≈δ ≈*◾ (σ≈δ ≈*⁻¹)) ≈◾ ⟦~⟧ t'~t'' Γᴾ Γᴾ' σ≈δ

mutual
  q≈ : ∀ {Γ A}{t t' : Tyᴺ A Γ} → t ≈ t' → qᴺ t ≡ qᴺ t'
  q≈ {A = ι}     t≈t' = t≈t'
  q≈ {A = A ⇒ B} t≈t' = lam & q≈ (t≈t' (wk {A}) (uᴾ _) (uᴾ _) (u≈ {n = var vz} refl))

  u≈ : ∀ {Γ A}{n n' : Ne Γ A} → n ≡ n' → uᴺ n ≈ uᴺ n'
  u≈ {A = ι}     p = ne & p
  u≈ {A = A ⇒ B} p = λ σ aᴾ aᴾ' a≈a' → u≈ (app & (Neₑ σ & p) ⊗ q≈ a≈a')

u≈* : ∀ {Γ} → uConᴺ {Γ} ≈* uConᴺ
u≈* {∙}     = ∙
u≈* {Γ , A} = ≈*ₑ wk u≈* , u≈ refl

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = q≈ (⟦~⟧ t~t' uConᴾ uConᴾ u≈*)

