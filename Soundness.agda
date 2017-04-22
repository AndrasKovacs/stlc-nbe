{-# OPTIONS --without-K #-}

module Soundness where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import Conversion
open import NormalForm

open import Normalization
open import PresheafRefinement

infix 3 _≈_ _≈ᶜ_

_≈_ : ∀ {A Γ} → Tyᴺ A Γ → Tyᴺ A Γ → Set
_≈_ {ι}    {Γ} t t' = t ≡ t'
_≈_ {A ⇒ B}{Γ} t t' = ∀ {Δ}(σ : OPE Δ Γ){a a'} → Tyᴾ a → Tyᴾ a' → a ≈ a' → t σ a ≈ t' σ a'

data _≈ᶜ_ : ∀ {Γ Δ} → Conᴺ Γ Δ → Conᴺ Γ Δ → Set where
  ∙   : ∀ {Γ} → _≈ᶜ_ {∙}{Γ} ∙ ∙
  _,_ : ∀ {A Γ Δ σ δ}{t t' : Tyᴺ A Δ} → _≈ᶜ_ {Γ}{Δ} σ δ → t ≈ t' → (σ , t) ≈ᶜ (δ , t')

_≈⁻¹ : ∀ {Γ A}{t t' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t
_≈⁻¹ {A = ι}     t≈t' = t≈t' ⁻¹
_≈⁻¹ {A = A ⇒ B} t≈t' = λ σ aᴾ a'ᴾ a≈a' → t≈t' σ a'ᴾ aᴾ (a≈a' ≈⁻¹) ≈⁻¹

_≈ᶜ⁻¹ : ∀ {Γ Δ}{σ δ : Conᴺ Γ Δ} → σ ≈ᶜ δ → δ ≈ᶜ σ
∙            ≈ᶜ⁻¹ = ∙
(σ≈δ , t≈t') ≈ᶜ⁻¹ = (σ≈δ ≈ᶜ⁻¹) , (t≈t' ≈⁻¹)

_≈◾_ : ∀ {Γ A}{t t' t'' : Tyᴺ A Γ} → t ≈ t' → t' ≈ t'' → t ≈ t''
_≈◾_ {A = ι}     p q = p ◾ q
_≈◾_ {A = A ⇒ B} p q = λ σ aᴾ a'ᴾ a≈a' → p σ aᴾ aᴾ (a≈a' ≈◾ (a≈a' ≈⁻¹)) ≈◾ q σ aᴾ a'ᴾ a≈a'

_≈ᶜ◾_ : ∀ {Γ Δ}{σ δ ν : Conᴺ Γ Δ} → σ ≈ᶜ δ → δ ≈ᶜ ν → σ ≈ᶜ ν
∙          ≈ᶜ◾ q            = q
(p , t≈t') ≈ᶜ◾ (q , t'≈t'') = (p ≈ᶜ◾ q) , (t≈t' ≈◾ t'≈t'')

≈ₑ : ∀ {Γ Δ A}(σ : OPE Δ Γ){t t' : Tyᴺ A Γ} → t ≈ t' → Tyᴺₑ σ t ≈ Tyᴺₑ σ t'
≈ₑ {A = ι}     σ t≈t' = Nfₑ σ & t≈t'
≈ₑ {A = A ⇒ B} σ t≈t' = λ δ → t≈t' (σ ∘ₑ δ)

≈ᶜₑ : ∀ {Γ Δ Σ}(σ : OPE Σ Γ){δ ν : Conᴺ Δ Γ} → δ ≈ᶜ ν → Conᴺₑ σ δ ≈ᶜ Conᴺₑ σ ν
≈ᶜₑ σ ∙          = ∙
≈ᶜₑ σ (p , t≈t') = ≈ᶜₑ σ p , ≈ₑ σ t≈t'

∈≈ : ∀ {Γ Δ A}(v : A ∈ Γ){σ δ : Conᴺ Γ Δ} → σ ≈ᶜ δ → ∈ᴺ v σ ≈ ∈ᴺ v δ
∈≈ vz     (σ≈δ , t≈t') = t≈t'
∈≈ (vs v) (σ≈δ , _   ) = ∈≈ v σ≈δ

Tm≈ : ∀ {Γ Δ A}(t : Tm Γ A){Γᴺ Γᴺ' : Conᴺ Γ Δ} → Conᴾ Γᴺ → Conᴾ Γᴺ' →  Γᴺ ≈ᶜ Γᴺ' → Tmᴺ t Γᴺ ≈ Tmᴺ t Γᴺ'
Tm≈ (var v)   Γᴾ Γᴾ' σ≈δ = ∈≈ v σ≈δ
Tm≈ (lam t)   Γᴾ Γᴾ' σ≈δ = λ ν aᴾ aᴾ' a≈a' → Tm≈ t (Conᴾₑ ν Γᴾ , aᴾ) (Conᴾₑ ν Γᴾ' , aᴾ') (≈ᶜₑ ν σ≈δ , a≈a')
Tm≈ (app f a) Γᴾ Γᴾ' σ≈δ = Tm≈ f Γᴾ Γᴾ' σ≈δ idₑ (Tmᴾ a Γᴾ) (Tmᴾ a Γᴾ') (Tm≈ a Γᴾ Γᴾ' σ≈δ)

Subᴺᴾ : ∀ {Γ Δ Σ}(σ : Sub Δ Γ){Γᴺ : Conᴺ Δ Σ} → Conᴾ Γᴺ → Conᴾ (Subᴺ σ Γᴺ)
Subᴺᴾ ∙       δᴾ = ∙
Subᴺᴾ (σ , t) δᴾ = Subᴺᴾ σ δᴾ , Tmᴾ t δᴾ

Subᴺ≈ᶜ :
  ∀ {Γ Δ Σ}(σ : Sub Δ Γ){Γᴺ Γᴺ' : Conᴺ Δ Σ} → Conᴾ Γᴺ → Conᴾ Γᴺ' → Γᴺ ≈ᶜ Γᴺ' → Subᴺ σ Γᴺ ≈ᶜ Subᴺ σ Γᴺ'
Subᴺ≈ᶜ ∙       Γᴾ Γᴾ' p = ∙
Subᴺ≈ᶜ (σ , x) Γᴾ Γᴾ' p = Subᴺ≈ᶜ σ Γᴾ Γᴾ' p , Tm≈ x Γᴾ Γᴾ' p

Tmₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(Γᴺ : Conᴺ Δ Σ) → Conᴾ Γᴺ → Γᴺ ≈ᶜ Γᴺ
 → Tmᴺ (Tmₛ σ t) Γᴺ ≈ Tmᴺ t (Subᴺ σ Γᴺ)
Tmₛᴺ σ (var v)   Γᴺ δᴾ Γᴺ≈ᶜ rewrite ∈ₛᴺ σ v Γᴺ ⁻¹ = Tm≈ (∈ₛ σ v) δᴾ δᴾ Γᴺ≈ᶜ
Tmₛᴺ σ (lam t)   Γᴺ δᴾ Γᴺ≈ᶜ ν {a}{a'} aᴾ aᴾ' a≈a'
  rewrite Subᴺ-nat σ ν Γᴺ δᴾ ⁻¹
  = let δᴾ' = Conᴾₑ ν δᴾ in
    Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν Γᴺ , a) (Conᴾₑ ν δᴾ , aᴾ) (≈ᶜₑ ν Γᴺ≈ᶜ , (a≈a' ≈◾ (a≈a' ≈⁻¹)))
  ≈◾ coe ((λ x → Tmᴺ t (x , a) ≈ _) & (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν Γᴺ , a) ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν Γᴺ)) ⁻¹)
     (Tm≈ t (Subᴺᴾ σ δᴾ' , aᴾ) (Subᴺᴾ σ δᴾ' , aᴾ') (Subᴺ≈ᶜ σ δᴾ' δᴾ' (≈ᶜₑ ν Γᴺ≈ᶜ) , a≈a'))
Tmₛᴺ σ (app f x) Γᴺ δᴾ Γᴺ≈ᶜ =
  Tmₛᴺ σ f Γᴺ δᴾ Γᴺ≈ᶜ idₑ (Tmᴾ (Tmₛ σ x) δᴾ) (Tmᴾ x (Subᴺᴾ σ δᴾ)) (Tmₛᴺ σ x Γᴺ δᴾ Γᴺ≈ᶜ)

~≈ :
  ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → ∀ {Γᴺ Γᴺ' : Conᴺ Γ Δ}
  → Conᴾ Γᴺ → Conᴾ Γᴺ' → Γᴺ ≈ᶜ Γᴺ' → Tmᴺ t Γᴺ ≈ Tmᴺ t' Γᴺ'
~≈ (η t) {Γᴺ} {Γᴺ'} Γᴾ Γᴾ' Γᴺ≈Γᴺ' ν {a} {a'} aᴾ aᴾ' a≈a'
  rewrite
    Tmₑᴺ wk t (Conᴺₑ ν Γᴺ' , a')
  | OPEᴺ-idₑ (Conᴺₑ ν Γᴺ')
  | Tmᴺ-nat t ν {Γᴺ'} Γᴾ'
  | idrₑ ν
  = Tm≈ t Γᴾ Γᴾ' Γᴺ≈Γᴺ' ν aᴾ aᴾ' a≈a'

~≈ (β t t') {Γᴺ} {Γᴺ'} Γᴾ Γᴾ' σ≈δ =
     coe ((λ x y → Tmᴺ t (x , Tmᴺ t' Γᴺ) ≈
           Tmᴺ t (y , Tmᴺ t' Γᴺ')) & (Conᴺ-idₑ Γᴺ ⁻¹) ⊗ (Subᴺ-idₛ Γᴺ' ⁻¹))
       (Tm≈ t (Γᴾ , Tmᴾ t' Γᴾ) (Γᴾ' , Tmᴾ t' Γᴾ') (σ≈δ , (Tm≈ t' Γᴾ Γᴾ' σ≈δ)))
  ≈◾ (Tmₛᴺ (idₛ , t') t Γᴺ' Γᴾ' ((σ≈δ ≈ᶜ⁻¹) ≈ᶜ◾ σ≈δ) ≈⁻¹)

~≈ (lam t~t') Γᴾ Γᴾ' Γᴺ≈Γᴺ' =
  λ ν aᴾ aᴾ' a≈a' → ~≈ t~t' (Conᴾₑ ν Γᴾ , aᴾ) (Conᴾₑ ν Γᴾ' , aᴾ') (≈ᶜₑ ν Γᴺ≈Γᴺ' , a≈a')
~≈ (app {f = f}{f'}{a = a}{a'} t~t' a~a') Γᴾ Γᴾ' Γᴺ≈Γᴺ' =
  ~≈ t~t' Γᴾ Γᴾ' Γᴺ≈Γᴺ' idₑ (Tmᴾ a Γᴾ) (Tmᴾ a' Γᴾ') (~≈ a~a' Γᴾ Γᴾ' Γᴺ≈Γᴺ')  
~≈ {t = t} ~refl    Γᴾ Γᴾ' Γᴺ≈Γᴺ' = Tm≈ t Γᴾ Γᴾ' Γᴺ≈Γᴺ'
~≈ (t'~t ~⁻¹)       Γᴾ Γᴾ' Γᴺ≈Γᴺ' = ~≈ t'~t Γᴾ' Γᴾ (Γᴺ≈Γᴺ' ≈ᶜ⁻¹) ≈⁻¹
~≈ (t~t' ~◾ t'~t'') Γᴾ Γᴾ' Γᴺ≈Γᴺ' = ~≈ t~t' Γᴾ Γᴾ (Γᴺ≈Γᴺ' ≈ᶜ◾ (Γᴺ≈Γᴺ' ≈ᶜ⁻¹)) ≈◾ ~≈ t'~t'' Γᴾ Γᴾ' Γᴺ≈Γᴺ'

mutual
  q≈ : ∀ {A Γ}{t t' : Tyᴺ A Γ} → t ≈ t' → qᴺ t ≡ qᴺ t'
  q≈ {ι}     t≈t' = t≈t'
  q≈ {A ⇒ B} t≈t' = lam & q≈ (t≈t' (wk {A}) (uᴾ _) (uᴾ _) (u≈ refl))

  u≈ : ∀ {A Γ}{n n' : Ne Γ A} → n ≡ n' → uᴺ n ≈ uᴺ n'
  u≈ {ι}     p = ne & p
  u≈ {A ⇒ B} p = λ σ aᴾ aᴾ' a≈a' → u≈ (app & (Neₑ σ & p) ⊗ q≈ a≈a')

uᶜ≈ : ∀ {Γ} → uᶜᴺ {Γ} ≈ᶜ uᶜᴺ
uᶜ≈ {∙}     = ∙
uᶜ≈ {Γ , A} = ≈ᶜₑ wk uᶜ≈ , u≈ refl

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = q≈ (~≈ t~t' uᶜᴾ uᶜᴾ uᶜ≈)

