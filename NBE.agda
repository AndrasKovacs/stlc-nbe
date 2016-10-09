{-# OPTIONS --without-K #-}

module NBE where

open import Lib

-- Syntax
--------------------------------------------------------------------------------

infixr 4 _⇒_

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data _∈_ (A : Ty) : Con → Set where
  vz : ∀ {Γ} → A ∈ (Γ , A)
  vs : ∀ {B Γ} → A ∈ Γ → A ∈ (Γ , B)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → Tm Γ (A ⇒ B) → Tm Γ A → Tm Γ B

-- Renaming
--------------------------------------------------------------------------------

infixr 9 _∘ᵣ_
infixl 8 _[_]∈ᵣ _[_]ᵣ

data Ren : Con → Con → Set where
  ∙    : Ren ∙ ∙
  drop : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) Δ
  keep : ∀ {A Γ Δ} → Ren Γ Δ → Ren (Γ , A) (Δ , A)

-- Ren is a category

idᵣ : ∀ {Γ} → Ren Γ Γ
idᵣ {∙}     = ∙
idᵣ {Γ , A} = keep (idᵣ {Γ})

wk : ∀ {A Γ} → Ren (Γ , A) Γ
wk = drop idᵣ

_∘ᵣ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Ren Γ Δ → Ren Γ Σ
σ      ∘ᵣ ∙      = σ
σ      ∘ᵣ drop δ = drop (σ ∘ᵣ δ)
drop σ ∘ᵣ keep δ = drop (σ ∘ᵣ δ)
keep σ ∘ᵣ keep δ = keep (σ ∘ᵣ δ)

idlᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → idᵣ ∘ᵣ σ ≡ σ
idlᵣ ∙        = refl
idlᵣ (drop σ) = drop & idlᵣ σ
idlᵣ (keep σ) = keep & idlᵣ σ

idrᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → σ ∘ᵣ idᵣ ≡ σ
idrᵣ ∙        = refl
idrᵣ (drop σ) = drop & idrᵣ σ
idrᵣ (keep σ) = keep & idrᵣ σ

assᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ∘ᵣ δ) ∘ᵣ ν ≡ σ ∘ᵣ (δ ∘ᵣ ν)
assᵣ σ        δ        ∙        = refl
assᵣ σ        δ        (drop ν) = drop & assᵣ σ δ ν
assᵣ σ        (drop δ) (keep ν) = drop & assᵣ σ δ ν
assᵣ (drop σ) (keep δ) (keep ν) = drop & assᵣ σ δ ν
assᵣ (keep σ) (keep δ) (keep ν) = keep & assᵣ σ δ ν

-- (A ∈_) : is a presheaf on Ren

_[_]∈ᵣ : ∀ {Γ Δ A} → A ∈ Δ → Ren Γ Δ → A ∈ Γ
v    [ ∙      ]∈ᵣ = v
v    [ drop σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)
vz   [ keep σ ]∈ᵣ = vz
vs v [ keep σ ]∈ᵣ = vs (v [ σ ]∈ᵣ)

idᵣ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idᵣ ]∈ᵣ ≡ v
idᵣ∈ vz     = refl
idᵣ∈ (vs v) = vs & idᵣ∈ v

∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  →  v [ σ ]∈ᵣ [ δ ]∈ᵣ ≡ v [ σ ∘ᵣ δ ]∈ᵣ
∘ᵣ∈ ()     ∙        ∙
∘ᵣ∈ v      σ        (drop δ)  = vs & ∘ᵣ∈ v σ δ
∘ᵣ∈ v      (drop σ) (keep δ)  = vs & ∘ᵣ∈ v σ δ
∘ᵣ∈ vz     (keep σ) (keep δ)  = refl
∘ᵣ∈ (vs v) (keep σ) (keep δ)  = vs & ∘ᵣ∈ v σ δ

-- (Tm _ A) is a presheaf on Ren

_[_]ᵣ : ∀ {Γ Δ A} → Tm Δ A → Ren Γ Δ → Tm Γ A
var v   [ σ ]ᵣ = var (v [ σ ]∈ᵣ)
lam t   [ σ ]ᵣ = lam (t [ keep σ ]ᵣ)
app f a [ σ ]ᵣ = app (f [ σ ]ᵣ) (a [ σ ]ᵣ)

idᵣTm : ∀ {Γ A}(t : Tm Γ A) → t [ idᵣ ]ᵣ ≡ t
idᵣTm (var v)   = var & idᵣ∈ v
idᵣTm (lam t)   = lam & idᵣTm t
idᵣTm (app f a) = app & idᵣTm f ⊗ idᵣTm a

∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ]ᵣ [ δ ]ᵣ ≡ t [ σ ∘ᵣ δ ]ᵣ
∘ᵣTm (var v)   σ δ = var & ∘ᵣ∈ v σ δ
∘ᵣTm (lam t)   σ δ = lam & ∘ᵣTm t (keep σ) (keep δ)
∘ᵣTm (app f a) σ δ = app & ∘ᵣTm f σ δ ⊗ ∘ᵣTm a σ δ

-- Substitution
-- (Satisfies the category-with-families equations except the β and η conversions)
--------------------------------------------------------------------------------

infixr  6 _ᵣ∘ₛ_ _ₛ∘ᵣ_
infixl 8 _[_] _[_]∈

data Tms (Γ : Con) : Con → Set where
  ∙   : Tms Γ ∙
  _,_ : ∀ {A Δ} → Tms Γ Δ → Tm Γ A → Tms Γ (Δ , A)

_ₛ∘ᵣ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Ren Γ Δ → Tms Γ Σ
∙       ₛ∘ᵣ δ = ∙
(σ , t) ₛ∘ᵣ δ = σ ₛ∘ᵣ δ , t [ δ ]ᵣ

_ᵣ∘ₛ_ : ∀ {Γ Δ Σ} → Ren Δ Σ → Tms Γ Δ → Tms Γ Σ
∙      ᵣ∘ₛ δ       = δ
drop σ ᵣ∘ₛ (δ , t) = σ ᵣ∘ₛ δ
keep σ ᵣ∘ₛ (δ , t) = σ ᵣ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) Δ
dropₛ σ = σ ₛ∘ᵣ wk

keepₛ : ∀ {A Γ Δ} → Tms Γ Δ → Tms (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var vz

idₛ : ∀ {Γ} → Tms Γ Γ
idₛ {∙}     = ∙
idₛ {Γ , A} = keepₛ {A} idₛ

assₛᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ₛ∘ᵣ δ) ₛ∘ᵣ ν ≡ σ ₛ∘ᵣ (δ ∘ᵣ ν)
assₛᵣᵣ ∙       δ ν = refl
assₛᵣᵣ (σ , t) δ ν = _,_ & assₛᵣᵣ σ δ ν ⊗ ∘ᵣTm t δ ν

assᵣₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Tms Δ Σ)(ν : Ren Γ Δ)
  → (σ ᵣ∘ₛ δ) ₛ∘ᵣ ν ≡ σ ᵣ∘ₛ (δ ₛ∘ᵣ ν)
assᵣₛᵣ ∙        δ       ν = refl
assᵣₛᵣ (drop σ) (δ , t) ν = assᵣₛᵣ σ δ ν
assᵣₛᵣ (keep σ) (δ , t) ν = (_, t [ ν ]ᵣ) & assᵣₛᵣ σ δ ν

⌜_⌝ʳ : ∀ {Γ Δ} → Ren Γ Δ → Tms Γ Δ
⌜ ∙      ⌝ʳ = ∙
⌜ drop σ ⌝ʳ = dropₛ ⌜ σ ⌝ʳ
⌜ keep σ ⌝ʳ = keepₛ ⌜ σ ⌝ʳ

idlᵣₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → idᵣ ᵣ∘ₛ σ ≡ σ
idlᵣₛ ∙       = refl
idlᵣₛ (σ , t) = (_, t) & idlᵣₛ σ

idlₛᵣ : ∀ {Γ Δ}(σ : Ren Γ Δ) → idₛ ₛ∘ᵣ σ ≡ ⌜ σ ⌝ʳ
idlₛᵣ ∙        = refl
idlₛᵣ (drop σ) =
      ((idₛ ₛ∘ᵣ_) ∘ drop) & idrᵣ σ ⁻¹
    ◾ assₛᵣᵣ idₛ σ wk ⁻¹
    ◾ dropₛ & idlₛᵣ σ
idlₛᵣ (keep σ) =
  (_, var vz) &
      (assₛᵣᵣ idₛ wk (keep σ)
    ◾ ((idₛ ₛ∘ᵣ_) ∘ drop) & (idlᵣ σ ◾ idrᵣ σ ⁻¹)
    ◾ assₛᵣᵣ idₛ σ wk ⁻¹
    ◾ (_ₛ∘ᵣ wk) & idlₛᵣ σ )

idrᵣₛ : ∀ {Γ Δ}(σ : Ren Γ Δ) → σ ᵣ∘ₛ idₛ ≡ ⌜ σ ⌝ʳ
idrᵣₛ ∙        = refl
idrᵣₛ (drop σ) = assᵣₛᵣ σ idₛ wk ⁻¹ ◾ dropₛ & idrᵣₛ σ
idrᵣₛ (keep σ) = (_, var vz) & (assᵣₛᵣ σ idₛ wk ⁻¹ ◾ (_ₛ∘ᵣ wk) & idrᵣₛ σ)

_[_]∈ : ∀ {Γ Δ A} → A ∈ Δ → Tms Γ Δ → Tm Γ A
vz   [ σ , t ]∈ = t
vs v [ σ , _ ]∈ = v [ σ ]∈

_[_] : ∀ {Γ Δ A} → Tm Δ A → Tms Γ Δ → Tm Γ A
var v   [ σ ] = v [ σ ]∈
lam t   [ σ ] = lam (t [ keepₛ σ ])
app f a [ σ ] = app (f [ σ ]) (a [ σ ])

_∘ₛ_ : ∀ {Γ Δ Σ} → Tms Δ Σ → Tms Γ Δ → Tms Γ Σ
∙       ∘ₛ δ = ∙
(σ , t) ∘ₛ δ = σ ∘ₛ δ , t [ δ ]

ᵣ∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Ren Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ᵣ [ δ ]∈ ≡ v [ σ ᵣ∘ₛ δ ]∈
ᵣ∘ₛ∈ v      ∙        δ       = refl
ᵣ∘ₛ∈ v      (drop σ) (δ , t) = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛ∈ vz     (keep σ) (δ , t) = refl
ᵣ∘ₛ∈ (vs v) (keep σ) (δ , t) = ᵣ∘ₛ∈ v σ δ

ᵣ∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Ren Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ]ᵣ [ δ ] ≡ t [ σ ᵣ∘ₛ δ ]
ᵣ∘ₛTm (var v)   σ δ = ᵣ∘ₛ∈ v σ δ
ᵣ∘ₛTm (lam t)   σ δ =
  lam &
      (ᵣ∘ₛTm t (keep σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) & (assᵣₛᵣ σ δ wk ⁻¹))
ᵣ∘ₛTm (app f a) σ δ = app & ᵣ∘ₛTm f σ δ ⊗ ᵣ∘ₛTm a σ δ

ₛ∘ᵣ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → v [ σ ]∈ [ δ ]ᵣ ≡ v [ σ ₛ∘ᵣ δ ]∈
ₛ∘ᵣ∈ vz     (σ , _) δ = refl
ₛ∘ᵣ∈ (vs v) (σ , _) δ = ₛ∘ᵣ∈ v σ δ

ₛ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Ren Γ Δ)
  → t [ σ ] [ δ ]ᵣ ≡ t [ σ ₛ∘ᵣ δ ]
ₛ∘ᵣTm (var v)   σ δ = ₛ∘ᵣ∈ v σ δ
ₛ∘ᵣTm (lam t)   σ δ =
  lam & (
      ₛ∘ᵣTm t (keepₛ σ) (keep δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣᵣ σ wk (keep δ)
      ◾ ((λ δ → σ ₛ∘ᵣ (drop δ)) &
          idlᵣ δ
        ◾ (λ δ → σ ₛ∘ᵣ drop δ) & (idrᵣ δ ⁻¹)
        ◾ assₛᵣᵣ σ δ wk ⁻¹)))
ₛ∘ᵣTm (app f a) σ δ = app & ₛ∘ᵣTm f σ δ ⊗ ₛ∘ᵣTm a σ δ

assₛᵣₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Tms Γ Δ)
  → (σ ₛ∘ᵣ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ᵣ∘ₛ ν)
assₛᵣₛ ∙       δ ν = refl
assₛᵣₛ (σ , t) δ ν = _,_ & assₛᵣₛ σ δ ν ⊗ ᵣ∘ₛTm t δ ν

assₛₛᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tms Δ Σ)(ν : Ren Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ᵣ ν ≡ σ ∘ₛ (δ ₛ∘ᵣ ν)
assₛₛᵣ ∙       δ ν = refl
assₛₛᵣ (σ , t) δ ν = _,_ & assₛₛᵣ σ δ ν ⊗ ₛ∘ᵣTm t δ ν

∘ₛ∈ :
  ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → v [ σ ]∈ [ δ ] ≡ v [ σ ∘ₛ δ ]∈
∘ₛ∈ vz     (σ , _) δ = refl
∘ₛ∈ (vs v) (σ , t) δ = ∘ₛ∈ v σ δ

∘ₛTm :
  ∀ {Γ Δ Σ A}(t : Tm Σ A)(σ : Tms Δ Σ)(δ : Tms Γ Δ)
  → t [ σ ] [ δ ] ≡ t [ σ ∘ₛ δ ]
∘ₛTm (var v)   σ δ = ∘ₛ∈ v σ δ
∘ₛTm (lam t)   σ δ =
  lam & (
      ∘ₛTm t (keepₛ σ) (keepₛ δ)
    ◾ (λ σ → t [ σ , var vz ]) &
        (assₛᵣₛ σ wk (keepₛ δ)
      ◾ (σ ∘ₛ_) & idlᵣₛ (δ ₛ∘ᵣ wk) ◾ assₛₛᵣ σ δ wk ⁻¹))
∘ₛTm (app f a) σ δ = app & ∘ₛTm f σ δ ⊗ ∘ₛTm a σ δ

idₛ∈ : ∀ {Γ A}(v : A ∈ Γ) → v [ idₛ ]∈ ≡ var v
idₛ∈ vz     = refl
idₛ∈ (vs v) = ₛ∘ᵣ∈ v idₛ wk ⁻¹ ◾ (_[ wk ]ᵣ) & idₛ∈ v ◾ (var ∘ vs) & idᵣ∈ v

idₛTm : ∀ {Γ A}(t : Tm Γ A) → t [ idₛ ] ≡ t
idₛTm (var v)   = idₛ∈ v
idₛTm (lam t)   = lam & idₛTm t
idₛTm (app f x) = app & idₛTm f ⊗ idₛTm x

idrₛ : ∀ {Γ Δ}(σ : Tms Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ ∙       = refl
idrₛ (σ , t) = _,_ & idrₛ σ ⊗ idₛTm t

-- Normal forms
--------------------------------------------------------------------------------

infix 3 _∈_
infixl 7 _$ₙ_
infixl 8 _[_]ₙᵣ _[_]ₙₑᵣ

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var  : ∀ {A} → A ∈ Γ → Ne Γ A
    _$ₙ_ : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  _[_]ₙᵣ : ∀ {Γ Δ A} → Nf Δ A → Ren Γ Δ → Nf Γ A
  ne  n [ σ ]ₙᵣ = ne (n [ σ ]ₙₑᵣ)
  lam n [ σ ]ₙᵣ = lam (n [ keep σ ]ₙᵣ)

  _[_]ₙₑᵣ : ∀ {Γ Δ A} → Ne Δ A → Ren Γ Δ → Ne Γ A
  var v    [ σ ]ₙₑᵣ = var (v [ σ ]∈ᵣ)
  (f $ₙ a) [ σ ]ₙₑᵣ = f [ σ ]ₙₑᵣ $ₙ a [ σ ]ₙᵣ

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v  ⌝Ne = var v
  ⌜ n $ₙ t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

-- Conversion
--------------------------------------------------------------------------------

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))                  →  t              ~ lam (app (t [ wk ]ᵣ) (var vz))
  β     : ∀ {A B}(t : Tm (Γ , A) B) t'               →  app (lam t) t' ~ t [ idₛ , t' ]

  lam   : ∀ {A B}{t t' : Tm (Γ , A) B}      → t ~ t' →  lam t          ~ lam t'
  app₁  : ∀ {A B}{f f' : Tm Γ (A ⇒ B)}{x}   → f ~ f' →  app f x        ~ app f' x
  app₂  : ∀ {A B}{f : Tm Γ (A ⇒ B)} {x x'}  → x ~ x' →  app f x        ~ app f x'
  ~refl : ∀ {A}{t : Tm Γ A}                 → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A}              → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A}          → t ~ t' → t' ~ t'' → t ~ t''

infix 3 _~_
infixl 4 _~◾_

mutual
  ⌜⌝Neᵣ : ∀ {Γ Δ A}(n : Ne Γ A)(σ : Ren Δ Γ) → ⌜ n [ σ ]ₙₑᵣ ⌝Ne ≡ ⌜ n ⌝Ne [ σ ]ᵣ
  ⌜⌝Neᵣ (var v)  σ = refl
  ⌜⌝Neᵣ (f $ₙ a) σ = app & ⌜⌝Neᵣ f σ ⊗ ⌜⌝ᵣ a σ

  ⌜⌝ᵣ : ∀ {Γ Δ A}(n : Nf Γ A)(σ : Ren Δ Γ) → ⌜ n [ σ ]ₙᵣ ⌝ ≡ ⌜ n ⌝ [ σ ]ᵣ
  ⌜⌝ᵣ (ne n)  σ = ⌜⌝Neᵣ n σ
  ⌜⌝ᵣ (lam n) σ = lam & ⌜⌝ᵣ n (keep σ)

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

-- Normalization + completeness
--------------------------------------------------------------------------------

Norm : ∀ {A Γ} → Tm Γ A → Set
Norm {A}{Γ} t = Σ (Nf Γ A) λ n → t ~ ⌜ n ⌝

⟦_⟧Ty : (A : Ty) → ∀ {Γ} → Tm Γ A → Set
⟦ ι     ⟧Ty {Γ} t = Norm t
⟦ A ⇒ B ⟧Ty {Γ} t = ∀ Δ (σ : Ren Δ Γ)(a : Tm Δ A)(⟦a⟧ : ⟦ A ⟧Ty a) → ⟦ B ⟧Ty (app (t [ σ ]ᵣ) a)

⟦_⟧Con : (Δ : Con) → ∀ {Γ} → Tms Γ Δ → Set
⟦ ∙     ⟧Con Δ       = ⊤
⟦ Γ , A ⟧Con (Δ , t) = ⟦ Γ ⟧Con Δ × ⟦ A ⟧Ty t

⟦Ty⟧ᵣ : ∀ {A Γ Δ t} → (σ : Ren Δ Γ) → ⟦ A ⟧Ty t → ⟦ A ⟧Ty (t [ σ ]ᵣ)
⟦Ty⟧ᵣ {ι}     σ (tₙ , p) = tₙ [ σ ]ₙᵣ , coe ((_ ~_) & (⌜⌝ᵣ tₙ σ ⁻¹)) (~ᵣ σ p)
⟦Ty⟧ᵣ {A ⇒ B} σ ⟦t⟧      =
  λ Σ δ a ⟦a⟧ → coe ((λ t → ⟦ B ⟧Ty (app t a)) & (∘ᵣTm _ σ δ ⁻¹) ) (⟦t⟧ Σ (σ ∘ᵣ δ) a ⟦a⟧)

⟦Ty⟧~ : ∀ {A Γ t t'} → t ~ t' → ⟦ A ⟧Ty {Γ} t → ⟦ A ⟧Ty t'
⟦Ty⟧~ {ι}     t~t' (n , p) = n , (t~t' ~⁻¹ ~◾ p)
⟦Ty⟧~ {A ⇒ B} t~t' ⟦t⟧     = λ Σ σ a ⟦a⟧ → ⟦Ty⟧~ (app₁ (~ᵣ σ t~t')) (⟦t⟧ Σ σ a ⟦a⟧)

⟦Con⟧ᵣ : ∀ {Σ Γ Δ}(σ : Ren Δ Γ)(δ : Tms Γ Σ) → ⟦ Σ ⟧Con δ → ⟦ Σ ⟧Con (δ ₛ∘ᵣ σ)
⟦Con⟧ᵣ σ ∙       ⟦δ⟧         = tt
⟦Con⟧ᵣ σ (δ , t) (⟦δ⟧ , ⟦t⟧) = ⟦Con⟧ᵣ σ δ ⟦δ⟧ , ⟦Ty⟧ᵣ σ ⟦t⟧

⟦_⟧∈ : ∀ {Γ A} → (v : A ∈ Γ) → ∀ {Δ}(σ : Tms Δ Γ) → ⟦ Γ ⟧Con σ → ⟦ A ⟧Ty (v [ σ ]∈)
⟦ vz   ⟧∈ (σ , _) (_  , tᴹ) = tᴹ
⟦ vs v ⟧∈ (σ , _) (σᴹ , _ ) = ⟦ v ⟧∈ σ σᴹ

⟦_⟧Tm : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}(σ : Tms Δ Γ) → ⟦ Γ ⟧Con σ → ⟦ A ⟧Ty (t [ σ ])
⟦ var v   ⟧Tm σ ⟦σ⟧ = ⟦ v ⟧∈ σ ⟦σ⟧
⟦ lam t   ⟧Tm σ ⟦σ⟧ = λ Σ δ a ⟦a⟧ →
    ⟦Ty⟧~
      (coe ((_~ app (lam (t [ keepₛ σ ] [ keep δ ]ᵣ)) a) &
            (ᵣ∘ₛTm (t [ keepₛ σ ]) (keep δ) (idₛ , a)
          ◾ ∘ₛTm t (keepₛ σ) ((δ ᵣ∘ₛ idₛ) , a)
          ◾ (λ ν → t [ ν , a ]) & ((λ ν → dropₛ σ ∘ₛ (ν , a)) &
              idrᵣₛ δ
            ◾ assₛᵣₛ σ wk (⌜ δ ⌝ʳ , a)
            ◾ (σ ∘ₛ_) & idlᵣₛ ⌜ δ ⌝ʳ
            ◾ (σ ∘ₛ_) & idlₛᵣ δ ⁻¹
            ◾ assₛₛᵣ σ idₛ δ ⁻¹
            ◾ (_ₛ∘ᵣ δ) & idrₛ σ)))
        (β (t [ keepₛ σ ] [ keep δ ]ᵣ) a ~⁻¹))
    (⟦ t ⟧Tm (σ ₛ∘ᵣ δ , a) (⟦Con⟧ᵣ δ σ ⟦σ⟧ , ⟦a⟧))
⟦ app f a ⟧Tm σ ⟦σ⟧ =
  coe ((λ t → ⟦ _ ⟧Ty (app t (a [ σ ]))) & idᵣTm (f [ σ ]))
  (⟦ f ⟧Tm σ ⟦σ⟧ _ idᵣ (a [ σ ]) (⟦ a ⟧Tm σ ⟦σ⟧))

mutual
   q : ∀ A {Γ}{t : Tm Γ A} → ⟦ A ⟧Ty t → Norm t
   q ι       ⟦t⟧ = ⟦t⟧
   q (A ⇒ B) ⟦t⟧ =
     let (tₙ , p) = q B (⟦t⟧ _ wk (var vz) (u A (var vz)))
     in lam tₙ , (η _ ~◾ lam p)

   u : ∀ A {Γ} → (n : Ne Γ A) → ⟦ A ⟧Ty ⌜ n ⌝Ne
   u ι       n = ne n , ~refl
   u (A ⇒ B) n = λ Δ σ a ⟦a⟧ →
     let (aₙ , a~aₙ) = q A ⟦a⟧
     in ⟦Ty⟧~
       (coe ((λ x → app ⌜ n [ σ ]ₙₑᵣ ⌝Ne ⌜ aₙ ⌝ ~ app x a) & ⌜⌝Neᵣ n σ)
         (app₂ (a~aₙ ~⁻¹)))
       (u B (n [ σ ]ₙₑᵣ $ₙ aₙ))

uCon : ∀ Γ → ⟦ Γ ⟧Con idₛ
uCon ∙       = tt
uCon (Γ , A) = ⟦Con⟧ᵣ wk _ (uCon Γ) , u A (var vz)

norm : ∀ {Γ A} → (t : Tm Γ A) → Norm t
norm {Γ}{A} t = q A (coe (⟦ A ⟧Ty & idₛTm t) (⟦ t ⟧Tm {Γ} idₛ (uCon Γ)))

-- Stability
--------------------------------------------------------------------------------
-- TODO

-- Soundness
--------------------------------------------------------------------------------

-- TODO
