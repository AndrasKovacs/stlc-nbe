{-# OPTIONS --without-K #-}

-- everything in one module (don't ask why)
-- slightly shorter version where we define A ∈ Γ as OPE Γ (∙ , A)

open import Lib
open import UIP

data Ty : Set where
  ι   : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  ∙   : Con
  _,_ : Con → Ty → Con

data OPE : Con → Con → Set where
  ∙    : OPE ∙ ∙
  drop : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) Δ
  keep : ∀ {A Γ Δ} → OPE Γ Δ → OPE (Γ , A) (Δ , A)

infix 3 _∈_
_∈_ : Ty → Con → Set
A ∈ Γ = OPE Γ (∙ , A)

data Tm Γ : Ty → Set where
  var : ∀ {A} → A ∈ Γ → Tm Γ A
  lam : ∀ {A B} → Tm (Γ , A) B → Tm Γ (A ⇒ B)
  app : ∀ {A B} → (f : Tm Γ (A ⇒ B)) → (a : Tm Γ A) → Tm Γ B

--------------------------------------------------------------------------------

idₑ : ∀ {Γ} → OPE Γ Γ
idₑ {∙}     = ∙
idₑ {Γ , A} = keep (idₑ {Γ})

wk : ∀ {A Γ} → OPE (Γ , A) Γ
wk = drop idₑ

infixr 6 _∘ₑ_
_∘ₑ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → OPE Γ Δ → OPE Γ Σ
σ      ∘ₑ ∙      = σ
σ      ∘ₑ drop δ = drop (σ ∘ₑ δ)
drop σ ∘ₑ keep δ = drop (σ ∘ₑ δ)
keep σ ∘ₑ keep δ = keep (σ ∘ₑ δ)

idlₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₑ ∘ₑ σ ≡ σ
idlₑ ∙        = refl
idlₑ (drop σ) = drop & idlₑ σ
idlₑ (keep σ) = keep & idlₑ σ

idrₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ∘ₑ idₑ ≡ σ
idrₑ ∙        = refl
idrₑ (drop σ) = drop & idrₑ σ
idrₑ (keep σ) = keep & idrₑ σ

assₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₑ δ) ∘ₑ ν ≡ σ ∘ₑ (δ ∘ₑ ν)
assₑ σ        δ        ∙        = refl
assₑ σ        δ        (drop ν) = drop & assₑ σ δ ν
assₑ σ        (drop δ) (keep ν) = drop & assₑ σ δ ν
assₑ (drop σ) (keep δ) (keep ν) = drop & assₑ σ δ ν
assₑ (keep σ) (keep δ) (keep ν) = keep & assₑ σ δ ν

Tmₑ : ∀ {A Γ Δ} → OPE Γ Δ → Tm Δ A → Tm Γ A
Tmₑ σ (var v)   = var (v ∘ₑ σ)
Tmₑ σ (lam t)   = lam (Tmₑ (keep σ) t)
Tmₑ σ (app f a) = app (Tmₑ σ f) (Tmₑ σ a)

Tm-idₑ : ∀ {A Γ}(t : Tm Γ A) → Tmₑ idₑ t ≡ t
Tm-idₑ (var v)   = var & idrₑ v
Tm-idₑ (lam t)   = lam & Tm-idₑ t
Tm-idₑ (app f a) = app & Tm-idₑ f ⊗ Tm-idₑ a

Tm-∘ₑ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₑ (σ ∘ₑ δ) t ≡ Tmₑ δ (Tmₑ σ t)
Tm-∘ₑ σ δ (var v)   = var & (assₑ v σ δ ⁻¹)
Tm-∘ₑ σ δ (lam t)   = lam & Tm-∘ₑ (keep σ) (keep δ) t
Tm-∘ₑ σ δ (app f a) = app & Tm-∘ₑ σ δ f ⊗ Tm-∘ₑ σ δ a

--------------------------------------------------------------------------------

infixr 6 _ₑ∘ₛ_ _ₛ∘ₑ_ _∘ₛ_

Sub : Con → Con → Set
Sub Γ ∙       = ⊤
Sub Γ (Δ , A) = Sub Γ Δ × Tm Γ A

_ₛ∘ₑ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → OPE Γ Δ → Sub Γ Σ
_ₛ∘ₑ_ {Σ = ∙}     σ δ = tt
_ₛ∘ₑ_ {Σ = Σ , A} σ δ = proj₁ σ ₛ∘ₑ δ , Tmₑ δ (proj₂ σ)

_ₑ∘ₛ_ : ∀ {Γ Δ Σ} → OPE Δ Σ → Sub Γ Δ → Sub Γ Σ
∙      ₑ∘ₛ δ       = δ
drop σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ
keep σ ₑ∘ₛ (δ , t) = σ ₑ∘ₛ δ , t

dropₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) Δ
dropₛ σ = σ ₛ∘ₑ wk

ε : ∀ {Γ} → OPE Γ ∙
ε {∙}     = ∙
ε {Γ , _} = drop ε

εη : ∀ {Γ}(σ : OPE Γ ∙) → σ ≡ ε
εη ∙        = refl
εη (drop σ) = drop & εη σ

keepₛ : ∀ {A Γ Δ} → Sub Γ Δ → Sub (Γ , A) (Δ , A)
keepₛ σ = dropₛ σ , var (keep ε)

⌜_⌝ᵒᵖᵉ : ∀ {Γ Δ} → OPE Γ Δ → Sub Γ Δ
⌜ ∙      ⌝ᵒᵖᵉ = tt
⌜ drop σ ⌝ᵒᵖᵉ = dropₛ ⌜ σ ⌝ᵒᵖᵉ
⌜ keep σ ⌝ᵒᵖᵉ = keepₛ ⌜ σ ⌝ᵒᵖᵉ

Tmₛ : ∀ {A Γ Δ} → Sub Γ Δ → Tm Δ A → Tm Γ A
Tmₛ σ (var v)   = proj₂ (v ₑ∘ₛ σ)
Tmₛ σ (lam t)   = lam (Tmₛ (keepₛ σ) t)
Tmₛ σ (app f a) = app (Tmₛ σ f) (Tmₛ σ a)

idₛ : ∀ {Γ} → Sub Γ Γ
idₛ {∙}     = tt
idₛ {Γ , A} = keepₛ idₛ

_∘ₛ_ : ∀ {Γ Δ Σ} → Sub Δ Σ → Sub Γ Δ → Sub Γ Σ
_∘ₛ_ {Σ = ∙}     σ δ = tt
_∘ₛ_ {Σ = Σ , A} σ δ = proj₁ σ ∘ₛ δ , Tmₛ δ (proj₂ σ)

assₛₑₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : OPE Γ Δ)
  → (σ ₛ∘ₑ δ) ₛ∘ₑ ν ≡ σ ₛ∘ₑ (δ ∘ₑ ν)
assₛₑₑ {Ξ = ∙}    _       δ ν = refl
assₛₑₑ {Ξ = Ξ , A}(σ , t) δ ν = _,_ & assₛₑₑ σ δ ν ⊗ (Tm-∘ₑ δ ν t ⁻¹)

assₑₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ₑ∘ₛ δ) ₛ∘ₑ ν ≡ σ ₑ∘ₛ (δ ₛ∘ₑ ν)
assₑₛₑ ∙        δ       ν = refl
assₑₛₑ (drop σ) (δ , t) ν = assₑₛₑ σ δ ν
assₑₛₑ (keep σ) (δ , t) ν = (_, Tmₑ ν t) & assₑₛₑ σ δ ν

idlₑₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → idₑ ₑ∘ₛ σ ≡ σ
idlₑₛ {Δ = ∙}    tt      = refl
idlₑₛ {Δ = Δ , A}(σ , t) = (_, t) & idlₑₛ σ

idlₛₑ : ∀ {Γ Δ}(σ : OPE Γ Δ) → idₛ ₛ∘ₑ σ ≡ ⌜ σ ⌝ᵒᵖᵉ
idlₛₑ ∙        = refl
idlₛₑ (drop σ) =
    (idₛ ₛ∘ₑ_) & (drop & (idrₑ σ ⁻¹))
  ◾ assₛₑₑ idₛ σ wk ⁻¹
  ◾ dropₛ & idlₛₑ σ
idlₛₑ (keep σ) =
  _,_ & (assₛₑₑ idₛ wk (keep σ) ◾ (idₛ ₛ∘ₑ_) & (drop & (idlₑ σ)) ◾ idlₛₑ (drop σ))
      ⊗ (var ∘ keep) & εη _

idrₑₛ : ∀ {Γ Δ}(σ : OPE Γ Δ) → σ ₑ∘ₛ idₛ ≡ ⌜ σ ⌝ᵒᵖᵉ
idrₑₛ ∙        = refl
idrₑₛ (drop σ) = assₑₛₑ σ idₛ wk ⁻¹ ◾ dropₛ & idrₑₛ σ
idrₑₛ (keep σ) = (_, var (keep ε)) & (assₑₛₑ σ idₛ wk ⁻¹ ◾ (_ₛ∘ₑ wk) & idrₑₛ σ)

assₑₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : OPE Δ Σ)(ν : Sub Γ Δ)
  → (σ ∘ₑ δ) ₑ∘ₛ ν ≡ σ ₑ∘ₛ (δ ₑ∘ₛ ν)
assₑₑₛ σ        ∙        ν       = refl
assₑₑₛ σ        (drop δ) (ν , t) = assₑₑₛ σ δ ν
assₑₑₛ (drop σ) (keep δ) (ν , t) = assₑₑₛ σ δ ν
assₑₑₛ (keep σ) (keep δ) (ν , t) = (_, t) & assₑₑₛ σ δ ν

Tm-ₑ∘ₛ : ∀ {A Γ Δ Σ}(σ : OPE Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₑ∘ₛ δ) t ≡ Tmₛ δ (Tmₑ σ t)
Tm-ₑ∘ₛ σ δ (var v) = proj₂ & assₑₑₛ v σ δ ⁻¹
Tm-ₑ∘ₛ σ δ (lam t) =
  lam & ((λ x → Tmₛ (x , var (keep ε)) t) & assₑₛₑ σ δ wk ◾ Tm-ₑ∘ₛ (keep σ) (keepₛ δ) t)
Tm-ₑ∘ₛ σ δ (app f a) = app & Tm-ₑ∘ₛ σ δ f ⊗ Tm-ₑ∘ₛ σ δ a

Tm-ₛ∘ₑ : ∀ {Γ Δ Σ A}(σ : Sub Δ Σ)(δ : OPE Γ Δ)(t : Tm Σ A) → Tmₛ (σ ₛ∘ₑ δ) t ≡ Tmₑ δ (Tmₛ σ t)
Tm-ₛ∘ₑ σ δ (var x) = proj₂ & assₑₛₑ x σ δ ⁻¹
Tm-ₛ∘ₑ σ δ (lam t) =
  lam &
      ((λ x → Tmₛ (x , var (keep ε)) t) &
          (assₛₑₑ σ δ wk
        ◾ (σ ₛ∘ₑ_) & (drop & (idrₑ δ ◾ idlₑ δ ⁻¹))
        ◾ assₛₑₑ σ wk (keep δ) ⁻¹)
    ◾ (λ x → Tmₛ (((σ ₛ∘ₑ drop idₑ) ₛ∘ₑ keep δ) , var (keep x)) t)
        & (εη (ε ∘ₑ δ) ⁻¹)
    ◾ Tm-ₛ∘ₑ (keepₛ σ) (keep δ) t )
Tm-ₛ∘ₑ σ δ (app f a) = app & Tm-ₛ∘ₑ σ δ f ⊗ Tm-ₛ∘ₑ σ δ a

assₛₑₛ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Δ Σ)(ν : Sub Γ Δ)
  → (σ ₛ∘ₑ δ) ∘ₛ ν ≡ σ ∘ₛ (δ ₑ∘ₛ ν)
assₛₑₛ {Ξ = ∙}    tt      δ ν = refl
assₛₑₛ {Ξ = Ξ , A}(σ , t) δ ν = _,_ & assₛₑₛ σ δ ν ⊗ (Tm-ₑ∘ₛ δ ν t ⁻¹)

assₑₛₛ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Sub Δ Σ)(ν : Sub Γ Δ)
  → (σ ₑ∘ₛ δ) ∘ₛ ν ≡ σ ₑ∘ₛ (δ ∘ₛ ν)
assₑₛₛ ∙        δ       ν = refl
assₑₛₛ (drop σ) (δ , t) ν = assₑₛₛ σ δ ν
assₑₛₛ (keep σ) (δ , t) ν = (_, Tmₛ ν t) & assₑₛₛ σ δ ν

assₛₛₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : Sub Δ Σ)(ν : OPE Γ Δ)
  → (σ ∘ₛ δ) ₛ∘ₑ ν ≡ σ ∘ₛ (δ ₛ∘ₑ ν)
assₛₛₑ {Ξ = ∙}    tt      δ ν = refl
assₛₛₑ {Ξ = Ξ , A}(σ , t) δ ν = _,_ & assₛₛₑ σ δ ν ⊗ (Tm-ₛ∘ₑ δ ν t ⁻¹)

Tm-∘ₛ : ∀ {Γ Δ Σ A}(σ : Sub Δ Σ)(δ : Sub Γ Δ)(t : Tm Σ A) → Tmₛ (σ ∘ₛ δ) t ≡ Tmₛ δ (Tmₛ σ t)
Tm-∘ₛ σ δ (var x) = proj₂ & assₑₛₛ x σ δ ⁻¹
Tm-∘ₛ σ δ (lam t) =
  lam &
      ((λ x → Tmₛ (x , var (keep ε)) t) &
          (assₛₛₑ σ δ wk
        ◾ (σ ∘ₛ_) & (idlₑₛ  (dropₛ δ) ⁻¹) ◾ assₛₑₛ σ wk (keepₛ δ) ⁻¹)
    ◾ Tm-∘ₛ (keepₛ σ) (keepₛ δ) t)
Tm-∘ₛ σ δ (app f a) = app & Tm-∘ₛ σ δ f ⊗ Tm-∘ₛ σ δ a

proj₂⌜⌝ : ∀ {Γ A}(x : A ∈ Γ) → proj₂ ⌜ x ⌝ᵒᵖᵉ ≡ var x
proj₂⌜⌝ (drop x) = Tmₑ wk & proj₂⌜⌝ x ◾ (var ∘ drop) & idrₑ x
proj₂⌜⌝ (keep x) = (var ∘ keep) & (εη x ⁻¹)

Tm-idₛ : ∀ {A Γ}(t : Tm Γ A) → Tmₛ idₛ t ≡ t
Tm-idₛ (var v)   = proj₂ & idrₑₛ v ◾ proj₂⌜⌝ v
Tm-idₛ (lam t)   = lam & Tm-idₛ t
Tm-idₛ (app f a) = app & Tm-idₛ f ⊗ Tm-idₛ a

idrₛ : ∀ {Γ Δ}(σ : Sub Γ Δ) → σ ∘ₛ idₛ ≡ σ
idrₛ {Δ = ∙}    tt      = refl
idrₛ {Δ = Δ , A}(σ , t) = _,_ & idrₛ σ ⊗ Tm-idₛ t

βₑₛ :
  ∀ {Γ Δ Σ A B}(σ : Sub Δ Γ)(ν : OPE Σ Δ) (t : Tm (Γ , A) B) (a : Tm Σ A)
  → Tmₛ (σ ₛ∘ₑ ν , a) t ≡ Tmₛ (idₛ , a) (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t))
βₑₛ σ ν t a =
    (λ x → Tmₛ (x , a) t) &
       (idrₛ (σ ₛ∘ₑ ν) ⁻¹
      ◾ assₛₑₛ σ ν idₛ
      ◾ (σ ∘ₛ_) & idlₑₛ (ν ₑ∘ₛ idₛ) ⁻¹
      ◾ assₛₑₛ σ wk ((ν ₑ∘ₛ idₛ) , a) ⁻¹)
  ◾ Tm-∘ₛ (keepₛ σ) (keep ν ₑ∘ₛ (idₛ , a)) t
  ◾ Tm-ₑ∘ₛ (keep ν) (idₛ , a) (Tmₛ (keepₛ σ) t)

--------------------------------------------------------------------------------

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var : ∀ {A} → A ∈ Γ → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  Nfₑ : ∀ {Γ Δ A} → OPE Γ Δ → Nf Δ A → Nf Γ A
  Nfₑ σ (ne n)  = ne (Neₑ σ n)
  Nfₑ σ (lam n) = lam (Nfₑ (keep σ) n)

  Neₑ : ∀ {Γ Δ A} → OPE Γ Δ → Ne Δ A → Ne Γ A
  Neₑ σ (var v)   = var (v ∘ₑ σ)
  Neₑ σ (app f a) = app (Neₑ σ f) (Nfₑ σ a)

mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v   ⌝Ne = var v
  ⌜ app n t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

mutual
  ⌜⌝Ne-nat : ∀ {Γ Δ A}(σ : OPE Δ Γ)(n : Ne Γ A) → ⌜ Neₑ σ n ⌝Ne ≡ Tmₑ σ ⌜ n ⌝Ne
  ⌜⌝Ne-nat σ (var v)   = refl
  ⌜⌝Ne-nat σ (app f a) = app & ⌜⌝Ne-nat σ f ⊗ ⌜⌝Nf-nat σ a

  ⌜⌝Nf-nat : ∀ {Γ Δ A}(σ : OPE Δ Γ)(n : Nf Γ A) → ⌜ Nfₑ σ n ⌝ ≡ Tmₑ σ ⌜ n ⌝
  ⌜⌝Nf-nat σ (ne n)  = ⌜⌝Ne-nat σ n
  ⌜⌝Nf-nat σ (lam n) = lam & ⌜⌝Nf-nat (keep σ) n

mutual
  Nf-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Nf Σ A)
    → Nfₑ (σ ∘ₑ δ) t ≡ Nfₑ δ (Nfₑ σ t)
  Nf-∘ₑ  σ δ (ne n)  = ne & Ne-∘ₑ σ δ n
  Nf-∘ₑ  σ δ (lam t) = lam & Nf-∘ₑ (keep σ) (keep δ) t

  Ne-∘ₑ :
    ∀ {Γ Δ Σ A}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(t : Ne Σ A)
    → Neₑ (σ ∘ₑ δ) t ≡ Neₑ δ (Neₑ σ t)
  Ne-∘ₑ σ δ (var v)   = var & (assₑ v σ δ ⁻¹)
  Ne-∘ₑ σ δ (app f a) = app & Ne-∘ₑ σ δ f ⊗ Nf-∘ₑ σ δ a

mutual
  Nf-idₑ : ∀ {Γ A}(t : Nf Γ A) → Nfₑ idₑ t ≡ t
  Nf-idₑ (ne n)  = ne & Ne-idₑ n
  Nf-idₑ (lam t) = lam & Nf-idₑ t

  Ne-idₑ : ∀ {Γ A}(t : Ne Γ A) → Neₑ idₑ t ≡ t
  Ne-idₑ (var v)   = var & idrₑ v
  Ne-idₑ (app f a) = app & Ne-idₑ f ⊗ Nf-idₑ a

--------------------------------------------------------------------------------

data _~_ {Γ} : ∀ {A} → Tm Γ A → Tm Γ A → Set where
  η     : ∀ {A B}(t : Tm Γ (A ⇒ B))     →  t ~ lam (app (Tmₑ wk t) (var (keep ε)))
  β     : ∀ {A B}(t : Tm (Γ , A) B) t'  →  app (lam t) t' ~ Tmₛ (idₛ , t') t

  lam   : ∀ {A B}{t t' : Tm (Γ , A) B}       → t ~ t' →  lam t   ~ lam t'
  app   : ∀ {A B}{f f' : Tm Γ (A ⇒ B)}{a a'} → f ~ f' →  a ~ a' → app f a ~ app f' a'
  ~refl : ∀ {A}{t : Tm Γ A}                  → t ~ t
  _~⁻¹  : ∀ {A}{t t' : Tm Γ A}               → t ~ t' → t' ~ t
  _~◾_  : ∀ {A}{t t' t'' : Tm Γ A}           → t ~ t' → t' ~ t'' → t ~ t''

infix 3 _~_
infixl 4 _~◾_
infix 6 _~⁻¹

~ₑ : ∀ {Γ Δ A}{t t' : Tm Γ A}(σ : OPE Δ Γ) → t ~ t' → Tmₑ σ t ~ Tmₑ σ t'
~ₑ σ (η t) =
  coe ((λ t' → Tmₑ σ t ~ lam (app t' (var (keep ε))))
    & (Tm-∘ₑ σ wk t ⁻¹
    ◾ (λ x → Tmₑ (drop x) t) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ Tm-∘ₑ wk  (keep σ) t)
    ◾ (λ x → (Tmₑ σ t ~ lam (app (Tmₑ (keep σ) (Tmₑ wk t)) (var (keep x)))))
        & (εη (ε ∘ₑ σ) ⁻¹))
  (η (Tmₑ σ t))

~ₑ σ (β t t') =
  coe ((app (lam (Tmₑ (keep σ) t)) (Tmₑ σ t') ~_) &
    (Tm-ₑ∘ₛ (keep σ) (idₛ , Tmₑ σ t') t ⁻¹
    ◾ (λ x → Tmₛ (x , Tmₑ σ t') t) & (idrₑₛ σ ◾ idlₛₑ σ ⁻¹)
    ◾ Tm-ₛ∘ₑ (idₛ , t') σ t))
  (β (Tmₑ (keep σ) t) (Tmₑ σ t'))

~ₑ σ (lam t~t')       = lam (~ₑ (keep σ) t~t')
~ₑ σ (app t~t' a~a')  = app (~ₑ σ t~t') (~ₑ σ a~a')
~ₑ σ ~refl            = ~refl
~ₑ σ (t~t' ~⁻¹)       = ~ₑ σ t~t' ~⁻¹
~ₑ σ (t~t' ~◾ t'~t'') = ~ₑ σ t~t' ~◾ ~ₑ σ t'~t''

-- Tyᴺ A : PSh 𝒪PE
--------------------------------------------------------------------------------
mutual
  Tyᴺ : Ty → Con → Set
  Tyᴺ ι       Γ = Nf Γ ι
  Tyᴺ (A ⇒ B) Γ =
    Σ (∀ {Δ} → OPE Δ Γ → Tyᴺ A Δ → Tyᴺ B Δ) λ fᴺ →
    ∀ {Δ Σ}(σ : OPE Δ Γ)(δ : OPE Σ Δ) aᴺ → fᴺ (σ ∘ₑ δ) (Tyᴺₑ δ aᴺ) ≡ Tyᴺₑ δ (fᴺ σ aᴺ)

  Tyᴺₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴺ A Γ → Tyᴺ A Δ
  Tyᴺₑ {ι}     σ tᴺ            = Nfₑ σ tᴺ
  Tyᴺₑ {A ⇒ B} σ (tᴺ , tᴺ-nat) =
    (λ δ → tᴺ (σ ∘ₑ δ)) ,
    (λ δ ν aᴺ → (λ x → tᴺ x (Tyᴺₑ ν aᴺ)) & (assₑ σ δ ν ⁻¹) ◾ tᴺ-nat (σ ∘ₑ δ) ν aᴺ)

⇒ᴺ≡ :
  ∀ {Γ A B}{f f' : Tyᴺ (A ⇒ B) Γ}
  → (∀ {Δ}(σ : OPE Δ Γ) a → proj₁ f σ a ≡ proj₁ f' σ a)
  → f ≡ f'
⇒ᴺ≡ {f = f}{f'} eq = ,Σ=
  (funexti λ _ → funext λ σ → funext λ aᴺ → eq σ aᴺ )
  (funexti λ _ → funexti λ _ → funext λ _ → funext λ _ → funext λ _ → UIP _ _)

Tyᴺ-idₑ : ∀ {Γ A}(tᴺ : Tyᴺ A Γ) → Tyᴺₑ idₑ tᴺ ≡ tᴺ
Tyᴺ-idₑ {A = ι}     tᴺ       = Nf-idₑ tᴺ
Tyᴺ-idₑ {A = A ⇒ B} (tᴺ , _) = ⇒ᴺ≡ λ σ aᴺ → (λ x → tᴺ x aᴺ) & idlₑ σ

Tyᴺ-∘ₑ :
  ∀ {Γ Δ Σ A}(tᴺ : Tyᴺ A Σ)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  → Tyᴺₑ (σ ∘ₑ δ) tᴺ ≡ Tyᴺₑ δ (Tyᴺₑ σ tᴺ)
Tyᴺ-∘ₑ {A = ι}     tᴺ       σ δ = Nf-∘ₑ σ δ tᴺ
Tyᴺ-∘ₑ {A = A ⇒ B} (tᴺ , _) σ δ = ⇒ᴺ≡ λ ν aᴺ → (λ x → tᴺ x aᴺ) & assₑ σ δ ν

-- Conᴺ Γ : PSh 𝒪PE
--------------------------------------------------------------------------------

Conᴺ : Con → Con → Set
Conᴺ ∙       Δ = ⊤
Conᴺ (Γ , A) Δ = Conᴺ Γ Δ × Tyᴺ A Δ

Conᴺₑ : ∀ {Γ Δ} → OPE Δ Γ → ∀ {Σ} → Conᴺ Σ Γ → Conᴺ Σ Δ
Conᴺₑ σ {∙}    tt       = tt
Conᴺₑ σ {Σ , A}(δ , tᴺ) = Conᴺₑ σ δ , Tyᴺₑ σ tᴺ

Conᴺ-idₑ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Conᴺₑ idₑ σᴺ ≡ σᴺ
Conᴺ-idₑ {∙}    tt       = refl
Conᴺ-idₑ {Γ , A}(σᴺ , t) = _,_ & Conᴺ-idₑ σᴺ ⊗ Tyᴺ-idₑ t

Conᴺ-∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(ν : Conᴺ Ξ Σ)
  → Conᴺₑ (σ ∘ₑ δ) ν ≡ Conᴺₑ δ (Conᴺₑ σ ν)
Conᴺ-∘ₑ {Ξ = ∙}     σ δ tt      = refl
Conᴺ-∘ₑ {Ξ = Ξ , A} σ δ (ν , t) = _,_ & Conᴺ-∘ₑ σ δ ν ⊗ Tyᴺ-∘ₑ t σ δ

-- OPEᴺ {Γ}{Δ} σ : PSh 𝒪PE (Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
OPEᴺ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
OPEᴺ ∙        δᴺ        = δᴺ
OPEᴺ (drop σ) (δᴺ , _)  = OPEᴺ σ δᴺ
OPEᴺ (keep σ) (δᴺ , tᴺ) = OPEᴺ σ δᴺ , tᴺ

OPEᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : OPE Γ Δ)(δ : OPE Ξ Σ) νᴺ → OPEᴺ σ (Conᴺₑ δ νᴺ) ≡ Conᴺₑ δ (OPEᴺ σ νᴺ)
OPEᴺ-nat ∙        δ νᴺ        = refl
OPEᴺ-nat (drop σ) δ (νᴺ , tᴺ) = OPEᴺ-nat σ δ νᴺ
OPEᴺ-nat (keep σ) δ (νᴺ , tᴺ) = (_, Tyᴺₑ δ tᴺ) & OPEᴺ-nat σ δ νᴺ

OPEᴺ-idₑ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → OPEᴺ idₑ σᴺ ≡ σᴺ
OPEᴺ-idₑ {∙}    tt        = refl
OPEᴺ-idₑ {Γ , A}(σᴺ , tᴺ) = (_, tᴺ) & OPEᴺ-idₑ σᴺ

OPEᴺ-∘ₑ : ∀ {Γ Δ Σ Ξ} σ δ νᴺ → OPEᴺ {Γ}{Σ} (σ ∘ₑ δ) {Ξ} νᴺ ≡ OPEᴺ {Δ}{Σ} σ (OPEᴺ δ νᴺ)
OPEᴺ-∘ₑ σ        ∙        νᴺ = refl
OPEᴺ-∘ₑ σ        (drop δ) νᴺ = OPEᴺ-∘ₑ σ δ (proj₁ νᴺ)
OPEᴺ-∘ₑ (drop σ) (keep δ) νᴺ = OPEᴺ-∘ₑ σ δ (proj₁ νᴺ)
OPEᴺ-∘ₑ (keep σ) (keep δ) νᴺ = (_, proj₂ νᴺ) & OPEᴺ-∘ₑ σ δ (proj₁ νᴺ)

-- Tmᴺ {Γ}{A} t : PSh 𝒪PE (Conᴺ Γ, Tyᴺ A)
--------------------------------------------------------------------------------
mutual
  Tmᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
  Tmᴺ (var v)   σᴺ = proj₂ (OPEᴺ v σᴺ)
  Tmᴺ (lam t)   σᴺ =
    (λ δ aᴺ → Tmᴺ t (Conᴺₑ δ σᴺ , aᴺ)) ,
    (λ δ ν aᴺ → (λ x → Tmᴺ t (x , Tyᴺₑ ν aᴺ)) & (Conᴺ-∘ₑ δ ν σᴺ ⁻¹) ⁻¹
              ◾ Tmᴺ-nat t ν (Conᴺₑ δ σᴺ , aᴺ))
  Tmᴺ (app f a) σᴺ = proj₁ (Tmᴺ f σᴺ) idₑ (Tmᴺ a σᴺ)

  Tmᴺ-nat : ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : OPE Σ Δ) δᴺ → Tmᴺ t (Conᴺₑ σ δᴺ) ≡ Tyᴺₑ σ (Tmᴺ t δᴺ)
  Tmᴺ-nat (var v)   σ δᴺ = proj₂ & OPEᴺ-nat v σ δᴺ
  Tmᴺ-nat (lam t)   σ δᴺ = ⇒ᴺ≡ λ ν aᴺ → (λ x → Tmᴺ t (x , aᴺ)) & Conᴺ-∘ₑ σ ν δᴺ ⁻¹
  Tmᴺ-nat (app f a) σ δᴺ rewrite Tmᴺ-nat f σ δᴺ | Tmᴺ-nat a σ δᴺ =
      (λ x → proj₁ (Tmᴺ f δᴺ) x (Tyᴺₑ σ (Tmᴺ a δᴺ))) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ proj₂ (Tmᴺ f δᴺ) idₑ σ (Tmᴺ a δᴺ)

Tmₑᴺ :
 ∀ {Γ Δ Σ A}(σ : OPE Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₑ σ t) δᴺ ≡ Tmᴺ t (OPEᴺ σ δᴺ)
Tmₑᴺ σ (var v)   δᴺ = proj₂ & OPEᴺ-∘ₑ v σ δᴺ
Tmₑᴺ σ (lam t)   δᴺ = ⇒ᴺ≡ λ ν aᴺ →
  Tmₑᴺ (keep σ) t (Conᴺₑ ν δᴺ , aᴺ) ◾ (λ x → Tmᴺ t (x , aᴺ)) & OPEᴺ-nat σ ν δᴺ
Tmₑᴺ σ (app f a) δᴺ rewrite Tmₑᴺ σ f δᴺ | Tmₑᴺ σ a δᴺ = refl


-- Subᴺ {Γ}{Δ} σ : PSh 𝒪PE (Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
Subᴺ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
Subᴺ {Δ = ∙}    tt      δᴺ = tt
Subᴺ {Δ = Δ , A}(σ , t) δᴺ = Subᴺ σ δᴺ , Tmᴺ t δᴺ

Subᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : Sub Γ Δ)(δ : OPE Ξ Σ) νᴺ → Subᴺ σ (Conᴺₑ δ νᴺ) ≡ Conᴺₑ δ (Subᴺ σ νᴺ)
Subᴺ-nat {Δ = ∙}    tt      δ νᴺ = refl
Subᴺ-nat {Δ = Δ , A}(σ , t) δ νᴺ = _,_ & Subᴺ-nat σ δ νᴺ ⊗ Tmᴺ-nat t δ νᴺ

Subᴺ-ₛ∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Γ Σ)(νᴺ : Conᴺ Γ Δ)
  → Subᴺ (σ ₛ∘ₑ δ) νᴺ ≡ Subᴺ σ (OPEᴺ δ νᴺ)
Subᴺ-ₛ∘ₑ {Ξ = ∙}    tt      δ νᴺ = refl
Subᴺ-ₛ∘ₑ {Ξ = Ξ , A}(σ , t) δ νᴺ = _,_ & Subᴺ-ₛ∘ₑ σ δ νᴺ ⊗ Tmₑᴺ δ t νᴺ

Tmₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₛ σ t) δᴺ ≡ Tmᴺ t (Subᴺ σ δᴺ)
Tmₛᴺ σ (var (drop v)) δᴺ = Tmₛᴺ (proj₁ σ) (var v) δᴺ
Tmₛᴺ σ (var (keep v)) δᴺ = refl
Tmₛᴺ σ (lam t)   δᴺ = ⇒ᴺ≡ λ ν aᴺ →
    Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν δᴺ , aᴺ)
  ◾ (λ x → Tmᴺ t (x , aᴺ)) &
      (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν δᴺ , aᴺ)
    ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν δᴺ)
    ◾ Subᴺ-nat σ ν δᴺ)
Tmₛᴺ σ (app f a) δᴺ rewrite Tmₛᴺ σ f δᴺ | Tmₛᴺ σ a δᴺ = refl

Subᴺ-idₛ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Subᴺ idₛ σᴺ ≡ σᴺ
Subᴺ-idₛ {∙}     tt         = refl
Subᴺ-idₛ {Γ , A} (σᴺ , tᴺ) =
  (_, tᴺ) & (Subᴺ-ₛ∘ₑ idₛ wk (σᴺ , tᴺ) ◾ Subᴺ-idₛ (OPEᴺ idₑ σᴺ) ◾ OPEᴺ-idₑ σᴺ)

--------------------------------------------------------------------------------

mutual
  qᴺ : ∀ {A Γ} → Tyᴺ A Γ → Nf Γ A
  qᴺ {ι}     tᴺ       = tᴺ
  qᴺ {A ⇒ B} (tᴺ , _) = lam (qᴺ (tᴺ wk (uᴺ (var (keep ε)))))

  qᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(tᴺ : Tyᴺ A Γ) → Nfₑ σ (qᴺ tᴺ) ≡ qᴺ (Tyᴺₑ σ tᴺ)
  qᴺ-nat {ι}     σ tᴺ            = refl
  qᴺ-nat {A ⇒ B} σ (tᴺ , tᴺ-nat) =
    lam & (qᴺ-nat (keep σ) (tᴺ wk (uᴺ (var (keep ε))))
         ◾ qᴺ & (tᴺ-nat wk (keep σ) (uᴺ (var (keep ε))) ⁻¹
                ◾ tᴺ & (drop & (idlₑ σ ◾ idrₑ σ ⁻¹)) ⊗ (uᴺ-nat (keep σ) (var (keep ε))
                                                        ◾ uᴺ & (var & (keep & εη (ε ∘ₑ σ))) )))

  uᴺ : ∀ {A Γ} → Ne Γ A → Tyᴺ A Γ
  uᴺ {ι}     n = ne n
  uᴺ {A ⇒ B} n =
    (λ δ aᴺ → uᴺ (app (Neₑ δ n) (qᴺ aᴺ))) ,
    (λ σ δ aᴺ → (λ x y → uᴺ (app x y)) & (Ne-∘ₑ σ δ n ⁻¹) ⊗ qᴺ-nat δ aᴺ ⁻¹
              ◾ uᴺ-nat δ (app (Neₑ σ n) (qᴺ aᴺ)) ⁻¹)

  uᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(n : Ne Γ A) → Tyᴺₑ σ (uᴺ n) ≡ uᴺ (Neₑ σ n)
  uᴺ-nat {ι}     σ n = refl
  uᴺ-nat {A ⇒ B} σ n = ⇒ᴺ≡ λ δ aᴺ → (λ x → uᴺ (app x (qᴺ aᴺ))) & Ne-∘ₑ σ δ n

uConᴺ : ∀ {Γ} → Conᴺ Γ Γ
uConᴺ {∙}     = tt
uConᴺ {Γ , A} = Conᴺₑ wk uConᴺ , uᴺ (var (keep ε))

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tmᴺ t uConᴺ)

--------------------------------------------------------------------------------

_≈_ : ∀ {A Γ} → Tm Γ A → Tyᴺ A Γ → Set
_≈_ {ι}        t tᴺ       = t ~ ⌜ qᴺ tᴺ ⌝
_≈_ {A ⇒ B}{Γ} t (tᴺ , _) = ∀ {Δ}(σ : OPE Δ Γ){a aᴺ} → a ≈ aᴺ → app (Tmₑ σ t) a ≈ tᴺ σ aᴺ

infix 3 _≈_ _≈*_

data _≈*_ {Γ} : ∀ {Δ} → Sub Γ Δ → Conᴺ Δ Γ → Set where
  ∙   : _≈*_ tt tt
  _,_ : ∀ {A Δ σ δ}{t : Tm Γ A}{t' : Tyᴺ A Γ} → _≈*_ {Γ}{Δ} σ δ → t ≈ t'
        → _≈*_ {Γ}{Δ , A} (σ , t) (δ , t')

≈ₑ : ∀ {A Γ Δ}(σ : OPE Δ Γ){t}{t' : Tyᴺ A Γ} → t ≈ t' → Tmₑ σ t ≈ Tyᴺₑ σ t'
≈ₑ {ι}     σ {t}{tᴺ} t≈tᴺ = coe ((_ ~_) & (⌜⌝Nf-nat σ tᴺ ⁻¹)) (~ₑ σ t≈tᴺ)
≈ₑ {A ⇒ B} σ {t}{tᴺ} t≈tᴺ δ rewrite Tm-∘ₑ σ δ t ⁻¹ = t≈tᴺ (σ ∘ₑ δ)

≈*ₑ : ∀ {Γ Δ Σ}(σ : OPE Σ Γ){δ}{νᴺ : Conᴺ Δ Γ} → δ ≈* νᴺ → (δ ₛ∘ₑ σ) ≈* Conᴺₑ σ νᴺ
≈*ₑ σ ∙              = ∙
≈*ₑ σ (δ≈*νᴺ , t≈tᴺ) = ≈*ₑ σ δ≈*νᴺ , ≈ₑ σ t≈tᴺ

_~≈◾_ : ∀ {Γ A}{t t'}{tᴺ : Tyᴺ A Γ} → t ~ t' → t' ≈ tᴺ → t ≈ tᴺ
_~≈◾_ {A = ι}     p q = p ~◾ q
_~≈◾_ {A = A ⇒ B} p q = λ σ a≈aᴺ → app (~ₑ σ p) ~refl ~≈◾ q σ a≈aᴺ

⟦Tm⟧ : ∀ {Γ Δ A}(t : Tm Γ A){σ}{δᴺ : Conᴺ Γ Δ} → σ ≈* δᴺ → Tmₛ σ t ≈ Tmᴺ t δᴺ
⟦Tm⟧ (var (drop v)) (σ≈δᴺ , _) = ⟦Tm⟧ (var v) σ≈δᴺ
⟦Tm⟧ (var (keep v)) (σ≈δᴺ , p) = p
⟦Tm⟧ (lam t) {σ} {δ} σ≈δᴺ ν {a} {aᴺ} a≈aᴺ
  = coe ((app (lam (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t))) a ~_ ) & (βₑₛ σ ν t a ⁻¹))
    (β (Tmₑ (keep ν) (Tmₛ (keepₛ σ) t)) a)
  ~≈◾ ⟦Tm⟧ t (≈*ₑ ν σ≈δᴺ , a≈aᴺ)
⟦Tm⟧ (app f a) {σ} {δ} σ≈δᴺ
  rewrite Tm-idₑ (Tmₛ σ f) ⁻¹ = ⟦Tm⟧ f σ≈δᴺ idₑ (⟦Tm⟧ a σ≈δᴺ)

mutual
  q≈ : ∀ {Γ A}{t}{tᴺ : Tyᴺ A Γ} → t ≈ tᴺ → t ~ ⌜ qᴺ tᴺ ⌝
  q≈ {A = ι}     t≈tᴺ = t≈tᴺ
  q≈ {A = A ⇒ B} t≈tᴺ = η _ ~◾ lam (q≈ (t≈tᴺ wk (u≈ (var (keep ε)))))

  u≈ : ∀ {Γ A}(n : Ne Γ A) → ⌜ n ⌝Ne ≈ uᴺ n
  u≈ {A = ι}     n = ~refl
  u≈ {A = A ⇒ B} n σ {a} {aᴺ} a≈aᴺ
    rewrite ⌜⌝Ne-nat σ n ⁻¹ = app ~refl (q≈ a≈aᴺ) ~≈◾ u≈ (app (Neₑ σ n) (qᴺ aᴺ))

u≈*  : ∀ {Γ} → idₛ {Γ} ≈* uConᴺ
u≈* {∙}     = ∙
u≈* {Γ , A} = ≈*ₑ wk u≈* , u≈ (var (keep ε))

complete : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝
complete t = coe ((_~ ⌜ qᴺ (Tmᴺ t uConᴺ) ⌝) & Tm-idₛ t) (q≈ (⟦Tm⟧ t u≈*))

⟦~⟧ : ∀ {Γ Δ A}{t t' : Tm Γ A} → t ~ t' → (σ : Conᴺ Γ Δ) → Tmᴺ t σ ≡ Tmᴺ t' σ
⟦~⟧ (η t) σ = ⇒ᴺ≡ λ {Σ} ν aᴺ →
    (λ x → proj₁ (Tmᴺ t σ) x aᴺ) & (idrₑ ν ⁻¹)
  ◾ (λ x → proj₁ x idₑ aᴺ) &
        (Tmₑᴺ wk t (Conᴺₑ ν σ , aᴺ)
      ◾ Tmᴺ t & OPEᴺ-idₑ (Conᴺₑ ν σ)
      ◾ Tmᴺ-nat t ν σ) ⁻¹
⟦~⟧ (β t t')         σ = (λ x → Tmᴺ t (x , Tmᴺ t' σ)) & (Conᴺ-idₑ σ ◾ Subᴺ-idₛ σ ⁻¹) ◾ Tmₛᴺ (idₛ , t') t σ ⁻¹
⟦~⟧ (lam t~t')       σ = ⇒ᴺ≡ λ {Σ} ν aᴺ → ⟦~⟧ t~t' (Conᴺₑ ν σ , aᴺ)
⟦~⟧ (app t~t' a~a')  σ = (λ f a → proj₁ f idₑ a) & ⟦~⟧ t~t' σ ⊗ ⟦~⟧ a~a' σ
⟦~⟧ ~refl            σ = refl
⟦~⟧ (t'~t ~⁻¹)       σ = ⟦~⟧ t'~t σ ⁻¹
⟦~⟧ (t~t' ~◾ t'~t'') σ = ⟦~⟧ t~t' σ ◾ ⟦~⟧ t'~t'' σ

sound : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
sound t~t' = qᴺ & ⟦~⟧ t~t' uConᴺ

mutual
  stab : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
  stab (ne n)  = stabNe n
  stab (lam n) = lam & stab n

  stabNe : ∀ {Γ A}(n : Ne Γ A) → Tmᴺ ⌜ n ⌝Ne uConᴺ ≡ uᴺ n
  stabNe (var (drop v)) =
      proj₂ & OPEᴺ-nat v wk uConᴺ
    ◾ Tyᴺₑ wk & stabNe (var v)
    ◾ uᴺ-nat wk (var v)
    ◾ uᴺ & (var & (drop & idrₑ v))
  stabNe (var (keep v)) = uᴺ & (var & (keep & (εη v ⁻¹)))
  stabNe (app f a) =
      (λ x → proj₁ x idₑ (Tmᴺ ⌜ a ⌝ uConᴺ)) & stabNe f
    ◾ (λ x → uᴺ (app (Neₑ idₑ f) x)) & stab a
    ◾ (λ x → uᴺ (app x a)) & Ne-idₑ f
