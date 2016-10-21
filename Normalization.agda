
module Normalization where

open import Lib
open import UIP
open import Syntax
open import Renaming
open import Substitution
open import Nf

infixr 6 _ᴺ∘ᵣ_
infixl 8 _ᴺ[_]ᵣ

mutual
  Tmᴺ : Con → Ty → Set
  Tmᴺ Γ ι       = Nf Γ ι
  Tmᴺ Γ (A ⇒ B) =
    Σ (∀ {Δ} → Ren Δ Γ → Tmᴺ Δ A → Tmᴺ Δ B) λ f →
    ∀ {Δ Σ}(σ : Ren Δ Γ)(δ : Ren Σ Δ)(a : Tmᴺ Δ A) → f σ a ᴺ[ δ ]ᵣ ≡ f (σ ∘ᵣ δ) (a ᴺ[ δ ]ᵣ)

  _ᴺ[_]ᵣ : ∀ {A Γ Δ} → Tmᴺ Γ A → Ren Δ Γ → Tmᴺ Δ A
  _ᴺ[_]ᵣ {ι}     = _[_]ₙᵣ
  _ᴺ[_]ᵣ {A ⇒ B} = λ fᴺ σ →
    (λ δ → proj₁ fᴺ (σ ∘ᵣ δ)) ,
    (λ δ ν aᴺ → proj₂ fᴺ (σ ∘ᵣ δ) ν aᴺ
              ◾ (λ x → proj₁ fᴺ x (aᴺ ᴺ[ ν ]ᵣ)) & assᵣ σ δ ν)

⇒ᴺ= :
  ∀ {Γ A B}{f f' : Tmᴺ Γ (A ⇒ B)}
  → (∀ {Δ}(σ : Ren Δ Γ) a → proj₁ f σ a ≡ proj₁ f' σ a)
  → f ≡ f'
⇒ᴺ= {f = f}{f'} eq = ,Σ=
  (funexti λ Δ → funext λ σ → funext λ aᴺ → eq σ aᴺ )
  (funexti λ _ → funexti λ _ → funext λ _ → funext λ _ → funext λ _ → UIP _ _)

data Tmsᴺ (Γ : Con) : Con → Set where
  ∙   : Tmsᴺ Γ ∙
  _,_ : ∀ {A Δ} (σ : Tmsᴺ Γ Δ)(t : Tmᴺ Γ A) → Tmsᴺ Γ (Δ , A)
infixr 5 _,_

_ᴺ∘ᵣ_ : ∀ {Γ Δ Σ} → Tmsᴺ Δ Σ → Ren Γ Δ → Tmsᴺ Γ Σ
∙       ᴺ∘ᵣ δ = ∙
(σ , t) ᴺ∘ᵣ δ = (σ ᴺ∘ᵣ δ) , (t ᴺ[ δ ]ᵣ)

ᴺ∘ᵣTm :
  ∀ {Γ Δ Σ A}(t : Tmᴺ Σ A)(σ : Ren Δ Σ)(δ : Ren Γ Δ)
  → t ᴺ[ σ ]ᵣ ᴺ[ δ ]ᵣ ≡ t ᴺ[ σ ∘ᵣ δ ]ᵣ
ᴺ∘ᵣTm {A = ι}     t σ δ = ∘ᵣNf t σ δ
ᴺ∘ᵣTm {A = A ⇒ B} t σ δ = ⇒ᴺ= (λ ν aᴺ → (λ x → proj₁ t x aᴺ) & (assᵣ σ δ ν ⁻¹))

assₙᵣᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tmsᴺ Σ Ξ)(δ : Ren Δ Σ)(ν : Ren Γ Δ)
  → (σ ᴺ∘ᵣ δ) ᴺ∘ᵣ ν ≡ σ ᴺ∘ᵣ (δ ∘ᵣ ν)
assₙᵣᵣ ∙       δ ν = refl
assₙᵣᵣ (σ , t) δ ν = _,_ & assₙᵣᵣ σ δ ν ⊗ ᴺ∘ᵣTm t δ ν

∈↑ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Tmsᴺ Δ Γ → Tmᴺ Δ A
∈↑ᴺ vz     (σ , t) = t
∈↑ᴺ (vs v) (σ , t) = ∈↑ᴺ v σ

∈↑ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σ : Tmsᴺ Δ Σ)(δ : Ren Γ Δ) → ∈↑ᴺ v (σ ᴺ∘ᵣ δ) ≡ ∈↑ᴺ v σ ᴺ[ δ ]ᵣ
∈↑ᴺ-nat vz     (σ , t) δ = refl
∈↑ᴺ-nat (vs v) (σ , t) δ = ∈↑ᴺ-nat v σ δ

appᴺ : ∀ {Γ A B} → Tmᴺ Γ (A ⇒ B) → Tmᴺ Γ A → Tmᴺ Γ B
appᴺ f a = proj₁ f idᵣ a

mutual
  Tm↑ᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Tmsᴺ Δ Γ → Tmᴺ Δ A
  Tm↑ᴺ (var v)   σ = ∈↑ᴺ v σ
  Tm↑ᴺ (lam t)   σ =
      (λ δ aᴺ → Tm↑ᴺ t (σ ᴺ∘ᵣ δ , aᴺ))
    , (λ δ ν aᴺ →
          Tm↑ᴺ-nat t (σ ᴺ∘ᵣ δ , aᴺ) ν ⁻¹
        ◾ (λ x → Tm↑ᴺ t (x , aᴺ ᴺ[ ν ]ᵣ)) & assₙᵣᵣ σ δ ν)
  Tm↑ᴺ (app f a) σ = appᴺ (Tm↑ᴺ f σ) (Tm↑ᴺ a σ)

  Tm↑ᴺ-nat :
    ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : Tmsᴺ Σ Γ)(δ : Ren Δ Σ)
    → Tm↑ᴺ t (σ ᴺ∘ᵣ δ) ≡ Tm↑ᴺ t σ ᴺ[ δ ]ᵣ
  Tm↑ᴺ-nat (var v)   σ δ = ∈↑ᴺ-nat v σ δ
  Tm↑ᴺ-nat (lam t)   σ δ = ⇒ᴺ= (λ ν aᴺ → (λ x → Tm↑ᴺ t (x , aᴺ)) & assₙᵣᵣ σ δ ν )
  Tm↑ᴺ-nat (app f a) σ δ
    rewrite proj₁ & Tm↑ᴺ-nat f σ δ | Tm↑ᴺ-nat a σ δ
    = (λ x → proj₁ (Tm↑ᴺ f σ) x (Tm↑ᴺ a σ ᴺ[ δ ]ᵣ)) & (idrᵣ δ ◾ idlᵣ δ ⁻¹)
     ◾ proj₂ (Tm↑ᴺ f σ) idᵣ δ (Tm↑ᴺ a σ) ⁻¹

mutual
  qᴺ : ∀ {Γ A} → Tmᴺ Γ A → Nf Γ A
  qᴺ {A = ι}     t = t
  qᴺ {A = A ⇒ B} t = lam (qᴺ (proj₁ t wk (uᴺ (var vz))))

  qᴺ-nat : ∀ {A Γ Δ}(tᴺ : Tmᴺ Γ A)(σ : Ren Δ Γ) → qᴺ tᴺ [ σ ]ₙᵣ ≡ qᴺ (tᴺ ᴺ[ σ ]ᵣ)
  qᴺ-nat {ι}     tᴺ        σ = refl
  qᴺ-nat {A ⇒ B} (f , nat) σ = lam &
      (qᴺ-nat (f wk (uᴺ (var vz))) (keep σ)
    ◾ qᴺ &
        (nat (drop idᵣ) (keep σ) (uᴺ (var vz))
      ◾ (λ x → f (drop x) (uᴺ (var vz) ᴺ[ keep σ ]ᵣ)) & (idlᵣ σ ◾ idrᵣ σ ⁻¹)
      ◾ f (drop (σ ∘ᵣ idᵣ)) & uᴺ-nat (var vz) (keep σ)))

  uᴺ : ∀ {Γ A} → Ne Γ A → Tmᴺ Γ A
  uᴺ {A = ι}     n = ne n
  uᴺ {A = A ⇒ B} n =
    (λ δ aᴺ → uᴺ (app (n [ δ ]ₙₑᵣ) (qᴺ aᴺ))) ,
    (λ σ δ aᴺ →
        uᴺ-nat (app (n [ σ ]ₙₑᵣ) (qᴺ aᴺ)) δ
      ◾ (λ x → uᴺ (app x (qᴺ aᴺ [ δ ]ₙᵣ))) & ∘ᵣNe n σ δ
      ◾ (λ x → uᴺ (app (n [ σ ∘ᵣ δ ]ₙₑᵣ) x)) & qᴺ-nat aᴺ δ)

  uᴺ-nat : ∀ {A Γ Δ} → (n : Ne Γ A) → (σ : Ren Δ Γ) → uᴺ n ᴺ[ σ ]ᵣ ≡ uᴺ (n [ σ ]ₙₑᵣ)
  uᴺ-nat {ι}     n σ = refl
  uᴺ-nat {A ⇒ B} n σ = ⇒ᴺ= (λ δ aᴺ → (λ x → uᴺ (app x (qᴺ aᴺ))) & ∘ᵣNe n σ δ ⁻¹)

idᴺₛ : ∀ {Γ} → Tmsᴺ Γ Γ
idᴺₛ {∙}     = ∙
idᴺₛ {Γ , t} = idᴺₛ {Γ} ᴺ∘ᵣ wk , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tm↑ᴺ t idᴺₛ)

--------------------------------------------------------------------------------

infixr 6 _ₛ∘ᴺ_
_ₛ∘ᴺ_ : ∀ {Γ Δ Σ} → Tms Γ Δ → Tmsᴺ Σ Γ → Tmsᴺ Σ Δ
∙       ₛ∘ᴺ δ = ∙
(σ , t) ₛ∘ᴺ δ = (σ ₛ∘ᴺ δ) , Tm↑ᴺ t δ

idᵣTmᴺ : ∀ {Γ A}(t : Tmᴺ Γ A) → t ᴺ[ idᵣ ]ᵣ ≡ t
idᵣTmᴺ {A = ι}     t = ⌜⌝-inj (⌜⌝ᵣ t idᵣ ◾ idᵣTm ⌜ t ⌝)
idᵣTmᴺ {A = A ⇒ B} t = ⇒ᴺ= λ σ aᴺ → (λ x → proj₁ t x aᴺ) & idlᵣ σ

idrᴺᵣ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → σ ᴺ∘ᵣ idᵣ ≡ σ
idrᴺᵣ ∙       = refl
idrᴺᵣ (σ , t) = _,_ & idrᴺᵣ σ ⊗ idᵣTmᴺ t

infixr 6 _ᵣ∘ᴺ_
_ᵣ∘ᴺ_ : ∀ {Γ Δ Σ} → Ren Γ Δ → Tmsᴺ Σ Γ → Tmsᴺ Σ Δ
∙      ᵣ∘ᴺ δ       = δ
drop σ ᵣ∘ᴺ (δ , t) = σ ᵣ∘ᴺ δ
keep σ ᵣ∘ᴺ (δ , t) = (σ ᵣ∘ᴺ δ) , t

∈↑ᴺ-nat₁ :
  ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : Ren Δ Γ)(δ : Tmsᴺ Σ Δ)
  → ∈↑ᴺ (v [ σ ]∈ᵣ) δ ≡ ∈↑ᴺ v (σ ᵣ∘ᴺ δ)
∈↑ᴺ-nat₁ ()     ∙        δ
∈↑ᴺ-nat₁ v      (drop σ) (δ , t) = ∈↑ᴺ-nat₁ v σ δ
∈↑ᴺ-nat₁ vz     (keep σ) (δ , t) = refl
∈↑ᴺ-nat₁ (vs v) (keep σ) (δ , t) = ∈↑ᴺ-nat₁ v σ δ

assᵣᴺᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Ren Σ Ξ)(δ : Tmsᴺ Δ Σ)(ν : Ren Γ Δ)
  → (σ ᵣ∘ᴺ δ) ᴺ∘ᵣ ν ≡ σ ᵣ∘ᴺ δ ᴺ∘ᵣ ν
assᵣᴺᵣ ∙        δ       ν = refl
assᵣᴺᵣ (drop σ) (δ , t) ν = assᵣᴺᵣ σ δ ν
assᵣᴺᵣ (keep σ) (δ , t) ν = (_, t ᴺ[ ν ]ᵣ) & assᵣᴺᵣ σ δ ν

Tm↑ᴺ-nat₁ :
  ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : Ren Δ Γ)(δ : Tmsᴺ Σ Δ)
  → Tm↑ᴺ (t [ σ ]ᵣ) δ ≡ Tm↑ᴺ t (σ ᵣ∘ᴺ δ)
Tm↑ᴺ-nat₁ (var v)   σ δ = ∈↑ᴺ-nat₁ v σ δ
Tm↑ᴺ-nat₁ (lam t)   σ δ = ⇒ᴺ= λ ν aᴺ →
    Tm↑ᴺ-nat₁ t (keep σ) (δ ᴺ∘ᵣ ν , aᴺ)
  ◾ (λ x → Tm↑ᴺ t (x , aᴺ)) & (assᵣᴺᵣ σ δ ν ⁻¹)
Tm↑ᴺ-nat₁ (app f a) σ δ
  rewrite Tm↑ᴺ-nat₁ f σ δ | Tm↑ᴺ-nat₁ a σ δ = refl

idlᴺᵣ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → idᵣ ᵣ∘ᴺ σ ≡ σ
idlᴺᵣ ∙       = refl
idlᴺᵣ (σ , t) = (_, t) & idlᴺᵣ σ

assₛᵣᴺ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Ren Δ Σ)(ν : Tmsᴺ Γ Δ)
  → (σ ₛ∘ᵣ δ) ₛ∘ᴺ ν ≡ σ ₛ∘ᴺ δ ᵣ∘ᴺ ν
assₛᵣᴺ ∙       δ ν = refl
assₛᵣᴺ (σ , t) δ ν = _,_ & assₛᵣᴺ σ δ ν ⊗ Tm↑ᴺ-nat₁ t δ ν

assₛᴺᵣ :
  ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tmsᴺ Δ Σ)(ν : Ren Γ Δ)
  → (σ ₛ∘ᴺ δ) ᴺ∘ᵣ ν ≡ σ ₛ∘ᴺ δ ᴺ∘ᵣ ν
assₛᴺᵣ ∙       δ ν = refl
assₛᴺᵣ (σ , t) δ ν = _,_ & assₛᴺᵣ σ δ ν ⊗ (Tm↑ᴺ-nat t δ ν ⁻¹)

idlᴺₛ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → σ ≡ idₛ ₛ∘ᴺ σ
idlᴺₛ ∙       = refl
idlᴺₛ (σ , t) =
  (_, t) & (((idlᴺᵣ σ ⁻¹ ◾ idlᴺₛ (idᵣ ᵣ∘ᴺ σ)) ◾ assₛᵣᴺ idₛ wk (σ , t) ⁻¹))

ₛ∘ᴺ∈↑ :
  ∀ {Γ Δ Σ A}(v : A ∈ Δ)(σ : Tms Γ Δ)(δ : Tmsᴺ Σ Γ)
  → Tm↑ᴺ (v [ σ ]∈) δ ≡ ∈↑ᴺ v (σ ₛ∘ᴺ δ)
ₛ∘ᴺ∈↑ vz     (σ , t) δ = refl
ₛ∘ᴺ∈↑ (vs v) (σ , t) δ = ₛ∘ᴺ∈↑ v σ δ

ₛ∘ᴺ↑ :
  ∀ {Γ Δ Σ A}(t : Tm Δ A)(σ : Tms Γ Δ)(δ : Tmsᴺ Σ Γ)
  → Tm↑ᴺ (t [ σ ]) δ ≡ Tm↑ᴺ t (σ ₛ∘ᴺ δ)
ₛ∘ᴺ↑ (var v)   σ δ = ₛ∘ᴺ∈↑ v σ δ
ₛ∘ᴺ↑ (lam t)   σ δ = ⇒ᴺ= λ ν aᴺ →
    ₛ∘ᴺ↑ t (keepₛ σ) (δ ᴺ∘ᵣ ν , aᴺ)
  ◾ (λ x → Tm↑ᴺ t ((x , aᴺ))) &
      (assₛᵣᴺ σ wk (δ ᴺ∘ᵣ ν , aᴺ)
    ◾ (σ ₛ∘ᴺ_) & idlᴺᵣ (δ ᴺ∘ᵣ ν)
    ◾ assₛᴺᵣ σ δ ν ⁻¹)
ₛ∘ᴺ↑ (app f a) σ δ
  rewrite ₛ∘ᴺ↑ f σ δ | ₛ∘ᴺ↑ a σ δ = refl

