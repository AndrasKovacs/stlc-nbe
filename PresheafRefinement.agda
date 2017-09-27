{-# OPTIONS --without-K #-}

module PresheafRefinement where

open import Lib
open import Syntax
open import Embedding
open import Substitution
open import NormalForm
open import Normalization

--------------------------------------------------------------------------------

Tyᴺ-idₑ : ∀ {Γ A}(tᴺ : Tyᴺ A Γ) → Tyᴺₑ idₑ tᴺ ≡ tᴺ
Tyᴺ-idₑ {A = ι}     tᴺ = Nf-idₑ tᴺ
Tyᴺ-idₑ {A = A ⇒ B} tᴺ = fexti λ Δ → fext λ δ → tᴺ & idlₑ δ

Tyᴺ-∘ₑ :
  ∀ {Γ Δ Σ A}(tᴺ : Tyᴺ A Σ)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  → Tyᴺₑ (σ ∘ₑ δ) tᴺ ≡ Tyᴺₑ δ (Tyᴺₑ σ tᴺ)
Tyᴺ-∘ₑ {A = ι}     tᴺ σ δ = Nf-∘ₑ σ δ tᴺ
Tyᴺ-∘ₑ {A = A ⇒ B} tᴺ σ δ = fexti λ Ξ → fext λ ν → tᴺ & assₑ σ δ ν

Conᴺ-idₑ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Conᴺₑ idₑ σᴺ ≡ σᴺ
Conᴺ-idₑ ∙        = refl
Conᴺ-idₑ (σᴺ , t) = _,_ & Conᴺ-idₑ σᴺ ⊗ Tyᴺ-idₑ t

Conᴺ-∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(ν : Conᴺ Ξ Σ)
  → Conᴺₑ (σ ∘ₑ δ) ν ≡ Conᴺₑ δ (Conᴺₑ σ ν)
Conᴺ-∘ₑ σ δ ∙       = refl
Conᴺ-∘ₑ σ δ (ν , t) = _,_ & Conᴺ-∘ₑ σ δ ν ⊗ Tyᴺ-∘ₑ t σ δ

∈ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : OPE Σ Δ) Γᴺ → ∈ᴺ v (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ σ (∈ᴺ v Γᴺ)
∈ᴺ-nat vz     σ (Γᴺ , _) = refl
∈ᴺ-nat (vs v) σ (Γᴺ , _) = ∈ᴺ-nat v σ Γᴺ

--------------------------------------------------------------------------------

Tyᴾ : ∀ {Γ A} → Tyᴺ A Γ → Set
Tyᴾ {Γ} {ι}     tᴺ = ⊤
Tyᴾ {Γ} {A ⇒ B} tᴺ =
  ∀ {Δ}(σ : OPE Δ Γ) {aᴺ : Tyᴺ A Δ} → Tyᴾ aᴺ
  → (∀ {Σ} (δ : OPE Σ Δ) → tᴺ (σ ∘ₑ δ) (Tyᴺₑ δ aᴺ) ≡ Tyᴺₑ δ (tᴺ σ aᴺ))
    × Tyᴾ (tᴺ σ aᴺ)

Tyᴾₑ : ∀ {A Γ Δ}(σ : OPE Δ Γ) → ∀ {tᴺ : Tyᴺ A Γ} → Tyᴾ tᴺ → Tyᴾ (Tyᴺₑ σ tᴺ)
Tyᴾₑ {ι}     σ {tᴺ} tᴾ           = tt
Tyᴾₑ {A ⇒ B} σ {tᴺ} tᴾ δ {aᴺ} aᴾ = let tᴺ-nat , taᴾ = tᴾ (σ ∘ₑ δ) aᴾ in
  (λ ν → (λ x → tᴺ x (Tyᴺₑ ν aᴺ)) & (assₑ σ δ ν ⁻¹) ◾ tᴺ-nat ν) , taᴾ

data Conᴾ : ∀ {Γ Δ} → Conᴺ Γ Δ → Set where
  ∙   : ∀ {Δ} → Conᴾ {∙} {Δ} ∙
  _,_ : ∀ {Γ Δ A Γᴺ tᴺ} → Conᴾ {Γ}{Δ} Γᴺ → Tyᴾ {Δ}{A} tᴺ → Conᴾ (Γᴺ , tᴺ)

Conᴾₑ : ∀ {Γ Δ Σ Γᴺ}(σ : OPE Σ Δ) → Conᴾ {Γ}{Δ} Γᴺ → Conᴾ {Γ}{Σ} (Conᴺₑ σ Γᴺ)
Conᴾₑ σ ∙         =  ∙
Conᴾₑ σ (Γᴾ , tᴾ) = Conᴾₑ σ Γᴾ , Tyᴾₑ σ tᴾ

∈ᴾ : ∀ {Γ A}(v : A ∈ Γ) → ∀ {Δ}{Γᴺ : Conᴺ Γ Δ}(Γᴾ : Conᴾ Γᴺ) → Tyᴾ (∈ᴺ v Γᴺ)
∈ᴾ vz     (Γᴾ , tᴾ) = tᴾ
∈ᴾ (vs v) (Γᴾ , _ ) = ∈ᴾ v Γᴾ

mutual
  Tmᴾ : ∀ {Γ A}(t : Tm Γ A) → ∀ {Δ}{Γᴺ : Conᴺ Γ Δ}(Γᴾ : Conᴾ Γᴺ) → Tyᴾ (Tmᴺ t Γᴺ)
  Tmᴾ (var v) Γᴾ = ∈ᴾ v Γᴾ
  Tmᴾ (lam t) Γᴾ = λ σ {aᴺ} aᴾ →
    (λ δ → (λ x → Tmᴺ t (x , Tyᴺₑ δ aᴺ)) & Conᴺ-∘ₑ σ δ _ ◾ Tmᴺ-nat t δ (Conᴾₑ σ Γᴾ , aᴾ))
    , Tmᴾ t (Conᴾₑ σ Γᴾ , aᴾ)
  Tmᴾ (app f x) Γᴾ = proj₂ (Tmᴾ f Γᴾ idₑ (Tmᴾ x Γᴾ))

  Tmᴺ-nat : ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : OPE Σ Δ) {Γᴺ} → Conᴾ Γᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ σ (Tmᴺ t Γᴺ)
  Tmᴺ-nat (var v)   σ {Γᴺ} Γᴾ = ∈ᴺ-nat v σ _
  Tmᴺ-nat (lam t)   σ {Γᴺ} Γᴾ =
    fexti λ Ξ → fext λ ν → fext λ aᴺ → Tmᴺ t & ((_, aᴺ) & (Conᴺ-∘ₑ σ ν Γᴺ ⁻¹ ))
  Tmᴺ-nat (app f x) σ {Γᴺ} Γᴾ rewrite Tmᴺ-nat f σ Γᴾ | Tmᴺ-nat x σ Γᴾ =
    (λ y → Tmᴺ f Γᴺ y (Tyᴺₑ σ (Tmᴺ x Γᴺ))) & (idrₑ σ ◾ idlₑ σ ⁻¹) ◾ proj₁ (Tmᴾ f Γᴾ idₑ (Tmᴾ x Γᴾ)) σ

mutual
  uᴾ : ∀ {A Γ}(n : Ne Γ A) → Tyᴾ (uᴺ n)
  uᴾ {ι}     n = tt
  uᴾ {A ⇒ B} n = λ σ {aᴺ} aᴾ →
    (λ {Δ} δ → (λ x y → uᴺ (app x y)) & (Ne-∘ₑ σ δ n ⁻¹) ⊗ qᴺ-nat δ aᴺ aᴾ ⁻¹
             ◾ uᴺ-nat δ (app (Neₑ σ n) (qᴺ aᴺ)) ⁻¹)
    , uᴾ (app (Neₑ σ n) (qᴺ aᴺ))

  qᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(tᴺ : Tyᴺ A Γ) → Tyᴾ tᴺ → Nfₑ σ (qᴺ tᴺ) ≡ qᴺ (Tyᴺₑ σ tᴺ)
  qᴺ-nat {ι}     σ tᴺ tᴾ = refl
  qᴺ-nat {A ⇒ B} σ tᴺ tᴾ = let tᴺ-nat , taᴾ = tᴾ wk (uᴾ (var vz)) in
    lam & (qᴺ-nat (keep σ) (tᴺ wk (uᴺ (var vz))) taᴾ
         ◾ qᴺ & (tᴺ-nat (keep σ) ⁻¹
               ◾ tᴺ & (drop & (idlₑ σ ◾ idrₑ σ ⁻¹)) ⊗ uᴺ-nat (keep σ) (var vz)))

  uᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(n : Ne Γ A) → Tyᴺₑ σ (uᴺ n) ≡ uᴺ (Neₑ σ n)
  uᴺ-nat {ι}     σ n = refl
  uᴺ-nat {A ⇒ B} σ n = fexti λ Σ → fext λ δ → fext λ aᴺ →
    (λ x → uᴺ (app x (qᴺ aᴺ))) & Ne-∘ₑ σ δ n

uᶜᴾ : ∀ {Γ} → Conᴾ (uᶜᴺ {Γ})
uᶜᴾ {∙}     = ∙
uᶜᴾ {Γ , A} = Conᴾₑ wk uᶜᴾ , uᴾ (var vz)

--------------------------------------------------------------------------------

OPEᴺ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
OPEᴺ ∙         Γᴺ       = Γᴺ
OPEᴺ (drop σ) (Γᴺ , _)  = OPEᴺ σ Γᴺ
OPEᴺ (keep σ) (Γᴺ , tᴺ) = OPEᴺ σ Γᴺ , tᴺ

OPEᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : OPE Γ Δ)(δ : OPE Ξ Σ) Γᴺ → OPEᴺ σ (Conᴺₑ δ Γᴺ) ≡ Conᴺₑ δ (OPEᴺ σ Γᴺ)
OPEᴺ-nat ∙        δ  Γᴺ       = refl
OPEᴺ-nat (drop σ) δ (Γᴺ , tᴺ) = OPEᴺ-nat σ δ Γᴺ
OPEᴺ-nat (keep σ) δ (Γᴺ , tᴺ) = (_, Tyᴺₑ δ tᴺ) & OPEᴺ-nat σ δ Γᴺ

OPEᴺ-idₑ : ∀ {Γ Δ}(Γᴺ : Conᴺ Γ Δ) → OPEᴺ idₑ Γᴺ ≡ Γᴺ
OPEᴺ-idₑ ∙         = refl
OPEᴺ-idₑ (Γᴺ , tᴺ) = (_, tᴺ) & OPEᴺ-idₑ Γᴺ

∈ₑᴺ :
 ∀ {Γ Δ Σ A}(σ : OPE Δ Γ)(v : A ∈ Γ)(Γᴺ : Conᴺ Δ Σ)
 → ∈ᴺ (∈ₑ σ v) Γᴺ ≡ ∈ᴺ v (OPEᴺ σ Γᴺ)
∈ₑᴺ ∙        v      Γᴺ        = refl
∈ₑᴺ (drop σ) v      (Γᴺ , _)  = ∈ₑᴺ σ v Γᴺ
∈ₑᴺ (keep σ) vz     (Γᴺ , tᴺ) = refl
∈ₑᴺ (keep σ) (vs v) (Γᴺ , tᴺ) = ∈ₑᴺ σ v Γᴺ

Tmₑᴺ :
 ∀ {Γ Δ Σ A}(σ : OPE Δ Γ)(t : Tm Γ A)(Γᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₑ σ t) Γᴺ ≡ Tmᴺ t (OPEᴺ σ Γᴺ)
Tmₑᴺ σ (var v)   Γᴺ = ∈ₑᴺ σ v Γᴺ
Tmₑᴺ σ (lam t)   Γᴺ = fexti λ Ξ → fext λ ν → fext λ aᴺ →
  Tmₑᴺ (keep σ) t (Conᴺₑ ν Γᴺ , aᴺ) ◾ ((λ x → Tmᴺ t (x , aᴺ)) & OPEᴺ-nat σ ν Γᴺ)
Tmₑᴺ σ (app f a) Γᴺ rewrite Tmₑᴺ σ f Γᴺ | Tmₑᴺ σ a Γᴺ = refl

--------------------------------------------------------------------------------

Subᴺ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
Subᴺ ∙       Γᴺ = ∙
Subᴺ (σ , t) Γᴺ = Subᴺ σ Γᴺ , Tmᴺ t Γᴺ

Subᴺ-nat :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Γ Δ)(δ : OPE Ξ Σ) Γᴺ → Conᴾ Γᴺ → Subᴺ σ (Conᴺₑ δ Γᴺ) ≡ Conᴺₑ δ (Subᴺ σ Γᴺ)
Subᴺ-nat ∙       δ Γᴺ Γᴾ = refl
Subᴺ-nat (σ , t) δ Γᴺ Γᴾ = _,_ & Subᴺ-nat σ δ Γᴺ Γᴾ ⊗ Tmᴺ-nat t δ Γᴾ

Subᴺ-ₛ∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Γ Σ)(Γᴺ : Conᴺ Γ Δ)
  → Subᴺ (σ ₛ∘ₑ δ) Γᴺ ≡ Subᴺ σ (OPEᴺ δ Γᴺ)
Subᴺ-ₛ∘ₑ ∙       δ Γᴺ = refl
Subᴺ-ₛ∘ₑ (σ , t) δ Γᴺ = _,_ & Subᴺ-ₛ∘ₑ σ δ Γᴺ ⊗ Tmₑᴺ δ t Γᴺ

∈ₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(v : A ∈ Γ)(Γᴺ : Conᴺ Δ Σ) → Tmᴺ (∈ₛ σ v) Γᴺ ≡ ∈ᴺ v (Subᴺ σ Γᴺ)
∈ₛᴺ (σ , t) vz     Γᴺ = refl
∈ₛᴺ (σ , _) (vs v) Γᴺ = ∈ₛᴺ σ v Γᴺ

Subᴺ-idₛ : ∀ {Γ Δ}(Γᴺ : Conᴺ Γ Δ) → Subᴺ idₛ Γᴺ ≡ Γᴺ
Subᴺ-idₛ ∙         = refl
Subᴺ-idₛ (Γᴺ , tᴺ) =
  (_, tᴺ) & (Subᴺ-ₛ∘ₑ idₛ wk (Γᴺ , tᴺ) ◾ Subᴺ-idₛ (OPEᴺ idₑ Γᴺ) ◾ OPEᴺ-idₑ Γᴺ)
