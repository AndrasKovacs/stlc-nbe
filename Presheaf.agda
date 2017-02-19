{-# OPTIONS --without-K #-}

module Presheaf where

open import Lib
open import UIP
open import Syntax
open import Embedding
open import Substitution
open import Nf

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
data Conᴺ : Con → Con → Set where
  ∙   : ∀ {Γ} → Conᴺ ∙ Γ
  _,_ : ∀ {A Γ Δ} (σ : Conᴺ Γ Δ)(t : Tyᴺ A Δ) → Conᴺ (Γ , A) Δ
infixr 5 _,_

Conᴺₑ : ∀ {Γ Δ} → OPE Δ Γ → ∀ {Σ} → Conᴺ Σ Γ → Conᴺ Σ Δ
Conᴺₑ σ ∙        = ∙
Conᴺₑ σ (δ , tᴺ) = Conᴺₑ σ δ , Tyᴺₑ σ tᴺ

Conᴺ-idₑ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Conᴺₑ idₑ σᴺ ≡ σᴺ
Conᴺ-idₑ ∙        = refl
Conᴺ-idₑ (σᴺ , t) = _,_ & Conᴺ-idₑ σᴺ ⊗ Tyᴺ-idₑ t

Conᴺ-∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(ν : Conᴺ Ξ Σ)
  → Conᴺₑ (σ ∘ₑ δ) ν ≡ Conᴺₑ δ (Conᴺₑ σ ν)  
Conᴺ-∘ₑ σ δ ∙       = refl
Conᴺ-∘ₑ σ δ (ν , t) = _,_ & Conᴺ-∘ₑ σ δ ν ⊗ Tyᴺ-∘ₑ t σ δ

-- ∈ᴺ {Γ}{A} v : PSh(Conᴺ Γ, Tyᴺ A)
--------------------------------------------------------------------------------
∈ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (σ , t) = t
∈ᴺ (vs v) (σ , t) = ∈ᴺ v σ

∈ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : OPE Σ Δ) δᴺ → ∈ᴺ v (Conᴺₑ σ δᴺ) ≡ Tyᴺₑ σ (∈ᴺ v δᴺ)
∈ᴺ-nat vz     σ (δᴺ , _) = refl
∈ᴺ-nat (vs v) σ (δᴺ , _) = ∈ᴺ-nat v σ δᴺ

-- Tmᴺ {Γ}{A} t : PSh(Conᴺ Γ, Tyᴺ A)
--------------------------------------------------------------------------------
mutual
  Tmᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
  Tmᴺ (var v)   σᴺ = ∈ᴺ v σᴺ
  Tmᴺ (lam t)   σᴺ =
    (λ δ aᴺ → Tmᴺ t (Conᴺₑ δ σᴺ , aᴺ)) ,
    (λ δ ν aᴺ → (λ x → Tmᴺ t (x , Tyᴺₑ ν aᴺ)) & (Conᴺ-∘ₑ δ ν σᴺ ⁻¹) ⁻¹
              ◾ Tmᴺ-nat t ν (Conᴺₑ δ σᴺ , aᴺ))
  Tmᴺ (app f a) σᴺ = proj₁ (Tmᴺ f σᴺ) idₑ (Tmᴺ a σᴺ)

  Tmᴺ-nat : ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : OPE Σ Δ) δᴺ → Tmᴺ t (Conᴺₑ σ δᴺ) ≡ Tyᴺₑ σ (Tmᴺ t δᴺ)
  Tmᴺ-nat (var v)   σ δᴺ = ∈ᴺ-nat v σ δᴺ
  Tmᴺ-nat (lam t)   σ δᴺ = ⇒ᴺ≡ λ ν aᴺ → (λ x → Tmᴺ t (x , aᴺ)) & Conᴺ-∘ₑ σ ν δᴺ ⁻¹
  Tmᴺ-nat (app f a) σ δᴺ rewrite Tmᴺ-nat f σ δᴺ | Tmᴺ-nat a σ δᴺ =
      (λ x → proj₁ (Tmᴺ f δᴺ) x (Tyᴺₑ σ (Tmᴺ a δᴺ))) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ proj₂ (Tmᴺ f δᴺ) idₑ σ (Tmᴺ a δᴺ)

-- OPEᴺ {Γ}{Δ} σ : PSh(Conᴺ Γ, Conᴺ Δ)
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
OPEᴺ-idₑ ∙         = refl
OPEᴺ-idₑ (σᴺ , tᴺ) = (_, tᴺ) & OPEᴺ-idₑ σᴺ

∈ₑᴺ :
 ∀ {Γ Δ Σ A}(σ : OPE Δ Γ)(v : A ∈ Γ)(δᴺ : Conᴺ Δ Σ)
 → ∈ᴺ (∈ₑ σ v) δᴺ ≡ ∈ᴺ v (OPEᴺ σ δᴺ)
∈ₑᴺ ∙        v      δᴺ        = refl
∈ₑᴺ (drop σ) v      (δᴺ , _)  = ∈ₑᴺ σ v δᴺ
∈ₑᴺ (keep σ) vz     (δᴺ , tᴺ) = refl
∈ₑᴺ (keep σ) (vs v) (δᴺ , tᴺ) = ∈ₑᴺ σ v δᴺ

Tmₑᴺ :
 ∀ {Γ Δ Σ A}(σ : OPE Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₑ σ t) δᴺ ≡ Tmᴺ t (OPEᴺ σ δᴺ)
Tmₑᴺ σ (var v)   δᴺ = ∈ₑᴺ σ v δᴺ
Tmₑᴺ σ (lam t)   δᴺ = ⇒ᴺ≡ λ ν aᴺ →
  Tmₑᴺ (keep σ) t (Conᴺₑ ν δᴺ , aᴺ) ◾ (λ x → Tmᴺ t (x , aᴺ)) & OPEᴺ-nat σ ν δᴺ
Tmₑᴺ σ (app f a) δᴺ rewrite Tmₑᴺ σ f δᴺ | Tmₑᴺ σ a δᴺ = refl 

-- Subᴺ {Γ}{Δ} σ : PSh(Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
Subᴺ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
Subᴺ ∙       δᴺ = ∙
Subᴺ (σ , t) δᴺ = Subᴺ σ δᴺ , Tmᴺ t δᴺ

Subᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : Sub Γ Δ)(δ : OPE Ξ Σ) νᴺ → Subᴺ σ (Conᴺₑ δ νᴺ) ≡ Conᴺₑ δ (Subᴺ σ νᴺ)
Subᴺ-nat ∙       δ νᴺ = refl
Subᴺ-nat (σ , t) δ νᴺ = _,_ & Subᴺ-nat σ δ νᴺ ⊗ Tmᴺ-nat t δ νᴺ

Subᴺ-ₛ∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Γ Σ)(νᴺ : Conᴺ Γ Δ)
  → Subᴺ (σ ₛ∘ₑ δ) νᴺ ≡ Subᴺ σ (OPEᴺ δ νᴺ)
Subᴺ-ₛ∘ₑ ∙       δ νᴺ = refl
Subᴺ-ₛ∘ₑ (σ , t) δ νᴺ = _,_ & Subᴺ-ₛ∘ₑ σ δ νᴺ ⊗ Tmₑᴺ δ t νᴺ  

∈ₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(v : A ∈ Γ)(δᴺ : Conᴺ Δ Σ)
 → Tmᴺ (∈ₛ σ v) δᴺ ≡ ∈ᴺ v (Subᴺ σ δᴺ)
∈ₛᴺ (σ , t) vz     δᴺ = refl
∈ₛᴺ (σ , _) (vs v) δᴺ = ∈ₛᴺ σ v δᴺ

Tmₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₛ σ t) δᴺ ≡ Tmᴺ t (Subᴺ σ δᴺ)
Tmₛᴺ σ (var v)   δᴺ = ∈ₛᴺ σ v δᴺ
Tmₛᴺ σ (lam t)   δᴺ = ⇒ᴺ≡ λ ν aᴺ →
    Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν δᴺ , aᴺ)
  ◾ (λ x → Tmᴺ t (x , aᴺ)) &
      (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν δᴺ , aᴺ)
    ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν δᴺ)
    ◾ Subᴺ-nat σ ν δᴺ)
Tmₛᴺ σ (app f a) δᴺ rewrite Tmₛᴺ σ f δᴺ | Tmₛᴺ σ a δᴺ = refl

Subᴺ-idₛ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Subᴺ idₛ σᴺ ≡ σᴺ
Subᴺ-idₛ ∙         = refl
Subᴺ-idₛ (σᴺ , tᴺ) =
  (_, tᴺ) & (Subᴺ-ₛ∘ₑ idₛ wk (σᴺ , tᴺ) ◾ Subᴺ-idₛ (OPEᴺ idₑ σᴺ) ◾ OPEᴺ-idₑ σᴺ)

