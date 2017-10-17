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

Conᴺ-idₑ : ∀ {Γ Δ}(Γᴺ : Conᴺ Γ Δ) → Conᴺₑ idₑ Γᴺ ≡ Γᴺ
Conᴺ-idₑ ∙        = refl
Conᴺ-idₑ (Γᴺ , t) = _,_ & Conᴺ-idₑ Γᴺ ⊗ Tyᴺ-idₑ t

Conᴺ-∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(ν : Conᴺ Ξ Σ)
  → Conᴺₑ (σ ∘ₑ δ) ν ≡ Conᴺₑ δ (Conᴺₑ σ ν)  
Conᴺ-∘ₑ σ δ ∙       = refl
Conᴺ-∘ₑ σ δ (ν , t) = _,_ & Conᴺ-∘ₑ σ δ ν ⊗ Tyᴺ-∘ₑ t σ δ

-- ∈ᴺ {Γ}{A} v : PSh 𝒪PE(Conᴺ Γ, Tyᴺ A)
--------------------------------------------------------------------------------
∈ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (σ , t) = t
∈ᴺ (vs v) (σ , t) = ∈ᴺ v σ

∈ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : OPE Σ Δ) Γᴺ → ∈ᴺ v (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ σ (∈ᴺ v Γᴺ)
∈ᴺ-nat vz     σ (Γᴺ , _) = refl
∈ᴺ-nat (vs v) σ (Γᴺ , _) = ∈ᴺ-nat v σ Γᴺ

-- Tmᴺ {Γ}{A} t : PSh 𝒪PE(Conᴺ Γ, Tyᴺ A)
--------------------------------------------------------------------------------
mutual
  Tmᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
  Tmᴺ (var v)   Γᴺ = ∈ᴺ v Γᴺ
  Tmᴺ (lam t)   Γᴺ =
    (λ δ aᴺ → Tmᴺ t (Conᴺₑ δ Γᴺ , aᴺ)) ,
    (λ δ ν aᴺ → (λ x → Tmᴺ t (x , Tyᴺₑ ν aᴺ)) & (Conᴺ-∘ₑ δ ν Γᴺ ⁻¹) ⁻¹
              ◾ Tmᴺ-nat t ν (Conᴺₑ δ Γᴺ , aᴺ))
  Tmᴺ (app f a) Γᴺ = proj₁ (Tmᴺ f Γᴺ) idₑ (Tmᴺ a Γᴺ)

  Tmᴺ-nat : ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : OPE Σ Δ) Γᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ σ (Tmᴺ t Γᴺ)
  Tmᴺ-nat (var v)   σ Γᴺ = ∈ᴺ-nat v σ Γᴺ
  Tmᴺ-nat (lam t)   σ Γᴺ = ⇒ᴺ≡ λ ν aᴺ → (λ x → Tmᴺ t (x , aᴺ)) & Conᴺ-∘ₑ σ ν Γᴺ ⁻¹
  Tmᴺ-nat (app f a) σ Γᴺ rewrite Tmᴺ-nat f σ Γᴺ | Tmᴺ-nat a σ Γᴺ =
      (λ x → proj₁ (Tmᴺ f Γᴺ) x (Tyᴺₑ σ (Tmᴺ a Γᴺ))) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ proj₂ (Tmᴺ f Γᴺ) idₑ σ (Tmᴺ a Γᴺ)

-- OPEᴺ {Γ}{Δ} σ : PSh 𝒪PE(Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
OPEᴺ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
OPEᴺ ∙        Γᴺ        = Γᴺ
OPEᴺ (drop σ) (Γᴺ , _)  = OPEᴺ σ Γᴺ
OPEᴺ (keep σ) (Γᴺ , tᴺ) = OPEᴺ σ Γᴺ , tᴺ

OPEᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : OPE Γ Δ)(δ : OPE Ξ Σ) Γᴺ → OPEᴺ σ (Conᴺₑ δ Γᴺ) ≡ Conᴺₑ δ (OPEᴺ σ Γᴺ)
OPEᴺ-nat ∙        δ Γᴺ        = refl
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
Tmₑᴺ σ (lam t)   Γᴺ = ⇒ᴺ≡ λ ν aᴺ →
  Tmₑᴺ (keep σ) t (Conᴺₑ ν Γᴺ , aᴺ) ◾ (λ x → Tmᴺ t (x , aᴺ)) & OPEᴺ-nat σ ν Γᴺ
Tmₑᴺ σ (app f a) Γᴺ rewrite Tmₑᴺ σ f Γᴺ | Tmₑᴺ σ a Γᴺ = refl 

-- Subᴺ {Γ}{Δ} σ : PSh 𝒪PE(Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
Subᴺ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
Subᴺ ∙       Γᴺ = ∙
Subᴺ (σ , t) Γᴺ = Subᴺ σ Γᴺ , Tmᴺ t Γᴺ

Subᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : Sub Γ Δ)(δ : OPE Ξ Σ) Γᴺ → Subᴺ σ (Conᴺₑ δ Γᴺ) ≡ Conᴺₑ δ (Subᴺ σ Γᴺ)
Subᴺ-nat ∙       δ Γᴺ = refl
Subᴺ-nat (σ , t) δ Γᴺ = _,_ & Subᴺ-nat σ δ Γᴺ ⊗ Tmᴺ-nat t δ Γᴺ

Subᴺ-ₛ∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Γ Σ)(Γᴺ : Conᴺ Γ Δ)
  → Subᴺ (σ ₛ∘ₑ δ) Γᴺ ≡ Subᴺ σ (OPEᴺ δ Γᴺ)
Subᴺ-ₛ∘ₑ ∙       δ Γᴺ = refl
Subᴺ-ₛ∘ₑ (σ , t) δ Γᴺ = _,_ & Subᴺ-ₛ∘ₑ σ δ Γᴺ ⊗ Tmₑᴺ δ t Γᴺ  

∈ₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(v : A ∈ Γ)(Γᴺ : Conᴺ Δ Σ)
 → Tmᴺ (∈ₛ σ v) Γᴺ ≡ ∈ᴺ v (Subᴺ σ Γᴺ)
∈ₛᴺ (σ , t) vz     Γᴺ = refl
∈ₛᴺ (σ , _) (vs v) Γᴺ = ∈ₛᴺ σ v Γᴺ

Tmₛᴺ :
 ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(Γᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₛ σ t) Γᴺ ≡ Tmᴺ t (Subᴺ σ Γᴺ)
Tmₛᴺ σ (var v)   Γᴺ = ∈ₛᴺ σ v Γᴺ
Tmₛᴺ σ (lam t)   Γᴺ = ⇒ᴺ≡ λ ν aᴺ →
    Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν Γᴺ , aᴺ)
  ◾ (λ x → Tmᴺ t (x , aᴺ)) &
      (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν Γᴺ , aᴺ)
    ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν Γᴺ)
    ◾ Subᴺ-nat σ ν Γᴺ)
Tmₛᴺ σ (app f a) Γᴺ rewrite Tmₛᴺ σ f Γᴺ | Tmₛᴺ σ a Γᴺ = refl

Subᴺ-idₛ : ∀ {Γ Δ}(Γᴺ : Conᴺ Γ Δ) → Subᴺ idₛ Γᴺ ≡ Γᴺ
Subᴺ-idₛ ∙         = refl
Subᴺ-idₛ (Γᴺ , tᴺ) =
  (_, tᴺ) & (Subᴺ-ₛ∘ₑ idₛ wk (Γᴺ , tᴺ) ◾ Subᴺ-idₛ (OPEᴺ idₑ Γᴺ) ◾ OPEᴺ-idₑ Γᴺ)

