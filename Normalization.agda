{-# OPTIONS --without-K #-}

module Normalization where

open import Syntax
open import Embedding
open import Substitution
open import Nf

Tyᴺ : Ty → Con → Set
Tyᴺ ι       Γ = Nf Γ ι
Tyᴺ (A ⇒ B) Γ = ∀ {Δ} → OPE Δ Γ → Tyᴺ A Δ → Tyᴺ B Δ

Tyᴺₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴺ A Γ → Tyᴺ A Δ
Tyᴺₑ {ι}     σ tᴺ = Nfₑ σ tᴺ
Tyᴺₑ {A ⇒ B} σ tᴺ = λ δ → tᴺ (σ ∘ₑ δ)

data Conᴺ : Con → Con → Set where
  ∙   : ∀ {Δ} → Conᴺ ∙ Δ
  _,_ : ∀ {A Γ Δ} → Conᴺ Γ Δ → Tyᴺ A Δ → Conᴺ (Γ , A) Δ

Conᴺₑ : ∀ {Γ Δ Σ} → OPE Σ Δ → Conᴺ Γ Δ → Conᴺ Γ Σ
Conᴺₑ σ ∙         = ∙
Conᴺₑ σ (Γᴺ , tᴺ) = Conᴺₑ σ Γᴺ , Tyᴺₑ σ tᴺ

∈ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (Γᴺ , tᴺ) = tᴺ
∈ᴺ (vs v) (Γᴺ , _ ) = ∈ᴺ v Γᴺ

Tmᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
Tmᴺ (var v)   Γᴺ = ∈ᴺ v Γᴺ
Tmᴺ (lam t)   Γᴺ = λ σ aᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ , aᴺ)
Tmᴺ (app f x) Γᴺ = Tmᴺ f Γᴺ idₑ (Tmᴺ x Γᴺ)

mutual
  qᴺ : ∀ {A Γ} → Tyᴺ A Γ → Nf Γ A
  qᴺ {ι}     tᴺ = tᴺ
  qᴺ {A ⇒ B} tᴺ = lam (qᴺ (tᴺ wk (uᴺ (var vz))))

  uᴺ : ∀ {A Γ} → Ne Γ A → Tyᴺ A Γ
  uᴺ {ι}     n = ne n
  uᴺ {A ⇒ B} n = λ σ aᴺ → uᴺ (app (Neₑ σ n) (qᴺ aᴺ))

uConᴺ : ∀ {Γ} → Conᴺ Γ Γ
uConᴺ {∙}      = ∙
uConᴺ {Γ , tᴺ} = Conᴺₑ wk uConᴺ , uᴺ (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tmᴺ t uConᴺ)

-- Trying to extend to PSh
--------------------------------------------------------------------------------

open import Lib

Tyᴺ-idₑ : ∀ {Γ A}(tᴺ : Tyᴺ A Γ) → Tyᴺₑ idₑ tᴺ ≡ tᴺ
Tyᴺ-idₑ {A = ι}     tᴺ = Nf-idₑ tᴺ
Tyᴺ-idₑ {A = A ⇒ B} tᴺ = funexti λ Δ → funext λ δ → tᴺ & idlₑ δ

Tyᴺ-∘ₑ :
  ∀ {Γ Δ Σ A}(tᴺ : Tyᴺ A Σ)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  → Tyᴺₑ (σ ∘ₑ δ) tᴺ ≡ Tyᴺₑ δ (Tyᴺₑ σ tᴺ)
Tyᴺ-∘ₑ {A = ι}     tᴺ σ δ = Nf-∘ₑ σ δ tᴺ
Tyᴺ-∘ₑ {A = A ⇒ B} tᴺ σ δ = funexti λ Ξ → funext λ ν → tᴺ & assₑ σ δ ν

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
    funexti λ Ξ → funext λ ν → funext λ aᴺ → Tmᴺ t & ((_, aᴺ) & (Conᴺ-∘ₑ σ ν Γᴺ ⁻¹ ))
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
  uᴺ-nat {A ⇒ B} σ n = funexti λ Σ → funext λ δ → funext λ aᴺ →
    (λ x → uᴺ (app x (qᴺ aᴺ))) & Ne-∘ₑ σ δ n

uConᴾ : ∀ {Γ} → Conᴾ (uConᴺ {Γ})
uConᴾ {∙}     = ∙
uConᴾ {Γ , A} = Conᴾₑ wk uConᴾ , uᴾ (var vz)

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
Tmₑᴺ σ (lam t)   δᴺ = funexti λ Ξ → funext λ ν → funext λ aᴺ →
  Tmₑᴺ (keep σ) t (Conᴺₑ ν δᴺ , aᴺ) ◾ (λ x → Tmᴺ t (x , aᴺ)) & OPEᴺ-nat σ ν δᴺ
Tmₑᴺ σ (app f a) δᴺ rewrite Tmₑᴺ σ f δᴺ | Tmₑᴺ σ a δᴺ = refl

--------------------------------------------------------------------------------


-- Subᴺ {Γ}{Δ} σ : PSh(Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
Subᴺ : ∀ {Γ Δ} → Sub Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
Subᴺ ∙       δᴺ = ∙
Subᴺ (σ , t) δᴺ = Subᴺ σ δᴺ , Tmᴺ t δᴺ

Subᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : Sub Γ Δ)(δ : OPE Ξ Σ) νᴺ → Conᴾ νᴺ → Subᴺ σ (Conᴺₑ δ νᴺ) ≡ Conᴺₑ δ (Subᴺ σ νᴺ)
Subᴺ-nat ∙       δ νᴺ νᴾ = refl
Subᴺ-nat (σ , t) δ νᴺ νᴾ = _,_ & Subᴺ-nat σ δ νᴺ νᴾ ⊗ Tmᴺ-nat t δ νᴾ

Subᴺ-ₛ∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : Sub Σ Ξ)(δ : OPE Γ Σ)(νᴺ : Conᴺ Γ Δ)
  → Subᴺ (σ ₛ∘ₑ δ) νᴺ ≡ Subᴺ σ (OPEᴺ δ νᴺ)
Subᴺ-ₛ∘ₑ ∙       δ νᴺ = refl
Subᴺ-ₛ∘ₑ (σ , t) δ νᴺ = _,_ & Subᴺ-ₛ∘ₑ σ δ νᴺ ⊗ Tmₑᴺ δ t νᴺ  

-- ∈ₛᴺ :
--  ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(v : A ∈ Γ)(δᴺ : Conᴺ Δ Σ)
--  → Tmᴺ (∈ₛ σ v) δᴺ ≡ ∈ᴺ v (Subᴺ σ δᴺ)
-- ∈ₛᴺ (σ , t) vz     δᴺ = refl
-- ∈ₛᴺ (σ , _) (vs v) δᴺ = ∈ₛᴺ σ v δᴺ

Subᴺ-idₛ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Subᴺ idₛ σᴺ ≡ σᴺ
Subᴺ-idₛ ∙         = refl
Subᴺ-idₛ (σᴺ , tᴺ) =
  (_, tᴺ) & (Subᴺ-ₛ∘ₑ idₛ wk (σᴺ , tᴺ) ◾ Subᴺ-idₛ (OPEᴺ idₑ σᴺ) ◾ OPEᴺ-idₑ σᴺ)

-- Tmₛᴺ :
--  ∀ {Γ Δ Σ A}(σ : Sub Δ Γ)(t : Tm Γ A)(δᴺ : Conᴺ Δ Σ)
--  → Conᴾ δᴺ
--  → Tmᴺ (Tmₛ σ t) δᴺ ≡ Tmᴺ t (Subᴺ σ δᴺ)
-- Tmₛᴺ σ (var v)   δᴺ δᴾ = ∈ₛᴺ σ v δᴺ
-- Tmₛᴺ σ (lam t)   δᴺ δᴾ = {!Tmᴾ (lam t) δ!}
--   -- funexti λ Ξ → funext λ ν → funext λ aᴺ →
--   --   Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν δᴺ , aᴺ) (Conᴾₑ ν δᴾ , {!!})
--   -- ◾ (λ x → Tmᴺ t (x , aᴺ)) & (
--   --      (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν δᴺ , aᴺ))
--   --    ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν δᴺ)
--   --    ◾ Subᴺ-nat σ ν δᴺ δᴾ)     
-- Tmₛᴺ σ (app f a) δᴺ δᴾ rewrite Tmₛᴺ σ f δᴺ δᴾ | Tmₛᴺ σ a δᴺ δᴾ = refl



