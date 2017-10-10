{-# OPTIONS --without-K #-}

module Presheaf where

open import Lib hiding (⊤; ⊥)
import Lib as L
open import UIP
open import Syntax
open import Embedding
open import Substitution
open import Nf

-- Tyᴺ A : (F : PSh 𝒪PE) × (qᴺ : PSh 𝒪PE (F, (Nf _ A))) × (uᴺ : PSh 𝒪PE ((Ne _ A), F))
--------------------------------------------------------------------------------

data +ᴺ (A B C : Set) : Set where
  ne+  : A → +ᴺ A B C
  inj₁ : B → +ᴺ A B C
  inj₂ : C → +ᴺ A B C

mutual
  Tyᴺ : Ty → Con → Set
  Tyᴺ ⊤       Γ = Nf Γ ⊤
  Tyᴺ ⊥       Γ = Ne Γ ⊥
  Tyᴺ (A * B) Γ = Tyᴺ A Γ × Tyᴺ B Γ
  Tyᴺ (A + B) Γ = +ᴺ (Ne Γ (A + B)) (Tyᴺ A Γ) (Tyᴺ B Γ)
  Tyᴺ (A ⇒ B) Γ =
    Σ (∀ {Δ} → OPE Δ Γ → Tyᴺ A Δ → Tyᴺ B Δ) λ fᴺ →
    ∀ {Δ Σ}(σ : OPE Δ Γ)(δ : OPE Σ Δ) aᴺ → fᴺ (σ ∘ₑ δ) (Tyᴺₑ {A} δ aᴺ) ≡ Tyᴺₑ {B} δ (fᴺ σ aᴺ)

  Tyᴺₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴺ A Γ → Tyᴺ A Δ
  Tyᴺₑ {⊤}     σ tᴺ = Nfₑ σ tᴺ
  Tyᴺₑ {⊥}     σ tᴺ = Neₑ σ tᴺ
  Tyᴺₑ {A ⇒ B} σ (tᴺ , tᴺ-nat) =
    (λ δ → tᴺ (σ ∘ₑ δ)) ,
    (λ δ ν aᴺ → (λ x → tᴺ x (Tyᴺₑ {A} ν aᴺ)) & (assₑ σ δ ν ⁻¹) ◾ tᴺ-nat (σ ∘ₑ δ) ν aᴺ)
  Tyᴺₑ {A * B} σ (tᴺ , uᴺ) = Tyᴺₑ {A} σ tᴺ , Tyᴺₑ {B} σ uᴺ
  Tyᴺₑ {A + B} σ (ne+  n)  = ne+ (Neₑ σ n)
  Tyᴺₑ {A + B} σ (inj₁ tᴺ) = inj₁ (Tyᴺₑ {A} σ tᴺ)
  Tyᴺₑ {A + B} σ (inj₂ tᴺ) = inj₂ (Tyᴺₑ {B} σ tᴺ)

⇒ᴺ≡ :
  ∀ {A B Γ}{f f' : Tyᴺ (A ⇒ B) Γ}
  → (∀ {Δ}(σ : OPE Δ Γ) a → proj₁ f σ a ≡ proj₁ f' σ a)
  → f ≡ f'
⇒ᴺ≡ {f = f}{f'} eq = ,Σ=
  (funexti λ _ → funext λ σ → funext λ aᴺ → eq σ aᴺ )
  (funexti λ _ → funexti λ _ → funext λ _ → funext λ _ → funext λ _ → UIP _ _)

Tyᴺ-idₑ : ∀ {A Γ}(tᴺ : Tyᴺ A Γ) → Tyᴺₑ {A} idₑ tᴺ ≡ tᴺ
Tyᴺ-idₑ {⊤}     tᴺ        = Nf-idₑ tᴺ
Tyᴺ-idₑ {⊥}     tᴺ        = Ne-idₑ tᴺ
Tyᴺ-idₑ {A * B} (tᴺ , uᴺ) = _,_ & Tyᴺ-idₑ {A} tᴺ ⊗ Tyᴺ-idₑ {B} uᴺ
Tyᴺ-idₑ {A + B} (ne+ n)   = ne+ & Ne-idₑ n
Tyᴺ-idₑ {A + B} (inj₁ tᴺ) = inj₁ & Tyᴺ-idₑ {A} tᴺ
Tyᴺ-idₑ {A + B} (inj₂ tᴺ) = inj₂ & Tyᴺ-idₑ {B} tᴺ
Tyᴺ-idₑ {A ⇒ B} (tᴺ , _)  = ⇒ᴺ≡ {A}{B} λ σ aᴺ → (λ x → tᴺ x aᴺ) & idlₑ σ

Tyᴺ-∘ₑ :
  ∀ {A Γ Δ Σ}(tᴺ : Tyᴺ A Σ)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  → Tyᴺₑ {A} (σ ∘ₑ δ) tᴺ ≡ Tyᴺₑ {A} δ (Tyᴺₑ {A} σ tᴺ)
Tyᴺ-∘ₑ {⊤}     tᴺ        σ δ = Nf-∘ₑ σ δ tᴺ
Tyᴺ-∘ₑ {A ⇒ B} (tᴺ , _)  σ δ = ⇒ᴺ≡ {A}{B} λ ν aᴺ → (λ x → tᴺ x aᴺ) & assₑ σ δ ν
Tyᴺ-∘ₑ {⊥}     tᴺ        σ δ = Ne-∘ₑ σ δ tᴺ
Tyᴺ-∘ₑ {A * B} (tᴺ , uᴺ) σ δ = _,_ & Tyᴺ-∘ₑ {A} tᴺ σ δ ⊗ Tyᴺ-∘ₑ {B} uᴺ σ δ
Tyᴺ-∘ₑ {A + B} (ne+ n)   σ δ = ne+ & Ne-∘ₑ σ δ n
Tyᴺ-∘ₑ {A + B} (inj₁ tᴺ) σ δ = inj₁ & Tyᴺ-∘ₑ {A} tᴺ σ δ
Tyᴺ-∘ₑ {A + B} (inj₂ tᴺ) σ δ = inj₂ & Tyᴺ-∘ₑ {B} tᴺ σ δ

mutual
  qᴺ : ∀ {A Γ} → Tyᴺ A Γ → Nf Γ A
  qᴺ {⊤}     tᴺ        = tt
  qᴺ {⊥}     tᴺ        = ne⊥ tᴺ
  qᴺ {A * B} (aᴺ , bᴺ) = qᴺ aᴺ , qᴺ bᴺ
  qᴺ {A ⇒ B} (tᴺ , _)  = lam (qᴺ (tᴺ wk (uᴺ {A} (var vz))))
  qᴺ {A + B} (ne+ n)   = ne+ n
  qᴺ {A + B} (inj₁ a)  = inj₁ (qᴺ a)
  qᴺ {A + B} (inj₂ b)  = inj₂ (qᴺ b)

  qᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(tᴺ : Tyᴺ A Γ) → Nfₑ σ (qᴺ {A} tᴺ) ≡ qᴺ (Tyᴺₑ {A} σ tᴺ)
  qᴺ-nat {⊤}     σ tᴺ = refl
  qᴺ-nat {⊥}     σ tᴺ = refl
  qᴺ-nat {A ⇒ B} σ (tᴺ , tᴺ-nat) =
    lam & (qᴺ-nat (keep σ) (tᴺ wk (uᴺ {A}(var vz)))
         ◾ qᴺ & (tᴺ-nat wk (keep σ) (uᴺ {A} (var vz)) ⁻¹
                ◾ tᴺ & (drop & (idlₑ σ ◾ idrₑ σ ⁻¹)) ⊗ uᴺ-nat (keep σ) (var vz)))
  qᴺ-nat {A * B} σ (tᴺ , uᴺ) = _,_ & qᴺ-nat {A} σ tᴺ ⊗ qᴺ-nat {B} σ uᴺ
  qᴺ-nat {A + B} σ (ne+ n)   = refl
  qᴺ-nat {A + B} σ (inj₁ tᴺ) = inj₁ & qᴺ-nat {A} σ tᴺ
  qᴺ-nat {A + B} σ (inj₂ tᴺ) = inj₂ & qᴺ-nat {B} σ tᴺ

  uᴺ : ∀ {A Γ} → Ne Γ A → Tyᴺ A Γ
  uᴺ {⊤}     n = tt
  uᴺ {⊥}     n = n
  uᴺ {A * B} n = uᴺ (π₁ n) , uᴺ (π₂ n)
  uᴺ {A ⇒ B} n =
    (λ δ aᴺ → uᴺ (app (Neₑ δ n) (qᴺ aᴺ))) ,
    (λ σ δ aᴺ → (λ x y → uᴺ (app x y)) & (Ne-∘ₑ σ δ n ⁻¹) ⊗ qᴺ-nat δ aᴺ ⁻¹
              ◾ uᴺ-nat δ (app (Neₑ σ n) (qᴺ aᴺ)) ⁻¹)
  uᴺ {A + B} n = ne+ n

  uᴺ-nat : ∀ {A Γ Δ}(σ : OPE Δ Γ)(n : Ne Γ A) → Tyᴺₑ {A} σ (uᴺ {A} n) ≡ uᴺ (Neₑ σ n)
  uᴺ-nat {⊤}     σ n = refl
  uᴺ-nat {⊥}     σ n = refl
  uᴺ-nat {A ⇒ B} σ n = ⇒ᴺ≡ {A}{B} λ δ aᴺ → (λ x → uᴺ {B} (Ne.app x (qᴺ {A} aᴺ))) & Ne-∘ₑ σ δ n
  uᴺ-nat {A * B} σ n = _,_ & uᴺ-nat {A} σ (π₁ n) ⊗ uᴺ-nat {B} σ (π₂ n)
  uᴺ-nat {A + B} σ n = refl


-- Conᴺ Γ : PSh 𝒪PE
--------------------------------------------------------------------------------
data Conᴺ : Con → Con → Set where
  ∙   : ∀ {Γ} → Conᴺ ∙ Γ
  _,_ : ∀ {A Γ Δ} (σ : Conᴺ Γ Δ)(t : Tyᴺ A Δ) → Conᴺ (Γ , A) Δ
infixr 5 _,_

Conᴺₑ : ∀ {Γ Δ} → OPE Δ Γ → ∀ {Σ} → Conᴺ Σ Γ → Conᴺ Σ Δ
Conᴺₑ σ ∙              = ∙
Conᴺₑ σ (_,_ {A} δ tᴺ) =  Conᴺₑ σ δ , Tyᴺₑ {A} σ tᴺ

Conᴺ-idₑ : ∀ {Γ Δ}(Γᴺ : Conᴺ Γ Δ) → Conᴺₑ idₑ Γᴺ ≡ Γᴺ
Conᴺ-idₑ ∙              = refl
Conᴺ-idₑ (_,_ {A} Γᴺ t) = _,_ & Conᴺ-idₑ Γᴺ ⊗ Tyᴺ-idₑ {A} t

Conᴺ-∘ₑ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(ν : Conᴺ Ξ Σ)
  → Conᴺₑ (σ ∘ₑ δ) ν ≡ Conᴺₑ δ (Conᴺₑ σ ν)
Conᴺ-∘ₑ σ δ ∙             = refl
Conᴺ-∘ₑ σ δ (_,_ {A} ν t) = _,_ & Conᴺ-∘ₑ σ δ ν ⊗ Tyᴺ-∘ₑ {A} t σ δ

--------------------------------------------------------------------------------

∈ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (σ , t) = t
∈ᴺ (vs v) (σ , t) = ∈ᴺ v σ

∈ᴺ-nat : ∀ {A Γ Δ Σ}(v : A ∈ Γ)(σ : OPE Σ Δ) Γᴺ → ∈ᴺ v (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ {A} σ (∈ᴺ v Γᴺ)
∈ᴺ-nat vz     σ (Γᴺ , _) = refl
∈ᴺ-nat (vs v) σ (Γᴺ , _) = ∈ᴺ-nat v σ Γᴺ

-- Tmᴺ {Γ}{A} t : PSh 𝒪PE(Conᴺ Γ, Tyᴺ A)
--------------------------------------------------------------------------------

mutual
  Tmᴺ : ∀ {A Γ} → Tm Γ A → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
  Tmᴺ (var v)   Γᴺ = ∈ᴺ v Γᴺ
  Tmᴺ {A ⇒ B}(lam t)  Γᴺ =
    (λ δ aᴺ → Tmᴺ t (Conᴺₑ δ Γᴺ , aᴺ)) ,
    (λ δ ν aᴺ → (λ x → Tmᴺ {B} t (x , Tyᴺₑ {A} ν aᴺ)) & (Conᴺ-∘ₑ δ ν Γᴺ ⁻¹) ⁻¹
              ◾ Tmᴺ-nat {B} t ν (Conᴺₑ δ Γᴺ , aᴺ))
  Tmᴺ (app f a) Γᴺ = proj₁ (Tmᴺ f Γᴺ) idₑ (Tmᴺ a Γᴺ)
  Tmᴺ tt Γᴺ = tt
  Tmᴺ (π₁ t) Γᴺ = proj₁ (Tmᴺ t Γᴺ)
  Tmᴺ (π₂ t) Γᴺ = proj₂ (Tmᴺ t Γᴺ)
  Tmᴺ (t , u) Γᴺ = Tmᴺ t Γᴺ , Tmᴺ u Γᴺ
  Tmᴺ (inj₁ t) Γᴺ = inj₁ (Tmᴺ t Γᴺ)
  Tmᴺ (inj₂ t) Γᴺ = inj₂ (Tmᴺ t Γᴺ)
  Tmᴺ {C} (case {A} {B} l r t) Γᴺ with Tmᴺ t Γᴺ
  ... | ne+ n = uᴺ {C}
    (case (qᴺ (Tmᴺ l (Conᴺₑ wk Γᴺ , uᴺ {A}(var vz))))
          (qᴺ (Tmᴺ r (Conᴺₑ wk Γᴺ , uᴺ {B}(var vz))))
          n)
  ... | inj₁ tᴺ = Tmᴺ l (Γᴺ , tᴺ)
  ... | inj₂ tᴺ = Tmᴺ r (Γᴺ , tᴺ)
  Tmᴺ {A} (⊥-rec t) Γᴺ = uᴺ {A} (⊥-rec (Tmᴺ t Γᴺ))

  Tmᴺ-nat : ∀ {A Γ Δ Σ}(t : Tm Γ A)(σ : OPE Σ Δ) Γᴺ → Tmᴺ t (Conᴺₑ σ Γᴺ) ≡ Tyᴺₑ {A} σ (Tmᴺ t Γᴺ)
  Tmᴺ-nat {A} (var v)     σ Γᴺ = ∈ᴺ-nat {A} v σ Γᴺ
  Tmᴺ-nat {A ⇒ B} (lam t) σ Γᴺ = ⇒ᴺ≡ {A}{B} λ ν aᴺ → (λ x → Tmᴺ t (x , aᴺ)) & Conᴺ-∘ₑ σ ν Γᴺ ⁻¹
  Tmᴺ-nat {B} (app {A} f a) σ Γᴺ rewrite Tmᴺ-nat f σ Γᴺ | Tmᴺ-nat a σ Γᴺ =
      (λ x → proj₁ (Tmᴺ f Γᴺ) x (Tyᴺₑ {A} σ (Tmᴺ a Γᴺ))) & (idrₑ σ ◾ idlₑ σ ⁻¹)
    ◾ proj₂ (Tmᴺ f Γᴺ) idₑ σ (Tmᴺ a Γᴺ)
  Tmᴺ-nat tt            σ Γᴺ = refl
  Tmᴺ-nat (π₁ t)        σ Γᴺ = proj₁ & Tmᴺ-nat t σ Γᴺ
  Tmᴺ-nat (π₂ t)        σ Γᴺ = proj₂ & Tmᴺ-nat t σ Γᴺ
  Tmᴺ-nat (t , u)       σ Γᴺ = _,_ & Tmᴺ-nat t σ Γᴺ ⊗ Tmᴺ-nat u σ Γᴺ
  Tmᴺ-nat (inj₁ t)      σ Γᴺ = inj₁ & Tmᴺ-nat t σ Γᴺ
  Tmᴺ-nat (inj₂ t)      σ Γᴺ = inj₂ & Tmᴺ-nat t σ Γᴺ
  Tmᴺ-nat (⊥-rec {A} t) σ Γᴺ =
    (uᴺ {A} ∘ ⊥-rec) & Tmᴺ-nat t σ Γᴺ ◾ uᴺ-nat {A} σ (⊥-rec (Tmᴺ t Γᴺ)) ⁻¹
  Tmᴺ-nat {C} (case {A} {B} l r t) σ Γᴺ rewrite Tmᴺ-nat {A + B} t σ Γᴺ with Tmᴺ t Γᴺ
  ... | ne+  n  =
      uᴺ {C} &
        (case &
             (qᴺ & (Tmᴺ l &
                 (_,_ &
                       (Conᴺ-∘ₑ σ wk Γᴺ ⁻¹
                     ◾ (λ x → Conᴺₑ (drop x) Γᴺ) & (idrₑ σ ◾ idlₑ σ ⁻¹)
                     ◾ Conᴺ-∘ₑ wk (keep σ) Γᴺ)
                   ⊗ (uᴺ-nat {A} (keep σ) (var vz) ⁻¹))
                 ◾ Tmᴺ-nat l (keep σ) (Conᴺₑ wk Γᴺ , uᴺ {A} (var vz)))
             ◾ qᴺ-nat {C} (keep σ) (Tmᴺ l (Conᴺₑ wk Γᴺ , uᴺ {A} (var vz))) ⁻¹)
          ⊗
             (qᴺ & (Tmᴺ r &
                 (_,_ &
                       (Conᴺ-∘ₑ σ wk Γᴺ ⁻¹
                     ◾ (λ x → Conᴺₑ (drop x) Γᴺ) & (idrₑ σ ◾ idlₑ σ ⁻¹)
                     ◾ Conᴺ-∘ₑ wk (keep σ) Γᴺ)
                   ⊗ (uᴺ-nat {B} (keep σ) (var vz) ⁻¹))
                 ◾ Tmᴺ-nat r (keep σ) (Conᴺₑ wk Γᴺ , uᴺ {B} (var vz)))
             ◾ qᴺ-nat {C} (keep σ) (Tmᴺ r (Conᴺₑ wk Γᴺ , uᴺ {B} (var vz))) ⁻¹)
          ⊗ refl)
    ◾ uᴺ-nat {C} σ
        (case (qᴺ (Tmᴺ l (Conᴺₑ wk Γᴺ , uᴺ {A} (var vz))))
              (qᴺ (Tmᴺ r (Conᴺₑ wk Γᴺ , uᴺ {B} (var vz))))
              n) ⁻¹
  ... | inj₁ tᴺ = Tmᴺ-nat l σ (Γᴺ , tᴺ)
  ... | inj₂ tᴺ = Tmᴺ-nat r σ (Γᴺ , tᴺ)


-- OPEᴺ {Γ}{Δ} σ : PSh(Conᴺ Γ, Conᴺ Δ)
--------------------------------------------------------------------------------
OPEᴺ : ∀ {Γ Δ} → OPE Γ Δ → ∀ {Σ} → Conᴺ Γ Σ → Conᴺ Δ Σ
OPEᴺ ∙        Γᴺ        = Γᴺ
OPEᴺ (drop σ) (Γᴺ , _)  = OPEᴺ σ Γᴺ
OPEᴺ (keep σ) (Γᴺ , tᴺ) = OPEᴺ σ Γᴺ , tᴺ

OPEᴺ-nat : ∀ {Γ Δ Σ Ξ}(σ : OPE Γ Δ)(δ : OPE Ξ Σ) Γᴺ → OPEᴺ σ (Conᴺₑ δ Γᴺ) ≡ Conᴺₑ δ (OPEᴺ σ Γᴺ)
OPEᴺ-nat ∙        δ Γᴺ        = refl
OPEᴺ-nat (drop σ) δ (Γᴺ , tᴺ) = OPEᴺ-nat σ δ Γᴺ
OPEᴺ-nat (keep {A} σ) δ (Γᴺ , tᴺ) = (_, Tyᴺₑ {A} δ tᴺ) & OPEᴺ-nat σ δ Γᴺ

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
 ∀ {A Γ Δ Σ}(σ : OPE Δ Γ)(t : Tm Γ A)(Γᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₑ σ t) Γᴺ ≡ Tmᴺ t (OPEᴺ σ Γᴺ)
Tmₑᴺ σ (var v)   Γᴺ = ∈ₑᴺ σ v Γᴺ
Tmₑᴺ σ (lam {A} {B} t) Γᴺ = ⇒ᴺ≡ {A}{B} λ ν aᴺ →
  Tmₑᴺ (keep σ) t (Conᴺₑ ν Γᴺ , aᴺ) ◾ (λ x → Tmᴺ t (x , aᴺ)) & OPEᴺ-nat σ ν Γᴺ
Tmₑᴺ σ (app f a) Γᴺ rewrite Tmₑᴺ σ f Γᴺ | Tmₑᴺ σ a Γᴺ = refl
Tmₑᴺ σ tt Γᴺ = refl
Tmₑᴺ σ (π₁ t) Γᴺ = proj₁ & Tmₑᴺ σ t Γᴺ
Tmₑᴺ σ (π₂ t) Γᴺ = proj₂ & Tmₑᴺ σ t Γᴺ
Tmₑᴺ σ (t , u) Γᴺ = _,_ & Tmₑᴺ σ t Γᴺ ⊗ Tmₑᴺ σ u Γᴺ
Tmₑᴺ σ (inj₁ t) Γᴺ = inj₁ & Tmₑᴺ σ t Γᴺ
Tmₑᴺ σ (inj₂ t) Γᴺ = inj₂ & Tmₑᴺ σ t Γᴺ
Tmₑᴺ {C} σ (case {A}{B} l r t) Γᴺ rewrite Tmₑᴺ σ t Γᴺ with Tmᴺ t (OPEᴺ σ Γᴺ)
... | ne+ n  =
  uᴺ {C} & (case &
           (qᴺ & (Tmₑᴺ (keep σ) l ((Conᴺₑ wk Γᴺ) , uᴺ {A} _)
               ◾ (λ x → Tmᴺ l (x , uᴺ {A} _)) & OPEᴺ-nat σ wk Γᴺ))
         ⊗ qᴺ & (Tmₑᴺ (keep σ) r ((Conᴺₑ wk Γᴺ) , uᴺ {B} _)
               ◾ (λ x → Tmᴺ r (x , uᴺ {B} _)) & OPEᴺ-nat σ wk Γᴺ)
         ⊗ refl)
... | inj₁ tᴺ = Tmₑᴺ (keep σ) l (Γᴺ , tᴺ)
... | inj₂ tᴺ = Tmₑᴺ (keep σ) r (Γᴺ , tᴺ)
Tmₑᴺ σ (⊥-rec {A} t) Γᴺ = (uᴺ {A} ∘ ⊥-rec) & Tmₑᴺ σ t Γᴺ

-- Subᴺ {Γ}{Δ} σ : PSh(Conᴺ Γ, Conᴺ Δ)
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
 ∀ {A Γ Δ Σ}(σ : Sub Δ Γ)(t : Tm Γ A)(Γᴺ : Conᴺ Δ Σ)
 → Tmᴺ (Tmₛ σ t) Γᴺ ≡ Tmᴺ t (Subᴺ σ Γᴺ)
Tmₛᴺ σ (var v)   Γᴺ = ∈ₛᴺ σ v Γᴺ
Tmₛᴺ σ (lam {A} {B} t) Γᴺ = ⇒ᴺ≡ {A}{B} λ ν aᴺ →
    Tmₛᴺ (keepₛ σ) t (Conᴺₑ ν Γᴺ , aᴺ)
  ◾ (λ x → Tmᴺ t (x , aᴺ)) &
      (Subᴺ-ₛ∘ₑ σ wk (Conᴺₑ ν Γᴺ , aᴺ)
    ◾ Subᴺ σ & OPEᴺ-idₑ (Conᴺₑ ν Γᴺ)
    ◾ Subᴺ-nat σ ν Γᴺ)
Tmₛᴺ σ (app f a) Γᴺ rewrite Tmₛᴺ σ f Γᴺ | Tmₛᴺ σ a Γᴺ = refl
Tmₛᴺ σ tt Γᴺ = refl
Tmₛᴺ σ (π₁ t) Γᴺ = proj₁ & Tmₛᴺ σ t Γᴺ
Tmₛᴺ σ (π₂ t) Γᴺ = proj₂ & Tmₛᴺ σ t Γᴺ
Tmₛᴺ σ (t , u) Γᴺ = _,_ & Tmₛᴺ σ t Γᴺ ⊗ Tmₛᴺ σ u Γᴺ
Tmₛᴺ σ (inj₁ t) Γᴺ = inj₁ & Tmₛᴺ σ t Γᴺ
Tmₛᴺ σ (inj₂ t) Γᴺ = inj₂ & Tmₛᴺ σ t Γᴺ
Tmₛᴺ {C} σ (case {A}{B} l r t) Γᴺ rewrite Tmₛᴺ σ t Γᴺ with Tmᴺ t (Subᴺ σ Γᴺ)
... | ne+ n   =
  uᴺ {C} &
    (case &
           (qᴺ & (Tmₛᴺ (keepₛ σ) l _
          ◾ (λ x → Tmᴺ l (x , uᴺ {A} _)) & (Subᴺ-ₛ∘ₑ σ wk _ ◾ Subᴺ σ & OPEᴺ-idₑ _ ◾ Subᴺ-nat σ wk Γᴺ)))
        ⊗  (qᴺ & (Tmₛᴺ (keepₛ σ) r _
          ◾ (λ x → Tmᴺ r (x , uᴺ {B} _)) & (Subᴺ-ₛ∘ₑ σ wk _ ◾ Subᴺ σ & OPEᴺ-idₑ _ ◾ Subᴺ-nat σ wk Γᴺ)))
        ⊗ refl)
... | inj₁ tᴺ =
    Tmₛᴺ (keepₛ σ) l (Γᴺ , tᴺ)
  ◾ (λ x → Tmᴺ l (x , tᴺ)) & (Subᴺ-ₛ∘ₑ σ wk (Γᴺ , tᴺ) ◾ Subᴺ σ & OPEᴺ-idₑ Γᴺ)
... | inj₂ tᴺ =
    Tmₛᴺ (keepₛ σ) r (Γᴺ , tᴺ)
  ◾ (λ x → Tmᴺ r (x , tᴺ)) & (Subᴺ-ₛ∘ₑ σ wk (Γᴺ , tᴺ) ◾ Subᴺ σ & OPEᴺ-idₑ Γᴺ)
Tmₛᴺ σ (⊥-rec {A} t) Γᴺ = (uᴺ {A} ∘ ⊥-rec) & Tmₛᴺ σ t Γᴺ

Subᴺ-idₛ : ∀ {Γ Δ}(Γᴺ : Conᴺ Γ Δ) → Subᴺ idₛ Γᴺ ≡ Γᴺ
Subᴺ-idₛ ∙         = refl
Subᴺ-idₛ (Γᴺ , tᴺ) =
  (_, tᴺ) & (Subᴺ-ₛ∘ₑ idₛ wk (Γᴺ , tᴺ) ◾ Subᴺ-idₛ (OPEᴺ idₑ Γᴺ) ◾ OPEᴺ-idₑ Γᴺ)
