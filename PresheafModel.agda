
module PresheafModel where

open import Lib
open import UIP
open import Syntax
open import Embedding
open import Substitution
open import Nf

-- Tyᴺ A : PSh 𝒪PE
--------------------------------------------------------------------------------

mutual
  -- Action on objects
  Tyᴺ : Ty → Con → Set
  Tyᴺ ι       Γ = Nf Γ ι
  Tyᴺ (A ⇒ B) Γ =  
    Σ (∀ {Δ} → OPE Δ Γ → Tyᴺ A Δ → Tyᴺ B Δ) λ fᴺ →
    ∀ {Δ Σ}(σ : OPE Δ Γ)(δ : OPE Σ Δ)(aᴺ : Tyᴺ A Δ) → Tyᴺₑ δ (fᴺ σ aᴺ) ≡ fᴺ (σ ∘ₑ δ) (Tyᴺₑ δ aᴺ)

  -- Action on morphisms
  Tyᴺₑ : ∀ {A Γ Δ} → OPE Δ Γ → Tyᴺ A Γ → Tyᴺ A Δ
  Tyᴺₑ {ι}     σ tᴺ            = tᴺ [ σ ]Nfₑ
  Tyᴺₑ {A ⇒ B} σ (tᴺ , tᴺ-nat) =
    (λ δ → tᴺ (σ ∘ₑ δ)) ,
    (λ δ ν aᴺ → tᴺ-nat (σ ∘ₑ δ) ν aᴺ ◾ (λ x → tᴺ x (Tyᴺₑ ν aᴺ)) & assₑ σ δ ν)

-- Equality constructor for semantic functions
⇒ᴺ= :
  ∀ {Γ A B}{f f' : Tyᴺ (A ⇒ B) Γ}
  → (∀ {Δ}(σ : OPE Δ Γ) a → proj₁ f σ a ≡ proj₁ f' σ a)
  → f ≡ f'
⇒ᴺ= {f = f}{f'} eq = ,Σ=
  (funexti λ Δ → funext λ σ → funext λ aᴺ → eq σ aᴺ )
  (funexti λ _ → funexti λ _ → funext λ _ → funext λ _ → funext λ _ → UIP _ _)

-- Action on identity morphism
idₑTyᴺ : ∀ {Γ A}(tᴺ : Tyᴺ A Γ) → Tyᴺₑ idₑ tᴺ ≡ tᴺ
idₑTyᴺ {A = ι}     tᴺ       = idₑNf tᴺ
idₑTyᴺ {A = A ⇒ B} (tᴺ , _) = ⇒ᴺ= λ σ aᴺ → (λ x → tᴺ x aᴺ) & idlₑ σ

-- Action on composition
∘ₑTyᴺ :
  ∀ {Γ Δ Σ A}(tᴺ : Tyᴺ A Σ)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
  → Tyᴺₑ (σ ∘ₑ δ) tᴺ ≡ Tyᴺₑ δ (Tyᴺₑ σ tᴺ)
∘ₑTyᴺ {A = ι}     tᴺ σ δ = ∘ₑNf tᴺ σ δ ⁻¹
∘ₑTyᴺ {A = A ⇒ B} tᴺ σ δ = ⇒ᴺ= (λ ν aᴺ → (λ x → proj₁ tᴺ x aᴺ) & assₑ σ δ ν)


-- Conᴺ Γ : PSh 𝒪PE
--------------------------------------------------------------------------------

-- Action on objects
data Conᴺ : Con → Con → Set where
  ∙   : ∀ {Γ} → Conᴺ ∙ Γ
  _,_ : ∀ {A Γ Δ} (σ : Conᴺ Γ Δ)(t : Tyᴺ A Δ) → Conᴺ (Γ , A) Δ
infixr 5 _,_

-- Action on morphisms
Conᴺₑ : ∀ {Γ Δ} → OPE Δ Γ → ∀ {Σ} → Conᴺ Σ Γ → Conᴺ Σ Δ
Conᴺₑ σ ∙        = ∙
Conᴺₑ σ (δ , tᴺ) = Conᴺₑ σ δ , Tyᴺₑ σ tᴺ

-- Action on composition
∘ₑOPEᴺ :
  ∀ {Γ Δ Σ Ξ}(σ : OPE Δ Σ)(δ : OPE Γ Δ)(ν : Conᴺ Ξ Σ)
  → Conᴺₑ (σ ∘ₑ δ) ν ≡ Conᴺₑ δ (Conᴺₑ σ ν)  
∘ₑOPEᴺ σ δ ∙       = refl
∘ₑOPEᴺ σ δ (ν , t) = _,_ & ∘ₑOPEᴺ σ δ ν ⊗ ∘ₑTyᴺ t σ δ

-- Action on identity
idₑConᴺ : ∀ {Γ Δ}(σᴺ : Conᴺ Γ Δ) → Conᴺₑ idₑ σᴺ ≡ σᴺ
idₑConᴺ ∙        = refl
idₑConᴺ (σᴺ , t) = _,_ & idₑConᴺ σᴺ ⊗ idₑTyᴺ t


-- ∈ᴺ v : Nat (Conᴺ Γ) (Tyᴺ A)
--------------------------------------------------------------------------------

∈ᴺ : ∀ {Γ A} → A ∈ Γ → ∀ {Δ} → Conᴺ Γ Δ → Tyᴺ A Δ
∈ᴺ vz     (σ , t) = t
∈ᴺ (vs v) (σ , t) = ∈ᴺ v σ

-- ∈ᴺ-nat : ∀ {Γ Δ Σ A}(v : A ∈ Σ)(σᴺ : Conᴺ Δ Σ)(δ : OPE Γ Δ) → ∈ᴺ v (Conᴺₑ σ δ) ≡ Tyᴺₑ δ (∈ᴺ v σ)
-- ∈ᴺ-nat vz     (σ , t) δ = refl
-- ∈ᴺ-nat (vs v) (σ , t) δ = ∈ᴺ-nat v σ δ

-- -- Tm
-- mutual
--   Tmᴺ : ∀ {Γ A} → Tm Γ A → ∀ {Δ} → Conᴺ Δ Γ → Tyᴺ A Δ
--   Tmᴺ (var v)   σ = ∈ᴺ v σ
--   Tmᴺ (lam t)   σ =
--       (λ δ aᴺ → Tmᴺ t (OPEᴺ δ σ , aᴺ))
--     , (λ δ ν aᴺ →
--           Tmᴺ-nat t (OPEᴺ δ σ , aᴺ) ν ⁻¹
--         ◾ (λ x → Tmᴺ t (x , aᴺ ᴺ[ ν ]ₑ)) & (OPEᴺ∘ δ ν σ ⁻¹))
--   Tmᴺ (app f a) σ = proj₁ (Tmᴺ f σ) idₑ (Tmᴺ a σ)

--   Tmᴺ-nat :
--     ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : Conᴺ Σ Γ)(δ : OPE Δ Σ)
--     → Tmᴺ t (OPEᴺ δ σ) ≡ Tmᴺ t σ ᴺ[ δ ]ₑ
--   Tmᴺ-nat (var v)   σ δ = ∈ᴺ-nat v σ δ
--   Tmᴺ-nat (lam t)   σ δ = ⇒ᴺ= (λ ν aᴺ → (λ x → Tmᴺ t (x , aᴺ)) & (OPEᴺ∘ δ ν σ ⁻¹))
--   Tmᴺ-nat (app f a) σ δ
--     rewrite proj₁ & Tmᴺ-nat f σ δ | Tmᴺ-nat a σ δ
--     = (λ x → proj₁ (Tmᴺ f σ) x (Tmᴺ a σ ᴺ[ δ ]ₑ)) & (idrₑ δ ◾ idlₑ δ ⁻¹)
--      ◾ proj₂ (Tmᴺ f σ) idₑ δ (Tmᴺ a σ) ⁻¹

-- mutual
--   qᴺ : ∀ {Γ A} → Tmᴺ Γ A → Nf Γ A
--   qᴺ {A = ι}     t = t
--   qᴺ {A = A ⇒ B} t = lam (qᴺ (proj₁ t wk (uᴺ (var vz))))

--   qᴺ-nat : ∀ {A Γ Δ}(tᴺ : Tmᴺ Γ A)(σ : OPE Δ Γ) → qᴺ tᴺ [ σ ]Nfₑ ≡ qᴺ (tᴺ ᴺ[ σ ]ₑ)
--   qᴺ-nat {ι}     tᴺ        σ = refl
--   qᴺ-nat {A ⇒ B} (f , nat) σ = lam &
--       (qᴺ-nat (f wk (uᴺ (var vz))) (keep σ)
--     ◾ qᴺ &
--         (nat (drop idₑ) (keep σ) (uᴺ (var vz))
--       ◾ (λ x → f (drop x) (uᴺ (var vz) ᴺ[ keep σ ]ₑ)) & (idlₑ σ ◾ idrₑ σ ⁻¹)
--       ◾ f (drop (σ ∘ₑ idₑ)) & uᴺ-nat (var vz) (keep σ)))

--   uᴺ : ∀ {Γ A} → Ne Γ A → Tmᴺ Γ A
--   uᴺ {A = ι}     n = ne n
--   uᴺ {A = A ⇒ B} n =
--     (λ δ aᴺ → uᴺ (app (n [ δ ]Neₑ) (qᴺ aᴺ))) ,
--     (λ σ δ aᴺ →
--         uᴺ-nat (app (n [ σ ]Neₑ) (qᴺ aᴺ)) δ
--       ◾ (λ x → uᴺ (app x (qᴺ aᴺ [ δ ]Nfₑ))) & ∘ₑNe n σ δ
--       ◾ (λ x → uᴺ (app (n [ σ ∘ₑ δ ]Neₑ) x)) & qᴺ-nat aᴺ δ)

--   uᴺ-nat : ∀ {A Γ Δ} → (n : Ne Γ A) → (σ : OPE Δ Γ) → uᴺ n ᴺ[ σ ]ₑ ≡ uᴺ (n [ σ ]Neₑ)
--   uᴺ-nat {ι}     n σ = refl
--   uᴺ-nat {A ⇒ B} n σ = ⇒ᴺ= (λ δ aᴺ → (λ x → uᴺ (app x (qᴺ aᴺ))) & ∘ₑNe n σ δ ⁻¹)

-- idᴺₛ : ∀ {Γ} → Tmsᴺ Γ Γ
-- idᴺₛ {∙}     = ∙
-- idᴺₛ {Γ , t} = idᴺₛ {Γ} ᴺ∘ₑ wk , uᴺ (var vz)

-- nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
-- nf t = qᴺ (Tm↑ᴺ t idᴺₛ)

--------------------------------------------------------------------------------

-- Tmsᴺ : ∀ {Γ Δ} → Tms Γ Δ → ∀ {Σ} → Conᴺ Σ Γ → Conᴺ Σ Δ
-- Tmsᴺ ∙       δ = ∙
-- Tmsᴺ (σ , t) δ = Tmsᴺ σ δ , Tmᴺ t δ

-- _ₛ∘ᴺ_ : ∀ {Γ Δ Σ} → Tms Γ Δ → Tmsᴺ Σ Γ → Tmsᴺ Σ Δ
-- ∙       ₛ∘ᴺ δ = ∙
-- (σ , t) ₛ∘ᴺ δ = (σ ₛ∘ᴺ δ) , Tm↑ᴺ t δ

-- idₑTmᴺ : ∀ {Γ A}(t : Tmᴺ Γ A) → t ᴺ[ idₑ ]ₑ ≡ t
-- idₑTmᴺ {A = ι}     t = idₑNf t
-- idₑTmᴺ {A = A ⇒ B} t = ⇒ᴺ= λ σ aᴺ → (λ x → proj₁ t x aᴺ) & idlₑ σ

-- idrᴺₑ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → σ ᴺ∘ₑ idₑ ≡ σ
-- idrᴺₑ ∙       = refl
-- idrᴺₑ (σ , t) = _,_ & idrᴺₑ σ ⊗ idₑTmᴺ t

-- infixr 6 _ₑ∘ᴺ_
-- _ₑ∘ᴺ_ : ∀ {Γ Δ Σ} → OPE Γ Δ → Tmsᴺ Σ Γ → Tmsᴺ Σ Δ
-- ∙      ₑ∘ᴺ δ       = δ
-- drop σ ₑ∘ᴺ (δ , t) = σ ₑ∘ᴺ δ
-- keep σ ₑ∘ᴺ (δ , t) = (σ ₑ∘ᴺ δ) , t

-- ∈↑ᴺ-nat₁ :
--   ∀ {Γ Δ Σ A}(v : A ∈ Γ)(σ : OPE Δ Γ)(δ : Tmsᴺ Σ Δ)
--   → ∈↑ᴺ (v [ σ ]∈ₑ) δ ≡ ∈↑ᴺ v (σ ₑ∘ᴺ δ)
-- ∈↑ᴺ-nat₁ ()     ∙        δ
-- ∈↑ᴺ-nat₁ v      (drop σ) (δ , t) = ∈↑ᴺ-nat₁ v σ δ
-- ∈↑ᴺ-nat₁ vz     (keep σ) (δ , t) = refl
-- ∈↑ᴺ-nat₁ (vs v) (keep σ) (δ , t) = ∈↑ᴺ-nat₁ v σ δ

-- assₑᴺₑ :
--   ∀ {Γ Δ Σ Ξ}(σ : OPE Σ Ξ)(δ : Tmsᴺ Δ Σ)(ν : OPE Γ Δ)
--   → (σ ₑ∘ᴺ δ) ᴺ∘ₑ ν ≡ σ ₑ∘ᴺ δ ᴺ∘ₑ ν
-- assₑᴺₑ ∙        δ       ν = refl
-- assₑᴺₑ (drop σ) (δ , t) ν = assₑᴺₑ σ δ ν
-- assₑᴺₑ (keep σ) (δ , t) ν = (_, t ᴺ[ ν ]ₑ) & assₑᴺₑ σ δ ν

-- Tm↑ᴺ-nat₁ :
--   ∀ {Γ Δ Σ A}(t : Tm Γ A)(σ : OPE Δ Γ)(δ : Tmsᴺ Σ Δ)
--   → Tm↑ᴺ (t [ σ ]ₑ) δ ≡ Tm↑ᴺ t (σ ₑ∘ᴺ δ)
-- Tm↑ᴺ-nat₁ (var v)   σ δ = ∈↑ᴺ-nat₁ v σ δ
-- Tm↑ᴺ-nat₁ (lam t)   σ δ = ⇒ᴺ= λ ν aᴺ →
--     Tm↑ᴺ-nat₁ t (keep σ) (δ ᴺ∘ₑ ν , aᴺ)
--   ◾ (λ x → Tm↑ᴺ t (x , aᴺ)) & (assₑᴺₑ σ δ ν ⁻¹)
-- Tm↑ᴺ-nat₁ (app f a) σ δ
--   rewrite Tm↑ᴺ-nat₁ f σ δ | Tm↑ᴺ-nat₁ a σ δ = refl

-- idlᴺₑ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → idₑ ₑ∘ᴺ σ ≡ σ
-- idlᴺₑ ∙       = refl
-- idlᴺₑ (σ , t) = (_, t) & idlᴺₑ σ

-- assₛₑᴺ :
--   ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : OPE Δ Σ)(ν : Tmsᴺ Γ Δ)
--   → (σ ₛ∘ₑ δ) ₛ∘ᴺ ν ≡ σ ₛ∘ᴺ δ ₑ∘ᴺ ν
-- assₛₑᴺ ∙       δ ν = refl
-- assₛₑᴺ (σ , t) δ ν = _,_ & assₛₑᴺ σ δ ν ⊗ Tm↑ᴺ-nat₁ t δ ν

-- assₛᴺₑ :
--   ∀ {Γ Δ Σ Ξ}(σ : Tms Σ Ξ)(δ : Tmsᴺ Δ Σ)(ν : OPE Γ Δ)
--   → (σ ₛ∘ᴺ δ) ᴺ∘ₑ ν ≡ σ ₛ∘ᴺ δ ᴺ∘ₑ ν
-- assₛᴺₑ ∙       δ ν = refl
-- assₛᴺₑ (σ , t) δ ν = _,_ & assₛᴺₑ σ δ ν ⊗ (Tm↑ᴺ-nat t δ ν ⁻¹)

-- idlᴺₛ : ∀ {Γ Δ}(σ : Tmsᴺ Γ Δ) → σ ≡ idₛ ₛ∘ᴺ σ
-- idlᴺₛ ∙       = refl
-- idlᴺₛ (σ , t) =
--   (_, t) & (((idlᴺₑ σ ⁻¹ ◾ idlᴺₛ (idₑ ₑ∘ᴺ σ)) ◾ assₛₑᴺ idₛ wk (σ , t) ⁻¹))

-- ₛ∘ᴺ∈↑ :
--   ∀ {Γ Δ Σ A}(v : A ∈ Δ)(σ : Tms Γ Δ)(δ : Tmsᴺ Σ Γ)
--   → Tm↑ᴺ (v [ σ ]∈) δ ≡ ∈↑ᴺ v (σ ₛ∘ᴺ δ)
-- ₛ∘ᴺ∈↑ vz     (σ , t) δ = refl
-- ₛ∘ᴺ∈↑ (vs v) (σ , t) δ = ₛ∘ᴺ∈↑ v σ δ

-- ₛ∘ᴺ↑ :
--   ∀ {Γ Δ Σ A}(t : Tm Δ A)(σ : Tms Γ Δ)(δ : Tmsᴺ Σ Γ)
--   → Tm↑ᴺ (t [ σ ]) δ ≡ Tm↑ᴺ t (σ ₛ∘ᴺ δ)
-- ₛ∘ᴺ↑ (var v)   σ δ = ₛ∘ᴺ∈↑ v σ δ
-- ₛ∘ᴺ↑ (lam t)   σ δ = ⇒ᴺ= λ ν aᴺ → 
--     ₛ∘ᴺ↑ t (keepₛ σ) (δ ᴺ∘ₑ ν , aᴺ)
--   ◾ (λ x → Tm↑ᴺ t ((x , aᴺ))) &
--       (assₛₑᴺ σ wk (δ ᴺ∘ₑ ν , aᴺ)
--     ◾ (σ ₛ∘ᴺ_) & idlᴺₑ (δ ᴺ∘ₑ ν)
--     ◾ assₛᴺₑ σ δ ν ⁻¹)
-- ₛ∘ᴺ↑ (app f a) σ δ
--   rewrite ₛ∘ᴺ↑ f σ δ | ₛ∘ᴺ↑ a σ δ = refl



