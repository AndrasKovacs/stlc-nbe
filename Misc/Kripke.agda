
module Misc.Kripke where

open import Syntax
open import Lib
open import Normalization
open import Embedding
open import NormalForm

record KripkeModel : Set₁ where
  field
    W       : Set
    _≤_     : W → W → Set
    ≤refl   : ∀ {w} → w ≤ w
    _≤◾_    : ∀ {w₁ w₂ w₃} → w₁ ≤ w₂ → w₂ ≤ w₃ → w₁ ≤ w₃
    _⊩ι     : W → Set
    ι-mono  : ∀ {w w'} → w ≤ w' → w ⊩ι → w' ⊩ι

  _⊩Ty_ : W → Ty → Set
  w ⊩Ty ι       = w ⊩ι
  w ⊩Ty (A ⇒ B) = ∀ {w'} → w ≤ w' → w' ⊩Ty A → w' ⊩Ty B

  _⊩Con_ : W → Con → Set
  w ⊩Con ∙       = ⊤
  w ⊩Con (Γ , A) = (w ⊩Con Γ) × (w ⊩Ty A)

  _⊩_ : Con → Ty → Set
  Γ ⊩ A = ∀ w → w ⊩Con Γ → w ⊩Ty A

  Ty-mono : ∀ {A w w'} → w ≤ w' → w ⊩Ty A → w' ⊩Ty A
  Ty-mono {ι}     σ p = ι-mono σ p
  Ty-mono {A ⇒ B} σ p δ q = p (σ ≤◾ δ) q

  Con-mono : ∀ {Γ}{w w'} → w ≤ w' → w ⊩Con Γ → w' ⊩Con Γ
  Con-mono {∙}     σ p = p
  Con-mono {Γ , A} σ p = Con-mono σ (proj₁ p) , Ty-mono {A} σ (proj₂ p)

  ⊩Tm : ∀ {Γ A} → Tm Γ A → Γ ⊩ A
  ⊩Tm (var vz)     w (_ , q) = q
  ⊩Tm (var (vs v)) w (p , q) = ⊩Tm (var v) w p
  ⊩Tm (lam t)      w p σ a   = ⊩Tm t _ (Con-mono σ p , a)
  ⊩Tm (app f a)    w p       = ⊩Tm f w p ≤refl (⊩Tm a w p)

N : KripkeModel
N = record {
    W      = Con
  ; _≤_    = λ Γ Δ → OPE Δ Γ
  ; ≤refl  = idₑ
  ; _≤◾_   = _∘ₑ_
  ; _⊩ι   = λ Γ → Nf Γ ι
  ; ι-mono = Nfₑ }

sound : ∀ {Γ A} → Tm Γ A → (M : KripkeModel) → let open KripkeModel M in Γ ⊩ A
sound (var vz)     M w (_ , q) = q
sound (var (vs v)) M w (p , _) = sound (var v) M w p
sound (lam t)      M w p σ a   = sound t M _ (Con-mono σ p  , a)     where open KripkeModel M
sound (app f a)    M w p       = sound f M w p ≤refl (sound a M w p) where open KripkeModel M

complete : Set₁
complete = ∀ {Γ A} → ((M : KripkeModel) → let open KripkeModel M in Γ ⊩ A) → Tm Γ A


