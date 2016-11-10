{-# OPTIONS --without-K #-}

module Nf where

open import Lib
open import Syntax
open import Embedding

infixl 8 _[_]Nfₑ _[_]Neₑ

mutual
  data Nf (Γ : Con) : Ty → Set where
    ne  : Ne Γ ι → Nf Γ ι
    lam : ∀ {A B} → Nf (Γ , A) B → Nf Γ (A ⇒ B)

  data Ne (Γ : Con) : Ty → Set where
    var : ∀ {A} → A ∈ Γ → Ne Γ A
    app : ∀ {A B} → Ne Γ (A ⇒ B) → Nf Γ A → Ne Γ B

mutual
  _[_]Nfₑ : ∀ {Γ Δ A} → Nf Δ A → OPE Γ Δ → Nf Γ A
  ne  n [ σ ]Nfₑ = ne (n [ σ ]Neₑ)
  lam n [ σ ]Nfₑ = lam (n [ keep σ ]Nfₑ)

  _[_]Neₑ : ∀ {Γ Δ A} → Ne Δ A → OPE Γ Δ → Ne Γ A
  var v     [ σ ]Neₑ = var (v [ σ ]∈ₑ)
  (app f a) [ σ ]Neₑ = app (f [ σ ]Neₑ) (a [ σ ]Nfₑ)

-- natural embedding into Tm
mutual
  ⌜_⌝ : ∀ {Γ A} → Nf Γ A → Tm Γ A
  ⌜ ne n  ⌝ = ⌜ n ⌝Ne
  ⌜ lam t ⌝ = lam ⌜ t ⌝

  ⌜_⌝Ne : ∀ {Γ A} → Ne Γ A → Tm Γ A
  ⌜ var v   ⌝Ne = var v
  ⌜ app n t ⌝Ne = app ⌜ n ⌝Ne ⌜ t ⌝

mutual
  ⌜⌝Neₑ-nat : ∀ {Γ Δ A}(n : Ne Γ A)(σ : OPE Δ Γ) → ⌜ n [ σ ]Neₑ ⌝Ne ≡ ⌜ n ⌝Ne [ σ ]ₑ
  ⌜⌝Neₑ-nat (var v)   σ = refl
  ⌜⌝Neₑ-nat (app f a) σ = app & ⌜⌝Neₑ-nat f σ ⊗ ⌜⌝Nfₑ-nat a σ

  ⌜⌝Nfₑ-nat : ∀ {Γ Δ A}(n : Nf Γ A)(σ : OPE Δ Γ) → ⌜ n [ σ ]Nfₑ ⌝ ≡ ⌜ n ⌝ [ σ ]ₑ
  ⌜⌝Nfₑ-nat (ne n)  σ = ⌜⌝Neₑ-nat n σ
  ⌜⌝Nfₑ-nat (lam n) σ = lam & ⌜⌝Nfₑ-nat n (keep σ)

-- (Ne _ A) and (Nf _ A) are presheaves on OPE
mutual
  ∘ₑNf :
    ∀ {Γ Δ Σ A}(t : Nf Σ A)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
    → t [ σ ∘ₑ δ ]Nfₑ ≡ t [ σ ]Nfₑ [ δ ]Nfₑ
  ∘ₑNf (ne n)  σ δ = ne & ∘ₑNe n σ δ
  ∘ₑNf (lam t) σ δ = lam & ∘ₑNf t (keep σ) (keep δ)  
    
  ∘ₑNe :
    ∀ {Γ Δ Σ A}(t : Ne Σ A)(σ : OPE Δ Σ)(δ : OPE Γ Δ)
    →  t [ σ ∘ₑ δ ]Neₑ ≡ t [ σ ]Neₑ [ δ ]Neₑ
  ∘ₑNe (var v)   σ δ = var & ∘ₑ∈ v σ δ
  ∘ₑNe (app f a) σ δ = app & ∘ₑNe f σ δ ⊗ ∘ₑNf a σ δ

mutual
  idₑNf : ∀ {Γ A}(n : Nf Γ A) → n [ idₑ ]Nfₑ ≡ n
  idₑNf (ne n)  = ne & idₑNe n
  idₑNf (lam n) = lam & idₑNf n

  idₑNe : ∀ {Γ A}(n : Ne Γ A) → n [ idₑ ]Neₑ ≡ n
  idₑNe (var v)   = var & idₑ∈ v
  idₑNe (app f a) = app & idₑNe f ⊗ idₑNf a

