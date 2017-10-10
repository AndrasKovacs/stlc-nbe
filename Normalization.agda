{-# OPTIONS --without-K #-}

module Normalization where

open import Syntax
open import Embedding
open import Nf
open import Presheaf

uConᴺ : ∀ {Γ} → Conᴺ Γ Γ
uConᴺ {∙}     = ∙
uConᴺ {Γ , A} = Conᴺₑ wk uConᴺ , uᴺ {A} (var vz)

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf t = qᴺ (Tmᴺ t uConᴺ)
