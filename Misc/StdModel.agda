{-# OPTIONS --without-K #-}

module Misc.StdModel where

open import Lib
open import Syntax

Tyˢ : Ty → Set
Tyˢ ι       = ⊥
Tyˢ (A ⇒ B) = Tyˢ A → Tyˢ B

Conˢ : Con → Set
Conˢ ∙       = ⊤
Conˢ (Γ , A) = Conˢ Γ × Tyˢ A

∈ˢ : ∀ {Γ A} → A ∈ Γ → Conˢ Γ → Tyˢ A
∈ˢ vz     Γˢ = proj₂ Γˢ
∈ˢ (vs v) Γˢ = ∈ˢ v (proj₁ Γˢ)

Tmˢ : ∀ {Γ A} → Tm Γ A → Conˢ Γ → Tyˢ A
Tmˢ (var v)   Γˢ = ∈ˢ v Γˢ
Tmˢ (lam t)   Γˢ = λ aˢ → Tmˢ t (Γˢ , aˢ)
Tmˢ (app f a) Γˢ = Tmˢ f Γˢ (Tmˢ a Γˢ)

idt : Tm ∙ (ι ⇒ ι)
idt = lam (var vz)



