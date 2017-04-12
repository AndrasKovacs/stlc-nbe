
module Misc.Category where

open import Lib hiding (_∘_)

record Category : Set₁ where
  field
    Obj   : Set
    morph : Obj → Obj → Set
    id    : ∀ {I} → morph I I
    _∘_   : ∀ {I J K} → morph J K → morph I J → morph I K
    idl   : ∀ {I J}(f : morph I J) → f ∘ id ≡ f
    idr   : ∀ {I J}(f : morph I J) → id ∘ f ≡ f
    ass   : ∀ {I J K L}(f : morph K L)(g : morph J K)(h : morph I J) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
open Category

record Functor (C D : Category) : Set₁ where
  field
    Obj⇒   : Obj C → Obj D
    morph⇒ : ∀ {I J} → morph C I J → morph D (Obj⇒ I) (Obj⇒ J)
    id⇒    : ∀ {I} → morph⇒ (id C {I}) ≡ id D
    ∘⇒     : ∀ {I J K}{f : morph C J K}{g : morph C I J} → morph⇒ (_∘_ C f g) ≡ _∘_ D (morph⇒ f) (morph⇒ g)
open Functor

record Nat {C D : Category}(F G : Functor C D) : Set₁ where
  field
    ψ   : ∀ {I} → morph D (Obj⇒ F I) (Obj⇒ G I)
    nat : ∀ {I J}{f : morph C I J} → _∘_ D ψ (morph⇒ F f) ≡ _∘_ D (morph⇒ G f) ψ





