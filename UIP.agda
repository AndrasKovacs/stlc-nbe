module UIP where

open import Lib

UIP : ∀ {α}{A : Set α}{a a' : A}(p q : a ≡ a') → p ≡ q
UIP refl refl = refl

