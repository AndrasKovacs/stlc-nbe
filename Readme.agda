module Readme where

-- Order in which you probably want to view modules
------------------------------------------------------------

import Syntax
import Renaming
import Nf
import Substitution
import Conversion

import Normalization
import Stability
import Completeness
import Soundness

-- Main results
------------------------------------------------------------

open import Lib

open Syntax
open Nf
open Conversion

nf : ∀ {Γ A} → Tm Γ A → Nf Γ A
nf = Normalization.nf

stability : ∀ {Γ A}(n : Nf Γ A) → nf (⌜ n ⌝) ≡ n
stability = Stability.stab

soundness : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
soundness = Soundness.sound

completeness : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝
completeness = Completeness.complete

