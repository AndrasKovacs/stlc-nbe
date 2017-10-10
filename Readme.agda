module Readme where

{-

Full correctness proof of normalization-by-evaluation for
simple type theory with finite products and finite weak (i. e. no eta) coproducts.

You can find a long writeup of a simpler formalization without products/coproducts
on the "separate-PSh" branch at "paper/stlc-nbe-otdk.pdf".
-}

-- Order in which you probably want to view modules
------------------------------------------------------------

import Syntax
import Embedding
import Nf
import Substitution
import Conversion

import Presheaf
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

stability : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝ ≡ n
stability = Stability.stab

soundness : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
soundness = Soundness.sound

completeness : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝
completeness = Completeness.complete
