module Readme where

{-

Full correctness proof of normalization-by-evaluation for simply typed
lambda calculus.

This branch uses a presheaf model over the category of order-preserving embeddings, making 
the overall formalization shorter but the normalization algorithm harder to read, compared
to the "separate-PSh" branch.

You can find a long writeup on the "separate-PSh" branch at "otdk-archive/stlc-nbe-otdk.pdf".

We use function extensionality and Axiom K, but no other postulates,
holes or unsafe pragmas. Extensionality doesn't interfere with the normalization
function, so it computes for all inputs. Also, the use of Axiom K could be eliminated with
a moderate amount of work.

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

-- Optionally, the whole development is mashed together in Everything.agda

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

