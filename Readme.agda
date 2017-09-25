module Readme where

{-
Full correctness proof of normalization-by-evaluation for simply typed
lambda calculus.

I have written up an MSc thesis from this. 
You can find the latest pdf version at otdk-archive/stlc-nbe-otdk.pdf

We use function extensionality, but no Axiom K, other postulates,
holes or unsafe pragmas.
-}

-- Order in which you probably want to view modules
------------------------------------------------------------

open import Syntax
open import Embedding
open import NormalForm
open import Substitution
open import Conversion

open import Normalization
open import Completeness

open import PresheafRefinement
open import Soundness
open import Stability


-- Main results
------------------------------------------------------------

open import Lib

normalization : ∀ {Γ A} → Tm Γ A → Nf Γ A
normalization = nf

stability : ∀ {Γ A}(n : Nf Γ A) → nf ⌜ n ⌝Nf ≡ n
stability = stable

soundness : ∀ {Γ A}{t t' : Tm Γ A} → t ~ t' → nf t ≡ nf t'
soundness = sound

completeness : ∀ {Γ A}(t : Tm Γ A) → t ~ ⌜ nf t ⌝Nf
completeness = complete

decidableConversion : ∀ {Γ A}(t t' : Tm Γ A) → Dec (t ~ t')
decidableConversion t t' with Nf≡? (nf t) (nf t')
... | inj₁ p = inj₁ (complete t ~◾ coe ((λ x → ⌜ x ⌝Nf ~ t') & p ⁻¹) (complete t' ~⁻¹))
... | inj₂ p = inj₂ (λ q → p (sound q))

