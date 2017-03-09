<!-- 
pandoc -s -N -F pandoc-crossref --toc --latex-engine=xelatex --biblatex stlc-nbe.md -o stlc-nbe.latex
&& latexmk -pdf -xelatex stlc-nbe.latex
-->

---
monofont: DejaVu Sans Mono
bibliography: [alti.bib, local.bib]
link-citations: true
csl: ieee.csl
lang: en

fontsize: 12pt
linestretch: 1.5
margin-left: 3.5cm
margin-right: 2.5cm
margin-top: 2.5cm
margin-bottom: 2.5cm

documentclass: article

header-includes:
   - \setlength\parindent{15pt}
   - \usepackage{amsthm}
   - \usepackage{indentfirst}
   - \newtheorem{theorem}{Theorem}
   - \newtheorem{definition}{Definition}

title: 
  A Machine-Checked Correctness Proof of Normalization by Evaluation
  for Simply Typed Lambda Calculus
author: 
- 'Author: András Kovács'
- 'Advisor: Ambrus Kaposi'
date: Budapest, 2017
abstract: "We implement and prove correct normalization by evaluation for simply typed lambda calculus, using the proof assistant Agda. The correctness proof consists of soundness, completeness and stability with respect to $\\beta\\eta$-conversion. The algorithm uses a Kripke model over the preordered set of order-preserving context embeddings. Completeness is given by a logical relation between the term model and the Kripke model. For soundness and stability, we first need to prove that evaluation, quoting and unquoting all commute with order-preserving embeddings, which amounts to showing that the codomain of the evaluation function can be refined to a presheaf model. Then, soundness is shown by a logical relation on semantic values which fall into the refined model. Stability is proved by induction on normal and neutral terms. Decidability of $\\beta\\eta$-conversion for terms also follows from correctness. The main advantage of the formalization is that normalization has a concise and structurally recursive specification and is presented separately from the correctness proofs. Also, the syntax of terms remains simple, making no use of explicit substitutions or closures. Overall, the technical overhead of the development is relatively light."

---

<!-- 
Diplomamunka fő részei spec szernint:

1. probléma  megfogalmazása
2. irodalom áttekintés
3. tárgyalás
4. értékelés

Program mellékelése elektronikusan (papírtokban a dipl-ban, lol)

Ez elég suta struktúra, jobb lenne, ha ezek csak szerepelnének, de nem így vagy ebben a sorrendben.
-->

\newpage

# Introduction

## Overview

Normalization animates the syntax of typed $\lambda$-calculi, make them useful as programming languages. Also, in contrast to general terms, normal forms possess a more restricted structure which simplifies formal reasoning. Moreover, normalization allows one to decide convertibility of terms, which is required during type checking polymorphic and dependent type theories.[^1] 

[^1]: In particular, the types of System F$_{\omega}$ largely correspond to simply typed $\lambda$-terms.

This thesis presents an efficient and verified implementation of $\beta\eta$-normalization for simply typed $\lambda$-calculus (STLC) in Agda, an implementation of constructive type theory. In this setting, the syntax can be seen as an embedded language, and manipulating embedded terms is a limited form of metaprogramming. Normalization can be reused in the implementation of proof tactics, decision procedures or domain-specific languages, therefore efficiency is desirable. We also keep the syntax as simple as possible, leaving substitutions implicit, as common in presentations of STLC.

We are not concerned with mapping the algorithm to lower-level abstract machines or hardware. Thus we are free to make use of the most convenient evaluation mechanism at hand: that of the metalanguage. This way, we can gloss over implementation details of efficient higher-order evaluation. This is the core idea of normalization by evaluation (NbE) from an operational point of view. Also, totality of evaluation in the metatheory is always implicitly assumed from the inside. This lets us implement normalization in a structurally recursive way, making its totality trivial. NbE is also naturally applicable for theories with $\eta$-conversion rules, in contrast to small-step reduction based approaches.

\pagebreak

If we are to trust a particular normalization algorithm, we need to prove the following properties (CIT: bigstep or alti):

* Completeness: terms are convertible to their normal forms.
* Soundness: normalization takes convertible terms to the same normal form.

Additionally, we may require stability, which establishes that there is no redundancy in normal forms:

* Stability: normalization acts as the identity function on normal terms.

TODO: Summary of chapters, some blahblah


## Related Work

TODO: Not directly related background: Martin-Löf, Berger & Schwichtenberg.

Catarina Coquand's work CIT is the most closely related to our development. She formally proves soundness and completeness of NbE for simple type theory, however she uses a nameful syntax with explicit substitutions, while we use intrinsic de Bruijn variables with implicit substitution.

Altenkirch and Chapman CIT formalize a big-step normalization algorithm in Agda. This development uses an explicit substitution calculus and implements normalization using an environment machine with first-order closures. The algorithm works similarly to ours on the common syntactic fragment, but it is not structurally recursive and hence specifies evaluation as a relation, using the Bove-Capretta method CIT.

Altenkirch and Kaposi CIT use a glued presheaf model ("presheaf logical predicate") for NbE for a minimal dependent type theory. This developments provided the initial impetus for this thesis; it seemed plausible that "scaling down" dependently typed NbE to simple type theory would yield a formalization that is more compact than existing ones. This turned to be the case; however the discussion of resulting development is relegated to [@sec:direct-psh-model], because using a Kripke model confers the advantage of clean separation of the actual algorithm and its naturality proofs, which was deemed preferable to the somewhat less transparent presheaf construction. Also, our work uses a simple presheaf model rather than the glued model used in Ibid. or in the work of Altenkirch, Hoffman and Streicher CIT.

For an alternative approach to NbE, see Abel CIT for an overview of NbE for a range of type theories, using extrinsic syntax and separate typed and untyped phases of evaluation.

\newpage

# Metatheory and Notation

In this chapter the metatheory used for formalization is presented, first broadly, then its specific implementation and notation in Agda.

## Type Theory

The basic system we use is intensional Martin-Löf type theory (MLTT) CIT. Moreover, we use:

* Strictly positive inductive types. These are required for an intrinsically well-typed syntax. We do not require induction-recursion, induction-induction or large inductive types.
* Two predicative universes, called `Set₀` and `Set₁`, with large elimination into `Set₀`. Large elimination is needed for recursive definitions of semantic types, since inductive definitions would not positive and hence would be illegal. We only need `Set₁` to type the large eliminations. 
* Function extensionality as an axiom. Its compatibility with MLTT is well-established; for instance the univalence axiom (which is compatible with MLTT) implies it. We could eschew function extensionality by using setoid reasoning with semantic equivalence, as C. Coquand does CIT. However, we only use function extensionality in correctness proofs, and the normalization function does not refer to it or to any other postulate. So, normalization is obviously executable, and we are content with *logical* as opposed to computational content for soundness and stability proofs. Also, function extensionality has computational interpretation in cubical CIT and observational CIT type theories, to which this development could be plausibly ported in the future (when practical implementations of the mentioned theories exist).

In the main development, we do not use Streicher's K axiom. We do use it in [@sec:direct-psh-model] for the direct preasheaf model, but the usage there is only for technical convenience, as it could be avoided by additional proofs of propositionality of equalities.


## Agda

TODO

# Syntax

## Base Syntax

<!-- Intrinsic vs extrinsic -->
<!-- dB vs nameful -->

## Context Embedding

TODO
<!-- adapted from Hoffman (semantics of TT) and Kaposi to STLC -->
  
## Substitution

TODO

## Conversion

TODO

## A Note on Categorical Semantics

TODO

# Normalization

TODO

## Preliminaries: Standard Model

TODO

## Normalization with a Kripke Model

TODO

## Completeness

TODO

## Naturality Proofs

TODO

## Soundness

TODO

## Stability

TODO

# Variations

## Direct Presheaf Model {#sec:direct-psh-model}

* Definition, proofs
* Semantic equality == propositional equality
* However: funext in definition of nf. Use external canonicity proof or metatheory with funext

## More Efficient Evaluation

* efficient embedding for semantic contexts
* Agda benchmarking
* performance limitations of intrinsic syntax compared to type assignment

# Discussion and Future Work

* Technical overhead: Vs big-step, hereditary subst, Coquand, Abel (?)
* Linecounts vs big-step and hsubst (email C. Coquand to get sources?)
* Usability as EDSL normalizer

* Scaling up the technique
  + With implicit substitution and conversion relation: to System F, probably
  foo


