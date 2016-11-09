<!-- build with: pandoc --filter pandoc-citeproc -N --toc --latex-engine=xelatex -->

---
monofont: DejaVu Sans Mono
bibliography: [alti.bib, local.bib]
link-citations: true
csl: computer-science-research-and-development.csl

header-includes:
   - \setlength\parindent{12pt}
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
date: Budapest, 2016
abstract: "We present an executable implementation and correctness proof of normalization by evaluation for the simply typed lambda calculus, using the proof assistant Agda. First, we use a presheaf model over the category of order-preserving context embeddings to define the normalization function. Then we prove completeness by a Kripke logical relation between the term and presheaf models, and soundess by another Kripke logical relation on the presheaf model. Stability is proven by induction on normal forms. We follow Altenkirch, Hoffman and Streicher [@alti:ctcs95] in the usage of presheaf models, but unlike loc. cit. we keep the definition of normalization and its correctness proofs separate, and rely on direct type-theoretic rather than categorical constructions. Our formalization is lightweight in comparison to previous correctness proofs of normalization based on big-step evaluation [TODO] and hereditary substitution [TODO]."

---

# Introduction
## Normalization by evaluation
<!-- principles, history, core idea (set diagram?), uses -->
## Related work
<!-- (alti:ctcs95, Altenkirch & Kaposi, C. Coquand, Abel thesis (?)) -->

# Metatheory
<!-- MLTT with one univ., inductive types + funext -->
<!-- used constructions (sigma, ap, trans etc?, or only have equational reasoning in article?) -->

# Syntax
## Terms and contexts
## Categories-with-families

<!-- adapted from Hoffman (semantics of TT) and Kaposi to STLC -->
  
## Order-preserving embeddings
## Substitution
## Conversion

# Preliminaries: normalization with a complete Kripke model

# Presheaf model
## Presheaves
## Terms and contexts
## Embeddings and substitutions
## Normalization
# Correctness
## Completeness
## Soundness
## Stability

# Discussion
## Formal development
## Efficiency

<!-- (identity renaming: efficient up to whnf, extrinsic alg) -->
  
## Comparison
### Big-step normalization
### Hereditary substitution
## Future work

<!-- System F normalization -->

# References
