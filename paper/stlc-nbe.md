<!-- 
pandoc -s -N --toc --latex-engine=xelatex --biblatex stlc-nbe.md -o stlc-nbe.latex
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





# Introduction

This paragraph won't be part of the note, because it
isn't indented. Here's a reference [@alti:tlca93]. Here's another [@alti:ctcs95].
And yet another here [@alti:csl98].

More references abound [@book; @devriese; @Palsberg; @mcbride2008applicative].

And yet more references [@alti:pisigma-new;@txa:mpc2010g;@alti:catind2;@alti:csl12;@alti:tlca13-hedberg;@alti:tlca13-small-ir].


## Normalization by evaluation

Lorem ipsum.

## Related work

Lorem ipsum.

# Metatheory

Lorem ipsum.

# Syntax

Lorem ipsum.

## Terms and contexts

Lorem ipsum.

## Categories-with-families


Lorem ipsum.
<!-- adapted from Hoffman (semantics of TT) and Kaposi to STLC -->
  
## Order-preserving embeddings

Lorem ipsum.

## Substitution

Lorem ipsum.

### Test level three header

Lorem ipsum.

## Conversion

Lorem ipsum.

# Preliminaries: normalization with a complete Kripke model

Lorem ipsum.

# Presheaf model

Lorem ipsum.

## Presheaves

Lorem ipsum.

## Terms and contexts

Lorem ipsum.

## Embeddings and substitutions

Lorem ipsum.

## Normalization

Lorem ipsum.

# Correctness

Lorem ipsum.

## Completeness

Lorem ipsum.

## Soundness

Lorem ipsum.

## Stability

Lorem ipsum.

# Discussion

Lorem ipsum.

## Formal development

Lorem ipsum.

## Efficiency

Lorem ipsum.

## Comparison

Lorem ipsum.

<!-- ### Big-step normalization -->
<!-- ### Hereditary substitution -->

## Future work

Lorem ipsum.

<!-- System F normalization -->

