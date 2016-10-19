# stlc-nbe
Will eventually be a full correctness proof for NbE for STLC, meaning:

- Stability
- Soundness
- Completeness

Currently, on `master` we have completeness and confluence in a way such that if we prove stability then soundness follows. Unfortunately, since we bake completeness and confluence into the normalization function, an external stability proof would involve a lot of equality and coercion shuffling. So that's a TODO now.

On `plain-nbe`, we have a very simple implementation of normalization without proofs, and we attepmpt to prove the three properties externally. Stability is easily done this way, and soundness and completeness wouldn't be hard except for one thing I have not figured out yet: how to prove that the semantic domain has eta conversion as strict equality. We know that this is true and provable if we define convertibility of the syntax as higher (quotient) constructors; see section 5.4 of [this](https://akaposi.github.io/th.pdf) and the Agda implementation [here](https://bitbucket.org/akaposi/tt-in-tt/src/7890e3effb05bf5662a9f339ab134a06bc85da05/PSh/?at=master). So, the TODO on this branch is to understand how eta conversion for semantics (presheaf model) is proven in the above link and how/whether it can be applied to our sytax which does not have a higher inductive definition of conversion.

