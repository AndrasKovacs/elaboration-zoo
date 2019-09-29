## elabzoo-poly-instantiation

WIP. This package will implement something which is called "impredicative
instantiation" in the literature related to GHC Haskell. Some prior publications
about this:

- Boxy Types: Inference for Higher-Rank Types and Impredicativity
- HMF: Simple type inference for first-class polymorphism
- Guarded Impredicative Polymorphism
- https://github.com/ghc-proposals/ghc-proposals/pull/274

My solution has the following properties:
  - Fully dependent types.
  - Agda-style optionally named implicit arguments with first-class
    implicit function types.
  - No polymorphic subsumption. It only makes sense if quantification
    is proof-irrelevant, which it isn't in dependent type theory.
  - No let-generalization. It's possible to support it, but it's a
    significant complexity which is orthogonal to the current focus.
  - More powerful inference than any of the prior solutions.
  - Mid-level complexity of implementation.
