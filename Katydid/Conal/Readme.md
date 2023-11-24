# ReProving Agda in Lean

In this subproject we are working on translating the paper [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives/paper.pdf) from Agda to LeanProver.

The goals of this project are to:

  - discover the differences between Agda and Lean
  - learn of different way to tackle proofs about derivatives of regular expressions
  - understand proofs and see if it is possible to not use too many tactics

## Links

  - [Agda code](https://github.com/conal/paper-2021-language-derivatives)
  - [Slides](http://conal.net/talks/language-derivatives.pdf)
  - [Paper](http://conal.net/papers/language-derivatives/paper.pdf)
  - [Collaboration with Conal Elliott](https://github.com/conal/Collaboration)

## Differences with Agda implementation

Simply renamings:

  - `Set` in Agda is `Type` in Lean.
  - universe levels is `ℓ` in Agda and `u` in Lean.
  - parametric types in Agda is `A` and `\alpha` in Lean.

Not just a renaming, but still a difference with little consequence:

  - `Lang` in Agda is defined as `Lang \alpha` in Lean. The `A` parameter for `Lang` is lifted to the module level in Agda, but there doesn't seem to be a way to hide this in Lean.