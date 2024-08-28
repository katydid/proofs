# ReProving Agda in Lean

In this subproject we are working on translating the paper [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives) from Agda to LeanProver.

The goals of this project are to:

  - discover the differences between Agda and Lean
  - learn of different way to tackle proofs about derivatives of regular expressions
  - understand proofs and see if it is possible to not use too many tactics

## Links

  - [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives)
  - [Collaboration with Conal Elliott](https://github.com/conal/Collaboration)

## Differences with Agda implementation

Simply renamings:

| Description  | Original Agda | Translated Lean |
| :---         | :---:         | :---:           |
| Content      | Content       | Content         |
|              | `Set`         | `Type`          |
| universe levels  | `ℓ`, `b`  | `u`, `v`        |
| parametric types | `A`, `B`  | `α`, `β`        |
| isomorphism      | `↔`       | `<=>`           |
| extensional isomorphism | `⟷` | `∀ {w: List α}, (P w) <=> (Q w)` |

Syntax:

  - We dropped most of the syntax, in favour of `([a-z]|[A-Z]|')` names.
  - We use namespaces as much as possible to make dependencies clear to the reader without requiring "Go to Definition" and Lean to be installed.

Not just a renaming, but still a difference with little consequence:

  - `Lang` in Agda is defined as `Lang α` in Lean. The `A` parameter for `Lang` is lifted to the module level in Agda, but there doesn't seem to be a way to hide this in Lean.
