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

### Simply renamings

Some things we renamed since they are simply called different things in Agda and Lean, while others were renamed to be closer to the Lean convention.

| Description  | Original Agda | Translated Lean |
| :---         | :---:         | :---:           |
|              | `Set`         | `Type`          |
| universe levels  | `ℓ`, `b`  | `u`, `v`        |
| parametric types | `A`, `B`  | `α`, `β`        |
| isomorphism      | `↔`       | `<=>`           |
| extensional isomorphism | `⟷` | `∀ {w: List α}, (P w) <=> (Q w)` |

### Namespaces / Qualified Imports

We use namespaces as much as possible to make dependencies clear to the reader without requiring "Go to Definition" and Lean to be installed.

| Description        | Original Agda | Translated Lean   |
| :---               | :---:         | :---:             |
| `List α -> Type u` | `◇.Lang`      | `Language.Lang`   |
| `List α -> β`      | `◇.ν`         | `Calculus.null`   |
| `(List α -> β) -> (a: α) -> (List α -> β)` | `◇.δ`     | `Calculus.derive` |
|                    | `Dec` | `Decidability.Dec` |

### Syntax

We dropped most of the syntax, in favour of `([a-z]|[A-Z]|')` names.

| Description  | Original Agda | Translated Lean |
| :---         | :---:         | :---:           |
| nullable     | `ν`           | `null`          |
| derivative of a string  | `𝒟` | `derives`      |
| derivative of a character    | `δ`  | `derive` |
|              | `∅`           | `emptyset`      |
|              | `𝒰`           | `universal`     |
| empty string | `𝟏`           | `emptystr`      |
| character    | ` c           | `char c`        |
|              | `∪`           | `or`            |
|              | `∩`           | `and`           |
| scalar       | `s · P`       | `scalar s P`    |
|              | `P ⋆ Q`       | `concat P Q`    |
| zero or more | `P ☆`        | `star P`        |
| decidable bottom  | `⊥?`     | `Decidability.empty?` |
| decidable top     | `⊤‽`     | `Decidability.unit?`  |
| decidable sum     | `_⊎‽_`   | `Decidability.sum?`   |
| decidable prod    | `_×‽_`   | `Decidability.prod?`   |
| `Dec α -> Dec (List α)` | `_✶‽` | `Decidability.list?` |
| `(β <=> α) -> Dec α -> Dec β` | `◃` | `Decidability.apply'` |

All language operators defined in `Language.lagda` are referenced in other modules as `◇.∅`, while in Lean they are references as qualified and non notational names `Language.emptyset`. The exception is `Calculus.lean`, where `Language.lean` is opened, so they are not qualified.

### Explicit parameters.

We use explicit parameters and almost no module level parameters, for example `Lang` in Agda is defined as `Lang α` in Lean. In Agda the `A` parameter for `Lang` is lifted to the module level, but in this translation we make it explicit.
