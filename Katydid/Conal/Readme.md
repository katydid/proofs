# ReProving Agda in Lean

In this subproject we are working on translating the paper [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives) from Agda to LeanProver.

The goals of this project are to:

  - Discover the differences between Agda and Lean
  - Define proofs on `Type` instead of `Prop`, since each proof represents a different parse of the language.
  - Avoid tactics if possible, in favour of simple `trfl` (our version of `rfl`).

## Links

  - [Symbolic and Automatic Differentiation of Languages - Conal Elliott](http://conal.net/papers/language-derivatives)
  - [Collaboration with Conal Elliott](https://github.com/conal/Collaboration)

## Differences with Agda implementation

### Equality `≡`

Lean has `Prop` and `Type` and Agda has `Set`, which we can think of as `Type` in Lean. We want out proofs to be proof revelant, since each proof represents a different parse of our language. This means the theorems have to be defined on `Type`. For example we have equality redefined in terms of `Type` as `TEq` (using the syntax `≡`) and  we replace `rfl` with `trfl`, but we do not a replacement tactic for `rfl`.

```
inductive TEq.{tu} {α: Type tu} (a b: α) : Type tu where
  | mk : a = b -> TEq a b

def trfl {α : Type u} {a : α} : TEq a a := TEq.mk rfl
```

We needed to redefine the following types and functions to use `Type` instead of `Prop`:

| Description  | Prop  | Type  |
| :---         | :---: | :---: |
| equality     | `=`   | `≡` in [Tipe.lean](./Tipe.lean)  |
| equivalance  | `Mathlib.Logic.Equiv.Defs.Equiv`  | `TEquiv` or `<=>` in [Function.lean](./Function.lean) |
| decidability | `Decidable`  | `Decidability.Dec` in [Decidability.lean](./Decidability.lean) |

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

We dropped most of the syntax, in favour of `([a-z]|[A-Z]|'|?|\.)*` names.

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
| decidable equality | `_≟_`   | `Decidability.decEq`

All language operators defined in `Language.lagda` are referenced in other modules as `◇.∅`, while in Lean they are references as qualified and non notational names `Language.emptyset`. The exception is `Calculus.lean`, where `Language.lean` is opened, so they are not qualified.

### Explicit parameters.

We use explicit parameters and almost no module level parameters, for example `Lang` in Agda is defined as `Lang α` in Lean. In Agda the `A` parameter for `Lang` is lifted to the module level, but in this translation we make it explicit.
