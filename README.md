# proofs

Proofs written in [Lean4](https://leanprover.github.io/) for the core [katydid](https://katydid.github.io/) validation algorithm

![Check Proofs](https://github.com/katydid/proofs/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core [katydid](https://katydid.github.io/) validation algorithm.  This algorithm allows us to validate millions of serialized data structures per second on a single core. The algorithm is based on derivatives for regular expressions and extends this to Visibly Pushdown Automata (VPA), by splitting the derivative function into two functions. It also includes several basic optimizations, such as memoization, simplification, laziness, zipping of multiple states, short circuiting, evaluation at compilation, symbolic derivatives and a pull based parser for serialized data structures that allows us to skip over some of the parsing.  You can play around with the validation language on its [playground](http://katydid.github.io/play/).

## Plan

This is just a quick overview of the steps towards our goal.

### Symbolic regular expressions

Prove theorems about Symbolic regular expressions as a foundation to build upon.

- [x] Prove correctness of derivative algorithm via a commuting diagram.
- [ ] Prove correctness of derivative algorithm via a Regex type indexed with Language.
- [x] Prove decidability of derivative algorithm.
- [x] Prove correctness of simplification rules.
- [ ] Prove correctness of smart constructors.

Reuse as much as we can from [our previous work in Coq](https://github.com/katydid/regex-derivatives-coq) and our attempt at [Reproving Agda in Lean](https://github.com/katydid/symbolic-automatic-derivatives)

### Symbolic predicates

- [ ] Create expression language as described in the post: [Derivatives of Symbolic Automata explained](https://medium.com/@awalterschulze/derivatives-of-symbolic-automata-explained-4673dee6af82)
- [ ] Prove correctness of simplification rules for `or`, `and`, `false`, etc.
- [ ] Prove that non-reader functions can be pre-computed before evaluating time
- [ ] Prove that the optimized comparison method using a hash is comparable (transitive, associative, etc.)

### Katydid Algorithm

- [ ] Create Language definition for the symbolic tree expressions.
- [ ] Code Pull-based Parser class in Lean and implement JSON as an example.
- [ ] Code Katydid algorithm in Lean.
- [ ] Prove correctness of derivative tree algorithm.
- [ ] Prove decidablity of derivative tree algorithm.
- [ ] Prove that the simple tree function and the VPA functions are equivalent and equivalent to the inductive predicate.
- [ ] Prove correctness of new simplification rules
- [ ] Prove all optimizations of the katydid algorithm

## Contributing

Please check the [prerequisites](https://github.com/katydid/proofs#prerequisites) and read the [contributing guidelines](https://github.com/katydid/proofs/blob/master/CONTRIBUTING.md).  The contributing guidelines are short and shouldn't be surprising.

### Understanding Brzozowski derivatives

Contributing to this repo requires an understanding the underlying algorithm that is the subject of the proofs in this repo:

  - [Derivatives of Regular Expressions explained](https://medium.com/@awalterschulze/how-to-take-the-derivative-of-a-regular-expression-explained-2e7cea15028d)
  - [Derivatives of Context-Free Grammars explained](https://medium.com/@awalterschulze/derivatives-of-context-free-grammars-explained-3f930c5e363b) (only the simplification rules, smart constructors and memoization are important)
  - [Derivatives of Symbolic Automata explained](https://medium.com/@awalterschulze/derivatives-of-symbolic-automata-explained-4673dee6af82)

### Understanding LeanProver

This repo also requires an understanding of proof assistants, since all the proofs in this repo are done using LeanProver:

  - Knowledge of dependent types, induction and understanding the difference between a property `True` and a boolean `true`. We recommend reading [The Little Typer](https://mitpress.mit.edu/9780262536431/the-little-typer/) to gain an understanding of the basics.
  - Experience with an Interactive Theorem Prover, like Coq or Lean, including using tactics and Inductive Predicates. If you are unfamiliar with interactive theorem provers you can watch our [talk](https://www.youtube.com/watch?v=-NHWF4ntc1I) for a taste. We recommend reading [Coq in a Hurry](https://cel.archives-ouvertes.fr/file/index/docid/459139/filename/coq-hurry.pdf) as a quick overview and [Coq Art](https://www.labri.fr/perso/casteran/CoqArt/) up to `Chapter 8: Inductive Predicates` for a proper understanding.

Optionally the following will also be helpful, but this is not required:

  - Experience with Lean4, since this project is written in Lean4. We recommend reading:
    + [Theorem Proving in Lean4](https://leanprover.github.io/theorem_proving_in_lean4/title_page.html) to close the gap between Coq and Lean.
    + [Lean Manual](https://leanprover.github.io/lean4/doc/whatIsLean.html) for programming in Lean and Monads.
    + [Lean Tactics File](https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean)
    + [Coq Lean Tactic Cheat Sheet](https://github.com/katydid/coq-lean-cheatsheet/)
    + [Lean Standard Libary Documentation](https://leanprover-community.github.io/mathlib4_docs/Std/Data/HashMap/Basic.html#Std.HashMap)
    + [Lean4 Meta Programming Book](https://github.com/arthurpaulino/lean4-metaprogramming-book)
    + [Tactic List](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)

Questions about Lean4 can be asked on [proofassistants.stackexchange](https://proofassistants.stackexchange.com/) by tagging questions with `lean` and `lean4` or in the [Zulip Chat](https://leanprover.zulipchat.com/).

### Setup

  - Lean4 has exceptional [instructions for installing Lean4 in VS Code](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md).
  - Remember to also add `lake` (the build system for lean) to your `PATH`.  You can do this on mac by adding `export PATH=~/.elan/bin/:${PATH}` to your  `~/.zshrc` file
  - Use mathlib's cache to speed up building time by running: `$ lake exe cache get`
