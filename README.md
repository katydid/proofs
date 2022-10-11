# proofs

Proofs written in [Lean4](https://leanprover.github.io/) for the core [katydid](https://katydid.github.io/) validation algorithm

![Check Proofs](https://github.com/katydid/proofs/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core [katydid](https://katydid.github.io/) validation algorithm.  This algorithm allows us to validate millions of serialized data structures per second on a single core.  The algorithm is based on derivatives for regular expressions and extends this to Visibly Pushdown Automata (VPA), by splitting the derivative function into two functions.  It also includes several basic optimizations, such as memoization, simplification, laziness, zipping of multiple states, short circuiting, evaluation at compilation, symbolic derivatives and a pull based parser for serialized data structures that allows us to skip over some of the parsing.  You can play around with the validation language on its [playground](http://katydid.github.io/play/).

## Prerequisites

This is required reading for understanding the underlying algorithm, the subject of the proofs in this repo:

  - [Derivatives of Regular Expressions explained](https://medium.com/@awalterschulze/how-to-take-the-derivative-of-a-regular-expression-explained-2e7cea15028d)
  - [Derivatives of Context-Free Grammars explained](https://medium.com/@awalterschulze/derivatives-of-context-free-grammars-explained-3f930c5e363b) (only the simplification rules, smart constructors and memoization are important)
  - [Derivatives of Symbolic Automata explained](https://medium.com/@awalterschulze/derivatives-of-symbolic-automata-explained-4673dee6af82)

This repo also requires the following background:

  - Knowledge of dependent types, induction and understanding the difference between a property `True` and a boolean `true`. We recommend reading [The Little Typer](https://mitpress.mit.edu/9780262536431/the-little-typer/) to gain an understanding of the basics.
  - Experience with an Interactive Theorem Prover, like Coq or Lean, including using tactics and Inductive Predicates.  We recommend reading [Coq in a Hurry](https://cel.archives-ouvertes.fr/file/index/docid/459139/filename/coq-hurry.pdf) as a teaser and [Coq Art](https://www.labri.fr/perso/casteran/CoqArt/) up to `Chapter 8: Inductive Predicates` for a proper understanding.

Optionally the following will also be helpful, but this is not required:

  - Experience with Lean4, since this project is written in Lean4. We recommend reading [Theorem Proving in Lean4](https://leanprover.github.io/theorem_proving_in_lean4/title_page.html) to close the gap between Coq and Lean.

## Development

### Pair Programming Proofs

We have pair programming sessions on some Saturdays 14:00 - 17:00 UK time, starting 29 October. 

- If you would like to watch, this will be streamed on [Twitch](https://www.twitch.tv/awalterschulze) starting at 14:30. We will use the time from 14:00 to 14:30 for preparation.
- If you would like to do more than watch and join us inside the zoom session, then please make sure you have meet the [prerequisites](https://github.com/katydid/proofs#prerequisites) and email [Walter](https://github.com/awalterschulze).

### Plan

This is just a quick overview of the steps towards our goal.

- Create Symbolic Predicates
  + Create expression language as described in the post: Derivatives of Symbolic Automata explained
  + Prove simplification rules for `or`, `and`, `false`, etc.
  + Prove that non-reader functions can be pre-computed before evaluating time
  + Prove that the optimized comparison method using a hash is comparable (transitive, associative, etc.)
- Create the symbolic regular expressions for trees
  + Steal as much as we can from [our previous work in Coq](https://github.com/awalterschulze/regex-reexamined-coq/)
  + Prove that the induction predicate is decidable.
  + Create derivative functions for the symbolic tree expressions.
  + Prove that the simple tree function and the VPA functions are equivalent and equivalent to the inductive predicate.
  + Prove simplification rules
  + Prove all optimizations of the katydid algorithm
  + ...

### Contributing

Please check the [prerequisites](https://github.com/katydid/proofs#prerequisites) and read the [contributing guidelines](https://github.com/katydid/proofs/blob/master/CONTRIBUTING.md).  The contributing guidelines are short and shouldn't be surprising.

### Setup

Lean4 has exceptional [instructions for installing Lean4 in VS Code](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md).


