# proofs

Proofs written in Lean4 for the core [katydid](https://katydid.github.io/) validation algorithm

![Check Proofs](https://github.com/katydid/proofs/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core [katydid](https://katydid.github.io/) validation algorithm.  This algorithm allows us to validate millions of serialized data structures per second on a single core.  The algorithm is based on derivatives for regular expressions and extends this to Visibly Pushdown Automata (VPA), by splitting the derivative function into two functions.  It also includes several basic optimizations, such as memoization, simplification, laziness, zipping of multiple states, short circuiting, evaluation at compilation, symbolic derivatives and a pull based parser for serialized data structures that allows us to skip over some of the parsing.  You can play around with the validation language on its [playground](http://katydid.github.io/play/).

## Background

This is required reading for understanding the underlying algorithm.

- [Derivatives of Regular Expressions explained](https://medium.com/@awalterschulze/how-to-take-the-derivative-of-a-regular-expression-explained-2e7cea15028d)
- **TODO by 7 October**: Derivatives of Context-Free Grammars explained
- **TODO by 14 October**: Derivatives of Symbolic Automata explained
- **TODO TBD**: Derivatives of Tree Expressions explained

## Plan

This is just a quick overview of the steps towards our goal.

- Create Symbolic Predicates
  + Create expression language as described in the post: Derivatives of Symbolic Automata explained
  + Prove simplification rules for `or`, `and`, `false`, etc.
  + Prove that non-reader functions can be pre-computed before evaluating time
  + Prove that the optimized comparison method using a hash is comparable (transitive, associative, etc.)
- Create symbolic regular expressions, stealing from [our previous work in Coq](https://github.com/awalterschulze/regex-reexamined-coq/)
  + Create Inductive Predicate for symbolic regular expressions
  + Prove that these expressions are decidable
  + Create derivative algorithm for symbolic regular expressions
  + Prove that it is equivalent to the inductive predicate
- Extend the symbolic regular expressions to trees
  + Prove that these expressions are still decidable
  + Create derivative algorithm for symbolic tree expressions
  + Prove that it is equivalent to the inductive predicate
  + Prove all optimizations of the katydid algorithm

## Development

### Contributing

Please read the [contributing guidelines](https://github.com/katydid/proofs/blob/master/CONTRIBUTING.md).  They are short and shouldn't be surprising.

### Setup

Lean has great [instructions for installing Lean4 in VS Code](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md).

### Pair Programming

We have pair programming session on some Saturdays 14:30 - 17:00 UK time, stating 29 October. 

- If you would like to watch, this will be streamed on [Twitch](https://www.twitch.tv/awalterschulze).
- If you would like to do more than watch and join us inside the zoom session that we will be streaming, then we have some prerequisites to make sure you won't be out of your depth.

Prerequisites:
- Interactive theorem proving experience in for example Coq or Lean. This experience should include:
  + Understanding the difference between a property and a boolean
  + Experience with using tactics
  + Having defined and used Inductive Predicates
  + The rest we can teach you on the fly or it might be something we need to learn from you
- Having read the posts explaining the derivative algorithm that we are trying to prove.  See the [Background](https://github.com/katydid/proofs#background) section of the Readme.

Please email [Walter](https://github.com/awalterschulze) if you would like to join us.

