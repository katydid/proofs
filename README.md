# proofs

Proofs written in Lean4 for the core katydid validation algorithm

![Check Proofs](https://github.com/katydid/proofs/workflows/Check%20Proofs/badge.svg)

## Goal

The goal is to formalize the core katydid validation algorithm.  This algorithm allows us to validate millions of serialized data structures per second on a single core.  The algorithm is based on derivatives for regular expressions and extends this to Visibly Pushdown Automata (VPA), by splitting the derivative function into two functions.  It also includes several basic optimizations, such as memoization, simplification, laziness, zipping of multiple states, short circuiting, evaluation at compilation and a pull based parser for serialized data structures that allows us to skip over some of the parsing.  You can play around with the validation language on its [playground](http://katydid.github.io/play/).

## Background

### Brzozowski's Derivatives of Regular Expressions

If you are unfamiliar with Brzozowski's Derivatives you can watch this video.

<a href="https://www.youtube.com/watch?v=k9linVmyIiE&list=PLYwF9EIrl42S9ldgii7kfBEIHPle7PqMk&index=1" target="_blank">
 <img src="https://img.youtube.com/vi/k9linVmyIiE/maxres1.jpg" alt="Watch the video" width="480" border="10" />
</a>

## Plan

This is just a quick overview of the steps towards our goal.

**TODO**

## Development

### Contributing

Please read the [contributing guidelines](https://github.com/awalterschulze/regex-reexamined-coq/blob/master/CONTRIBUTING.md).  They are short and shouldn't be surprising.

### Setup

Lean has great [instructions for installing Lean4 in VS Code](https://github.com/leanprover/lean4/blob/master/doc/quickstart.md).

### Pair Programming

We have pair programming session on some Saturdays 14:00 - 17:00 UK time.
Please email [Walter](https://github.com/awalterschulze) if you would like to join us.

It would be helpful to already have an understanding of Inductive Predicates, but more advanced knowledge is not required.
