# proofs
Proofs written in Coq for the core katydid validation algorithm

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

### Symbolic Derivatives

We will start small, taking our learnings from [regex-reexamined-coq](https://github.com/awalterschulze/regex-reexamined-coq/) and applying them to symbolic derivatives.  Symbolic derivatives is a simple abstraction of regular expression derivatives that abstracts out the alphabet.  It replaces the alphabet with predicates, such that in a classic automaton a transition is made by comparing the input character to the character on the transition:

```
start_state -> next_state if input = 'a'
```

The symbolic automaton generalizes the classic automaton's transition to a predicate:

```
state_state -> next_state if pred(input), where pred = \input -> input == 'a'
```

This has the implication that we could explore the automaton without knowing the full alphabet and in fact the alphabet can now be infinite, without sacrificing any decidability properties. Unfortunately this does push some complexity onto the transitions, which can grow into `if` expressions with exponential complexity.

- A basic introduction to symbolic automaton can be found in [Symbolic Boolean Derivatives - Caleb Stanford, Margus Veanes and Nikolaj Bjorner](https://www.cis.upenn.edu/~castan/doc/2021/PLDI21.pdf). They also show how derivatives can be used to add better regex support to z3, which is very interesting, but adds complexities that aren't necessarily applicable to us.
- For a larger overview of how symbolic automata fit into the larger computer science field including tree transducers and more, see ["The Power of Symbolic Automata and Transducers" Loris D’Antoni | CAV 2017](https://www.youtube.com/watch?v=ca9IF-7nSOA)

In the final implementation of the algorithm, these predicates can be a set of nested functions, for example: `and(ge($int, 10), lt($int, 20))`. This is also something we can explore, and we could prove that evaluation during compilation of the constant parts is equivalent to evaluation at runtime.

The reason to explore symbolic automaton first, is because symbolic derivatives can technically use trees as their input alphabet and so provide a quick win, but also we will also heavily use the `if` expressions in our final VPA implementation.

A tree in Haskell is simply:

```haskell
data Tree a = Node {
  rootLabel :: a,
  subForest :: [Tree a]
}
```

Side note: The subForest is a list of trees, or in theoretical terms a Hedge.

A predicate on a tree would simply reuse the derivative function on it's children:
```
pred = \(Node label children) ->
  label == 'a' &&
  nullable (foldl derive children childexpr)
```

### Derivatives on Trees

Applying our symbolic derivatives on trees, would require creating a tree and a pull based parser abstraction, see [an example in Go](https://katydid.github.io/parser/addingparsers.html)

This is an optional opportunity to create a formalization of JSON, Protocol Buffers and/or [XML](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.105.8616&rep=rep1&type=pdf).

Another optional opportunity is to formalize the [Haskell algorithm for RelaxNG](http://www.thaiopensource.com/download/old/relaxng/20020531/derivative.html), which is where the whole derivative approach on this project started.

### Visibly Pushdown Automaton Derivatives

[Visibly Pushdown Automata (VPA)](https://repository.upenn.edu/cgi/viewcontent.cgi?article=1174&context=cis_papers) are built for nested words.  They have 3 transition types: calls (to go down), returns (to go up) and internals (to go forward).  They include a stack, but unlike pushdown automata, the alphabets for these 3 transition types are disjoint, which gives them the same decidability properties as regular expressions.  The downside is some of these decisions come at a much higher complexity.

VPAs are slightly more expressive than we require, since we are only interested in trees, but VPAs can technically work on for example unbalanced parentheses, where we are only interested in balanced grammars.  The advantage of using BVPAs (Balanced Visibly Pushdown Automata) over Regular Tree Automata, is that they first walk down and then back up the tree, which makes a big difference in how easy it is to express and translate our validation language to the underlying algorithm.  Also of note is that when implementing a bottom up Tree Automaton, one would have to walk down the tree before one could start running the bottom up algorithm, so as you are walking down anyway, why not evaluate and try to short circuit using some predicates.

Applying derivatives to BVPAs requires splitting the derivative function into two parts: `deriveCall` and `deriveReturn`, which can be pull together to express the original derive function:

```haskell
derive :: Regex -> Char -> Regex
derive e a = fst $ derivReturn e $ map nullable $ derivCall e a
```

These two functions are much better at memoization and lazily building the VPAs states, than the original derive function, as they take a single label as input, instead of a whole tree.
This algorithm also makes heavy use of the `if` expressions that we will cover during our implementation of symbolic automaton.  These `if` expressions don't just return a single state, but rather a list of states, which provides an opportunity to zip the states, before sending them down the recursive algorithm and unzip them when the results are returned. The calls also provide an opportunity to short circuit and skip parsing a part of the tree, if the resulting expressions of the `if` expression are all dead ends, such as `.*` and empty set.

## Development

### Contributing

Please read the [contributing guidelines](https://github.com/awalterschulze/regex-reexamined-coq/blob/master/CONTRIBUTING.md).  They are short and shouldn't be surprising.

### Setup

1. Install [Coq 8.14.0](https://github.com/coq/platform/releases/tag/2021.02.2)
2. Remember to set coq in your PATH. For example, in your `~/.bash_profile` add `export PATH="/Applications/Coq_Platform_2021.09.0.app/Contents/Resources/bin/:${PATH}"` and run `$ source ~/.bash_profile`.
3. Open CoqIDE by right clicking (since it is not properly signed for mac).
4. Run make in this folder.

### Clean

 - `make cleanall` cleans all files even `.aux` files.

### Regenerate Makefile

Coq version upgrade requires regenerating the Makefile with the following command:

```
$ coq_makefile -f _CoqProject -o Makefile
```

### VS Code

1. Install VS Code
2. Install the VSCoq extension
3. Go to settings and set your `CoqTop: Bin Path` to `/Applications/Coq_Platform_2021.09.0.app/Contents/Resources/bin/`
4. Use Cmd+Option+Down and Cmd+Option+Left to walk through the proof

### Pair Programming

We have pair programming session on some Saturdays 14:00 - 17:00 UK time.
Please email [Walter](https://github.com/awalterschulze) if you would like to join us.
It would be helpful to understand how to use Coq's Inductive Predicates, but more advanced knowledge is not required.
