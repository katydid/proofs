(*
The predicate will be used in our symbolic derivatives

In a classic automaton a transition is made by comparing the input character to the defined character on the transition:
start_state -> next_state if input = 'a'
The symbolic automaton generalizes the classic automaton's transition to a predicate:
symbolic: state_state -> next_state if pred(input)

We need the predicates to be comparable, so that we can apply simplification rules.
We also need greater than and less than, to simplify large expressions, such as (A | B) & (B | A)
For example, sorting the ors in alphabetical order allows us to simplify to (A | B) & (A | B) , which can be simplified to A | B
*)

Require Import CoqStock.Cmp.
Require Import Symbolic.Expr.Eval.

Class Pred (P: Type) :=
  {
    is_eval: Eval P bool
  ; is_cmp: Cmp P
  }.
