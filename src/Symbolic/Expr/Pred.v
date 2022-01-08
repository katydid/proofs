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

Require Import Coq.Arith.Compare.

Require Import CoqStock.Cmp.

Require Import Symbolic.Expr.Eval.

(*
  Pred is a data structure that contains a predicate.
  It contains all the info required to satisfy predicate constraints,
  such as being comparable.
  Pred is intended to be opaque, such that we only rely on it's properties.
*)

Record RPred (A: Type): Type := mkRPred
  {
    fn : A -> bool
  ; name: nat (* TODO: name should be string *)
  }.

(* TODO: There will be more fields to compare in future *)
Definition compare_pred {A: Type} (p1 p2: RPred A) :=
  Nat.compare (name A p1) (name A p2).

Theorem proof_compare_eq_implies_equal: forall {A: Type} (p1 p2: RPred A)
  (c: compare_pred p1 p2 = Eq)
  , p1 = p2.
(* TODO *)
Admitted.

Theorem proof_compare_eq_reflex: forall {A: Type} (p: RPred A)
  , compare_pred p p = Eq.
(* TODO *)
Admitted.

Theorem proof_compare_eq_trans: forall {A: Type} (p1 p2 p3: RPred A)
  (c12: compare_pred p1 p2 = Eq)
  (c23: compare_pred p2 p3 = Eq)
  , compare_pred p1 p3 = Eq.
(* TODO *)
Admitted.

Theorem proof_compare_lt_trans: forall {A: Type} (p1 p2 p3: RPred A)
  (c12: compare_pred p1 p2 = Lt)
  (c23: compare_pred p2 p3 = Lt)
  , compare_pred p1 p3 = Lt.
(* TODO *)
Admitted.

Theorem proof_compare_gt_trans: forall {A: Type} (p1 p2 p3: RPred A)
  (c12: compare_pred p1 p2 = Gt)
  (c23: compare_pred p2 p3 = Gt)
  , compare_pred p1 p3 = Gt.
(* TODO *)
Admitted.

Instance CmpPred {A: Type}: Cmp (RPred A) :=
  {
    compare := compare_pred
  ; proof_compare_eq_implies_equal := proof_compare_eq_implies_equal
  ; proof_compare_eq_reflex := proof_compare_eq_reflex
  ; proof_compare_eq_trans := proof_compare_eq_trans
  ; proof_compare_lt_trans := proof_compare_lt_trans
  ; proof_compare_gt_trans := proof_compare_gt_trans
  }.

Definition eval_pred {A: Type} (p: RPred A) := (fn A p).

Instance EvalPred {A: Type}: Eval (RPred A) bool :=
  {
    eval :=  eval_pred
  }.

Class Pred (P: Type) :=
  {
    is_eval: Eval P bool
  ; is_cmp: Cmp P
  }.

Instance PredRPred {A: Type}: Pred (RPred A) :=
  {
    is_eval := EvalPred
  ; is_cmp := CmpPred
  }.
