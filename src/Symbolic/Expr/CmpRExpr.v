Require Import CoqStock.List.
Require Export CoqStock.Cmp.

Require Import Symbolic.Expr.RExpr.


Definition compare_rexpr {A: Set} {B: Set} (x y: RExpr B): comparison :=
  compare_info (@get_info A B x) (@get_info A B y).

Theorem proof_rexpr_compare_eq_implies_equal: forall {A: Set} {B: Set} (x y: RExpr B)
  (c: @compare_rexpr A B x y = Eq)
  , x = y.
(*TODO*)
Admitted.

Theorem proof_rexpr_compare_eq_reflex: forall {A: Set} {B: Set} (p: RExpr B)
  , @compare_rexpr A B p p = Eq.
(*TODO*)
Admitted.

Theorem proof_rexpr_compare_eq_trans: forall {A: Set} {B: Set} (x y z: RExpr B)
  (xy: @compare_rexpr A B x y = Eq)
  (yz: @compare_rexpr A B y z = Eq)
  , @compare_rexpr A B x z = Eq.
(*TODO*)
Admitted.

Theorem proof_rexpr_compare_lt_trans: forall {A: Set} {B: Set} (x y z: RExpr B)
  (xy: @compare_rexpr A B x y = Lt)
  (yz: @compare_rexpr A B y z = Lt)
  , @compare_rexpr A B x z = Lt.
(*TODO*)
Admitted.

Theorem proof_rexpr_compare_gt_trans: forall {A: Set} {B: Set} (x y z: RExpr B)
  (xy: @compare_rexpr A B x y = Gt)
  (yz: @compare_rexpr A B y z = Gt)
  , @compare_rexpr A B x z = Gt.
(*TODO*)
Admitted.

#[export]
Instance CmpRExpr {A: Set} {B: Set}: Cmp (RExpr B) :=
  {
    compare := @compare_rexpr A B
  ; proof_compare_eq_implies_equal := proof_rexpr_compare_eq_implies_equal
  ; proof_compare_eq_reflex := proof_rexpr_compare_eq_reflex
  ; proof_compare_eq_trans := proof_rexpr_compare_eq_trans
  ; proof_compare_lt_trans := proof_rexpr_compare_lt_trans
  ; proof_compare_gt_trans := proof_rexpr_compare_gt_trans
  }.