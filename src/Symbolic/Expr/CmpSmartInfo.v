Require Import CoqStock.List.
Require Export CoqStock.Cmp.

Require Import Symbolic.Expr.CmpInfo.
Require Import Symbolic.Expr.SmartInfo.

Fixpoint compare_smart_info (x y: SmartInfo) {struct x} :=
  match x with
  | mkSmart x' _ =>
    match y with
    | mkSmart y' _ =>
      CmpInfo.compare_info x' y'
    end
  end.

Theorem proof_info_compare_eq_implies_equal: forall (x y: Info)
  (c: compare_info x y = Eq)
  , x = y.
Proof.
(*TODO*)
Admitted.

Theorem proof_info_compare_eq_reflex: forall (p: Info)
  , compare_info p p = Eq.
(*TODO*)
Admitted.

Theorem proof_info_compare_eq_trans: forall (x y z: Info)
  (xy: compare_info x y = Eq)
  (yz: compare_info y z = Eq)
  , compare_info x z = Eq.
(*TODO*)
Admitted.

Theorem proof_info_compare_lt_trans: forall (x y z: Info)
  (xy: compare_info x y = Lt)
  (yz: compare_info y z = Lt)
  , compare_info x z = Lt.
(*TODO*)
Admitted.

Theorem proof_info_compare_gt_trans: forall (x y z: Info)
  (xy: compare_info x y = Gt)
  (yz: compare_info y z = Gt)
  , compare_info x z = Gt.
(*TODO*)
Admitted.

#[export]
Instance CmpInfo: Cmp (Info) :=
  {
    compare := compare_info
  ; proof_compare_eq_implies_equal := proof_info_compare_eq_implies_equal
  ; proof_compare_eq_reflex := proof_info_compare_eq_reflex
  ; proof_compare_eq_trans := proof_info_compare_eq_trans
  ; proof_compare_lt_trans := proof_info_compare_lt_trans
  ; proof_compare_gt_trans := proof_info_compare_gt_trans
  }.