(*
CmpBool is an instance of Cmp for bool_compare.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import CoqStock.Cmp.

Definition bool_compare (x: bool) (y: bool) : comparison :=
  match x with
  | false =>
    match y with
    | false => Eq
    | true => Lt
    end
  | true =>
    match y with
    | false => Gt
    | true => Eq
    end
  end.

Theorem bool_proof_compare_eq_implies_equal
  : forall (x y: bool)
           (p: bool_compare x y = Eq)
  , x = y.
Proof.
intros.
destruct x, y;
cbn in p;
try discriminate;
reflexivity.
Qed.

Theorem bool_proof_compare_eq_reflex
  : forall (x: bool)
  , bool_compare x x = Eq.
Proof.
intros.
destruct x; cbn; reflexivity.
Qed.

Theorem bool_proof_compare_eq_trans
  : forall (x y z: bool)
           (xy: bool_compare x y = Eq)
           (yz: bool_compare y z = Eq)
  , bool_compare x z = Eq.
Proof.
intros.
destruct x, y, z;
cbn in *;
try discriminate;
reflexivity.
Qed.

Theorem bool_proof_compare_lt_trans
  : forall (x y z: bool)
           (xy: bool_compare x y = Lt)
           (yz: bool_compare y z = Lt)
  , bool_compare x z = Lt.
Proof.
intros.
destruct x, y, z;
cbn in *;
try discriminate;
reflexivity.
Qed.

Theorem bool_proof_compare_gt_trans
  : forall (x y z: bool)
           (xy: bool_compare x y = Gt)
           (yz: bool_compare y z = Gt)
  , bool_compare x z = Gt.
Proof.
intros.
destruct x, y, z;
cbn in *;
try discriminate;
reflexivity.
Qed.

#[export]
Instance CmpBool : Cmp bool :=
  { compare := bool_compare
  ; proof_compare_eq_implies_equal := bool_proof_compare_eq_implies_equal
  ; proof_compare_eq_reflex := bool_proof_compare_eq_reflex
  ; proof_compare_eq_trans := bool_proof_compare_eq_trans
  ; proof_compare_lt_trans := bool_proof_compare_lt_trans
  ; proof_compare_gt_trans := bool_proof_compare_gt_trans
}.