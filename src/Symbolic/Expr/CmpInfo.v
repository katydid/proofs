Require Import CoqStock.List.
Require Export CoqStock.Cmp.

Require Import Symbolic.Expr.Info.

Fixpoint compare_info (x y: Info) {struct x} :=
  match x with
  | mkInfo xname xparams _ xhash =>
    match y with
    | mkInfo yname yparams _ yhash =>
      match Nat.compare xhash yhash with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
        match Nat.compare xname yname with
        | Lt => Lt
        | Gt => Gt
        | Eq => ((fix compare_params (xs ys: list Info) {struct xs} :=
        (match xs with
         | [] =>
           match ys with
           | [] => Eq
           | _ => Lt
           end
         | (x'::xs') =>
           match ys with
           | [] => Gt
           | (y'::ys') =>
             match compare_info x' y' with
             | Lt => Lt
             | Gt => Gt
             | Eq => compare_params xs' ys'
             end
           end
         end)) xparams yparams)
        end
      end
    end
  end
.

Theorem proof_info_compare_eq_implies_equal: forall (x y: Info)
  (c: compare_info x y = Eq)
  , x = y.
Proof.
intros.
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