(*
CmpSmartFunc is an instance of Cmp for smart_func_compare.
*)

Require Import CoqStock.Cmp.
Require Import CoqStock.CmpBool.
Require Import CoqStock.CmpNat.
Require Import CoqStock.List.

Require Import Symbolic.Ast.Func.
Require Import Symbolic.Ast.SmartFunc.

Fixpoint sfunc_compare (x y: Func) {struct x}: comparison :=
  match x with
  | mkFunc xname xparams xhash xstatic =>
    match y with
    | mkFunc yname yparams yhash ystatic =>
      match compare xhash yhash with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
        match compare xname yname with
        | Lt => Lt
        | Gt => Gt
        | Eq =>
          match compare xstatic ystatic with
          | Lt => Lt
          | Gt => Gt
          | Eq => ((fix sparams_compare (xs ys: list Func) {struct xs} :=
            match xs with
            | [] =>
              match ys with
              | [] => Eq
              | _ => Lt
              end
            | (x'::xs') =>
              match ys with
              | [] => Gt
              | (y'::ys') =>
                match sfunc_compare x' y' with
                | Lt => Lt
                | Gt => Gt
                | Eq => sparams_compare xs' ys'
                end
              end
            end
          ) xparams yparams)
          end
        end
      end
    end
  end.

Definition smart_func_compare (x y: SmartFunc): comparison :=
  let (fx, sx) := x in
  let (fy, sy) := y in
  sfunc_compare fx fy.


Theorem func_proof_compare_eq_implies_equal
  : forall (x y: SmartFunc)
           (p: smart_func_compare x y = Eq)
  , x = y.
Proof.
(* TODO *)
Admitted.

Theorem func_proof_compare_eq_reflex
  : forall (x: SmartFunc)
  , smart_func_compare x x = Eq.
Proof.
(* TODO *)
Admitted.

Theorem func_proof_compare_eq_trans
  : forall (x y z: SmartFunc)
           (xy: smart_func_compare x y = Eq)
           (yz: smart_func_compare y z = Eq)
  , smart_func_compare x z = Eq.
Proof.
(* TODO *)
Admitted.


Theorem func_proof_compare_lt_trans
  : forall (x y z: SmartFunc)
           (xy: smart_func_compare x y = Lt)
           (yz: smart_func_compare y z = Lt)
  , smart_func_compare x z = Lt.
Proof.
(* TODO *)
Admitted.


Theorem func_proof_compare_gt_trans
  : forall (x y z: SmartFunc)
           (xy: smart_func_compare x y = Gt)
           (yz: smart_func_compare y z = Gt)
  , smart_func_compare x z = Gt.
Proof.
(* TODO *)
Admitted.

#[export]
Instance CmpSmartFunc : Cmp SmartFunc :=
  { compare := smart_func_compare
  ; proof_compare_eq_implies_equal := func_proof_compare_eq_implies_equal
  ; proof_compare_eq_reflex := func_proof_compare_eq_reflex
  ; proof_compare_eq_trans := func_proof_compare_eq_trans
  ; proof_compare_lt_trans := func_proof_compare_lt_trans
  ; proof_compare_gt_trans := func_proof_compare_gt_trans
  }.
