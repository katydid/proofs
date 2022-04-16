(*
CmpFunc is an instance of Cmp for func_compare.
*)

Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import CoqStock.Cmp.
Require Import CoqStock.CmpBool.
Require Import CoqStock.CmpNat.
Require Import CoqStock.List.

Require Import Symbolic.Ast.Func.

Fixpoint func_compare (x y: Func) {struct x}: comparison :=
  match x with
  | mkFunc xname xparams xhash xstatic =>
    match y with
    | mkFunc yname yparams yhash ystatic =>
      match compare xhash yhash with
      | Lt => Lt
      | Gt => Gt
      | Eq =>
        match compare xstatic ystatic with
        | Lt => Lt
        | Gt => Gt
        | Eq =>
          match compare xname yname with
          | Lt => Lt
          | Gt => Gt
          | Eq => ((fix params_compare (xs ys: list Func) {struct xs} :=
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
                match func_compare x' y' with
                | Lt => Lt
                | Gt => Gt
                | Eq => params_compare xs' ys'
                end
              end
            end
          ) xparams yparams)
          end
        end
      end
    end
  end.

Theorem func_proof_compare_eq_implies_equal
  : forall (x y: Func)
           (p: func_compare x y = Eq)
  , x = y.
Proof.
(* TODO *)
Admitted.

Theorem func_proof_compare_eq_reflex
  : forall (x: Func)
  , func_compare x x = Eq.
Proof.
(* TODO *)
Admitted.

Theorem func_proof_compare_eq_trans
  : forall (x y z: Func)
           (xy: func_compare x y = Eq)
           (yz: func_compare y z = Eq)
  , func_compare x z = Eq.
Proof.
(* TODO *)
Admitted.


Theorem func_proof_compare_lt_trans
  : forall (x y z: Func)
           (xy: func_compare x y = Lt)
           (yz: func_compare y z = Lt)
  , func_compare x z = Lt.
Proof.
(* TODO *)
Admitted.


Theorem func_proof_compare_gt_trans
  : forall (x y z: Func)
           (xy: func_compare x y = Gt)
           (yz: func_compare y z = Gt)
  , func_compare x z = Gt.
Proof.
(* TODO *)
Admitted.

#[export]
Instance CmpFunc : Cmp Func :=
  { compare := func_compare
  ; proof_compare_eq_implies_equal := func_proof_compare_eq_implies_equal
  ; proof_compare_eq_reflex := func_proof_compare_eq_reflex
  ; proof_compare_eq_trans := func_proof_compare_eq_trans
  ; proof_compare_lt_trans := func_proof_compare_lt_trans
  ; proof_compare_gt_trans := func_proof_compare_gt_trans
  }.
