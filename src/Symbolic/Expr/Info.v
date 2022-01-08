Require Import CoqStock.Cmp.
Require Import CoqStock.DubStep.
Require Import CoqStock.List.
Require Import CoqStock.Invs.

(*
  Info is the all the information about the Parsed expression.
  This is mostly used to efficiently compare two expressions.
  This includes a hash and whether the expression has a variable.
*)
Inductive Info: Type :=
  mkInfo:
    forall
    (name: nat)
    (params: list Info)
    (hasvar: bool)
    (hash: nat),
  Info.

(* Info: Getters *)

Definition get_name (x: Info): nat :=
  match x with
  | mkInfo name _ _ _ => name
  end.

Definition get_params (x: Info): list Info :=
  match x with
  | mkInfo _ params _ _ => params
  end.

Definition get_hasvar (x: Info): bool :=
  match x with
  | mkInfo _ _ hasvar _ => hasvar
  end.

Definition get_hash (x: Info): nat :=
  match x with
  | mkInfo _ _ _ hash => hash
  end.

(* HasVar *)

Fixpoint any (xs: list bool): bool :=
  match xs with
  | [] => false
  | (x::xs) =>
    match x with
    | true => true
    | _ => any xs
    end
  end.

Definition has_var_from_params (params: list Info): bool :=
  let param_hasvars := map get_hasvar params in
  any param_hasvars.

(* Hash *)

Definition hash_per_elem (state: nat) (x: nat): nat :=
    31 * state + x.

Fixpoint hash_from_info (i: Info): nat :=
  match i with
  | mkInfo name params _ _ =>
    let name_hashed := 31 * 17 * name in
    let param_hashes := map hash_from_info params in
    fold_left hash_per_elem param_hashes name_hashed
  end.

(* Defined for the purpose of a generalized proof *)

(* hname is an already hashed name *)
Definition hash_from_params (hname: nat) (params: list Info): nat :=
  let param_hashes := map hash_from_info params in
  fold_left hash_per_elem param_hashes hname.

Definition hash_from_name_and_params (name: nat) (params: list Info): nat :=
  hash_from_params (31 * 17 * name) params.

Lemma same_hash_from_name_and_params_or_hash_from_info:
  forall (name: nat) (params: list Info) (hasvar: bool) (hash: nat),
  hash_from_name_and_params name params = hash_from_info (mkInfo name params hasvar hash).
Proof.
reflexivity.
Qed.
