Require Import CoqStock.List.
Require Import CoqStock.Cmp.

(*
  Info is the all the information about the expression.
  This is mostly used to efficiently compare two expressions.
*)
Inductive Info: Type :=
  mkInfo :
    forall
    (name: nat)
    (params: list Info)
    (hasvar: bool)
    (hash: nat),
  Info.

(*
  TODO: Create Inductive type isSmartConstructed
  This will be useful for proofs
*)

(*
  RExpr is the underlying representation of an expression.
  Unlike Expr which is the class abstraction that will be exposed, RExpr is only meant for internal usage.
*)
Record RExpr {A: Set} (B: Set): Type :=
  mkRExpr {
    fn: A -> B
    ; info: Info
  }.

(* Getters *)

Definition get_fn {A: Set} {B: Set} (x: RExpr B): A -> B :=
  fn B x.

Definition get_info {A: Set} {B: Set} (x: RExpr B): Info :=
  @info A B x.

Definition get_name {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_info A B x with
  | mkInfo name _ _ _ => name
  end.

Definition get_name' (x: Info): nat :=
  match x with
  | mkInfo name _ _ _ => name
  end.

Definition get_params {A: Set} {B: Set} (x: RExpr B): list Info :=
  match @get_info A B x with
  | mkInfo _ params _ _ => params
  end.

Definition get_params' (x: Info): list Info :=
  match x with
  | mkInfo _ params _ _ => params
  end.

Definition get_hasvar {A: Set} {B: Set} (x: RExpr B): bool :=
  match @get_info A B x with
  | mkInfo _ _ hasvar _ => hasvar
  end.

Definition get_hasvar' (x: Info): bool :=
  match x with
  | mkInfo _ _ hasvar _ => hasvar
  end.

Definition get_hash {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_info A B x with
  | mkInfo _ _ _ hash => hash
  end.

Definition get_hash' (x: Info): nat :=
  match x with
  | mkInfo _ _ _ hash => hash
  end.

(* Smart Constructor for Info: Hash *)

Definition hash_info_per_elem (state: nat) (x: nat): nat :=
    31 * state + x.

Definition hash_info (name: nat) (params: list Info): nat :=
  let name_hash := 17 * 31 + name in
  let param_hashes := map get_hash' params in
  fold_left hash_info_per_elem param_hashes name_hash.

(* Smart Constructor for Info: HasVar *)

Fixpoint any (xs: list bool): bool :=
  match xs with
  | [] => false
  | (x::xs) =>
    match x with
    | true => true
    | _ => any xs
    end
  end.

Definition has_var_info (params: list Info): bool :=
  let param_hasvars := map get_hasvar' params in
  any param_hasvars.

(* Smart Constructor for Info *)

Definition smartInfo (name: nat) (params: list Info): Info :=
  mkInfo name params (has_var_info params) (hash_info name params).
