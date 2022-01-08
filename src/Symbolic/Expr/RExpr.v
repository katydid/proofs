Require Import CoqStock.Cmp.
Require Import CoqStock.DubStep.
Require Import CoqStock.List.
Require Import CoqStock.Invs.

Require Import Symbolic.Input.Result.
Require Import Symbolic.Expr.Info.
Require Import Symbolic.Expr.SmartInfo.

(*
  RExpr is the underlying representation of an expression.
  Unlike Expr which is the class abstraction that will be exposed, RExpr is only meant for internal usage.
*)
Record RExpr {A: Set} (B: Set): Type :=
  mkRExpr {
    fn: A -> Result B
    ; sinfo: SmartInfo
  }.

(* Getters *)

Definition get_fn {A: Set} {B: Set} (x: RExpr B): A -> Result B :=
  fn B x.

Definition get_info {A: Set} {B: Set} (x: RExpr B): Info :=
  get_info (@sinfo A B x).

Definition get_sinfo {A: Set} {B: Set} (x: RExpr B): SmartInfo :=
  @sinfo A B x.

Definition get_name {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_info A B x with
  | mkInfo name _ _ _ => name
  end.

Definition get_params {A: Set} {B: Set} (x: RExpr B): list Info :=
  match @get_info A B x with
  | mkInfo _ params _ _ => params
  end.

Definition get_sparams {A: Set} {B: Set} (x: RExpr B): list SmartInfo :=
  get_smart_params (@sinfo A B x).

Definition get_hasvar {A: Set} {B: Set} (x: RExpr B): bool :=
  match @get_info A B x with
  | mkInfo _ _ hasvar _ => hasvar
  end.

Definition get_hash {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_info A B x with
  | mkInfo _ _ _ hash => hash
  end.

(* Smart Constructor for RExpr *)

Definition smartRExpr {A: Set} {B: Set} (fn: A -> Result B) (name: nat) (sparams: list SmartInfo): @RExpr A B :=
  mkRExpr A B fn (smartInfo name sparams).

Definition smartRExprVar {A: Set} {B: Set} (fn: A -> Result B) (name: nat) (sparams: list SmartInfo): @RExpr A B :=
  mkRExpr A B fn (smartInfoVar name sparams).
