Require Import CoqStock.Cmp.
Require Import CoqStock.DubStep.
Require Import CoqStock.List.
Require Import CoqStock.Invs.

Require Import Symbolic.Input.Result.
Require Import Symbolic.Ast.Func.
Require Import Symbolic.Ast.SmartFunc.

(*
  RExpr is the underlying representation of an expression.
  Unlike Expr which is the class abstraction that will be exposed, RExpr is only meant for internal usage.
*)
Record RExpr {A: Set} (B: Set): Type :=
  mkRExpr {
    fn: A -> Result B
    ; sfunc: SmartFunc
  }.

(* Getters *)

Definition get_fn {A: Set} {B: Set} (x: RExpr B): A -> Result B :=
  fn B x.

Definition get_func {A: Set} {B: Set} (x: RExpr B): Func :=
  get_func (@sfunc A B x).

Definition get_sfunc {A: Set} {B: Set} (x: RExpr B): SmartFunc :=
  @sfunc A B x.

Definition get_name {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_func A B x with
  | mkFunc name _ _ => name
  end.

Definition get_params {A: Set} {B: Set} (x: RExpr B): list Func :=
  match @get_func A B x with
  | mkFunc _ params _ => params
  end.

Definition get_sparams {A: Set} {B: Set} (x: RExpr B): list SmartFunc :=
  get_smart_params (@sfunc A B x).

Definition get_hash {A: Set} {B: Set} (x: RExpr B): nat :=
  match @get_func A B x with
  | mkFunc _ _ hash => hash
  end.

(* Smart Constructor for RExpr *)

Definition smartRExpr {A: Set} {B: Set} (fn: A -> Result B) (name: nat) (sparams: list SmartFunc): @RExpr A B :=
  mkRExpr A B fn (mkSmartFunc name sparams).
