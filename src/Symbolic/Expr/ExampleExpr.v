(* Example Expressions to check that our representation of RExpr is what we want. *)
Require Import CoqStock.List.

Require Import Symbolic.Expr.Expr.
Require Import Symbolic.Expr.CmpExpr.

Require Import Symbolic.Input.BoolInput.
Require Import Symbolic.Input.NatInput.
Require Import Symbolic.Input.Result.

Definition boolConst {A: Set} (v: bool): RExpr bool :=
  smartRExpr (fun (_:A) => ok v) 0 [].

Definition boolVar {A: Set} {b: BoolInput A}: RExpr bool :=
  smartRExprVar getBool 1 [].

Definition natConst {A: Set} (v: nat): RExpr nat :=
  smartRExpr (fun (_:A) => ok v) 2 [].

Definition natVar {A: Set} {b: NatInput A}: RExpr nat :=
  smartRExprVar getNat 3 [].

Definition natEq {A: Set} (x y: RExpr nat): RExpr bool :=
  let f := (fun (v: A)  => swallow Nat.eqb (get_fn x v) (get_fn y v)) in
  smartRExpr f 4 (map get_sinfo [x; y]).

Definition smartAnd {A: Set} (x y: RExpr bool): RExpr bool :=
  let f := (fun (v: A)  => swallow andb (get_fn x v) (get_fn y v)) in
  match compare x y with
  | Lt => smartRExpr f 5 (map get_sinfo [x; y])
  | Gt => smartRExpr f 5 (map get_sinfo [y; x])
  | Eq => x
  end.
