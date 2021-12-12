(* Example Expressions to check that our representation of RExpr is what we want. *)
Require Import CoqStock.List.

Require Import Symbolic.Expr.Expr.
Require Import Symbolic.Expr.CmpExpr.



(* TODO: Add a module implicit for A *)

Definition boolConst {A: Set} (v: bool): RExpr bool :=
  smartRExpr (fun (_:A) => v) 0 [].

Definition boolVar: RExpr bool :=
  smartRExprVar (fun (v:bool) => v) 1 [].

Definition natConst {A: Set} (v: nat): RExpr nat :=
  smartRExpr (fun (_:A) => v) 2 [].

Definition natVar: RExpr nat :=
  (* TODO: how do we know A is nat, it could not be, see https://github.com/katydid/katydid/blob/master/parser/parser.go#L32 *)
  smartRExprVar (fun (v:nat) => v) 3 [].

Definition natEq {A: Set} (x y: RExpr nat): RExpr bool :=
  let f := (fun (v: A)  => Nat.eqb (get_fn x v) (get_fn y v)) in
  smartRExpr f 4 (map get_info [x; y]).

(* Definition andBool {A: Set} (x y: RExpr bool): RExpr bool :=
  let f := (fun (v: A) => andb (get_fn x v) (get_fn y v)) in
  smartRExpr f 5 (map get_info [x; y]). *)

Definition smartAnd {A: Set} (x y: @RExpr nat bool): @RExpr bool bool :=
  let f := (fun (v: A)  => andb (get_fn x v) (get_fn y v)) in
  match compare x y with
  | Lt => smartRExpr f 5 (map get_info [x; y])
  | Gt => smartRExpr f 5 (map get_info [y; x])
  | Eq => x
  end.
