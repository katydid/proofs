Require Import Symbolic.Input.Result.
Require Import CoqStock.Cmp.
Require Import Symbolic.Expr.Eval.

Class Expr (E: Type) (B: Set) :=
  {
    is_eval: Eval E (Result B)
  ; is_cmp: Cmp E
  }
.
