Set Implicit Arguments.
Set Asymmetric Patterns.

Require Import Coq.Lists.List.

Require Import CoqStock.Comparable.
Require Import CoqStock.Comparable_nat.

Fixpoint comparable_list {A: Type} {cmp: comparable A} (xs: list A) (ys: list A) : comparison :=
  match xs with
  | nil => match ys with
      | nil => Eq
      | _ => Lt
      end
  | x :: xs => match ys with
      | nil => Gt
      | y :: ys => match compare x y with
          | Eq => comparable_list xs ys
          | Lt => Lt
          | Gt => Gt
          end
      end
  end.

(* test_compare_list simply tests whether nat can be used
   with a function that expects a comparable instance.
   compare_list is defined in comparable,
   specifically for this use case.
*)
Definition test_compare_list : Prop :=
    comparable_list (1 :: 2 :: nil) (1 :: 3 :: nil) = Lt.