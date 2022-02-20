(* class Tree a where
    getLabel :: a -> Label
    getChildren :: a -> [a] *)

  (* #[export]
  Instance BoolIsInput: Input bool :=
    {
      getBool := Symbolic.Input.BoolInput.getBool
      ; getNat := Symbolic.Input.NatInput.getNat
    }. *)

Require Import Symbolic.Input.Input.
Require Import Symbolic.Input.BoolInput.

(* TODO:
Implement monad instance for stream from
https://github.com/coq-community/coq-ext-lib
*)

Class Stream (S: Set) (A: Set) {i: Input A} :=
  {
    getNext : S -> S * (bool + A)
  }.

Require Import CoqStock.List.

Print BoolIsInput.

#[export]
Instance ListBoolIsStream: Stream (list bool) bool :=
  {
    getNext := fun(l: list bool) =>
      match l with
      | [] => ([], inl true)
      | (x::xs) => (xs, inr x)
      end
  }.

#[export]
Instance ListIsStream {A: Set} {i: Input A}: Stream (list A) A :=
  {
    getNext := fun(l: list A) =>
      match l with
      | [] => ([], inl true)
      | (x::xs) => (xs, inr x)
      end
  }.