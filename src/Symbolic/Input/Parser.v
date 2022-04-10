Require Import CoqStock.List.

Require Import Symbolic.Input.Input.
Require Import Symbolic.Input.BoolInput.

(* TODO:
Implement monad instance for stream from
https://github.com/coq-community/coq-ext-lib
*)

Inductive next (A : Set) : Set :=
  | EOF : next A
  | Next : A -> next A
.

Arguments EOF {A}.
Arguments Next {A} _.

Class Stream (S: Set) (A: Set) {i: Input A} :=
  {
    getNext : S -> S * next A
  }.

#[export]
Instance ListBoolIsStream: Stream (list bool) bool :=
  {
    getNext := fun(l: list bool) =>
      match l with
      | [] => ([], EOF)
      | (x::xs) => (xs, Next x)
      end
  }.

#[export]
Instance ListIsStream {A: Set} {i: Input A}: Stream (list A) A :=
  {
    getNext := fun(l: list A) =>
      match l with
      | [] => ([], EOF)
      | (x::xs) => (xs, Next x)
      end
  }.