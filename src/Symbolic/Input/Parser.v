<<<<<<< HEAD
(* class Tree a where
    getLabel :: a -> Label
    getChildren :: a -> [a] *)

  (* #[export]
  Instance BoolIsInput: Input bool :=
    {
      getBool := Symbolic.Input.BoolInput.getBool
      ; getNat := Symbolic.Input.NatInput.getNat
    }. *)
=======
Require Import CoqStock.List.
>>>>>>> main

Require Import Symbolic.Input.Input.
Require Import Symbolic.Input.BoolInput.

(* TODO:
Implement monad instance for stream from
https://github.com/coq-community/coq-ext-lib
*)

<<<<<<< HEAD
Class Stream (S: Set) (A: Set) {i: Input A} :=
  {
    getNext : S -> S * (bool + A)
  }.

Require Import CoqStock.List.

Print BoolIsInput.

=======
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

>>>>>>> main
#[export]
Instance ListBoolIsStream: Stream (list bool) bool :=
  {
    getNext := fun(l: list bool) =>
      match l with
<<<<<<< HEAD
      | [] => ([], inl true)
      | (x::xs) => (xs, inr x)
=======
      | [] => ([], EOF)
      | (x::xs) => (xs, Next x)
>>>>>>> main
      end
  }.

#[export]
Instance ListIsStream {A: Set} {i: Input A}: Stream (list A) A :=
  {
    getNext := fun(l: list A) =>
      match l with
<<<<<<< HEAD
      | [] => ([], inl true)
      | (x::xs) => (xs, inr x)
=======
      | [] => ([], EOF)
      | (x::xs) => (xs, Next x)
>>>>>>> main
      end
  }.