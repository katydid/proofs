(* Musketeers One for all *)

Require Import CoqStock.List.

Definition ForAll {A: Set} (P: A -> Prop) (xs: list A): Prop :=
  fold_left (fun p x => p /\ (P x)) xs True.