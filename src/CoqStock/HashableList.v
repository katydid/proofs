(*
A list is hashed by starting with a prime number, such as 17.
Next every element is added, by first multiplying the current hash with another prime number, such as 31 and then adding the value hash of the element.
*)

Require Import CoqStock.Hashable.
Require Import CoqStock.List.

Definition hash_per_elem {A: Type} {h: hashable A} (state: nat) (x: A): nat :=
    31 * state + hash x.

Definition list_hash {A: Type} {h: hashable A} (xs: list A): nat :=
    fold_left hash_per_elem xs 17.

Instance hashable_list {A: Type} {c: hashable A} : hashable (list A) :=
  {
    hash := list_hash
  }.
