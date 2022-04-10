Require Import Symbolic.Input.Result.

Class NatInput (A: Type) :=
  {
    getNat : A -> Result nat
  }.

#[export]
Instance NatIsNatInput: NatInput nat :=
  {
    getNat := fun (n: nat) => ok n
  }.

(* An example to show that different types can be cast to the same input type. *)
#[export]
Instance BoolIsNatInput: NatInput bool :=
  {
    getNat := fun (b: bool) =>
      match b with
      | false => ok 0
      | true => ok 1
      end
  }.