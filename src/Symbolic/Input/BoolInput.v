Require Import Symbolic.Input.Result.

Class BoolInput (A: Type) :=
  {
    getBool : A -> Result bool
  }.

#[export]
Instance BoolIsBoolInput: BoolInput bool :=
  {
    getBool := fun (b: bool) => ok b
  }.

<<<<<<< HEAD
(* Just and example of an input that is an error *)
=======
(* An example of an input that is an error *)
>>>>>>> main
#[export]
Instance NatIsBoolInput: BoolInput nat :=
  {
    getBool := fun (n: nat) => error 0
  }.
