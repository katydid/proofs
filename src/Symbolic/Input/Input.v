
Require Import Symbolic.Input.BoolInput.
Require Import Symbolic.Input.NatInput.

Class Input (A: Type) :=
  {
    getBool : A -> bool
    ; getNat : A -> nat
  }.

#[export]
Instance BoolIsInput: Input bool :=
  {
    getBool := Symbolic.Input.BoolInput.getBool
    ; getNat := Symbolic.Input.NatInput.getNat
  }.

#[export]
Instance InputIsBoolInput (A: Type) {i: Input A}: BoolInput A :=
  {
    getBool := getBool
  }.

#[export]
Instance InputIsNatInput (A: Type) {i: Input A}: NatInput A :=
  {
    getNat := getNat
  }.

Definition boolConst {A: Set} (v: bool): A -> bool :=
  fun _ => v.

Definition boolVar {A: Set} {b: BoolInput A}: A -> bool :=
  BoolInput.getBool.

Definition natConst {A: Set} (v: nat): A -> nat :=
  fun _ => v.

Definition natVar {A: Set} {n: NatInput A}: A -> nat :=
  NatInput.getNat.

Definition natEq {A: Set} (x y: A -> nat): A -> bool :=
  fun (v: A)  => Nat.eqb (x v) (y v).

Definition andBool {A: Set} (x y: A -> bool): A -> bool :=
  fun (v: A) => andb (x v) (y v).

Definition example_expr1 {A: Set}: A -> bool :=
  andBool (boolConst true) (boolConst false).

Definition example_expr2 {A: Set} {b: BoolInput A}: A -> bool :=
  andBool boolVar (boolConst false).

Definition example_expr3 {A: Set} {i: Input A}: A -> bool :=
  andBool boolVar (boolConst false).

Definition example_expr4 {A: Set} {i: Input A}: A -> bool :=
  andBool (natEq natVar (natConst 1)) boolVar.