
Require Import Symbolic.Input.BoolInput.
Require Import Symbolic.Input.NatInput.
Require Import Symbolic.Input.Result.

Class Input (A: Type) :=
  {
    getBool : A -> Result bool
    ; getNat : A -> Result nat
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

Definition boolConst {A: Set} (v: bool): A -> Result bool :=
  fun _ => ok v.

Definition boolVar {A: Set} {b: BoolInput A}: A -> Result bool :=
  BoolInput.getBool.

Definition natConst {A: Set} (v: nat): A -> Result nat :=
  fun _ => ok v.

Definition natVar {A: Set} {n: NatInput A}: A -> Result nat :=
  NatInput.getNat.

Definition natEq {A: Set} (x y: A -> Result nat): A -> Result bool :=
  fun (v: A) => swallow Nat.eqb (x v) (y v).

Definition andBool {A: Set} (x y: A -> Result bool): A -> Result bool :=
  fun (v: A) => swallow andb (x v) (y v).

Definition example_expr1 {A: Set}: A -> Result bool :=
  andBool (boolConst true) (boolConst false).

Definition example_expr2 {A: Set} {b: BoolInput A}: A -> Result bool :=
  andBool boolVar (boolConst false).

Definition example_expr3 {A: Set} {i: Input A}: A -> Result bool :=
  andBool boolVar (boolConst false).

Definition example_expr4 {A: Set} {i: Input A}: A -> Result bool :=
  andBool (natEq natVar (natConst 1)) boolVar.