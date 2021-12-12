Class NatInput (A: Type) :=
  {
    getNat : A -> nat
  }.

#[export]
Instance NatIsNatInput: NatInput nat :=
  {
    getNat := fun (n: nat) => n
  }.

#[export]
Instance BoolIsNatInput: NatInput bool :=
  {
    getNat := fun (b: bool) =>
      match b with
      | false => 0
      | true => 1
      end
  }.