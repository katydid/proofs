Class BoolInput (A: Type) :=
  {
    getBool : A -> bool
  }.

#[export]
Instance BoolIsBoolInput: BoolInput bool :=
  {
    getBool := fun (b: bool) => b
  }.