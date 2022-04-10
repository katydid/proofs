(*
Eval is an evaluable function, that requires one input value.
Only the output value's type is encoded in the type.
*)

Class Eval (F: Type) (B: Set) :=
  {
    A : Set
  ; eval : F -> A -> B
  }
.