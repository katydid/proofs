(*
Eval is an evaluable function, that requires one input value.
Only the output value's type is encoded in the type.
*)

Class Eval (F: Type) (B: Type) :=
  {
    A : Type
  ; eval : F -> A -> B
  }.