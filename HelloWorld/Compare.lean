
def less_than (x: Ordering) (y: Ordering): Ordering :=
  match x with
  | Ordering.eq => y
  | _ => x

instance : Repr Ordering where
  reprPrec
    | Ordering.lt, _ => "<"
    | Ordering.gt, _ => ">"
    | Ordering.eq, _ => "="

instance:  Mul Ordering where
  mul := less_than

theorem ordering_mul_assoc (a b c: Ordering):
  a * b * c = a * (b * c) := by
  cases a
  {
    case lt => rfl
  }
  case eq => rfl
  case gt => rfl

theorem ordering_mul_assoc' (a b c: Ordering):
  a * b * c = a * (b * c) :=
  by cases a with
  | eq => rfl
  | lt => rfl
  | gt => rfl

theorem ordering_mul_assoc'' (a b c: Ordering):
  a * b * c = a * (b * c) :=
  match a with
  | Ordering.eq => rfl
  | Ordering.lt => by rfl
  | Ordering.gt => by rfl