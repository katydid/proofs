import HelloWorld.Algebra

instance : Repr Ordering where
  reprPrec
    | Ordering.lt, _ => "<"
    | Ordering.gt, _ => ">"
    | Ordering.eq, _ => "="

-- lexicographical ordering
def lex (x: Ordering) (y: Ordering): Ordering :=
  match x with
  | Ordering.eq => y
  | _ => x

theorem lex_assoc:
  ∀ a b c, lex (lex a b) c = lex a (lex b c) := by
  intros a b c
  cases a <;> simp [lex]

theorem lex_assoc' (a b c: Ordering):
  lex (lex a b) c = lex a (lex b c) := by
  cases a
  {
    case lt => rfl
  }
  case eq => rfl
  case gt => rfl

theorem lex_assoc'' (a b c: Ordering):
  lex (lex a b) c = lex a (lex b c) :=
  by cases a with
  | eq => rfl
  | lt => rfl
  | gt => rfl

theorem lex_assoc''' (a b c: Ordering):
  lex (lex a b) c = lex a (lex b c) :=
  match a with
  | Ordering.eq => rfl
  | Ordering.lt => by rfl
  | Ordering.gt => by rfl

theorem lex_left_identity (a: Ordering):
  lex Ordering.eq a = a := by
  cases a <;> rfl

theorem lex_right_identity (a: Ordering):
  lex a Ordering.eq = a := by
  cases a <;> rfl

theorem lex_right_identity':
  ∀ x, lex x Ordering.eq = x := by
  intro x
  cases x
  · rfl
  · rfl
  · rfl

theorem lex_right_identity'':
  ∀ x, lex x Ordering.eq = x := by
  intro x
  cases x
  { rfl }
  { rfl }
  { rfl }

instance : Magma Ordering where
  op a b := lex a b

instance : Semigroup Ordering where
  is_assoc := lex_assoc

instance : Monoid Ordering where
  identity := Ordering.eq
  left_identity := lex_left_identity
  right_identity := lex_right_identity


section instances_using_structure'

  open algebra_using_structure'

  def instanceMagmaLex := Magma'Struct.mk Ordering lex
  def instanceMagmaLex': Magma'Struct := {
    carrier := Ordering,
    op := lex
  }

  def instanceSemigroupLex : Semigroup'Struct := {
    toMagma'Struct := instanceMagmaLex,
    is_assoc := lex_assoc
  }
  def instanceSemigroupLex' : Semigroup'Struct := {
    carrier := Ordering,
    op := lex,
    is_assoc := lex_assoc
  }

  def instanceMonoidLex : Monoid'Struct := {
    carrier := Ordering,
    op := lex,
    is_assoc := lex_assoc,
    e := Ordering.eq,
    left_identity := lex_left_identity,
    right_identity := lex_right_identity,
  }
  def instanceMonoidLex' : Monoid'Struct := {
    toSemigroup'Struct := instanceSemigroupLex,
    e := Ordering.eq,
    left_identity := lex_left_identity,
    right_identity := lex_right_identity,
  }

end instances_using_structure'