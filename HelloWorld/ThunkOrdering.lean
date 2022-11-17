import HelloWorld.Algebra

instance : Repr (Thunk Ordering) where
  reprPrec thunk _ :=
    match thunk.get with
    | Ordering.lt => "<"
    | Ordering.gt => ">"
    | Ordering.eq => "="

-- lexicographical ordering
def lex (x: Thunk Ordering) (y: Thunk Ordering): Thunk Ordering :=
  match x.get with
  | Ordering.eq => y
  | _ => x.get

theorem thunkAux : (fun _ => as ()) = as := funext fun x => by
    cases x
    exact rfl

theorem thunk' : (fun _ => as ()) = as := funext fun x => by
    cases x
    exact rfl

theorem lex_assoc:
  ∀ a b c, lex (lex a b) c = lex a (lex b c) := by
  intros a b c
  unfold lex
  cases a.get with
  | lt => simp only
          simp [Thunk.get]
  | gt => dsimp
          rfl
  | eq => dsimp only

theorem lex_left_identity (a: Thunk Ordering):
  lex Ordering.eq a = a := by
  cases a <;> rfl

theorem thunky (x: Thunk α):
  x = Thunk.mk (fun _ => x.get) :=
  rfl

theorem lex_right_identity (a: Thunk Ordering):
  lex a Ordering.eq = a := by
  unfold lex
  cases h: a.get <;>
    simp only <;>
    rw [<-h] <;>
    rfl

instance : Magma (Thunk Ordering) where
  op a b := lex a b

instance : Semigroup (Thunk Ordering) where
  is_assoc := lex_assoc

instance : Monoid (Thunk Ordering) where
  empty := Ordering.eq
  left_identity := lex_left_identity
  right_identity := lex_right_identity
