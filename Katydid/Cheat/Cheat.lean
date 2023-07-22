theorem example2:
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intros a b H
  cases H with
  | intro H1 H2 =>
    exact ⟨H2, H1⟩

theorem example2':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intros a b H
  cases H with
  | intro H1 H2 =>
    constructor -- apply And.intro
    case left => exact H2
    case right => exact H1

theorem example2'':
  ∀ a b: Prop, a /\ b -> b /\ a := by
  intros a b H
  cases H
  apply And.intro
  case left => assumption
  case right => assumption

theorem plus_assoc:
 forall x y z: Nat , (x+y)+z = x+(y+z) := by
intros x
induction x
case zero =>
  simp
case succ x0 IHx0 =>
  intros y z
  repeat rw [Nat.succ_add]
  rewrite [IHx0] -- rewrite [<- IHx0]
  rfl

theorem list_cons_ne_nil (x : α) (xs : List α):
  x :: xs ≠ [] := by
  intro h'
  contradiction

open List

theorem length_gt_zero (xs: List α):
  xs ≠ [] -> 0 < length xs := by
intros h
induction xs with
| nil =>
  contradiction
| cons x xs' _ =>
  simp
  apply Nat.zero_lt_succ

-- induction xs.
-- - contradiction.
-- - cbn.
--   lia.
