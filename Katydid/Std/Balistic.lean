import Katydid.Std.Lists

import Katydid.Std.Ltac
import Qq
open Qq

-- balistic is a tactic that tries to solve simple theorems about lists

-- list_empty is a tactic that tries to solve simple theorems about empty lists
-- Reference for list tactic in Coq: https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/Listerine.v#L59-L107
local elab "list_empty" : tactic => do
  let goal ← getGoalProp
  match goal with
  | ~q([] ≠ $xs ++ ($y :: $ys)) =>
    -- [] ≠ xs ++ y :: ys
    run `(tactic| apply list_app_cons_not_nil )
  | ~q([] ≠ $x :: $xs) =>
    -- [] ≠ x :: xs
    run `(tactic| apply list_cons_nil_ne )
  | ~q($x :: $xs ≠ []) =>
    -- x :: xs ≠ []
    run `(tactic| apply list_cons_ne_nil )
  | _ => return ()
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match ty with
    | ~q([] = $x :: $xs) =>
      -- [] = x :: xs -> False
      run `(tactic| contradiction )
    | ~q($x :: $xs = []) =>
      -- x :: xs = [] -> False
      run `(tactic| contradiction )
    | ~q([] = $xs ++ ($y :: $ys)) =>
      -- [] = xs ++ y :: ys -> False
      _ ← mkHyp (toString name) `(list_app_cons_not_nil _ _ _ $name)
      run `(tactic| contradiction )
    | ~q($xs ++ $ys = []) =>
      -- xs ++ ys = [] -> xs = [] /\ ys = []
      let conjName ← mkHyp "H" `((list_app_nil_nil _ _).mp $name)
      run `(tactic| clear $name)
      _ ← mkHyp (toString name ++ "Left") `(($conjName).left )
      _ ← mkHyp (toString name ++ "Right") `(($conjName).right )
      run `(tactic| clear $conjName)
      run `(tactic| try subst_vars )
    | ~q([] = $xs ++ $ys) =>
      -- [] = xs ++ ys -> xs = [] /\ ys = []
      let symmName ← mkHyp "Hsymm" `(Eq.symm $name)
      run `(tactic| clear $name)
      let conjName ← mkHyp "H" `((list_app_nil_nil _ _).mp $symmName)
      run `(tactic| clear $symmName)
      _ ← mkHyp (toString name ++ "Left") `(($conjName).left )
      _ ← mkHyp (toString name ++ "Right") `(($conjName).right )
      run `(tactic| clear $conjName)
      run `(tactic| try subst_vars )
    | _ => return ()
  run `(tactic| try rw [list_app_nil_l] at * )
  run `(tactic| try rw [list_app_nil_r] at * )
  run `(tactic| try subst_vars )

example (H: [] = List.cons x xs): False := by
  have h: Lean.Name := `list_empty
  list_empty

example (H: List.cons x xs = []): False := by
  list_empty

example (H: [] = x :: xs): False := by
  list_empty

example (H: x :: xs = []): False := by
  list_empty

example: [] ≠ x :: xs := by
  list_empty

example: x :: xs ≠ [] := by
  list_empty

example (H : xs ++ ys = []): ys = [] := by
  list_empty
  rfl

example (H0: xs ++ ys = []) (H1: zs = ys): zs = [] := by
  list_empty
  rfl

example (H0: [] = xs ++ ys) (H1: zs = ys): zs = [] := by
  list_empty
  rfl

example: [] ++ xs = xs := by
  list_empty

example: xs ++ [] = xs := by
  list_empty

example (H: [] ++ xs = ys): ys = xs := by
  list_empty
  rfl

example (H: xs ++ [] = ys): ys = xs := by
  list_empty
  rfl

example: [] ≠ [x] := by
  list_empty

example: [x] ≠ [] := by
  list_empty

example (y: α) (xs ys: List α): [] ≠ xs ++ (y :: ys) := by
  list_empty

example (y: α) (xs ys: List α) (H: [] = xs ++ (y :: ys)): False := by
  list_empty

local elab "list_single" : tactic => do
  let goal ← getGoalProp
  match goal with
  | ~q([] ≠ $xs ++ ($y :: $ys)) =>
    -- [] ≠ xs ++ y :: ys
    run `(tactic| apply list_app_cons_not_nil )
  | _ => return ()
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match ty with
    | ~q($xs ++ $ys = [$a]) =>
      -- xs ++ ys = [a] -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = [])
      applyIn name `(list_app_eq_unit)
    | _ => return ()

example (H: xs ++ ys = [a]): (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  list_single
  assumption
