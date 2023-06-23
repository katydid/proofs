import Katydid.Std.Lists

import Katydid.Std.Ltac
import Qq
open Qq

-- balistic is a tactic that tries to solve simple theorems about lists

-- TODO: incorporate ac_rfl into balistic
-- ac_rfl uses IsAssociative to prove associativity of operators
example (xs ys zs: List α): (xs ++ ys ++ zs) = (xs ++ ys) ++ zs := by
  ac_rfl

-- list_empty is a tactic that tries to solve simple theorems about empty lists
-- Reference for list tactic in Coq: https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/Listerine.v#L59-L107
local elab "list_empty" : tactic => newTactic do
  let goal ← getGoalProp
  match goal with
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
  have _: Lean.Name := `list_empty
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

local elab "list_single" : tactic => newTactic do
  let goal ← getGoalProp
  match goal with
  | ~q([] ≠ $xs ++ ($y :: $ys)) =>
    -- [] ≠ xs ++ y :: ys
    run `(tactic| apply list_nil_ne_app_cons )
  | ~q($xs ++ ($y :: $ys) ≠ []) =>
    -- xs ++ y :: ys ≠ []
    run `(tactic| apply list_app_cons_ne_nil )
  | ~q($xs ++ [$x] = $ys ++ [$y]) =>
      -- xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y
    run `(tactic| apply list_inj_tail_app)
  | ~q($x :: $xs = $y :: $ys) =>
    -- x :: xs = y :: ys -> x = y /\ xs = ys
    run `(tactic| apply list_cons_eq.mpr)
  | _ => return ()
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match ty with
    | ~q($xs ++ $ys = [$a]) =>
      -- xs ++ ys = [a] -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = [])
      applyIn name `(list_app_eq_unit)
    | ~q([$a] = $xs ++ $ys) =>
      -- [a] = xs ++ ys -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = [])
      applyIn name `(list_eq_unit_app)
    | ~q([] = $xs ++ ($y :: $ys)) =>
      -- [] = xs ++ y :: ys -> False
      _ ← mkHyp (toString name) `(list_nil_ne_app_cons _ _ _ $name)
      run `(tactic| contradiction )
    | ~q($xs ++ [$x] = $ys ++ [$y]) =>
      -- xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y
      applyIn name `(list_app_inj_tail)
      _ ← mkHyp (toString name ++ "Left") `(($name).left )
      _ ← mkHyp (toString name ++ "Right") `(($name).right )
    | ~q($x :: $xs = $y :: $ys) =>
      -- x :: xs = y :: ys -> x = y /\ xs = ys
      applyIn name `(list_cons_eq.mp)
      _ ← mkHyp (toString name ++ "Left") `(($name).left )
      _ ← mkHyp (toString name ++ "Right") `(($name).right )
    | _ =>
      return ()
  run `(tactic| try rw [list_app_assoc_singleton] at * )
  run `(tactic| try rw [← list_app_comm_cons] at * )

example (H: xs ++ ys = [a]): (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  list_single
  assumption

example (H: [a] = xs ++ ys): (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  list_single
  assumption

example (y: α) (xs ys: List α): [] ≠ xs ++ (y :: ys) := by
  list_single

example (y: α) (xs ys: List α) (H: [] = xs ++ (y :: ys)): False := by
  list_single

example (xs ys: List α) (y: α): ([] ≠ xs ++ (y :: ys)) := by
  list_single

example (xs ys: List α) (y: α): (xs ++ (y :: ys) ≠ []) := by
  list_single

example (as xs ys: List α) (z: α) (H: xs ++ (ys ++ [z]) = as): as = (xs ++ ys) ++ [z] := by
  list_single
  apply Eq.symm
  assumption

example (as xs ys: List α) (z: α) (H: (xs ++ ys) ++ [z] = as): as = xs ++ (ys ++ [z]) := by
  list_single
  apply Eq.symm
  assumption

example (x: α) (xs ys: List α): x :: (xs ++ ys) = (x :: xs) ++ ys := by
  list_single

example (x: α) (as xs ys: List α) (H: as = x :: (xs ++ ys)): (x :: xs) ++ ys = as := by
  list_single
  apply Eq.symm
  assumption

example (x y: α) (xs ys: List α) (H: x :: xs = y :: ys): x = y := by
  list_single
  assumption

example (x y: α) (xs ys zs: List α) (H: x = y) (H0: xs = zs) (H1: ys = zs): x :: xs = y :: ys := by
  list_single
  rw [H, H0, H1]
  apply And.intro <;> rfl

example (xs ys: List α) (x y: α) (H: xs ++ [x] = ys ++ [y]): x = y := by
  list_single
  assumption

example (xs ys zs: List α) (x y: α) (H: x = y) (H0: xs = zs) (H1: ys = zs): xs ++ [x] = ys ++ [y] := by
  list_single
  rw [H, H0, H1]
  apply And.intro <;> rfl

example (xs ys zs: List α) (y z: α) (H: xs ++ ys ++ [y] = zs ++ [z]): y = z := by
  list_single
  assumption

example (xs ys zs: List α) (y z: α) (H: xs ++ (ys ++ [y]) = zs ++ [z]): y = z := by
  list_single
  list_single
  assumption

-- In the goal and hypotheses, simplify at least these two theorems
-- list_app_inv_head: xs ++ ys = xs ++ zs -> ys = zs
-- list_app_inv_tail: xs ++ zs = ys ++ zs -> xs = ys
local elab "list_app" : tactic => newTactic do
  run `(tactic| simp )

example (xs ys zs: List α):
  xs ++ ys = xs ++ zs -> ys = zs := by
  list_app

example (xs ys zs: List α):
  ys ++ xs = zs ++ xs -> ys = zs := by
  list_app

example (xs ys zs: List α):
  ys = zs -> xs ++ ys = xs ++ zs := by
  list_app

example (xs ys zs: List α):
  ys = zs -> ys ++ xs = zs ++ xs := by
  list_app


local elab "wreck_exists" : tactic => newTactic do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match ty with
    | ~q(∃ x _y, $p x) =>
      let e ← fresh "e"
      let E ← fresh "E"
      run `(tactic| cases $name:ident <;> rename_i $name:ident <;> rename_i $e:ident)
      run `(tactic| cases $name:ident <;> rename_i $name:ident <;> rename_i $E:ident)
    | _ =>
      return ()

local elab "wreck_conj": tactic => newTactic do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match ty with
    | ~q($x /\ $y) =>
      _ ← mkHyp (toString name ++ "Left") `(($name).left )
      _ ← mkHyp (toString name ++ "Right") `(($name).right )
    | _ =>
      return ()

-- list_app_uncons:
--  Finds an hypotheses that it can deconstruct using the list_app_cons lemma:
--  ys ++ zs = x :: xs
--  into the two goals, which consist of the possible combinations, as in:
--  - ys = [] /\ zs = x :: xs
--  - .
local elab "list_app_uncons" : tactic => newTactic do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    match ty with
    | ~q($ys ++ $zs = $x :: $xs ) =>
      applyIn name `(list_app_uncons)
      run `(tactic| cases $name:ident <;> rename_i $name:ident)
      run `(tactic| any_goals wreck_exists)
      run `(tactic| all_goals wreck_conj)
      run `(tactic| all_goals simp [*])
    | _ =>
      return ()

example (xs ys: List α) (x y: α):
  xs ++ ys = [x,y] ->
  (xs = [] /\ ys = [x,y])
  \/ (xs = [x] /\ ys = [y])
  \/ (xs = [x,y] /\ ys = []) := by
  intro H
  list_app_uncons
  list_single
  cases H with
  | inl H =>
    apply Or.inl
    assumption
  | inr H =>
    apply Or.inr
    assumption

example (xs ys: List α) (x y: α):
  xs ++ ys = [x,y,z] ->
  (xs = [] /\ ys = [x,y,z])
  \/ (xs = [x] /\ ys = [y,z])
  \/ (xs = [x,y] /\ ys = [z])
  \/ (xs = [x,y,z] /\ ys = []) := by
  intro H
  list_app_uncons
  list_app_uncons
  list_single
  assumption

-- Tactic Combinators
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html#tactic-combinators

-- or tactics
-- first | t₁ | t₂ | ... | tₙ

-- repeat tactic
-- repeat (first | t1 | ... | tₙ)

local elab "balistic" : tactic => newTactic do
  run `(tactic| repeat (first| list_empty | list_single | list_app | list_app_uncons))




