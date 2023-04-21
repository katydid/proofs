import Katydid.Std.Lists

import Katydid.Std.Ltac
import Qq
open Qq

-- balistic is a tactic that tries to solve simple theorems with empty lists
-- Reference for list tactic in Coq: https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/Listerine.v#L59-L107
elab "balistic" : tactic => do
  let goal ← getGoalProp
    if let ~q([] ≠ $xs ++ ($y :: $ys)) := goal then
      -- [] ≠ xs ++ y :: ys
      run `(tactic| apply list_app_cons_not_nil )
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    if let ~q([] = $x :: $xs) := ty then
      -- [] = x :: xs -> False
      run `(tactic| contradiction )
    if let ~q($x :: $xs = []) := ty then
      -- x :: xs = [] -> False
      run `(tactic| contradiction )
    if let ~q([] = $xs ++ ($y :: $ys)) := ty then
      -- [] = xs ++ y :: ys -> False
      _ ← mkHyp "H" `(list_app_cons_not_nil _ _ _ $name)
      run `(tactic| contradiction )
    if let ~q($xs ++ $ys = []) := ty then
      -- xs ++ ys = [] -> xs = [] /\ ys = []
      let hypName ← mkHyp "H" `((list_app_nil_nil _ _).mp $name)
      _ ← mkHyp "HLeft" `(($hypName).left )
      _ ← mkHyp "HRight" `(($hypName).right )

example (H : [] = (x::xs)): False := by
  balistic

example (y: α) (xs ys: List α) (H: [] = xs ++ (y :: ys)): False := by
  balistic

example (H : xs ++ ys = []): ys = [] := by
  balistic
  assumption