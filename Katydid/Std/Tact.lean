-- TODO: Rename and clean up this file

import Katydid.Std.Lists
import Std.Lean.Meta.UnusedNames
import Qq
open Qq Lean Elab Meta Tactic

-- https://github.com/gebner/quote4/blob/master/examples/conjs.lean
-- https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/Listerine.v#L59-L107
-- https://github.com/leanprover-community/mathlib4/blob/7e2613afa5a47788e24f31a386e4dfad92b40289/Mathlib/Tactic/Set.lean#L58
-- https://github.com/leanprover-community/mathlib4/blob/2d97a156aa63b50456ed3e5a7d6af3096ac7958e/Mathlib/Tactic/Tauto.lean
-- https://github.com/leanprover-community/mathlib4/blob/bac7310cc18d6ed292606d26ccb5fb9ffc697c7a/Mathlib/Tactic/Slice.lean

def fresh [Monad m] [MonadLCtx m] (suggestion : Name) : m Ident := do
  let name ← getUnusedUserName suggestion
  return mkIdent name

elab "applyit" : tactic => do
  let goal ← getMainTarget
  if let some goalType ← checkTypeQ (u := levelOne) goal q(Prop) then
    if let ~q([] ≠ $xs ++ ($y :: $ys)) := goalType then
      evalTactic (← `(tactic| apply (list_app_cons_not_nil _) ))

example : [] ≠ xs ++ (y::ys) := by
  applyit

elab "print_hypotheses" : tactic => do
  for ldecl in ← getLCtx do
    if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
      let name := ldecl.userName
      logInfo m!"Hypothesis | {name}: {ty}"

elab "print_list_cons_in_hypotheses" : tactic => do
  for ldecl in ← getLCtx do
    if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
      if let ~q([] = $xs ++ ($y :: $ys)) := ty then
        let name := ldecl.userName
        logInfo m!"name1 = {name}, xs = {xs}, y = {y}, ys = {ys}"
      if let ~q($x = $y) := ty then
        let name := ldecl.userName
        if ← Lean.Meta.isExprDefEq x y
        then
          logInfo m!"name2 = {name}, x = {x}"
        else
          logInfo m!"name3 = {name}, x = {x}, y = {y}"

-- example (H1 : [] = xs ++ (y::ys)) (H2 : 2 = 2): 1 = 1 := by
--   print_list_cons_in_hypotheses
--   sorry

elab "it" : tactic => do
  for ldecl in ← getLCtx do
    if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
      if let ~q((((($a : Prop)) → $b) : Prop)) := ty then
        let name :=  mkIdent ldecl.userName
        logInfo m!"it = {name}, a = {a}, b = {b}"
        evalTactic (← `(tactic| apply $name ))

-- example {A B: Prop} (P: A -> B) (a: A): B := by
--   it
--   assumption

example (H : [] = (x::xs)): False := by
  contradiction

elab "list_empty" : tactic => do
  let goal ← getMainTarget
    if let some goalType ← checkTypeQ (u := levelOne) goal q(Prop) then
      if let ~q([] ≠ $xs ++ ($y :: $ys)) := goalType then
        -- [] ≠ xs ++ y :: ys
        evalTactic (← `(tactic| apply list_app_cons_not_nil ))
  let ctx ← getLCtx
  for ldecl in ctx do
    if let some ty ← checkTypeQ (u := levelOne) ldecl.type q(Prop) then
      let name :=  mkIdent ldecl.userName
      if let ~q([] = $x :: $xs) := ty then
        -- [] = x :: xs -> False
        evalTactic (← `(tactic| contradiction ))
      if let ~q($x :: $xs = []) := ty then
        -- x :: xs = [] -> False
        evalTactic (← `(tactic| contradiction ))
      if let ~q([] = $xs ++ ($y :: $ys)) := ty then
        -- [] = xs ++ y :: ys -> False
        let hypName := mkIdent (← getUnusedUserName "H")
        evalTactic (← `(tactic| have $hypName := list_app_cons_not_nil _ _ _ $name ))
        evalTactic (← `(tactic| contradiction ))
      if let ~q($xs ++ $ys = []) := ty then
        -- xs ++ ys = [] -> xs = [] /\ ys = []
        let hypName := mkIdent (← getUnusedUserName "H")
        evalTactic (← `(tactic| have $hypName := (list_app_nil_nil _ _).mp $name ))
        let leftName := mkIdent (← getUnusedUserName "HLeft")
        let rightName := mkIdent (← getUnusedUserName "HRight")
        evalTactic (← `(tactic| have $leftName := ($hypName).left ))
        evalTactic (← `(tactic| have $rightName := ($hypName).right ))


example (H : [] = (x::xs)): False := by
  list_empty

theorem test_list_app_cons_nil_not' (y: α) (xs ys: List α) (H: [] = xs ++ (y :: ys)): False := by
  list_empty

example (H : xs ++ ys = []): ys = [] := by
  list_empty
  assumption



















