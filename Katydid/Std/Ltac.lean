import Katydid.Std.Lists
import Std.Lean.Meta.UnusedNames
import Qq
open Qq

-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← Lean.Meta.getUnusedUserName suggestion
  return Lean.mkIdent name

-- Check if the expression is a Prop and return it as a Q(Prop) that can be used in a pattern match.
def getQProp (e: Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Q(Prop)) := do
  Qq.checkTypeQ (u := Lean.levelOne) e q(Prop)

-- Returns the main goal as a Q(Prop), such that it can be used in a pattern match.
def getGoalProp : Lean.Elab.Tactic.TacticM Q(Prop) := do
  let goal ← Lean.Elab.Tactic.getMainTarget
  match ← getQProp goal with
  | some qType => return qType
  | none => throwError "goal is not a proposition"

-- run is shorthand for evalTactic (← t).
def run (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic)): Lean.Elab.Tactic.TacticM Unit := do
  let t' ← t
  Lean.Elab.Tactic.evalTactic t'

-- An example to show how we can create a new tactic that only applies a lemma, if it matches the goal
elab "example_apply" : tactic => do
  match ← getGoalProp with
  -- Reference for pattern matching: https://github.com/gebner/quote4/blob/master/examples/conjs.lean
  | ~q([] ≠ $xs ++ ($y :: $ys)) => do
    run `(tactic| apply (list_app_cons_not_nil _) )
  | _ => return ()

example : [] ≠ xs ++ (y::ys) := by
  example_apply

-- getHypotheses returns the hypotheses as an array of tuples of (Hypothesis name, Q(Prop))
-- This way the hypothesis Q(Prop) can be used in a pattern match and
-- the name can be used to refer to the hypothesis in other tactics
def getHypotheses : Lean.Elab.Tactic.TacticM (Array (Lean.Syntax.Ident × Q(Prop))) := do
  let ldecls ← Lean.MonadLCtx.getLCtx
  let mut res := #[]
  for ldecl in ldecls do
    if let some htyp ← getQProp ldecl.type then
      let name := Lean.mkIdent ldecl.userName
      res := res.push (name, htyp)
  return res

-- haveBy is shorthand for
--  let name ← fresh suggestion
--  evalTactic ← `(tactic| have $name := $t )
def haveBy (suggestion: String) (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `term)): Lean.Elab.Tactic.TacticM Lean.Ident := do
  let t' ← t
  let name ← fresh suggestion
  run `(tactic| have $name := $t' )
  return name

-- a tactic that prints the hypotheses and their types
elab "print_hypotheses" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    Lean.logInfo m!"{name}: {ty}"

example (H1 : [] = xs ++ (y::ys)) (H2 : 2 = 2): 1 = 1 := by
  print_hypotheses
  sorry

-- a tactic that prints the hypotheses, but only if they match a pattern
elab "example_print_list_cons_in_hypotheses" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    if let ~q([] = $xs ++ ($y :: $ys)) := ty then
      Lean.logInfo m!"name1 = {name}, xs = {xs}, y = {y}, ys = {ys}"
    if let ~q($x = $y) := ty then
      if ← Lean.Meta.isExprDefEq x y
      then
        Lean.logInfo m!"name2 = {name}, x = {x}"
      else
        Lean.logInfo m!"name3 = {name}, x = {x}, y = {y}"

-- an example tactic that applies a hypothesis to the goal if it matches a pattern
elab "example_apply_hypothesis" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    if let ~q((((($a : Prop)) → $b) : Prop)) := ty then
      run `(tactic| apply $name )

example {A B: Prop} (P: A -> B) (a: A): B := by
  example_apply_hypothesis
  assumption

-- an example that tries to solve simple theorems with empty lists
-- Reference for list tactic in Coq: https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/Listerine.v#L59-L107
elab "example_list_empty" : tactic => do
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
      _ ← haveBy "H" `(list_app_cons_not_nil _ _ _ $name)
      run `(tactic| contradiction )
    if let ~q($xs ++ $ys = []) := ty then
      -- xs ++ ys = [] -> xs = [] /\ ys = []
      let hypName ← haveBy "H" `((list_app_nil_nil _ _).mp $name)
      _ ← haveBy "HLeft" `(($hypName).left )
      _ ← haveBy "HRight" `(($hypName).right )

example (H : [] = (x::xs)): False := by
  example_list_empty

example (y: α) (xs ys: List α) (H: [] = xs ++ (y :: ys)): False := by
  example_list_empty

example (H : xs ++ ys = []): ys = [] := by
  example_list_empty
  assumption

-- Other References of using quote4:
--  - https://github.com/leanprover-community/mathlib4/blob/7e2613afa5a47788e24f31a386e4dfad92b40289/Mathlib/Tactic/Set.lean#L58
--  - https://github.com/leanprover-community/mathlib4/blob/2d97a156aa63b50456ed3e5a7d6af3096ac7958e/Mathlib/Tactic/Tauto.lean
--  - https://github.com/leanprover-community/mathlib4/blob/bac7310cc18d6ed292606d26ccb5fb9ffc697c7a/Mathlib/Tactic/Slice.lean
















