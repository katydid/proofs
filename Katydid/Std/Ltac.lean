import Std.Lean.Meta.UnusedNames
import Qq
open Qq

-- Check if the expression is a Prop and if so return it as a Q(Prop) that can be used in a pattern match.
private def getQProp (e: Lean.Expr) : Lean.Elab.Tactic.TacticM (Option Q(Prop)) := do
  Qq.checkTypeQ (u := Lean.levelOne) e q(Prop)

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

-- a tactic that prints the hypotheses and their types
elab "print_hypotheses" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    Lean.logInfo m!"{name}: {ty}"

example (H1 : x = 5) (_H2 : x > 1): x < 6 := by
  print_hypotheses
  rw [H1]
  simp

-- a tactic that prints the hypotheses, but only if they match a pattern
local elab "example_print_rfl_hypotheses" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    if let ~q($x = $y) := ty then
      if ← Lean.Meta.isExprDefEq x y then
        Lean.logInfo m!"{name} is rfl"

example (_H1 : x = 5) (_H2 : 2 = 2) (_H3: y = y) (H4: 5 = 4): False := by
  example_print_rfl_hypotheses
  contradiction

-- run is shorthand for evalTactic (← t).
def run (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `tactic)): Lean.Elab.Tactic.TacticM Unit := do
  let t' ← t
  Lean.Elab.Tactic.evalTactic t'

-- an example tactic that applies a hypothesis to the goal if it matches a pattern
local elab "example_apply_hypothesis" : tactic => do
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    if let ~q((((($a : Prop)) → $b) : Prop)) := ty then
      run `(tactic| apply $name )

example {A B: Prop} (P: A -> B) (a: A): B := by
  example_apply_hypothesis
  assumption

-- Returns the main goal as a Q(Prop), such that it can be used in a pattern match.
def getGoalProp : Lean.Elab.Tactic.TacticM Q(Prop) := do
  let goal ← Lean.Elab.Tactic.getMainTarget
  match ← getQProp goal with
  | some qType => return qType
  | none => throwError "goal is not a proposition"

-- An example to check whether the goal is already an hypothesis
local elab "example_assumption_tactic" : tactic => do
  let goal ← getGoalProp
  let hyps ← getHypotheses
  for (name, ty) in hyps do
    if ← Lean.Meta.isExprDefEq ty goal then
      run `(tactic| exact $name )

example (Hx: x) (_Hy: y): x := by
  example_assumption_tactic

private theorem anda (a: Prop): a -> (a /\ a) := by
  intro a
  apply And.intro
  case left => assumption
  case right => assumption

-- An example to show how we can create a new tactic that only applies a lemma, if it matches the goal
elab "example_apply" : tactic => do
  match ← getGoalProp with
  -- Reference for pattern matching: https://github.com/gebner/quote4/blob/master/examples/conjs.lean
  | ~q($x /\ $y) => do
    if ← Lean.Meta.isExprDefEq x y then
      -- x /\ x -> x
      run `(tactic| apply anda )
  | _ => return ()

example (H: x): x /\ x := by
  example_apply
  example_assumption_tactic

-- Creates a fresh variable with the suggested name.
def fresh [Monad m] [Lean.MonadLCtx m] (suggestion : Lean.Name) : m Lean.Syntax.Ident := do
  let name ← Lean.Meta.getUnusedUserName suggestion
  return Lean.mkIdent name

-- mkHyp makes a new hypothesis
--  let name ← fresh suggestion
--  evalTactic ← `(tactic| have $name := $t )
def mkHyp (suggestion: String) (t: Lean.Elab.Tactic.TacticM (Lean.TSyntax `term)): Lean.Elab.Tactic.TacticM Lean.Ident := do
  let t' ← t
  let name ← fresh suggestion
  run `(tactic| have $name := $t' )
  return name

-- an example that tries to apply a bunch to tactics to specific patterns
local elab "example_combo_tactic" : tactic => do
  let goal ← getGoalProp
  let hyps ← getHypotheses
  if let ~q($x /\ $y) := goal then
    if ← Lean.Meta.isExprDefEq x y then
    -- x /\ x -> x
    run `(tactic| apply anda )
  for (name, ty) in hyps do
    match ty with
    | ~q($x = $y) =>
      -- rewrite x = y everywhere
      run `(tactic| rw [ $name:term ] at * )
    | ~q($x :: $xs = []) =>
      -- x :: xs = [] -> False
      run `(tactic| contradiction )
    | ~q(($x : Nat) < $y) =>
      -- x < y -> x + 1 <= y
      let hsucc ← mkHyp "Hsucc" `(Nat.succ_lt_succ $name)
      _ ← mkHyp "HLe" `(Nat.le_of_lt_succ $hsucc)
    | _ => return ()

example (H : x = y) (Y: y): x /\ x := by
  example_combo_tactic
  example_assumption_tactic

example (x: Nat) (Hz: x = z) (H: z < y): (x + 1 <= y /\ x + 1 <= y):= by
  example_combo_tactic
  example_assumption_tactic

-- Other References of using quote4 and other tactics:
--  - https://github.com/leanprover-community/mathlib4/blob/7e2613afa5a47788e24f31a386e4dfad92b40289/Mathlib/Tactic/Set.lean#L58
--  - https://github.com/leanprover-community/mathlib4/blob/2d97a156aa63b50456ed3e5a7d6af3096ac7958e/Mathlib/Tactic/Tauto.lean
--  - https://github.com/leanprover-community/mathlib4/blob/bac7310cc18d6ed292606d26ccb5fb9ffc697c7a/Mathlib/Tactic/Slice.lean
--  - https://github.com/siddhartha-gadgil/LeanAide
















