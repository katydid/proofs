-- Lean Tactics
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html
-- Lean List Proofs
-- https://github.com/leanprover/std4/blob/main/Std/Data/List/Lemmas.lean
-- Coq List Proofs
-- https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/List.v
-- List of Lean Tactics
-- https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean

open Nat
open List

theorem cons_ne_nil (a : α) (l : List α) : a :: l ≠ [] := by
  intro h'
  contradiction

theorem cons_nil_ne (a : α) (l : List α) : [] ≠ a :: l := by
  intro h'
  contradiction

theorem length_zero_list_is_empty (xs: List α) : length xs = 0 -> xs = [] := by
  cases xs
  · intro _
    rfl
  · intro _
    contradiction

theorem list_cons_eq (x y: α) (xs ys: List α):
  x :: xs = y :: ys <-> x = y /\ xs = ys := by
  apply Iff.intro
  · intro h
    apply And.intro
    · injections
      assumption
    · injections
      assumption
  · intro h
    congr
    · exact h.left
    · exact h.right

theorem list_append_assoc (l m n: List α):
  l ++ (m ++ n) = (l ++ m) ++ n := by
  induction l with
  | nil => rfl
  | cons head tail =>
    apply (congrArg (cons head))
    assumption

def reverse' (xs: List α): List α :=
  match xs with
  | [] => []
  | (x'::xs') => reverse' xs' ++ [x']

theorem list_reverse_nil (α : Type): @reverse' α [] = [] := by
  rfl

theorem list_reverse' (xs: List α) (y: α):
  reverse' (xs ++ [y]) = y :: reverse' xs := by
  induction xs with
  | nil => rfl
  | cons x' xs' h =>
    have hr : reverse' (x' :: xs' ++ [y]) = reverse' (xs' ++ [y]) ++ [x'] := by rfl
    rw [h] at hr
    rw [hr]
    apply (congrArg (cons y))
    rfl

