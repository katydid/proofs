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

theorem list_cons_ne_nil (x : α) (xs : List α):
  x :: xs ≠ [] := by
  intro h'
  contradiction

theorem list_cons_nil_ne (x : α) (xs : List α):
  [] ≠ x :: xs := by
  intro h'
  contradiction

theorem list_length_zero_is_empty (xs: List α):
  length xs = 0 -> xs = [] := by
  cases xs
  · intro _
    rfl
  · intro _
    contradiction

theorem list_nil_cons (x: α) (xs: List α):
  [] ≠ x :: xs := by
  -- TODO
  sorry


theorem list_app_nil_l (xs: List α):
  [] ++ xs = xs := by
  -- TODO
  sorry

theorem list_app_nil_r (xs: List α):
  xs ++ [] = xs := by
  -- TODO
  sorry

theorem list_app_assoc (xs ys zs: List α):
  xs ++ ys ++ zs = (xs ++ ys) ++ zs := by
  induction xs with
  | nil => rfl
  | cons head tail =>
    apply (congrArg (cons head))
    assumption

theorem list_app_assoc_reverse (xs ys zs: List α):
  (xs ++ ys) ++ zs = xs ++ ys ++ zs := by
  -- TODO
  sorry

theorem list_app_comm_cons (x: α) (xs ys: List α):
  x :: (xs ++ ys) = (x :: xs) ++ ys := by
  -- TODO
  sorry

theorem list_app_cons_not_nil (x: α) (xs ys: List α):
  [] ≠ xs ++ y :: ys := by
  -- TODO
  sorry

theorem list_app_eq_unit (a: α) (xs ys: List α):
  xs ++ ys = [a] -> xs = [] /\ ys = [a] \/ xs = [a] /\ ys = [] := by
  -- TODO
  sorry

theorem list_app_inj_tail (xs ys: List α) (x y: α):
  xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y := by
  -- TODO
  sorry

theorem list_app_nil_end (xs: List α):
  xs = xs ++ [] := by
  -- TODO
  sorry

theorem list_app_length (xs ys: List α):
  length (xs ++ ys) = length xs + length ys := by
  -- TODO
  sorry

theorem list_last_length (xs: List α):
  length (xs ++ x :: nil) = (length xs) + 1 := by
  -- TODO
  sorry

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

theorem list_length_zero_or_smaller_is_empty (xs: List α):
  length xs <= 0 -> xs = [] := by
  -- TODO
  sorry


theorem list_take_nil {α: Type u} (n: Nat):
  take n ([] : List α) = [] := by
  -- TODO
  sorry

theorem list_take_cons (n: Nat) (x: α) (xs: List α):
  take (n + 1) (x::xs) = x :: (take n xs) := by
  -- TODO
  sorry

theorem list_take_all (xs: List α):
  take (length xs) xs = xs := by
  -- TODO
  sorry

theorem list_take_all2 (n: Nat) (xs: List α):
  (length xs) <= n -> take n xs = xs := by
  -- TODO
  sorry

theorem list_take_O (xs: List α):
  take 0 xs = [] := by
  -- TODO
  sorry

theorem list_take_le_length (n: Nat) (xs: List α):
  length (take n xs) <= n := by
  -- TODO
  sorry

theorem list_take_length_le (n: Nat) (xs: List α):
  n <= length xs -> length (take n xs) = n := by
  -- TODO
  sorry

theorem list_take_app (n: Nat) (xs ys: List α):
  take n (xs ++ ys) = (take n xs) ++ (take (n - length xs) ys) := by
  -- TODO
  sorry

theorem list_take_app_2 (n: Nat) (xs ys: List α):
  take ((length xs) + n) (xs ++ ys) = xs ++ take n ys := by
  -- TODO
  sorry

theorem list_take_take (n n: Nat) (xs: List α):
  take n (take m xs) = take (min n m) xs := by
  -- TODO
  sorry

theorem list_take_drop_comm (n m: Nat) (xs: List α):
  take m (drop n xs) = drop n (take (n + m) xs) := by
  -- TODO
  sorry

theorem list_drop_take_comm (n m: Nat) (xs: List α):
  drop m (take n xs) = take (n - m) (drop m xs) := by
  -- TODO
  sorry

theorem list_drop_O (xs: List α):
  drop 0 xs = xs := by
  -- TODO
  sorry

theorem list_drop_nil {α: Type u} (n: Nat):
  drop n ([] : List α) = [] := by
  -- TODO
  sorry

theorem list_drop_cons (n: Nat) (x: α) (xs: List α):
  drop (n + 1) (x::xs) = drop n xs := by
  -- TODO
  sorry

theorem list_drop_all (xs: List α):
  drop (length xs) xs = nil := by
  -- TODO
  sorry

theorem list_drop_all2 (n: Nat) (xs: List α):
  length xs <= n -> drop n xs = [] := by
  -- TODO
  sorry

theorem list_take_drop (n: Nat) (xs: List α):
  take n xs ++ drop n xs = xs := by
  -- TODO
  sorry

theorem list_take_length (n: Nat) (xs: List α):
  length (take n xs) = min n (length xs) := by
  -- TODO
  sorry

theorem list_drop_length (n: Nat) (xs: List α):
  length (drop n xs) = length xs - n := by
  -- TODO
  sorry

theorem list_drop_app (n: Nat) (xs ys: List α):
  drop n (xs ++ ys) = (drop n xs) ++ (drop (n - length xs) ys) := by
  -- TODO
  sorry

theorem list_take_app_length (xs ys: List α):
  take (length xs) (xs ++ ys) = xs := by
  -- TODO
  sorry

theorem list_drop_app_length (xs ys: List α):
  drop (length xs) (xs ++ ys) = ys := by
  -- TODO
  sorry

theorem list_split_list (xs: List α) (n : Nat): ∀ (ys zs: List α),
  length ys = n ->
  xs = ys ++ zs ->
  ys = take n xs /\
  zs = drop n xs := by
  -- TODO
  sorry

theorem list_prefix_leq_length (xs ys zs: List α):
  xs = ys ++ zs -> length ys <= length xs := by
  -- TODO
  sorry

theorem list_drop_length_prefix_is_suffix (xs ys: List α):
  drop (length xs) (xs ++ ys) = ys := by
  -- TODO
  sorry

theorem list_take_length_prefix_is_prefix (xs ys: List α):
  take (length xs) (xs ++ ys) = xs := by
  -- TODO
  sorry

theorem list_prefix_length_leq: ∀ (xs ys zs: List α),
  xs ++ ys = zs -> length xs <= length zs := by
  -- TODO
  sorry

theorem list_length_gt_zero: ∀ (xs: List α),
  xs ≠ [] -> 0 < length xs := by
  -- TODO
  sorry

theorem list_prefix_is_gt_zero_and_leq: ∀ (xs ys zs: List α),
  (xs ≠ []) ->
  xs ++ ys = zs ->
  (0 < length xs /\ length xs <= length zs) := by
  -- TODO
  sorry

theorem list_prefix_is_not_empty_with_index_gt_zero: ∀ (xs: List α) (n: Nat)
  (range: 0 < n /\ n <= length xs),
  take index xs ≠ [] :=
  -- TODO
  sorry

theorem list_app_uncons: ∀ (x: α) (xs ys zs: List α),
  ys ++ zs = x :: xs ->
  (ys = [] /\ zs = x :: xs)
  \/ (∃
     (ys': List α)
     (pys: ys = x :: ys'),
     ys' ++ zs = xs
  ) := by
  -- TODO
  sorry