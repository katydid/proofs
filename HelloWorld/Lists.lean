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

theorem list_append_ne_nil (x : α) (xs : List α):
  [x] ++ xs ≠ [] := by
  intro h'
  contradiction

theorem list_append_nil_ne (x : α) (xs : List α):
  xs ++ [x] ≠ [] := by
  intro h'
  cases xs with
  | nil =>
    contradiction
  | cons head tail =>
    contradiction

theorem list_length_zero_is_empty (xs: List α):
  length xs = 0 -> xs = [] := by
  cases xs
  · intro _
    rfl
  · intro h'
    simp [length] at h'
    contradiction

theorem list_app_nil_l (xs: List α):
  [] ++ xs = xs := by
  rfl

theorem list_app_nil_r (xs: List α):
  xs ++ [] = xs := by
  induction xs with
  | nil =>
    rfl
  | cons head tail ih =>
    apply (congrArg (cons head))
    assumption

theorem list_app_assoc (xs ys zs: List α):
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    apply (congrArg (cons head))
    exact ih

theorem list_app_assoc_reverse (xs ys zs: List α):
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  apply Eq.symm -- same as symmetry tactic in Coq and Lean3
  apply list_app_assoc

theorem list_app_comm_cons (x: α) (xs ys: List α):
  x :: (xs ++ ys) = (x :: xs) ++ ys := by
  apply (congrArg (cons x))
  rfl

theorem list_app_cons_not_nil (x: α) (xs ys: List α):
  [] ≠ xs ++ (y :: ys) := by
  cases xs <;> { intro h' ; contradiction }

theorem list_app_nil_nil (xs ys: List α):
  xs ++ ys = [] <-> xs = [] /\ ys = [] := by
  apply Iff.intro
  case mp =>
    cases xs with
    | nil =>
      simp
      intro h'
      assumption
    | cons head tail =>
      intro h'
      contradiction
  case mpr =>
    intro h'
    cases h' with
    | intro h1 h2 =>
      rw [h1, h2]
      rfl

theorem list_app_eq_unit (a: α) (xs ys: List α):
  xs ++ ys = [a] -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  cases xs with
  | nil =>
    intro hy
    simp at hy
    apply Or.intro_left
    apply And.intro
    case left => rfl
    case right => assumption
  | cons head tail =>
    intro hy
    simp at hy
    apply Or.intro_right
    cases hy with
    | intro h1 h2 =>
      rw [h1]
      have h3: tail = [] /\ ys = [] := (Iff.mp (list_app_nil_nil tail ys)) h2
      cases h3 with
      | intro h4 h5 =>
        rw [h4, h5]
        apply And.intro <;> rfl

theorem list_app_inj_tail (xs ys: List α) (x y: α):
  xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y := by
  revert ys -- same as generalize dependent ys in Coq
  induction xs with
  | nil =>
    intro ys h'
    simp at h'
    have h3: (ys = [] /\ [y] = [x]) \/ (ys = [x] /\ [y] = []) := (list_app_eq_unit x ys [y]) (Eq.symm h')
    cases h3 with -- Or
    | inl left =>
      cases left with
      | intro empty xy =>
        simp at xy
        rw [empty, xy]
        apply And.intro <;> rfl
    | inr right =>
      cases right with
      | intro empty ysx =>
        contradiction
  | cons headx tailx ihx =>
    intro ys
    cases ys with
    | nil =>
      intro h'
      simp at h'
      cases h' with
      | intro _ hfalse =>
        simp [List.append] at hfalse
        have h: tailx ++ [x] ≠ [] := list_append_nil_ne x tailx
        contradiction
    | cons heady taily =>
      intro h'
      simp at h'
      cases h' with
      | intro heads tails =>
        rw [heads]
        have h: tailx = taily ∧ x = y := (ihx taily tails)
        cases h with
        | intro tailxy xy =>
          rw [tailxy]
          rw [xy]
          apply And.intro <;> rfl

theorem list_app_nil_end (xs: List α):
  xs = xs ++ [] := by
  cases xs with
  | nil => rfl
  | cons head tail => simp [List.append]

theorem list_app_length (xs ys: List α):
  length (xs ++ ys) = length xs + length ys := by
  induction xs with
  | nil => simp
  | cons _ tailx ih => simp [ih, Nat.succ_add]

theorem list_last_length (xs: List α):
  length (xs ++ x :: nil) = (length xs) + 1 := by
  induction xs with
  | nil => rfl
  | cons _ tail ih => simp [ih]

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
  cases xs with
  | nil => intro; rfl
  | cons head tail => intro; contradiction

theorem list_take_nil {α: Type u} (n: Nat):
  take n ([] : List α) = [] := by
  cases n with
  | zero => rfl
  | succ => rfl

theorem list_take_cons (n: Nat) (x: α) (xs: List α):
  take (n + 1) (x::xs) = x :: (take n xs) := by
  rw [take]

theorem list_take_all (xs: List α):
  take (length xs) xs = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    have h : take (length (head::tail)) (head::tail) =
        head :: (take (length tail) tail) := by
      apply list_take_cons
    rw [ih] at h
    trivial

theorem list_take_zero_is_empty (xs : List α) :
  take zero xs = [] := by rw [take]

theorem list_rev_empty (xs : List α) :
  reverse xs = [] -> xs = [] := by
  cases xs with
  | nil => simp
  | cons head tail =>
    intro h
    have h' : (reverse (reverse (head :: tail)) = []) := congrArg reverse h
    simp at h'

theorem list_rev_empty2 (xs : List α) :
  reverse ([] : List α) = [] := by trivial

theorem list_rev_eq (n : Nat) (xs ys : List α) :
  reverse xs = reverse ys -> xs = ys := by
  intro h
  have h' : reverse (reverse xs) = reverse (reverse ys) :=
    congrArg reverse h
  simp at h'
  assumption

theorem take_one_nil : take 1 ([] : List α) = [] := by
  rw [take]

theorem nat_succ_leq : succ n ≤ succ m -> n ≤ m := by
  sorry

theorem list_length_cons_succ : length (head :: tail) ≤ succ k -> length tail ≤ k := by
  sorry

theorem list_take_all2 (n: Nat) (xs: List α):
  (length xs) <= n -> take n xs = xs := by
  revert xs
  induction n with
  | zero =>
    intro xs h
    have f := list_length_zero_or_smaller_is_empty xs h
    rw [f]
    rw [take]
  | succ k ih =>
    intro xs
    cases xs with
    | nil =>
      intro h
      apply list_take_nil
    | cons head tail =>
      intro h
      rw [take]
      apply (congrArg (cons head))
      sorry

theorem list_take_O (xs: List α):
  take 0 xs = [] := by
  rw [take]

theorem list_take_le_length (n: Nat) (xs: List α):
  length (take n xs) <= n := by
  revert n
  induction xs with
  | nil =>
    intro n
    rw [list_take_nil]
    simp
  | cons head tail ih =>
    intro n
    cases n with
    | zero  =>
      rw [take]
      simp
    | succ k =>
      rw [take]
      rw [length]
      apply succ_le_succ
      apply (ih k)

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