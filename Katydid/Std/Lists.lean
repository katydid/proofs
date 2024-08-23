-- Lean Tactics
-- https://leanprover.github.io/theorem_proving_in_lean4/tactics.html
-- Lean List Proofs
-- https://github.com/leanprover/std4/blob/main/Std/Data/List/Lemmas.lean
-- Coq List Proofs
-- https://github.com/katydid/proofs/blob/old-coq/src/CoqStock/List.v
-- List of Lean Tactics
-- https://github.com/leanprover/lean4/blob/master/src/Init/Tactics.lean

import Mathlib.Tactic.Linarith

open Nat
open List

theorem nat_succ_le_succ_iff (x y: Nat):
  succ x ≤ succ y <-> x ≤ y := by
  apply Iff.intro
  case mp =>
    apply Nat.le_of_succ_le_succ
  case mpr =>
    apply Nat.succ_le_succ

theorem nat_succ_eq_plus_one : succ n = n + 1 := by
  simp only

theorem nat_pred_le_succ : {n m : Nat} -> Nat.le n (succ m) -> Nat.le (pred n) m
  | zero, zero, _ => Nat.le.refl
  | _, _, Nat.le.refl => Nat.le.refl
  | zero, succ _, Nat.le.step h => h
  | succ _, succ _, Nat.le.step h => Nat.le_trans (le_succ _) h

theorem nat_pred_le_succ' : {n m : Nat} -> Nat.le n (succ m) -> Nat.le (pred n) m := by
  intro n m h
  cases h with
  | refl =>
    constructor
  | step h =>
    cases n with
    | zero =>
      dsimp only [zero_eq, Nat.pred_zero, le_eq]
      exact h
    | succ n =>
      dsimp only [Nat.pred_succ, le_eq]
      have h_n_le_succ_n := Nat.le_succ n
      exact (Nat.le_trans h_n_le_succ_n h)

theorem nat_min_zero {n: Nat}: min 0 n = 0 := by
  unfold min
  unfold instMinNat
  unfold minOfLe
  simp

theorem nat_zero_min {n: Nat}: min n 0 = 0 := by
  cases n with
  | zero =>
    simp
  | succ n =>
    unfold min
    unfold instMinNat
    unfold minOfLe
    simp only [nonpos_iff_eq_zero, ite_false]

theorem nat_add_succ_is_succ_add (n m: Nat): succ n + m = succ (n + m) := by
  cases n with
  | zero =>
    rewrite [Nat.add_comm]
    simp only [zero_eq, zero_add]
  | succ n =>
    rewrite [Nat.add_comm]
    rewrite [Nat.add_comm (succ n)]
    repeat rewrite [Nat.add_succ]
    rfl

theorem nat_pred_le_pred : {n m : Nat} → LE.le n m → LE.le (pred n) (pred m) := by
  intro n m h
  cases h with
  | refl => constructor
  | step h =>
    rename_i m
    cases n with
    | zero =>
      dsimp
      exact h
    | succ n =>
      dsimp
      have h_n_le_succ_n := Nat.le_succ n
      exact (Nat.le_trans h_n_le_succ_n h)

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
    simp only [length, add_eq_zero, and_false] at h'

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

theorem list_app_assoc_singleton (xs ys: List α) (z: α):
  xs ++ (ys ++ [z]) = (xs ++ ys) ++ [z] := by
  apply list_app_assoc

theorem list_app_assoc_reverse (xs ys zs: List α):
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs) := by
  apply Eq.symm -- same as symmetry tactic in Coq and Lean3
  apply list_app_assoc

theorem list_app_comm_cons (x: α) (xs ys: List α):
  x :: (xs ++ ys) = (x :: xs) ++ ys := by
  apply (congrArg (cons x))
  rfl

theorem list_nil_ne_app_cons (y: α) (xs ys: List α):
  [] ≠ xs ++ (y :: ys) := by
  cases xs <;> { intro h' ; contradiction }

theorem list_app_cons_ne_nil (y: α) (xs ys: List α):
  xs ++ (y :: ys) ≠ [] := by
  cases xs <;> { intro h' ; contradiction }

theorem list_app_nil_nil (xs ys: List α):
  xs ++ ys = [] <-> xs = [] /\ ys = [] := by
  apply Iff.intro
  case mp =>
    cases xs with
    | nil =>
      simp only [nil_append, true_and, imp_self]
    | cons head tail =>
      intro h'
      contradiction
  case mpr =>
    intro h'
    cases h' with
    | intro h1 h2 =>
      rw [h1, h2]
      rfl

theorem list_app_eq_unit {a: α} {xs ys: List α}:
  xs ++ ys = [a] -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  cases xs with
  | nil =>
    intro hy
    simp only [nil_append] at hy
    apply Or.intro_left
    apply And.intro
    case left => rfl
    case right => assumption
  | cons head tail =>
    intro hy
    simp only [cons_append, cons.injEq, append_eq_nil] at hy
    apply Or.intro_right
    cases hy with
    | intro h1 h2 =>
      rw [h1]
      cases h2 with
      | intro h4 h5 =>
        rw [h4, h5]
        apply And.intro <;> rfl

theorem list_eq_unit_app {a: α} {xs ys: List α}:
  [a] = xs ++ ys -> (xs = [] /\ ys = [a]) \/ (xs = [a] /\ ys = []) := by
  intro H
  apply list_app_eq_unit
  apply Eq.symm
  assumption

theorem list_app_inj_tail {xs ys: List α} {x y: α}:
  xs ++ [x] = ys ++ [y] -> xs = ys /\ x = y := by
  revert ys -- same as generalize dependent ys in Coq
  induction xs with
  | nil =>
    intro ys h'
    simp only [nil_append] at h'
    have h3: (ys = [] /\ [y] = [x]) \/ (ys = [x] /\ [y] = []) := list_app_eq_unit (Eq.symm h')
    cases h3 with -- Or
    | inl left =>
      cases left with
      | intro empty xy =>
        simp only [cons.injEq, and_true] at xy
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
      simp only [cons_append, nil_append, cons.injEq, append_eq_nil, and_false] at h'
    | cons heady taily =>
      intro h'
      simp only [cons_append, cons.injEq] at h'
      cases h' with
      | intro heads tails =>
        rw [heads]
        have h: tailx = taily ∧ x = y := (ihx tails)
        cases h with
        | intro tailxy xy =>
          rw [tailxy]
          rw [xy]
          apply And.intro <;> rfl

theorem list_inj_tail_app {xs ys: List α} {x y: α}:
  xs = ys /\ x = y -> xs ++ [x] = ys ++ [y] := by
  intro H
  cases H with
  | intro H1 H2 =>
    rw [H1, H2]

theorem list_app_nil_end (xs: List α):
  xs = xs ++ [] := by
  cases xs with
  | nil => rfl
  | cons head tail => simp only [append_nil]

theorem list_app_length (xs ys: List α):
  length (xs ++ ys) = length xs + length ys := by
  cases xs with
  | nil => simp only [nil_append, length_nil, zero_add]
  | cons _ tailx => simp only [cons_append, length_cons, length_append, succ_add]

theorem list_last_length (xs: List α):
  length (xs ++ x :: nil) = (length xs) + 1 := by
  induction xs with
  | nil => rfl
  | cons _ tail ih => simp [ih]

theorem list_cons_eq {x y: α} {xs ys: List α}:
  x :: xs = y :: ys <-> x = y /\ xs = ys := by
  apply Iff.intro
  · intro h
    apply And.intro
    · injections
    · injections
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

theorem list_take_zero (xs : List α) :
  take zero xs = [] := by rw [take]

theorem list_rev_empty (xs : List α) :
  reverse xs = [] -> xs = [] := by
  cases xs with
  | nil => simp only [reverse_nil, forall_true_left]
  | cons head tail =>
    intro h
    have h' : (reverse (reverse (head :: tail)) = []) := congrArg reverse h
    simp only [reverse_cons, reverse_append, reverse_nil, nil_append, reverse_reverse, singleton_append] at h'

theorem list_rev_empty2 :
  reverse ([] : List α) = [] := by trivial

theorem list_rev_eq (_n : Nat) (xs ys : List α) :
  reverse xs = reverse ys -> xs = ys := by
  intro h
  have h' : reverse (reverse xs) = reverse (reverse ys) :=
    congrArg reverse h
  simp only [reverse_reverse] at h'
  assumption

theorem take_one_nil : take 1 ([] : List α) = [] := by
  rw [take]

private theorem list_length_cons_le_succ (head : α) (tail : List α) (k : Nat):
  length (head :: tail) ≤ succ k -> length tail ≤ k := by
  rw [length]
  apply Nat.le_of_succ_le_succ

theorem list_take_all2 (n: Nat) (xs: List α):
  (length xs) <= n -> take n xs = xs := by
  revert xs
  induction n with
  | zero =>
    intro xs h
    rw [list_length_zero_or_smaller_is_empty xs h]
    rw [take]
  | succ k ih =>
    intro xs
    cases xs with
    | nil =>
      intro _
      apply list_take_nil
    | cons head tail =>
      intro h
      rw [take]
      apply (congrArg (cons head))
      apply ih tail (list_length_cons_le_succ head tail k h)

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
      simp only [length_nil, zero_eq, le_refl]
    | succ k =>
      rw [take]
      rw [length]
      apply Nat.succ_le_succ
      apply (ih k)

theorem list_length_succ_le_cons  (head : α) (tail : List α) (k : Nat):
  k ≤ length tail -> succ k ≤ length (head :: tail) := by
  rw [length, <-nat_succ_eq_plus_one]
  apply Nat.succ_le_succ

theorem list_length_pred_le_cons (head : α) (tail : List α) (k : Nat):
  k ≤ length (head :: tail) -> pred k ≤ length tail := by
  rw [length, <-nat_succ_eq_plus_one]
  apply nat_pred_le_succ

theorem list_length_cons_succ : length (x :: xs) = succ (length xs) := by simp

theorem list_take_length_le (n: Nat) (xs: List α):
  n <= length xs -> length (take n xs) = n := by
  revert n
  induction xs with
  | nil =>
    intro n
    rw [list_take_nil]
    rw [length]
    cases n with
    | zero =>
      intro _
      rfl
    | succ n' =>
      intro h
      contradiction
  | cons head tail ih =>
    intro n
    intro h
    have h' : _ := ih (pred n)
    have h₂ : _ := h' ((list_length_pred_le_cons head tail n) h)
    cases n with
    | zero => rw [list_take_zero, length]
    | succ n' =>
      simp only [Nat.pred_succ, length_take, ge_iff_le, min_eq_left_iff] at h₂
      rw [list_take_cons, list_length_cons_succ]
      simp only [length_take, ge_iff_le, succ.injEq, min_eq_left_iff]
      exact h₂

theorem list_take_app (n: Nat) (xs ys: List α):
  take n (xs ++ ys) = (take n xs) ++ (take (n - length xs) ys) := by
  revert xs ys
  induction n with
  | zero =>
    intro xs ys
    rw [Nat.zero_sub]
    repeat rw [take]
    simp only [append_nil]
  | succ n ih =>
    intro xs ys
    cases xs with
    | nil =>
      repeat rw [take]
      simp only [nil_append, length_nil, ge_iff_le, nonpos_iff_eq_zero, tsub_zero]
    | cons x xs =>
      rw [take]
      rw [length]
      rw [succ_sub_succ]
      rw [<- list_app_comm_cons]
      rw [take]
      apply (congrArg (cons x))
      apply ih

theorem list_take_app_2 (n: Nat) (xs ys: List α):
  take ((length xs) + n) (xs ++ ys) = xs ++ take n ys := by
  induction xs with
  | nil =>
    simp only [length_nil, zero_add, nil_append]
  | cons x xs ih =>
    rw [<- list_app_comm_cons]
    rw [length]
    have hcomm: length xs + 1 + n = succ (length xs + n) := by
      rw [Nat.add_comm (length xs) 1]
      rw [Nat.add_assoc]
      rw [Nat.add_comm]
    rw [hcomm]
    rw [take]
    apply (congrArg (cons x))
    apply ih

theorem list_take_take (n: Nat) (xs: List α):
  take n (take m xs) = take (min n m) xs := by
  revert m xs
  induction n with
  | zero =>
    intro m xs
    rw [nat_min_zero]
    repeat rw [take]
  | succ n ihn =>
    intro m xs
    cases m with
    | zero =>
      unfold min
      unfold instMinNat
      unfold minOfLe
      rw [take]
      simp only [take]
    | succ m =>
      unfold min
      unfold instMinNat
      unfold minOfLe
      simp only
      split
      next h =>
        rw [nat_succ_le_succ_iff] at h
        cases xs with
        | nil =>
          rw [take]
        | cons x xs =>
          repeat rw [take]
          apply (congrArg (cons x))
          have hmin : min n m = n := by
            unfold min
            unfold instMinNat
            unfold minOfLe
            simp only [ite_eq_left_iff, not_le]
            intro hless
            linarith
          have ihn' : _ := @ihn m xs
          rw [hmin] at ihn'
          exact ihn'
      next h =>
        rw [nat_succ_le_succ_iff] at h
        cases xs with
        | nil =>
          rw [take]
          apply list_take_nil
        | cons x xs =>
          repeat rw [take]
          apply (congrArg (cons x))
          have hmin : min n m = m := by
            unfold min
            unfold instMinNat
            unfold minOfLe
            simp only [ite_eq_right_iff]
            intro hless
            linarith
          have ihn' : _ := @ihn m xs
          rw [hmin] at ihn'
          exact ihn'

theorem list_drop_O (xs: List α):
  drop 0 xs = xs := by
  rw [drop]

theorem list_drop_zero (xs: List α):
  drop zero xs = xs := by
  rw [drop]

theorem list_drop_nil {α: Type u} (n: Nat):
  drop n ([] : List α) = [] := by
  cases n with
  | zero => rw [drop]
  | succ n' => rw [drop]

theorem list_take_drop_comm (n m: Nat) (xs: List α):
  take m (drop n xs) = drop n (take (n + m) xs) := by
  revert m xs
  induction n with
  | zero =>
    intro m xs
    rw [Nat.zero_add]
    repeat rw [list_drop_zero]
  | succ n ih =>
    intro m xs
    cases xs with
    | nil =>
      rw [list_drop_nil, list_take_nil, list_take_nil, list_drop_nil]
    | cons x xs =>
      rw [drop]
      rw [nat_add_succ_is_succ_add]
      rw [take]
      rw [drop]
      apply ih

theorem list_drop_take_comm (n m: Nat) (xs: List α):
  drop m (take n xs) = take (n - m) (drop m xs) := by
  revert m xs
  induction n with
  | zero =>
    intro m xs
    rw [Nat.zero_sub]
    repeat rw [list_take_zero]
    rw [list_drop_nil]
  | succ n ih =>
    intro m xs
    cases m with
    | zero =>
      rw [Nat.sub_zero]
      repeat rw [list_drop_zero]
    | succ m =>
      cases xs with
      | nil =>
        rw [list_take_nil, list_drop_nil, list_take_nil]
      | cons x xs =>
        rw [take]
        rw [drop]
        rw [Nat.succ_sub_succ]
        rw [drop]
        apply ih

theorem list_drop_cons (n: Nat) (x: α) (xs: List α):
  drop (n + 1) (x::xs) = drop n xs := by
  rw [drop]

theorem list_drop_all (xs: List α):
  drop (length xs) xs = nil := by
  induction xs with
  | nil =>
    rw [list_drop_nil]
  | cons head tail ih =>
    rw [length]
    rw [drop]
    exact ih

theorem list_drop_all2 (n: Nat) (xs: List α):
  length xs <= n -> drop n xs = [] := by
  revert xs
  induction n with
  | zero =>
    intro xs
    intro h
    have empty_list := list_length_zero_or_smaller_is_empty xs h
    rw [empty_list]
    rw [drop]
  | succ n ih =>
    intro xs
    cases xs with
    | nil =>
      rw [length]
      intro _
      rw [drop]
    | cons x xs =>
      rw [length]
      intro h
      rw [drop]
      rw [nat_succ_le_succ_iff] at h
      exact ih xs h

theorem list_take_drop (n: Nat) (xs: List α):
  take n xs ++ drop n xs = xs := by
  revert xs
  induction n with
  | zero =>
    intro xs
    rw [take]
    rw [drop]
    rw [list_app_nil_l]
  | succ n ih =>
    intro xs
    cases xs with
    | nil =>
      rw [take, drop]
      simp only [append_nil]
    | cons x xs =>
      rw [take, drop]
      apply (congrArg (cons x))
      apply ih

theorem nat_succ_gt_succ {n m: Nat}:
  succ n > succ m -> n > m := by
  intro h
  cases h with
  | refl =>
    constructor
  | step s =>
    apply Nat.le_of_succ_le_succ
    exact (Nat.le_succ_of_le s)

theorem nat_succ_gt_succ' {n m: Nat}:
  succ n > succ m -> n > m := by
  apply Nat.le_of_succ_le_succ

theorem list_take_large_length {n: Nat} {xs: List α}:
  n > length xs -> length (take n xs) = length xs := by
  revert xs
  induction n with
  | zero =>
    intro xs
    intro h
    contradiction
  | succ n ih =>
    intro xs
    intro h
    cases xs with
    | nil =>
      rw [take]
    | cons x xs =>
      rw [take]
      repeat rw [length]
      apply congrArg succ
      rw [length] at h
      have h' := nat_succ_gt_succ h
      exact ih h'

theorem list_take_length (n: Nat) (xs: List α):
  length (take n xs) = min n (length xs) := by
  unfold min
  unfold instMinNat
  unfold minOfLe
  simp only [length_take, ge_iff_le]
  split
  next =>
    rename_i c
    unfold min; unfold instMinNat; unfold minOfLe; simp only [ite_eq_left_iff, not_le]
    intro c'
    linarith
  next =>
    rename_i c
    have c' := gt_of_not_le c
    unfold min; unfold instMinNat; unfold minOfLe; simp only [ite_eq_right_iff]
    intro c''
    linarith

theorem list_drop_length (n: Nat) (xs: List α):
  length (drop n xs) = length xs - n := by
  revert xs
  induction n with
  | zero =>
    intro xs
    rw [drop]
    rw [Nat.sub_zero]
  | succ n ih =>
    intro xs
    cases xs with
    | nil =>
      rw [drop]
      rw [length]
      rw [Nat.zero_sub]
    | cons x xs =>
      rw [drop]
      rw [length]
      rw [Nat.succ_sub_succ]
      apply ih

theorem list_take_app_length (xs ys: List α):
  take (length xs) (xs ++ ys) = xs := by
  revert ys
  induction xs with
  | nil =>
    simp only [take, forall_const]
  | cons x xs ih =>
    intro ys
    rw [length]
    rw [<- list_app_comm_cons]
    rw [take]
    apply (congrArg (cons x))
    apply ih

theorem list_split_list (xs: List α) (n : Nat): ∀ (ys zs: List α),
  length ys = n ->
  xs = ys ++ zs ->
  ys = take n xs /\
  zs = drop n xs := by
  revert xs
  induction n with
  | zero =>
    intro xs ys zs hl ha
    have he := list_length_zero_is_empty _ hl
    rw [he]
    rw [he] at ha
    rw [take]
    rw [drop]
    rw [list_app_nil_l] at ha
    have ha' := Eq.symm ha
    constructor
    case left =>
      rfl
    case right =>
      exact ha'
  | succ n ih =>
    intro xs ys zs hl ha
    cases xs with
    | nil =>
      rw [take]
      rw [drop]
      have ha' := Eq.symm ha
      rw [list_app_nil_nil] at ha'
      exact ha'
    | cons x xs =>
      rw [take, drop]
      cases ys with
      | nil =>
        rw [length] at hl
        contradiction
      | cons y ys =>
        simp only [length_cons, succ.injEq] at hl
        have hzs : y :: ys ++ zs = y :: (ys ++ zs) := by
          simp only [cons_append]
        rw [hzs] at ha
        rw [list_cons_eq] at ha
        cases ha with
        | intro hxy ha =>
          rw [hxy]
          have ih' := ih xs ys zs hl ha
          cases ih' with
          | intro hys hzs =>
            rw [<- hys]
            rw [<- hzs]
            simp only [and_self]

theorem list_length_split (xs ys: List α):
  length (xs ++ ys) = length xs + length ys := by
  simp only [length_append]

theorem list_prefix_leq_length (xs ys zs: List α):
  xs = ys ++ zs -> length ys <= length xs := by
  intro xsyszs
  have h := list_split_list xs (length ys) ys zs rfl xsyszs
  cases h with
  | intro hys hzs =>
    rw [hzs] at xsyszs
    rw [xsyszs]
    rw [list_length_split]
    linarith

theorem list_drop_length_prefix_is_suffix (xs ys: List α):
  drop (length xs) (xs ++ ys) = ys := by
  induction xs with
  | nil =>
    simp only [drop, nil_append]
  | cons x xs ih =>
    simp only [drop, add_eq, add_zero, append_eq]
    exact ih

theorem list_drop_app_length (xs ys: List α):
  drop (length xs) (xs ++ ys) = ys := by
  apply list_drop_length_prefix_is_suffix

theorem list_drop_app (n: Nat) (xs ys: List α):
  drop n (xs ++ ys) = (drop n xs) ++ (drop (n - length xs) ys) := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp
      exact ih n

-- list_drop_app's alternative proof using revert instead of generalizing
theorem list_drop_app' (n: Nat) (xs ys: List α):
  drop n (xs ++ ys) = (drop n xs) ++ (drop (n - length xs) ys) := by
  revert n
  induction xs with
  | nil => simp
  | cons x xs ih =>
    intro n
    cases n with
    | zero => simp
    | succ n =>
      simp
      exact ih n

theorem list_take_length_prefix_is_prefix (xs ys: List α):
  take (length xs) (xs ++ ys) = xs := by
  induction xs with
  | nil =>
    simp only [take]
  | cons x xs ih =>
    simp only [take, add_eq, add_zero, append_eq, cons.injEq, true_and]
    exact ih

theorem list_prefix_length_leq: ∀ (xs ys zs: List α),
  xs ++ ys = zs -> length xs <= length zs := by
  intro xs ys zs xsyszs
  apply (list_prefix_leq_length zs xs ys)
  apply Eq.symm
  exact xsyszs

theorem list_length_gt_zero: ∀ (xs: List α),
  xs ≠ [] -> 0 < length xs := by
  intro xs
  cases xs with
  | nil =>
    intro h
    contradiction
  | cons x xs =>
    intro _
    rw [length]
    apply Nat.zero_lt_succ

theorem list_prefix_is_gt_zero_and_leq: ∀ (xs ys zs: List α),
  (xs ≠ []) ->
  xs ++ ys = zs ->
  (0 < length xs /\ length xs <= length zs) := by
  intro xs ys zs
  revert xs ys
  cases zs with
  | nil =>
    intro xs ys hneq ha
    rw [list_app_nil_nil] at ha
    cases ha with
    | intro hxs hys =>
      contradiction
  | cons z zs =>
    intro xs ys hneq ha
    have hl := list_length_gt_zero _ hneq
    rw [<- ha]
    apply And.intro
    case left =>
      exact hl
    case right =>
      rw [list_app_length]
      apply Nat.le_add_right

theorem list_prefix_is_not_empty_with_index_gt_zero: ∀ (xs: List α) (n: Nat)
  (_range: 0 < n /\ n <= length xs),
  take n xs ≠ [] := by
  intro xs n range h
  cases range with
  | intro notzero max =>
    cases n with
    | zero =>
      contradiction
    | succ n =>
      cases xs with
      | nil =>
        contradiction
      | cons x xs =>
        simp only [succ_pos', take] at *

theorem list_app_uncons: ∀ {x: α} {xs ys zs: List α},
  ys ++ zs = x :: xs ->
  (ys = [] /\ zs = x :: xs)
  \/ (∃
     (ys': List α)
     (_pys: ys = x :: ys'),
     ys' ++ zs = xs
  ) := by
  intro x xs ys zs H
  cases ys with
  | nil =>
    apply Or.inl
    apply And.intro
    · rfl
    · simp only [nil_append] at H
      assumption
  | cons y_ ys_ =>
    -- ys = y_ :: ys_
    apply Or.inr
    have H' := list_cons_eq.mp H
    have HR := H'.right
    have HL := H'.left
    -- pys = (y_ :: ys_ = x :: ys')
    apply Exists.intro ys_
    -- pys = (y_ :: ys_ = x :: ys_)
    rw [HL]
    -- pys = (x :: ys_ = x :: ys_)
    apply Exists.intro rfl
    exact HR

theorem list_app_inv_head: ∀ {xs ys zs: List α},
  xs ++ ys = xs ++ zs -> ys = zs := by
  intro xs ys zs H
  simp only [append_cancel_left_eq] at H
  assumption

theorem list_app_inv_head_reverse: ∀ {xs ys zs: List α},
  ys = zs -> xs ++ ys = xs ++ zs := by
  intro xs ys zs H
  simp only [append_cancel_left_eq]
  assumption

theorem list_app_inv_tail: ∀ {xs ys zs: List α},
  xs ++ zs = ys ++ zs -> xs = ys := by
  intro xs ys zs H
  simp only [append_cancel_right_eq] at H
  assumption

theorem list_app_inv_tail_reverse: ∀ {xs ys zs: List α},
  xs = ys -> xs ++ zs = ys ++ zs := by
  intro xs ys zs H
  simp only [append_cancel_right_eq]
  assumption
