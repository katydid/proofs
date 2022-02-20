Require Import Symbolic.Input.Error.

Definition Result (A: Set): Set := Error + A.

Definition ok {A: Set} (a: A): Result A := inr a.
Definition error {A: Set} (e: Error): Result A := inl e.

Definition swallow {A B: Set} (f: A -> B -> bool) (x: Result A) (y: Result B): Result bool :=
  match x with
  | inl _ => ok false
  | inr xr =>
    match y with
    | inl _ => ok false
    | inr yr => ok (f xr yr)
    end
  end.