-- Here we show how proofs are inspectable, since we have proof relevant proofs.
-- Each proof represents a different parse and not just a validation.

import Katydid.Conal.Language

open Language
open String

def example_of_proof_relevant_parse : (or (char 'a') (char 'b')) (toList "a") -> Nat := by
  intro x
  cases x with
  | inl xa =>
    cases xa with
    | mk eq =>
      cases eq with
      | refl =>
        exact 0
  | inr xb =>
    cases xb with
    | mk eq =>
      contradiction

def example_of_proof_relevant_parse2 : (concat (char 'a') (or (char 'b') (char 'c'))) (toList "ab") -> Nat := by
  intro x1
  simp at x1
  cases x1 with
  | mk x1 x2 =>
    cases x2 with
    | mk x2 x3 =>
      cases x3 with
      | mk x3 x4 =>
        cases x3 with
        | mk x3 =>
          cases x4 with
          | mk x4 x5 =>
            cases x4 with
            | inl x4 =>
                cases x4 with
                | mk x4 =>
                  subst_vars
                  exact 0
            | inr x4 =>
              cases x4 with
              | mk x4 =>
                subst_vars
                contradiction
