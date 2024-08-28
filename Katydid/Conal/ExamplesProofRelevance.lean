-- Here we show how proofs are inspectable, since we have proof relevant proofs.
-- Each proof represents a different parse and not just a validation.

import Katydid.Conal.Language

open Language
open String

-- This is a simple language a ⋃ a, to show case proof relevance.
def aora: Language.Lang Char := (or (char 'a') (char 'a'))
-- In the case of proof irrevelance, which is the default in Lean, this would be a Prop, but now it is Type.
def parse_aora_with_string_a: Type := aora (toList "a")
-- Since the proof of parse_aora_with_string_a is proof relevant (Type),
-- we can inspect it and return a string based on which parse was successful, "left" or "right".
def example_of_proof_relevant_parse_left_or_right : parse_aora_with_string_a -> String := by
  intro x
  cases x with
  | inl xa =>
    cases xa with
    | mk eq =>
      cases eq with
      | refl =>
        exact "left"
  | inr xb =>
    cases xb with
    | mk eq =>
    cases eq with
      | refl =>
        exact "right"

-- This is just a lame example to show that less obvious languages can still be parsed and proofs inspected.
def example_of_proof_relevant_parse1 : (or (char 'a') (char 'b')) (toList "a") -> Nat := by
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

-- This checks that concat's proof can be inspected, even though it uses a Sigma type Σ'
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
