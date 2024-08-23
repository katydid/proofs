import Mathlib.Init.Algebra.Classes

example {α : Type u} {a b : α} (p q : a = b) : p = q := by
  cases p
  cases q
  rfl

inductive TEq.{tu} {α: Type tu} (a b: α) : Type tu where
  | mk : a = b -> TEq a b

example : TEq 1 1 := by
  constructor
  rfl

@[match_pattern] def trfl {α : Type u} {a : α} : TEq a a := TEq.mk rfl
attribute [simp] trfl

-- the abbreviation ≡ is typed with `slash = =`
infixl:65 " ≡ " => TEq

example : 1 ≡ 1 := by
  constructor -- we need to destruct before we can call rfl
  rfl

example : 1 ≡ 1 := by
  apply trfl

example : 1 ≡ 1 := by
  apply TEq.mk
  rfl

example {α : Type u} {a b : α} (p q : a ≡ b) : p ≡ q := by
  cases p
  next p =>
  cases q
  next q =>
  constructor
  rfl

-- TODO: How can we make rewrite easier, without needing to destruct first?
--   TODO: if all else fails, write a tactic

def rewrite_test:
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  constructor
  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]

def rewrite_test_with_next:
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  constructor
  cases ab
  next ab =>
  rw [ab]
  cases bc
  next bc =>
  rw [bc]

def rewrite_test_with_trfl:
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]
      exact trfl
