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
  constructor -- TODO: do we need to destruct before we can call rfl
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

def rewrite_test':
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]
      constructor
      rfl
      -- exact trifle

def rewrite_test'' (ab: a ≡ b) (bc: b ≡ c): a ≡ c :=
  match (ab, bc) with
  | ⟨ ⟨ ab' ⟩ , ⟨ bc' ⟩ ⟩ => by sorry

def rewrite_test''':
  ∀ (_: a ≡ b) (_: b ≡ c),
    a ≡ c := by
  intro ab bc
  cases ab with
  | mk ab =>
    rw [ab]
    cases bc with
    | mk bc =>
      rw [bc]
      constructor
      rfl
      -- exact trifle
