-- Tipe is a collection of standard types and functions associated with Type,
-- that we would expect to be in the Lean standard library at some point in future.
-- The file is named Tipe, since it is Afrikaans for Type and common way to avoid using the keyword Type, since it has the same pronounciation as type.

-- required for `attribute [refl]`
import Mathlib.Init.Algebra.Classes

example {α : Type u} {a b : α} (p q : a = b) : p = q := by
  cases p
  cases q
  rfl

/--
The equality relation. We use this instead of Lean's `Eq` because
we need it to be defined on Type instead of Prop.
-/
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

def eq_of_teq {α : Type u} {a a' : α} (h : TEq a a') : Eq a a' :=
  have : (α β : Type u) → (a b: α) → TEq a b → (h : Eq α β) → Eq a b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ _ => by assumption)
  this α α a a' h rfl

-- This is legal because TEq is a sub singleton (it has one of fewer ways to be constructed).
def teq_of_eq {α : Type u} {a a' : α} (h : Eq a a') : TEq a a' :=
  have : (α β : Type u) → (a b: α) → Eq a b → (h : TEq α β) → TEq a b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => trfl)
  this α α a a' h trfl

-- rewrite requires using constructor and cases to go from ≡ to = in the goal and hypothesis respectively.
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
