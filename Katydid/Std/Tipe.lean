-- Tipe is a collection of standard types and functions associated with Type,
-- that we would expect to be in the Lean standard library at some point in future.
-- The file is named Tipe, since it is Afrikaans for Type and common way to avoid using the keyword Type, since it has the same pronounciation as type.

-- required for `attribute [refl]`
import Mathlib.Init.Algebra.Classes

/--
The equality relation. We use this instead of Lean's `Eq` because
we need it to be defined on Type instead of Prop.
-/
inductive TEq {α : Type u} : α -> α -> Type u where
  | refl (x : α) : TEq x x

#check TEq.casesOn

-- the abbreviation ≡ is typed with `slash = =`
infixl:65 " ≡ " => TEq

example : 1 ≡ 1 := TEq.refl 1

-- attribute [refl] allows us to use the rfl tactic on TEq, see the example below.
-- Discussion where we got the tips for this library: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/is.20there.20a.20refl.20for.20Type
attribute [refl] TEq.refl

example : 1 ≡ 1 := by rfl

-- rfl for Type instead of Prop
@[match_pattern] def trifle {α : Type u} {a : α} : TEq a a := @TEq.refl α a
attribute [simp] trifle

example : 1 ≡ 1 := trifle

-- Only the Prop version is available in mathlib https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Defs.html#List.Forall
-- so we have to create our own version for Type
inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u)  where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)

infixr:29 " ∷ " => All.cons
-- TODO: Find a better notation
notation (priority:=low) " ∀[] " => All.nil

-- Also note that the following doesn't work, once you start trying to prove things like that are required to be in Type and not in Prop.
-- def All {α: Type u} (P : α -> Type u) (xs: List α): Type u :=
--   ∀ x ∈ xs, P x

-- TNot is the Type version to replace the Prop version of Not
def TNot (a : Type u) : Type u := a → Empty

-- TIff is the Type version to replace the Prop version of Iff
structure TIff (a b : Type) : Type where
  /-- If `a → b` and `b → a` then `a` and `b` are equivalent. -/
  intro ::
  /-- Modus ponens for if and only if. If `a ↔ b` and `a`, then `b`. -/
  mp : a → b
  /-- Modus ponens for if and only if, reversed. If `a ↔ b` and `b`, then `a`. -/
  mpr : b → a

infix:19 " <-> " => TIff

structure Tiso (a b : Type) : Type where
  intro ::
  f : a → b
  f' : b → a
  ff' : ∀ x, f (f' x) ≡ x
  f'f : ∀ x, f' (f x) ≡ x

infix:19 " <--> " => Tiso

def Teso {w : α} (P : α -> Type) (Q : α -> Type) := Tiso (P w) (Q w)

infix:19 " <---> " => Teso
