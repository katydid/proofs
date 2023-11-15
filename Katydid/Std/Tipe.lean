-- required for `attribute [refl]`
import Mathlib.Init.Algebra.Classes

-- Tipe is a collection of standard types and functions associated with Type,
-- that we would expect to be in the Lean standard library at some point in future.
-- The file is named Tipe, since it is Afrikaans for Type and common way to avoid using the keyword Type, since it has the same pronounciation as type.

-- Discussion where we got the tips for this library: https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/is.20there.20a.20refl.20for.20Type

/--
The equality relation. We use this instead of Lean's `Eq` because
we need it to be defined on Type instead of Prop.
-/
inductive TEq {α : Type u} (x : α) : α -> Type u where
  | rrefl : TEq x x

-- the abbreviation ≡ is typed with `slash = =`
infixl:65 " ≡ " => TEq

-- attribute [refl] allows us to use the rfl tactic on TEq, see the example below.
attribute [refl] TEq.rrefl

example : 1 ≡ 1 := by rfl

-- Only the Prop version is available in mathlib https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/List/Defs.html#List.Forall
-- so we have to create our own version for Type
inductive All {α: Type u} (P : α -> Type u) : (List α -> Type u)  where
  | nil : All P []
  | cons : ∀ {x xs} (_px : P x) (_pxs : All P xs), All P (x :: xs)
