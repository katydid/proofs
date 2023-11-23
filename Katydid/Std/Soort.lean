-- required for `attribute [refl]`
import Mathlib.Init.Algebra.Classes

-- Tipe is a collection of standard types and functions associated with Sort,
-- that we would expect to be in the Lean standard library at some point in future.
-- The file is named Soort, since it is Afrikaans for Sort.

-- See Tipe.lean for the Type version of this library.

/--
The equality relation. We use this instead of Lean's `Eq` because
we need it to be defined on Type instead of Prop.
-/
inductive SEq {α : Type u} (x : α) : α -> Sort (max 1 u) where
  | rrefl : SEq x x

-- the abbreviation ≡ is typed with `slash = =`
infixl:65 " ≡ " => SEq

-- attribute [refl] allows us to use the rfl tactic on TEq, see the example below.
attribute [refl] SEq.rrefl

example : 1 ≡ 1 := by rfl
