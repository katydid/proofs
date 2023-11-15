import Katydid.Conal.Language

-- open Lang is used to avoid qualifications for Lang.or, Lang.char etc.
open Lang

-- a∪b : Lang
-- a∪b = ` 'a' ∪ ` 'b'

-- _ : a∪b [ 'b' ]
-- _ = inj₂ refl
example : (or (char 'a') (char 'b')) ['a'] :=
  Sum.inl TEq.rrefl

example : (or (char 'a') (char 'b')) ['a'] := by
  apply Sum.inl
  constructor

-- an example showing:
--   - how to use `simp` for `char`
--   - how to use `rfl` for `TEq`
example : (or (char 'a') (char 'b')) ['a'] := by
  apply Sum.inl
  simp
  rfl
