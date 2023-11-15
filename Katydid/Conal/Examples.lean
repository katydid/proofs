import Katydid.Conal.Language

-- a∪b : Lang
-- a∪b = ` 'a' ∪ ` 'b'

-- _ : a∪b [ 'b' ]
-- _ = inj₂ refl
example : (or_ (char 'a') (char 'b')) ['a'] :=
  Sum.inl REq.rrefl

example : (or_ (char 'a') (char 'b')) ['a'] := by
  apply Sum.inl
  constructor
