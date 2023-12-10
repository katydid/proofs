-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Examples.lagda

import Katydid.Conal.RegexNotation

example: (Lang.char 'a') ['a'] := by
  simp
  rfl

-- a∪b : Lang
-- a∪b = ` 'a' ∪ ` 'b'

-- _ : a∪b [ 'b' ]
-- _ = inj₂ refl
example : (regex| a⋃b) ['b'] :=
  Sum.inr trifle

example : (regex| a⋃b ≈ "b") := by
  apply Sum.inr
  constructor

-- an example showing:
--   - how to use `simp` for `char`
--   - how to use `rfl` for `TEq`
example : (regex| a⋃b ≈ "b") := by
  apply Sum.inr
  simp
  rfl

-- a⋆b : Lang
-- a⋆b = ` 'a' ⋆ ` 'b'

-- _ : a⋆b ('a' ∷ 'b' ∷ [])
-- _ = ([ 'a' ] , [ 'b' ]) , refl , refl , refl
example : (regex| ab ≈ "ab") :=
  ⟨ ['a'], ['b'], trifle, trifle, trifle ⟩

example : (regex| a* ≈ "a") := by
  simp
  refine ⟨[['a']], ?a ⟩
  refine ⟨ trifle, ?b ⟩
  apply All.cons
  · simp; rfl
  · apply All.nil

example : (regex| a* ≈ "a") := by
  simp
  refine ⟨[['a']], ?a ⟩
  refine ⟨ trifle, ?b ⟩
  exact All.cons trifle All.nil

-- a∪b☆ : Lang
-- a∪b☆ = a∪b ☆

-- _ : a∪b☆ ('a' ∷ 'b' ∷ 'a' ∷ [])
-- _ = [ 'a' ] ∷ [ 'b' ] ∷ [ 'a' ] ∷ []
--   , refl
--   , inj₁ refl ∷ inj₂ refl ∷ inj₁ refl ∷ []
example : (regex| (a⋃b)* ≈ "aba") := by
  simp
  refine ⟨ [['a'], ['b'], ['a']] , ?a ⟩
  refine ⟨ trifle, ?b ⟩
  apply All.cons
  · apply Sum.inl
    simp; rfl
  · apply All.cons
    · apply Sum.inr
      simp; rfl
    · apply All.cons
      · apply Sum.inl
        simp; rfl
      · apply All.nil

example : (regex| (a⋃b)* ≈ "aba") :=
  ⟨ [['a'], ['b'], ['a']],
    trifle,
    Sum.inl trifle ∷ Sum.inr trifle ∷ Sum.inl trifle ∷ ∀[]⟩
