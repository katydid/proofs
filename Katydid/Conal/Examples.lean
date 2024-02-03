-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Examples.lagda

import Katydid.Conal.LanguageNotation
open Lang

example: (Lang.char 'a') ['a'] := by
  simp
  constructor
  rfl

-- a∪b : Lang
-- a∪b = ` 'a' ∪ ` 'b'

-- _ : a∪b [ 'b' ]
-- _ = inj₂ refl
example : (char 'a' ⋃ char 'b') ['b'] :=
  Sum.inr (TEq.mk rfl)

example : (char 'a' ⋃ char 'b') (String.toList "b") := by
  apply Sum.inr
  constructor
  rfl

-- a⋆b : Lang
-- a⋆b = ` 'a' ⋆ ` 'b'

-- _ : a⋆b ('a' ∷ 'b' ∷ [])
-- _ = ([ 'a' ] , [ 'b' ]) , refl , refl , refl
example : (char 'a', char 'b') (String.toList "ab") := by sorry
  -- TODO: ⟨ ['a'], ['b'], TEq.mk rfl, TEq.mk rfl, rfl ⟩

example : ((char 'a')*) (String.toList "a") := by sorry
  -- TODO:
  -- simp
  -- refine ⟨[['a']], ?a ⟩
  -- refine ⟨ by simp; , ?b ⟩
  -- apply All.cons
  -- · simp; rfl
  -- · apply All.nil

example : ((char 'a')*) (String.toList "a") := by sorry
  -- TODO:
  -- simp
  -- refine ⟨[['a']], ?a ⟩
  -- refine ⟨ trifle, ?b ⟩
  -- exact All.cons trifle All.nil

-- a∪b☆ : Lang
-- a∪b☆ = a∪b ☆

-- _ : a∪b☆ ('a' ∷ 'b' ∷ 'a' ∷ [])
-- _ = [ 'a' ] ∷ [ 'b' ] ∷ [ 'a' ] ∷ []
--   , refl
--   , inj₁ refl ∷ inj₂ refl ∷ inj₁ refl ∷ []
example : ((char 'a' ⋃ char 'b')*) (String.toList "aba") := by sorry
  -- TODO:
  -- simp
  -- refine ⟨ [['a'], ['b'], ['a']] , ?a ⟩
  -- refine ⟨ trifle, ?b ⟩
  -- apply All.cons
  -- · apply Sum.inl
  --   simp; rfl
  -- · apply All.cons
  --   · apply Sum.inr
  --     simp; rfl
  --   · apply All.cons
  --     · apply Sum.inl
  --       simp; rfl
  --     · apply All.nil

example : ((char 'a' ⋃ char 'b')*) (String.toList "aba") := by sorry
  -- TODO:
  -- ⟨ [['a'], ['b'], ['a']],
  --   trifle,
  --   Sum.inl trifle ∷ Sum.inr trifle ∷ Sum.inl trifle ∷ ∀[]⟩
