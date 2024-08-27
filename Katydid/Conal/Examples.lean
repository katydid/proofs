-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Examples.lagda

import Katydid.Conal.Language
open Language

example: (char 'a') ['a'] := by
  simp
  constructor
  rfl

-- a∪b : Lang
-- a∪b = ` 'a' ∪ ` 'b'

-- _ : a∪b [ 'b' ]
-- _ = inj₂ refl
example : (or (char 'a') (char 'b')) ['b'] :=
  Sum.inr trfl

example : (or (char 'a') (char 'b')) (String.toList "b") := by
  apply Sum.inr
  constructor
  rfl

-- a⋆b : Lang
-- a⋆b = ` 'a' ⋆ ` 'b'

-- _ : a⋆b ('a' ∷ 'b' ∷ [])
-- _ = ([ 'a' ] , [ 'b' ]) , refl , refl , refl
example : (concat (char 'a') (char 'b')) (String.toList "ab") := by
  simp
  exists ['a']
  exists ['b']
  exists trfl
  exists trfl

example : (concat (char 'a') (char 'b')) (String.toList "ab") := by
  simp
  refine PSigma.mk ['a'] ?a
  refine PSigma.mk ['b'] ?b
  refine PSigma.mk trfl ?c
  refine PSigma.mk trfl ?d
  rfl

example : (concat (char 'a') (char 'b')) (String.toList "ab") :=
  PSigma.mk ['a'] (PSigma.mk ['b'] (PSigma.mk trfl (PSigma.mk trfl rfl)))

example : (concat (char 'a') (char 'b')) (String.toList "ab") :=
  PSigma.mk ['a'] (PSigma.mk ['b'] (PSigma.mk trfl (PSigma.mk trfl rfl)))

example : (star (char 'a')) (String.toList "a") := by
  refine ⟨[['a']], ?a⟩
  refine ⟨?b, rfl⟩
  apply All.cons
  · exact trfl
  · apply All.nil

example : (star (char 'a')) (String.toList "a") := by
  exact ⟨_, All.cons trfl All.nil, rfl⟩

-- a∪b☆ : Lang
-- a∪b☆ = a∪b ☆

-- _ : a∪b☆ ('a' ∷ 'b' ∷ 'a' ∷ [])
-- _ = [ 'a' ] ∷ [ 'b' ] ∷ [ 'a' ] ∷ []
--   , refl
--   , inj₁ refl ∷ inj₂ refl ∷ inj₁ refl ∷ []
example : (star (or (char 'a') (char 'b'))) (String.toList "aba") := by
  refine ⟨[['a'], ['b'], ['a']], ?a⟩
  refine ⟨?b, rfl⟩
  apply All.cons
  · exact Sum.inl trfl
  · apply All.cons
    · exact Sum.inr trfl
    · apply All.cons
      · exact Sum.inl trfl
      · apply All.nil

example : (star (or (char 'a') (char 'b'))) (String.toList "aba") := by
  exact ⟨_, All.cons (Sum.inl trfl) (All.cons (Sum.inr trfl) (All.cons (Sum.inl trfl) All.nil)), rfl⟩
