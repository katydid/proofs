import Katydid.Conal.Language

-- ν⇃ : Lang → Set ℓ      -- “nullable”
-- ν⇃ P = P []
def ν (P : Lang α) : Type u :=
  P []

-- δ⇃ : Lang → A → Lang   -- “derivative”
-- δ⇃ P a w = P (a ∷ w)
def δ (P : Lang α) (a : α) : Lang α :=
  fun (w : List α) => P (a :: w)
