import Katydid.Conal.Decidability
import Katydid.Conal.Function
import Katydid.Conal.Language
import Katydid.Conal.Calculus

namespace Automatic

-- record Lang (P : ◇.Lang) : Set (suc ℓ) where
--   coinductive
--   field
--     ν : Dec (◇.ν P)
--     δ : (a : A) → Lang (◇.δ P a)

inductive Lang: {α: Type u} -> Language.Lang.{u} α -> Type (u + 1) where
  | mk
   (null: Decidability.Dec (Language.null R))
   (derive: {R: Language.Lang.{u} α} -> (a: α) -> Lang (Language.derive R a))
   : Lang R

end Automatic
