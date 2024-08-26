-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Symbolic.lagda

import Katydid.Conal.Decidability
import Katydid.Conal.Function
import Katydid.Conal.Language
import Katydid.Conal.Calculus

inductive Lang {P Q : Language.Lang α}: (List α -> Type u) -> Type (u + 1) where
  -- ∅ : Lang ◇.∅
  | emptyset : Lang Language.emptyset
  -- 𝒰 : Lang ◇.𝒰
  | universal : Lang Language.universal
  -- 𝟏 : Lang ◇.𝟏
  | emptystr : Lang Language.emptystr
  -- ` : (a : A) → Lang (◇.` a)
  | char {a: Type u}: (a: α) -> Lang (Language.char a)
  -- _∪_ : Lang P → Lang Q → Lang (P ◇.∪ Q)
  | or : Lang P -> Lang Q -> Lang (Language.or P Q)
  -- _∩_ : Lang P → Lang Q → Lang (P ◇.∩ Q)
  | and : Lang P -> Lang Q -> Lang (Language.and P Q)
  -- _·_ : Dec s → Lang P → Lang (s ◇.· P)
  | scalar {s: Type u}: (Decidability.Dec s) -> Lang P -> Lang (Language.scalar s P)
  -- _⋆_ : Lang  P → Lang Q → Lang (P ◇.⋆ Q)
  | concat : Lang P -> Lang Q -> Lang (Language.concat P Q)
  -- _☆  : Lang P → Lang (P ◇.☆)
  | star : Lang P -> Lang (Language.star P)
  -- _◂_  : (Q ⟷ P) → Lang P → Lang Q
  | iso : (Q ⟷ P) -> Lang P -> Lang Q
