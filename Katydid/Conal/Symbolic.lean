-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Symbolic.lagda

import Katydid.Conal.Decidability
import Katydid.Conal.Function
import Katydid.Conal.Language

variable {P Q : dLang α}
variable {s : Type u}

inductive Lang : (List α -> Type u) -> Type (u + 1) where
  -- ∅ : Lang ◇.∅
  | emptySet : Lang dLang.emptyset
  -- 𝒰 : Lang ◇.𝒰
  | universal : Lang dLang.universal
  -- 𝟏 : Lang ◇.𝟏
  | emptyStr : Lang dLang.emptystr
  -- ` : (a : A) → Lang (◇.` a)
  | char {a: Type u}: (a: α) -> Lang (dLang.char a)
  -- _∪_ : Lang P → Lang Q → Lang (P ◇.∪ Q)
  | or : Lang P -> Lang Q -> Lang (dLang.or P Q)
  -- _∩_ : Lang P → Lang Q → Lang (P ◇.∩ Q)
  | and : Lang P -> Lang Q -> Lang (dLang.and P Q)
  -- _·_ : Dec s → Lang P → Lang (s ◇.· P)
  | scalar {s: Type u}: (Dec s) -> Lang P -> Lang (dLang.scalar s P)
  -- _⋆_ : Lang  P → Lang Q → Lang (P ◇.⋆ Q)
  | concat : Lang P -> Lang Q -> Lang (dLang.concat P Q)
  -- _☆  : Lang P → Lang (P ◇.☆)
  | star : Lang P -> Lang (dLang.star P)
  -- _◂_  : (Q ⟷ P) → Lang P → Lang Q
  | iso: (Q ⟷ P) -> Lang P -> Lang Q
