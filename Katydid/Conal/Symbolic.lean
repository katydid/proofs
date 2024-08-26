-- A translation to Lean from Agda
-- https://github.com/conal/paper-2021-language-derivatives/blob/main/Symbolic.lagda

import Katydid.Conal.Decidability
import Katydid.Conal.Language

variable {P Q : dLang α}
variable {s : Type u}

inductive Lang : (List α -> Type u) -> Type (u + 1) where
  | emptySet : Lang dLang.emptyset
  | universal : Lang (fun _ => PUnit)
  | emptyStr : Lang dLang.emptystr
  | char {a: Type u}: (a: α) -> Lang (dLang.char a)
  | or : Lang P -> Lang Q -> Lang (dLang.or P Q)
  | and : Lang P -> Lang Q -> Lang (dLang.and P Q)
  | scalar {s: Type u}: (Dec s) -> Lang P -> Lang (dLang.scalar s P)
  | concat : Lang P -> Lang Q -> Lang (dLang.concat P Q)
  | star : Lang P -> Lang (dLang.star P)
