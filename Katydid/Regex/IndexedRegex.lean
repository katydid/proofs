import Katydid.Std.Decidable

import Katydid.Regex.Language

namespace IndexedRegex

open List

inductive Regex (α: Type): (List α -> Prop) -> Type where
  | emptyset : Regex α Language.emptyset
  | emptystr : Regex α Language.emptystr
  | char : (a: α) → Regex α (Language.char a)
  | or : Regex α x → Regex α y → Regex α (Language.or x y)
  | concat : Regex α x → Regex α y → Regex α (Language.concat x y)
  | star : Regex α x → Regex α (Language.star x)

def null (r: Regex α l): Decidable (Language.null l) :=
  match r with
  | Regex.emptyset => Decidable.isFalse (Language.not_null_if_emptyset)
  | Regex.emptystr => Decidable.isTrue (Language.null_if_emptystr)
  | Regex.char _ => Decidable.isFalse (Language.not_null_if_char)
  | Regex.or x y =>
    Decidable.map (symm Language.null_iff_or)
      (Decidable.or (null x) (null y))
  | Regex.concat x y =>
    Decidable.map (symm Language.null_iff_concat)
      (Decidable.and (null x) (null y))
  | Regex.star _ => Decidable.isTrue (Language.null_if_star)

def derive [DecidableEq α] (r: Regex α l) (a: α): Regex α (Language.derive l a) := by
  sorry
