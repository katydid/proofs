import Katydid.Regex.Language

open List

namespace SmartRegex

inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α

def denote {α: Type} (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.pred p => Language.pred p
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

-- TODO: incorporate more simplification rules into the smart constructor
def smartOr (x y: Regex α): Regex α :=
  match x with
  | Regex.emptyset => y
  | _ =>
    match y with
    | Regex.emptyset => x
    | _ => Regex.or x y

-- TODO: incorporate more simplification rules into the smart constructor
def smartConcat (x y: Regex α): Regex α :=
  match x with
  | Regex.emptystr => y
  | _ =>
    match y with
    | Regex.emptystr => x
    | _ => Regex.concat x y

-- TODO: incorporate more simplification rules into the smart constructor
def smartStar (x: Regex α): Regex α :=
  match x with
  | Regex.star x' =>
    Regex.star x'
  | _ =>
    Regex.star x

theorem smartOr_is_correct (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  sorry

theorem smartConcat_is_correct (x y: Regex α):
  denote (Regex.concat x y) = denote (smartConcat x y) := by
  sorry

theorem smartStar_is_correct (x: Regex α):
  denote (Regex.star x) = denote (smartStar x) := by
  sorry
