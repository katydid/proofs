import Katydid.Regex.Language
import Katydid.Regex.SimpleRegex

open List
open SimpleRegex

namespace SmartRegex

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
  | _otherwise =>
    match y with
    | Regex.emptystr => x
    | _otherwise => Regex.concat x y

-- TODO: incorporate more simplification rules into the smart constructor
def smartStar (x: Regex α): Regex α :=
  match x with
  | Regex.star x' =>
    Regex.star x'
  | _ =>
    Regex.star x

theorem smartOr_is_correct (x y: Regex α):
  denote (Regex.or x y) = denote (smartOr x y) := by
  cases x with
  | emptyset =>
    unfold smartOr
    simp [denote]
    exact (Language.simp_or_emptyset_l_is_r (denote y))
  | emptystr =>
    cases y <;> (try simp [smartOr])
    · case emptyset =>
      simp [denote]
      exact (Language.simp_or_emptyset_r_is_l _)
  | pred p =>
    cases y <;> (try simp [smartOr])
    · case emptyset =>
      simp [denote]
      exact (Language.simp_or_emptyset_r_is_l _)
  | or x1 x2 =>
    cases y <;> (try simp [smartOr])
    · case emptyset =>
      simp [denote]
      exact (Language.simp_or_emptyset_r_is_l _)
  | concat x1 x2 =>
    cases y <;> (try simp [smartOr])
    · case emptyset =>
      simp [denote]
      exact (Language.simp_or_emptyset_r_is_l _)
  | star x =>
    cases y <;> (try simp [smartOr])
    · case emptyset =>
      simp [denote]
      exact (Language.simp_or_emptyset_r_is_l _)

theorem smartConcat_is_correct (x y: Regex α):
  denote (Regex.concat x y) = denote (smartConcat x y) := by
  sorry

theorem smartStar_is_correct (x: Regex α):
  denote (Regex.star x) = denote (smartStar x) := by
  sorry
