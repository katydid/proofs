import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.CongrM

import Katydid.Regex.Language
import Katydid.Regex.Regex

namespace Denote

def denote {α: Type} (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.pred p => Language.pred p
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

private theorem decide_prop (P: Prop) [dP: Decidable P]:
  (P <-> True) \/ (P <-> False) := by
    match dP with
    | isTrue hp =>
      left
      simp only [iff_true]
      exact hp
    | isFalse hp =>
      right
      simp only [iff_false]
      exact hp

def denote_onlyif {α: Type} (condition: Prop) [dcond: Decidable condition] (r: Regex α):
  denote (Regex.onlyif condition r) = Language.onlyif condition (denote r) := by
  unfold Language.onlyif
  unfold Regex.onlyif
  funext xs
  have hc : (condition <-> True) \/ (condition <-> False) :=
    decide_prop condition
  cases hc with
  | inl ctrue =>
    split_ifs
    case pos hc' =>
      rw [ctrue]
      simp
    case neg hc' =>
      rw [ctrue] at hc'
      contradiction
  | inr cfalse =>
    split_ifs
    case neg hc' =>
      rw [cfalse]
      simp [denote]
    case pos hc' =>
      rw [cfalse] at hc'
      contradiction

theorem null_commutes {α: Type} (r: Regex α):
  ((Regex.null r) = true) = Language.null (denote r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold Regex.null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold Regex.null
    simp only
  | pred p =>
    unfold denote
    rw [Language.null_pred]
    unfold Regex.null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold Regex.null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold Regex.null
    simp only

theorem derive_commutes {α: Type} (r: Regex α) (x: α):
  denote (Regex.derive r x) = Language.derive (denote r) x := by
  induction r with
  | emptyset =>
    simp only [denote]
    rw [Language.derive_emptyset]
  | emptystr =>
    simp only [denote]
    rw [Language.derive_emptystr]
  | pred p =>
    simp only [denote]
    rw [Language.derive_pred]
    unfold Regex.derive
    rw [denote_onlyif]
    simp only [denote]
  | or p q ihp ihq =>
    simp only [denote]
    rw [Language.derive_or]
    unfold Language.or
    rw [ihp]
    rw [ihq]
  | concat p q ihp ihq =>
    simp only [denote]
    rw [Language.derive_concat]
    rw [<- ihp]
    rw [<- ihq]
    rw [denote_onlyif]
    congrm (Language.or (Language.concat (denote (Regex.derive p x)) (denote q)) ?_)
    rw [null_commutes]
  | star r ih =>
    simp only [denote]
    rw [Language.derive_star]
    guard_target =
      Language.concat (denote (Regex.derive r x)) (Language.star (denote r))
      = Language.concat (Language.derive (denote r) x) (Language.star (denote r))
    congrm ((Language.concat ?_ (Language.star (denote r))))
    guard_target = denote (r.derive x) = Language.derive (denote r) x
    exact ih
