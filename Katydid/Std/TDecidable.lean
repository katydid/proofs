-- TDecidable copies the Prelude from Lean and changes Prop to Type
-- To avoid conflicts everything is prefixed with a 't'.

import Katydid.Std.Tipe

class inductive TDecidable (p : Type) where
  /-- Prove that `p` is decidable by supplying a proof of `¬p` -/
  | tisFalse (h : TNot p) : TDecidable p
  /-- Prove that `p` is decidable by supplying a proof of `p` -/
  | tisTrue (h : p) : TDecidable p

@[inline_if_reduce, nospecialize] def TDecidable.tdecide (p : Type) [h : TDecidable p] : Bool :=
  h.casesOn (fun _ => false) (fun _ => true)

export TDecidable (tisTrue tisFalse tdecide)

/-- A decidable predicate. See `TDecidable`. -/
abbrev TDecidablePred {α : Sort u} (r : α → Type) :=
  (a : α) → TDecidable (r a)

/-- A decidable relation. See `TDecidable`. -/
abbrev TDecidableRel {α : Sort u} (r : α → α → Type) :=
  (a b : α) → TDecidable (r a b)

/--
Asserts that `α` has decidable equality, that is, `a = b` is decidable
for all `a b : α`. See `Decidable`.
-/
abbrev TDecidableEq (α : Type) :=
  (a b : α) → TDecidable (TEq a b)

/-- Proves that `a = b` is decidable given `DecidableEq α`. -/
def tdecEq {α : Type} [inst : TDecidableEq α] (a b : α) : TDecidable (TEq a b) :=
  inst a b

@[macro_inline] def tabsurd {a : Type} {b : Sort v} (h₁ : a) (h₂ : TNot a) : b :=
  (h₂ h₁).rec

set_option linter.unusedVariables false in
theorem tdecide_eq_true : [inst : TDecidable p] → p → TEq (tdecide p) true
  | tisTrue  _, _   => trifle
  | tisFalse h₁, h₂ => tabsurd h₂ h₁

def tdecide_eq_false : [TDecidable p] → TNot p → TEq (tdecide p) false
  | tisTrue  h₁, h₂ => tabsurd h₁ h₂
  | tisFalse _, _   => trifle

theorem tne_true_of_eq_false : {b : Bool} → TEq b false → TNot (TEq b true)
  | true, h  => by contradiction
  | false, _ => fun h => by contradiction

theorem of_tdecide_eq_true [inst : TDecidable p] : TEq (tdecide p) true → p := fun h =>
  match (generalizing := false) inst with
  | tisTrue  h₁ => h₁
  | tisFalse h₁ => tabsurd h (tne_true_of_eq_false (tdecide_eq_false h₁))

theorem tne_false_of_eq_true : {b : Bool} → TEq b true → TNot (TEq b false)
  | true, _  => fun h => by contradiction
  | false, h => by contradiction

theorem of_tdecide_eq_false [inst : TDecidable p] : TEq (tdecide p) false → TNot p := fun h =>
  match (generalizing := false) inst with
  | tisTrue  h₁ => tabsurd h (tne_false_of_eq_true (tdecide_eq_true h₁))
  | tisFalse h₁ => h₁

theorem of_tdecide_eq_self_eq_true [inst : TDecidableEq α] (a : α) : TEq (tdecide (TEq a a)) true :=
  match (generalizing := false) inst a a with
  | tisTrue  _  => trifle
  | tisFalse h₁ => tabsurd trifle h₁

/-- Decidable equality for Bool -/
@[inline] def Bool.tdecEq (a b : Bool) : TDecidable (TEq a b) :=
   match a, b with
   | false, false => tisTrue trifle
   | false, true  => tisFalse (fun h => by contradiction)
   | true, false  => tisFalse (fun h => by contradiction)
   | true, true   => tisTrue trifle

@[inline] instance : TDecidableEq Bool :=
   Bool.tdecEq

open BEq (beq)

instance [TDecidableEq α] : BEq α where
  beq a b := tdecide (TEq a b)

@[macro_inline] def tdite {α : Sort u} (c : Type) [h : TDecidable c] (t : c → α) (e : TNot c → α) : α :=
  h.casesOn e t

@[macro_inline] def tite {α : Sort u} (c : Type) [h : TDecidable c] (t e : α) : α :=
  h.casesOn (fun _ => e) (fun _ => t)

@[macro_inline] instance {p q} [dp : TDecidable p] [dq : TDecidable q] : TDecidable (Prod p q) :=
  match dp with
  | tisTrue  hp =>
    match dq with
    | tisTrue hq  => tisTrue ⟨hp, hq⟩
    | tisFalse hq => tisFalse (fun h => hq (Prod.snd h))
  | tisFalse hp =>
    tisFalse (fun h => hp (Prod.fst h))

@[macro_inline] instance [dp : TDecidable p] [dq : TDecidable q] : TDecidable (Sum p q) :=
  match dp with
  | tisTrue  hp => tisTrue (Sum.inl hp)
  | tisFalse hp =>
    match dq with
    | tisTrue hq  => tisTrue (Sum.inr hq)
    | tisFalse hq =>
      tisFalse fun h => match h with
        | Sum.inl h => hp h
        | Sum.inr h => hq h

instance [dp : TDecidable p] : TDecidable (TNot p) :=
  match dp with
  | tisTrue hp  => tisFalse (tabsurd hp)
  | tisFalse hp => tisTrue hp
