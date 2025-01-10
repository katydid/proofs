import Lean

import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.CongrM

import Katydid.Std.Decidable

import Katydid.Regex.Language

open List

namespace SimpleRegex

inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α

def mkChar (c: Char): Regex Char :=
  Regex.pred (· = c)

def mkList (chars: List Char): Regex Char :=
  match chars with
  | [] => Regex.emptystr
  | [c] => mkChar c
  | [a,b] => Regex.concat (mkChar a) (mkChar b)
  | _ => foldl (λ r c => Regex.concat r (mkChar c)) Regex.emptystr chars

def mkString (s: String): Regex Char :=
  mkList (s.toList)

declare_syntax_cat regex
syntax "∅" : regex -- \ emptyset
syntax "ε" : regex -- \ eps
syntax char : regex -- char
syntax ident : regex -- string
syntax str : regex -- string
syntax regex " | " regex : regex -- or
syntax regex regex : regex -- concat
syntax regex "*" : regex -- star
syntax "(" regex ")" : regex -- parenthesis

partial def elabRegex : Lean.Syntax → Lean.Meta.MetaM Lean.Expr
  | `(regex| ∅) => Lean.Meta.mkAppM ``Regex.emptyset #[]
  | `(regex| ε) => Lean.Meta.mkAppM ``Regex.emptystr #[]
  | `(regex| $c:char) => Lean.Meta.mkAppM ``mkString #[Lean.mkStrLit c.getChar.toString]
  | `(regex| $i:ident) => Lean.Meta.mkAppM ``mkString #[Lean.mkStrLit i.getId.toString]
  | `(regex| $s:str) => Lean.Meta.mkAppM ``mkString #[Lean.mkStrLit s.getString]
  | `(regex| $x | $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Regex.or #[x, y]
  | `(regex| $x $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Regex.concat #[x, y]
  | `(regex| $x*) => do
    let x ← elabRegex x
    Lean.Meta.mkAppM ``Regex.star #[x]
  | `(regex| ($x)) => elabRegex x
  | _ => Lean.Elab.throwUnsupportedSyntax

elab " ~ " e:regex " ~ " : term => elabRegex e

example: Regex Char := ~ 'a' ~
example: Regex Char := ~ a ~
example: Regex Char := ~ abc ~
example: Regex Char := ~ 'a''b''c' ~
example: Regex Char := ~ "" ~
example: Regex Char := ~ a ~
example: Regex Char := ~ "a" ~
example: Regex Char := ~ ab ~
example: Regex Char := ~ "ab" ~
example: Regex Char := ~ abc ~
example: Regex Char := ~ "abc" ~
example: Regex Char := ~ abc ~
example: Regex Char := ~ "abc" ~
example: Regex Char := ~ 'a' ~
example: Regex Char := ~ a ~
example: Regex Char := ~ 'a' | 'b' ~
example: Regex Char := ~ ab ~
example: Regex Char := ~ a b ~
example: Regex Char := ~ a b c ~
example: Regex Char := ~ a* ~
example: Regex Char := ~ (a)* ~
example: Regex Char := ~ "a"* ~
example: Regex Char := ~ ("a")* ~
example: Regex Char := ~ (a)(b) ~
example: Regex Char := ~ (a | b)* ~

def null (r: Regex α): Bool :=
  match r with
  | Regex.emptyset => false
  | Regex.emptystr => true
  | Regex.pred _ => false
  | Regex.or x y => null x || null y
  | Regex.concat x y => null x && null y
  | Regex.star _ => true

def onlyif (cond: Prop) [dcond: Decidable cond] (r: Regex α): Regex α :=
  if cond then r else Regex.emptyset

def derive (r: Regex α) (a: α): Regex α :=
  match r with
  | Regex.emptyset => Regex.emptyset
  | Regex.emptystr => Regex.emptyset
  | Regex.pred p => onlyif (p a) Regex.emptystr
  | Regex.or x y => Regex.or (derive x a) (derive y a)
  | Regex.concat x y =>
      Regex.or
        (Regex.concat (derive x a) y)
        (onlyif (null x) (derive y a))
  | Regex.star x =>
      Regex.concat (derive x a) (Regex.star x)

def denote {α: Type} (r: Regex α): Language.Lang α :=
  match r with
  | Regex.emptyset => Language.emptyset
  | Regex.emptystr => Language.emptystr
  | Regex.pred p => Language.pred p
  | Regex.or x y => Language.or (denote x) (denote y)
  | Regex.concat x y => Language.concat (denote x) (denote y)
  | Regex.star x => Language.star (denote x)

def denote_onlyif {α: Type} (condition: Prop) [dcond: Decidable condition] (r: Regex α):
  denote (onlyif condition r) = Language.onlyif condition (denote r) := by
  unfold Language.onlyif
  unfold onlyif
  funext xs
  have hc : (condition <-> True) \/ (condition <-> False) :=
    Decidable.true_or_false condition
  cases hc with
  | inl ctrue =>
    split_ifs
    case pos hc' =>
      rw [ctrue]
      simp only [true_and]
    case neg hc' =>
      rw [ctrue] at hc'
      contradiction
  | inr cfalse =>
    split_ifs
    case neg hc' =>
      rw [cfalse]
      simp only [denote, Language.emptyset, false_and]
    case pos hc' =>
      rw [cfalse] at hc'
      contradiction

theorem null_commutes {α: Type} (r: Regex α):
  ((null r) = true) = Language.null (denote r) := by
  induction r with
  | emptyset =>
    unfold denote
    rw [Language.null_emptyset]
    unfold null
    apply Bool.false_eq_true
  | emptystr =>
    unfold denote
    rw [Language.null_emptystr]
    unfold null
    simp only
  | pred p =>
    unfold denote
    rw [Language.null_pred]
    unfold null
    apply Bool.false_eq_true
  | or p q ihp ihq =>
    unfold denote
    rw [Language.null_or]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.or_eq_true]
  | concat p q ihp ihq =>
    unfold denote
    rw [Language.null_concat]
    unfold null
    rw [<- ihp]
    rw [<- ihq]
    rw [Bool.and_eq_true]
  | star r ih =>
    unfold denote
    rw [Language.null_star]
    unfold null
    simp only

theorem derive_commutes {α: Type} (r: Regex α) (x: α):
  denote (derive r x) = Language.derive (denote r) x := by
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
    unfold derive
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
    congrm (Language.or (Language.concat (denote (derive p x)) (denote q)) ?_)
    rw [null_commutes]
  | star r ih =>
    simp only [denote]
    rw [Language.derive_star]
    guard_target =
      Language.concat (denote (derive r x)) (Language.star (denote r))
      = Language.concat (Language.derive (denote r) x) (Language.star (denote r))
    congrm ((Language.concat ?_ (Language.star (denote r))))
    guard_target = denote (derive r x) = Language.derive (denote r) x
    exact ih

def derives (r: Regex α) (xs: List α): Regex α :=
  (List.foldl derive r) xs

theorem derives_commutes {α: Type} (r: Regex α) (xs: List α):
  denote (derives r xs) = Language.derives (denote r) xs := by
  unfold derives
  rw [Language.derives_foldl]
  revert r
  induction xs with
  | nil =>
    simp only [foldl_nil]
    intro h
    exact True.intro
  | cons x xs ih =>
    simp only [foldl_cons]
    intro r
    have h := derive_commutes r x
    have ih' := ih (derive r x)
    rw [h] at ih'
    exact ih'

def validate (r: Regex α) (xs: List α): Bool :=
  null (derives r xs)

theorem validate_commutes {α: Type} (r: Regex α) (xs: List α):
  (validate r xs = true) = (denote r) xs := by
  rw [<- Language.validate (denote r) xs]
  unfold validate
  rw [<- derives_commutes]
  rw [<- null_commutes]

-- decidableDenote shows that the derivative algorithm is decidable
def decidableDenote (r: Regex α): DecidablePred (denote r) := by
  unfold DecidablePred
  intro xs
  rw [<- validate_commutes]
  cases (validate r xs)
  · simp only [Bool.false_eq_true]
    apply Decidable.isFalse
    simp only [not_false_eq_true]
  · simp only
    apply Decidable.isTrue
    exact True.intro

#print axioms decidableDenote
