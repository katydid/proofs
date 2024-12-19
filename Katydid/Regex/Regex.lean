import Lean
open List

inductive Regex (α: Type): Type where
  | emptyset : Regex α
  | emptystr : Regex α
  | pred : (p: α -> Prop) → [DecidablePred p] → Regex α
  | or : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α

def Regex.mkChar (c: Char): Regex Char :=
  Regex.pred (· = c)

def Regex.mkList (chars: List Char): Regex Char :=
  match chars with
  | [] => Regex.emptystr
  | [c] => Regex.mkChar c
  | [a,b] => Regex.concat (Regex.mkChar a) (Regex.mkChar b)
  | _ => foldl (λ r c => Regex.concat r (Regex.mkChar c)) Regex.emptystr chars

def Regex.mkString (s: String): Regex Char :=
  Regex.mkList (s.toList)

namespace Regex

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
  | `(regex| $c:char) => Lean.Meta.mkAppM ``Regex.mkString #[Lean.mkStrLit c.getChar.toString]
  | `(regex| $i:ident) => Lean.Meta.mkAppM ``Regex.mkString #[Lean.mkStrLit i.getId.toString]
  | `(regex| $s:str) => Lean.Meta.mkAppM ``Regex.mkString #[Lean.mkStrLit s.getString]
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
