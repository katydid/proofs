-- RegexNotation is used to create `Lang Char` languages, which we know as regular expressions, using a more convenient notation: (regex| (a|b)* )

import Katydid.Conal.Language

open List

def Regex := Lang Char

@[inline, simp] abbrev universal: Regex :=
  @Lang.universal Char

@[inline, simp] abbrev emptySet: Regex :=
  @Lang.emptySet Char

@[inline, simp] abbrev emptyStr: Regex :=
  @Lang.emptyStr Char

@[inline, simp] abbrev Regex.fromList (chars: List Char): Regex :=
  match chars with
  | [] => emptyStr
  | [c] => Lang.char c
  | c::cs => Lang.concat (Lang.char c) (Regex.fromList cs)

@[inline, simp] abbrev Regex.char (s: String): Regex :=
  match s.toList with
  | [c] => Lang.char c
  | cs => Regex.fromList cs

@[inline, simp] abbrev Regex.ofNat (c: Nat): Regex :=
  Lang.char (Char.ofNat c)

@[inline, simp] abbrev Regex.fromString (s: String): Regex :=
  Regex.fromList (s.toList)

declare_syntax_cat regex
syntax "μ" : regex -- universal: backslash mu
syntax "∅" : regex -- emptySet: backslash emptyset
syntax "ε" : regex -- emptyStr: backslash eps
syntax char : regex -- char
syntax str : regex -- string
syntax ident : regex -- string
syntax regex " ⋃ " regex : regex -- or: backslash U
syntax regex " | " regex : regex -- or
syntax regex " ⋂ " regex : regex -- and: backslash I
syntax regex regex : regex -- concat
syntax regex "*" : regex -- star
syntax "(" regex ")" : regex -- parenthesis

partial def elabChars (s: List Char): Lean.Meta.MetaM Lean.Expr :=
  match s with
  | [] => Lean.Meta.mkAppM ``emptyStr #[]
  | [c] => do
    let c' <- Lean.Meta.mkAppM ``Char.ofNat #[Lean.mkNatLit c.toNat]
    Lean.Meta.mkAppM ``Lang.char #[c']
  | c::cs => do
    let c'' <- Lean.Meta.mkAppM ``Char.ofNat #[Lean.mkNatLit c.toNat]
    let c' <- Lean.Meta.mkAppM ``Lang.char #[c'']
    let cs' <- elabChars cs
    Lean.Meta.mkAppM ``Lang.concat #[c', cs']

partial def elabRegex : Lean.Syntax → Lean.Meta.MetaM Lean.Expr
  | `(regex| μ) => Lean.Meta.mkAppM ``universal #[]
  | `(regex| ∅) => Lean.Meta.mkAppM ``emptySet #[]
  | `(regex| ε) => Lean.Meta.mkAppM ``emptyStr #[]
  | `(regex| $c:char) => elabChars [c.getChar]
  | `(regex| $s:str) => elabChars s.getString.toList
  | `(regex| $i:ident) => elabChars i.getId.toString.toList
  | `(regex| $x ⋃ $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Lang.or #[x, y]
  | `(regex| $x | $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Lang.or #[x, y]
  | `(regex| $x ⋂ $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Lang.and #[x, y]
  | `(regex| $x $y) => do
    let x ← elabRegex x
    let y ← elabRegex y
    Lean.Meta.mkAppM ``Lang.concat #[x, y]
  | `(regex| $x*) => do
    let x ← elabRegex x
    Lean.Meta.mkAppM ``Lang.star #[x]
  | `(regex| ($x)) => elabRegex x
  | _ => Lean.Elab.throwUnsupportedSyntax

elab " (regex| " r:regex " ) " : term => elabRegex r

@[inline, simp] abbrev Regex.match (l: Regex) (s: String): Type :=
  l (s.toList)

declare_syntax_cat matchregex
syntax regex " ≈ " ident : matchregex -- backslash approx
syntax regex " ≈ " str : matchregex -- backslash approx

partial def elabMatchRegex : Lean.Syntax → Lean.Meta.MetaM Lean.Expr
  | `(matchregex| $r:regex ≈ $i:ident) => do
    let l ← elabRegex r
    Lean.Meta.mkAppM ``Regex.match #[l, Lean.mkStrLit i.getId.toString]
  | `(matchregex| $r:regex ≈ $s:str) => do
    let l ← elabRegex r
    Lean.Meta.mkAppM ``Regex.match #[l, Lean.mkStrLit s.getString]
  | _ => Lean.Elab.throwUnsupportedSyntax

elab " (regex| " e:matchregex " ) " : term => (elabMatchRegex e)

example : (regex| ∅ ) [] -> Empty := by
  intro H
  cases H

example : (regex| ε ) [] := by
  simp
  rfl

example : (regex| ε ≈ "") := by
  simp
  rfl

example : (regex| a) ['a'] := by
  simp
  rfl

example : (regex| a ≈ a) := by
  simp
  rfl

example : (regex| "a" ≈ "a") := by
  simp
  rfl

example : (regex| 'a' ≈ "a") := by
  simp
  rfl
