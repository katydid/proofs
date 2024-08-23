import Lean
open List

namespace Regex

inductive Regex : Type where
  | emptyset : Regex
  | emptystr : Regex
  | char : Char → Regex
  | or : Regex → Regex → Regex
  | concat : Regex → Regex → Regex
  | star : Regex → Regex
  deriving Repr

def regexFromList (chars: List Char): Regex :=
  match chars with
  | [] => Regex.emptystr
  | [c] => Regex.char c
  | [a,b] => Regex.concat (Regex.char a) (Regex.char b)
  | _ => foldl (λ r c => Regex.concat r (Regex.char c)) Regex.emptystr chars

def regexFromString (s: String): Regex :=
  regexFromList (s.toList)

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
  | `(regex| $c:char) => Lean.Meta.mkAppM ``regexFromString #[Lean.mkStrLit c.getChar.toString]
  | `(regex| $i:ident) => Lean.Meta.mkAppM ``regexFromString #[Lean.mkStrLit i.getId.toString]
  | `(regex| $s:str) => Lean.Meta.mkAppM ``regexFromString #[Lean.mkStrLit s.getString]
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

elab " {{ " e:regex " }} " : term => elabRegex e

example: Regex := {{ ∅ }}

example: Regex := {{ 'a' }}

example: Regex := {{ a }}

example: Regex := {{ abc }}

example: Regex := {{ 'a''b''c' }}

example: Regex := {{ "" }}

example: Regex := {{ a }}

example: Regex := {{ "a" }}

example: Regex := {{ ab }}

example: Regex := {{ "ab" }}

example: Regex := {{ abc }}

example: Regex := {{ "abc" }}

example: Regex := {{ abc }}

example: Regex := {{ "abc" }}

example: Regex := {{ ε }}

example: Regex := {{ 'a' }}

example: Regex := {{ a }}

example: Regex := {{ 'a' | 'b' }}

example: Regex := {{ ab }}

example: Regex := {{ a b }}

example: Regex := {{ a b c }}

example: Regex := {{ a* }}

example: Regex := {{ (a)* }}

example: Regex := {{ "a"* }}

example: Regex := {{ ("a")* }}

example: Regex := {{ (a)(b) }}

example: Regex := {{ (a | b)* }}

end Regex
