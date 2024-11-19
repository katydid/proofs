-- Haskell
--   data RegexF r = EmptySet
--     | EmptyString
--     | Character Char
--     | Concat r r
--     | ZeroOrMore r
--     | Or r r
--     deriving Functor
-- Ocaml
--  type 'r expr_node =
--    | Const of int
--    | Var of Id.t
--    | Add of 'r * 'r
--    | ...
-- Lean
inductive RegexF (r: Type u) where
  | emptyset: RegexF r
  | emptystr: RegexF r
  | char: Char -> RegexF r
  | concat: r -> r -> RegexF r
  | star: r -> RegexF r
  | or: r -> r -> RegexF r

def RegexF.map {α β : Type u} (f: α → β) (r: RegexF α): RegexF β :=
  match r with
  | emptyset => emptyset
  | emptystr => emptystr
  | char c => char c
  | concat p q => concat (f p) (f q)
  | star p => star (f p)
  | or p q => or (f p) (f q)

instance : Functor RegexF where
  map := RegexF.map

-- Haskell
--   type Regex = Fix RegexF
-- Ocaml
--   type expr = { unfix : expr expr_node }
-- Lean
inductive Regex where
  | unfix: RegexF Regex -> Regex

-- Haskell
--   newtype Fix f = Fix (f (Fix f))
-- Ocaml
--   let fix : expr expr_node -> expr = fun e -> { unfix = e }
-- Lean
def fix: RegexF Regex -> Regex :=
  fun (e) => Regex.unfix e

-- Haskell
--   wreckit :: Fix f -> f (Fix f)
--   wreckit (Fix x) = x
--   wreckit :: Regex -> RegexF Regex
-- Ocaml
--   let unfix r = r.unfix
-- Lean
def unfix: Regex -> RegexF Regex :=
  fun r =>
    match r with
    | Regex.unfix rf => rf

def RegexF.sizeof [SizeOf a] (r: RegexF a): Nat :=
  match r with
  | RegexF.emptyset => 0
  | RegexF.emptystr => 1
  | RegexF.char _ => 2
  | RegexF.concat p q =>  1 + sizeOf p + sizeOf q
  | RegexF.star p => 1 + sizeOf p
  | RegexF.or p q => 1 + sizeOf p + sizeOf q

instance [SizeOf r]: SizeOf (RegexF r) where
  sizeOf := RegexF.sizeof

def Regex.sizeof (r: Regex): Nat :=
  match r with
  | Regex.unfix rf =>
    match rf with
    | RegexF.emptyset => 0
    | RegexF.emptystr => 1
    | RegexF.char _ => 2
    | RegexF.concat p q =>  1 + sizeof p + sizeof q
    | RegexF.star p => 1 + sizeof p
    | RegexF.or p q => 1 + sizeof p + sizeof q

instance : SizeOf Regex where
  sizeOf := Regex.sizeof

def emptyset: Regex :=
  fix RegexF.emptyset

def emptystr: Regex :=
  fix RegexF.emptystr

def char (c: Char): Regex :=
  fix (RegexF.char c)

def concat (p q: Regex): Regex :=
  fix (RegexF.concat p q)

def star (p: Regex): Regex :=
  fix (RegexF.star p)

def or' (p q: Regex): Regex :=
  fix (RegexF.or p q)

def nullableAlg (r: RegexF Bool): Bool :=
  match r with
  | RegexF.emptyset => false
  | RegexF.emptystr => true
  | RegexF.char _ => false
  | RegexF.concat p q => p && q
  | RegexF.star _ => true
  | RegexF.or p q => p || q

-- type FAlgebra f r = f r -> r
-- type NullableFAlgebra = FAlgebra RegexF Bool
-- cata :: NullableFAlgebra -> Regex -> Bool
-- cata nullableAlg regex =
--   wreckit regex
--   |> fmap (cata nullableAlg)
--   |> nullableAlg
def cata (f: RegexF Bool -> Bool) (regex: Regex): Bool :=
  let uregex := unfix regex
  let cf := fun (rr: Regex) => cata f rr
  f (Functor.map cf uregex)
  termination_by regex
  decreasing_by sorry
















-- nullable :: Regex -> Bool
-- nullable = cata nullableAlg
def nullable (r: Regex): Bool :=
  cata nullableAlg r

-- def cata [Functor f] : FAlgebra f r -> Fix f -> r
-- cata alg = alg . fmap (cata alg) . wreckit
