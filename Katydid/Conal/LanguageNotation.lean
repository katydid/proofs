import Katydid.Conal.Language

-- `(priority := high)` is required to avoid the error: "ambiguous, possible interpretations"
notation (priority := high) "∅" => Lang.emptySet -- backslash emptyset

notation "μ" => Lang.universal -- backslash mu

notation "ε" => Lang.emptyStr -- backslash epsilon

notation:6 (priority := high) "{" c "}" => Lang.char c

-- TODO: fix scalar to work in Calculus.lean
infixl:4 " · " => Lang.scalar -- backslash .

infixl:5 (priority := high) " ⋃ " => Lang.or -- backslash U

infixl:4 " ⋂ " => Lang.and -- backslash I

infixr:5 " , " => Lang.concat

postfix:6 "*" => Lang.star

-- Tests for notation

-- #check μ
-- #check ε
-- #check (ε ⋃ μ)
-- #check (ε ⋂ μ)
-- #check ∅
-- #check (∅*)
-- #check {'a'}
-- #check {'b'}
-- #check ({'a'} ⋂ ∅)
-- #check ({'a'} ⋂ {'b'})
-- #check ({1} ⋂ {2})
-- #check (PUnit · {2})
-- #check ({1}, {2})
