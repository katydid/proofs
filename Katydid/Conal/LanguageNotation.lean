import Katydid.Conal.Language

-- `(priority := high)` is required to avoid the error: "ambiguous, possible interpretations"
notation (priority := high) "∅" => dLang.emptySet -- backslash emptyset

notation "𝒰" => dLang.universal -- backslash McU

notation "ε" => dLang.emptyStr -- backslash epsilon

-- TODO: fix scalar to work in Calculus.lean
infixl:4 " · " => dLang.scalar -- backslash .

infixl:5 (priority := high) " ⋃ " => dLang.or -- backslash U

infixl:4 " ⋂ " => dLang.and -- backslash I

infixr:5 " , " => dLang.concat

postfix:6 "*" => dLang.star

-- Tests for notation

open dLang
example: dLang α := 𝒰
example: dLang α := ε
example: dLang α := (ε ⋃ 𝒰)
example: dLang α := (ε ⋂ 𝒰)
example: dLang α := ∅
example: dLang α := (∅*)
example: dLang Char := char 'a'
example: dLang Char := char 'b'
example: dLang Char := (char 'a' ⋂ ∅)
example: dLang Char := (char 'a' ⋂ char 'b')
example: dLang Nat := (char 1 ⋂ char 2)
example: (_t: Type) -> dLang Nat := (PUnit · char 2)
example: dLang Nat := (char 1, char 2)
