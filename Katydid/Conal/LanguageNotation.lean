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
#check 𝒰
#check ε
#check (ε ⋃ 𝒰)
#check (ε ⋂ 𝒰)
#check ∅
#check (∅*)
#check char 'a'
#check char 'b'
#check (char 'a' ⋂ ∅)
#check (char 'a' ⋂ char 'b')
#check (char 1 ⋂ char 2)
#check (PUnit · char 2)
#check (char 1, char 2)
