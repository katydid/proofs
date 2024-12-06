import Lake
open Lake DSL

package katydid

@[default_target]
lean_lib Katydid

-- dependencies std4, quote4 are obtained transitively through mathlib4
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.14.0"
