import Lake
open Lake DSL

package katydid

@[default_target]
lean_lib Katydid

require std from git "https://github.com/leanprover/std4" @ "main"
