import Lake
open Lake DSL

package hello {
  -- add package configuration options here
}

lean_lib Hello {
  -- add library configuration options here
}

@[default_target]
lean_exe hello {
  root := `Main
}