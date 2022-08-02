import Lake
open Lake DSL

package «lean-gym» {
  -- add package configuration options here
}

lean_lib LeanGym {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe «lean-gym» {
  root := `Main
}
