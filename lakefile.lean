import Lake
open Lake DSL

package «fmclean» {
  -- add package configuration options here
}

lean_lib «Fmclean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fmclean» {
  root := `Main
}
