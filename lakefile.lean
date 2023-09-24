import Lake
open Lake DSL

require std from git "https://github.com/leanprover/std4" @ "main"

package «darray» {
  -- add package configuration options here
}

@[default_target]
lean_lib «DArray» {
  roots := #[`DArray]
  precompileModules := true
  -- add library configuration options here
}

lean_exe «Test» {
 root := `Test
}