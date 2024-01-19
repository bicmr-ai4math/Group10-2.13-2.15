import Lake
open Lake DSL

package «tutorial» where
  -- add package configuration options here

lean_lib «Tutorial» where
  -- add library configuration options here

@[default_target]
lean_exe «tutorial» where
  root := `Main

require mathlib from git "https://github.com/leanprover-community/mathlib4"@"master"
