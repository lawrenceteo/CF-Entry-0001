import Lake
open Lake DSL

package ToyModel {
  -- No extra config needed
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib ToyModel {
  srcDir := "."
}
