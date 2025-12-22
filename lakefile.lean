import Lake
open Lake DSL

package ToyModel {
  dependencies := #[{
    name := `mathlib,
    src := Source.git "https://github.com/leanprover-community/mathlib4.git" "master"
  }]
}

@[default_target]
lean_lib ToyModel {
  srcDir := "."
}

