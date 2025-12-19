import Lake
open Lake DSL

package «proofs» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

require lean4export from git
  "https://github.com/Kha/lean4export.git"

@[default_target]
lean_lib «Proofs» {
  -- add any library configuration options here
}

@[default_target]
lean_lib «SquarePyramid» {
  -- add any library configuration options here
}

@[default_target]
lean_lib BusyLean {
  -- add any library configuration options here
}

@[default_target]
lean_lib BBfLean {
  -- add any library configuration options here
}
