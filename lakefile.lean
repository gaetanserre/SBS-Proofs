import Lake
open Lake DSL

package «gO_SVGD_proofs» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «GOSVGDProofs» {
  -- add any library configuration options here
}
