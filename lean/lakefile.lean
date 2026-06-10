import Lake
open Lake DSL

package "Erdos539" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]

require "leanprover-community" / "mathlib" @ git "v4.29.1"

@[default_target]
lean_lib «Erdos539» where
  -- add any library configuration options here
