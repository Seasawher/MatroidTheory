import Lake
open Lake DSL

package "MatroidTheory" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require "leanprover-community" / "mathlib"

@[default_target]
lean_lib «MatroidTheory» where
  -- add any library configuration options here
