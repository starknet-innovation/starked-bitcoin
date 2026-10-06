import Lake
open Lake DSL

package StarkedAir where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.33.1"

@[default_target]
lean_lib StarkedAir

lean_exe «export-air» where
  root := `Export
