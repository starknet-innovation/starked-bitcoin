import Lake
open Lake DSL

package StarkedAir where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.33.1"

@[default_target]
lean_lib StarkedAir

-- Export with `lake env lean --run Export.lean <name>` (interpreted; avoids
-- natively linking all of Mathlib).
