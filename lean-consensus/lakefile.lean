import Lake
open Lake DSL

package BitcoinConsensus where
  leanOptions := #[⟨`autoImplicit, false⟩, ⟨`relaxedAutoImplicit, false⟩]

require "leanprover-community" / "mathlib" @ git "v4.33.1"

@[default_target]
lean_lib BitcoinConsensus
