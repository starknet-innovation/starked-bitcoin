/-
**(W) for the block system's components.** `hashSysW` names the condition for each component of
`hashSys`, at own size `L` inside a `2^N` proof (`Circuit.Lift.LiftOK`).

- **Proven for eight components** (`w_bytes` … `w_undo`): bytes, fields, merkle, tables, walk, ctx,
  wmerkle and undo. Each reads every main column at no more than two distinct offsets (`offsOk`,
  checked by the kernel).
- **Assumed for seven** (`hardW`): msg, sha, b2msg, b2s, fpwalk, urec and coin. Each has a column read
  at three or more offsets, where lifting can fail in general. For these, (W) is evidence from
  stwo-zig's `lifting_wrapcheck.py`: all 115 checked (component, size) runs pass. A Lean proof is a
  later step.

`hashSysW_of_hard` reduces (W) for the whole system to the seven assumed components.
-/
import StarkedAir.Block.Link
import StarkedAir.Circuit.Lift

namespace StarkedAir.Block

open StarkedAir StarkedAir.Circuit.Lift

/-- **(W) for component `i` of `hashSys`**, at own size `L` inside a `2^N` proof. -/
def hashSysW (i N L : ℕ) : Prop := LiftOK (hashSys.comp i) N L

section
variable {N L : ℕ}

theorem w_bytes (hLN : L ≤ N) : hashSysW 0 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_fields (hLN : L ≤ N) : hashSysW 1 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_merkle (hLN : L ≤ N) : hashSysW 4 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_tables (hLN : L ≤ N) : hashSysW 5 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_walk (hLN : L ≤ N) : hashSysW 6 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_ctx (hLN : L ≤ N) : hashSysW 7 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_wmerkle (hLN : L ≤ N) : hashSysW 8 N L := liftOK_of_offsOk hLN (by decide +kernel)
theorem w_undo (hLN : L ≤ N) : hashSysW 9 N L := liftOK_of_offsOk hLN (by decide +kernel)

end

/-- The components whose (W) is assumed: msg, sha, b2msg, b2s, fpwalk, urec, coin. -/
def hardW : List ℕ := [2, 3, 10, 11, 12, 13, 14]

/-- **(W) for the whole block system from the seven assumed components.** -/
theorem hashSysW_of_hard {N : ℕ} {Ls : ℕ → ℕ} (hLs : ∀ i < hashSys.m, Ls i ≤ N)
    (hard : ∀ i ∈ hardW, hashSysW i N (Ls i)) : ∀ i < hashSys.m, LiftOK (hashSys.comp i) N (Ls i) := by
  intro i hi
  have hm : hashSys.m = 15 := rfl
  have hL := hLs i hi
  rw [hm] at hi
  interval_cases i
  · exact w_bytes hL
  · exact w_fields hL
  · exact hard 2 (by decide)
  · exact hard 3 (by decide)
  · exact w_merkle hL
  · exact w_tables hL
  · exact w_walk hL
  · exact w_ctx hL
  · exact w_wmerkle hL
  · exact w_undo hL
  · exact hard 10 (by decide)
  · exact hard 11 (by decide)
  · exact hard 12 (by decide)
  · exact hard 13 (by decide)
  · exact hard 14 (by decide)

end StarkedAir.Block
