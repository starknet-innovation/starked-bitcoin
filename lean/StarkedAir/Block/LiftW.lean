/-
**(W) for the block system's components.** `hashSysW` names the condition for each component of
`hashSys`, at own size `L` inside a `2^N` proof (`Circuit.Lift.LiftOK`).

- **Proven for eight components by offset count** (`w_bytes` … `w_undo`): bytes, fields, merkle,
  tables, walk, ctx, wmerkle and undo. Each reads every main column at no more than two distinct
  offsets (`offsOk`, checked by the kernel).
- **Proven for three more by guarded wraps** (`w_b2msg`, `w_fpwalk`, `w_urec`), at every own size
  `L ≥ 5`. Each has one column read at three offsets (`−1, 0, +1`); every wrapped read of it sits under
  a preprocessed guard that vanishes at that boundary row, or (fpwalk) under a factor that another
  constraint forces to zero at that row (`Circuit.Lift.liftOK_of_guard`, checked by the kernel).
- **Assumed for four** (`hardW`): msg, sha, b2s and coin. For these, (W) is evidence from stwo-zig's
  `lifting_wrapcheck.py`: all 115 checked (component, size) runs pass. What the check above misses:
  - coin: the wrapped reads are zero because a sum of boolean columns is forced to zero at the last
    row, so each column is; the guard check does not reason about booleans;
  - msg: two lookup values read a three-offset column at wrapped rows, unguarded (the lookup
    multiplicity vanishes there, but the batch's denominators still see the values);
  - sha, b2s: 96 and 194 three-or-more-offset columns, 250 and 258 wrapped instances.

`hashSysW_of_hard` reduces (W) for the whole system to the four assumed components.
-/
import StarkedAir.Block.Link
import StarkedAir.Circuit.LiftGuard
import StarkedAir.Circuit.LiftOffs

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

/-! Components with a three-offset column whose wrapped reads are guarded (`liftOK_of_guard`), at every
own size `L ≥ 5`. -/

theorem w_b2msg (hL : 5 ≤ L) (hLN : L ≤ N) : hashSysW 10 N L :=
  liftOK_of_guard (K := 1) (cells := []) (rf := []) hL hLN (by decide +kernel)
theorem w_fpwalk (hL : 5 ≤ L) (hLN : L ≤ N) : hashSysW 12 N L :=
  liftOK_of_guard (K := 1) (cells := []) (rf := [(0, 6, true), (-1, 17, true)]) hL hLN (by decide +kernel)
theorem w_urec (hL : 5 ≤ L) (hLN : L ≤ N) : hashSysW 13 N L :=
  liftOK_of_guard (K := 1) (cells := []) (rf := []) hL hLN (by decide +kernel)

end

/-- Every component reads only layout columns, so `mainOffs` matches the layout for every column it
names (`lt_nMain_of_mem_mainOffs`, `mainOffs_length_eq_shape`). -/
theorem hashSys_colsOk : ∀ i < hashSys.m, colsOk (hashSys.comp i) = true := by decide +kernel

/-- The components whose (W) is assumed: msg, sha, b2s, coin. -/
def hardW : List ℕ := [2, 3, 11, 14]

/-- **(W) for the whole block system from the four assumed components.** -/
theorem hashSysW_of_hard {N : ℕ} {Ls : ℕ → ℕ} (hLs : ∀ i < hashSys.m, Ls i ≤ N) (h5 : ∀ i < hashSys.m, 5 ≤ Ls i)
    (hard : ∀ i ∈ hardW, hashSysW i N (Ls i)) : ∀ i < hashSys.m, LiftOK (hashSys.comp i) N (Ls i) := by
  intro i hi
  have hm : hashSys.m = 15 := rfl
  have hL := hLs i hi
  have h5i := h5 i hi
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
  · exact w_b2msg h5i hL
  · exact hard 11 (by decide)
  · exact w_fpwalk h5i hL
  · exact w_urec h5i hL
  · exact hard 14 (by decide)

end StarkedAir.Block
