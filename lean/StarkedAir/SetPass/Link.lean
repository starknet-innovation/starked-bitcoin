/-
**The segment system's lookups (set-pass step 3, soundness).** The nine components as a `System`, which
lookups are uses (multiplicity `−1` or `0` at every row) and which yield, and `link`: in a satisfied,
balanced system below the size bound, a use with multiplicity `−1` is matched by a yield with nonzero
multiplicity, the same relation and the same tuple (`used_in_table_ext`). Then the reads every component
relies on: byte reads are the segment's bytes (`byte_read`), range reads are bytes (`r8_read`), pending
reads are the public pending bytes (`pend_read`).

The use multiplicities need the public `HASLAST` to be `0` or `1` (`set_rec`'s key comparison is gated by
it on row 0).
-/
import StarkedAir.SetPass.System
import StarkedAir.Block.Link

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst)

/-- The segment system, in proof order. -/
def segSys : System := ⟨9, fun i => comps.getD i Block.bytes⟩

/-- Use sites `(component, lookup)`; all others yield. -/
def isUse : ℕ → ℕ → Bool
  | 3, k => decide (k < 57) || k == 63 || decide (64 ≤ k)
  | 4, k => decide (k < 3)
  | 5, k => k != 12
  | 6, k => k == 0
  | 7, k => k != 6
  | 8, k => k == 0
  | _, _ => false

def relAt (i k : ℕ) : ℕ := ((segSys.comp i).lookups.getD k ⟨0, .const 0, []⟩).rel

/-- The yield sites and their relations. -/
def yieldTable : List (ℕ × ℕ × ℕ) :=
  [(0, 0, 3), (1, 0, 9), (1, 1, 10), (2, 0, 26), (2, 1, 27), (2, 2, 28), (2, 3, 29), (3, 57, 32), (3, 58, 33),
   (3, 59, 33), (3, 60, 33), (3, 61, 33), (3, 62, 21), (4, 3, 22), (5, 12, 30), (6, 1, 31), (7, 6, 34), (8, 1, 35)]

theorem lookups_len : ∀ i < 9, (segSys.comp i).lookups.length = [1, 2, 4, 89, 4, 14, 2, 8, 2].getD i 0 := by
  decide

def yieldOK : Bool :=
  (List.range 9).all fun i => (List.range (segSys.comp i).lookups.length).all fun k =>
    isUse i k || yieldTable.contains (i, k, relAt i k)

set_option maxRecDepth 20000 in
theorem yieldOK_true : yieldOK = true := by decide

theorem yield_table : ∀ i < 9, ∀ k < (segSys.comp i).lookups.length, isUse i k = false →
    (i, k, relAt i k) ∈ yieldTable := by
  intro i hi k hk hu
  have h := yieldOK_true
  simp only [yieldOK, List.all_eq_true, List.mem_range] at h
  have := h i hi k hk
  simp only [hu, Bool.false_or, List.contains_iff_mem] at this
  exact this

/-- Lookup sites over all rows: `Σᵢ kᵢ · 2^(Ls i)` (bytes 1, tables 2, pending 4, records 89,
fingerprints 4, Blake2s words 14, Blake2s 2, `TxOutSer` 8, SHA-256 2). -/
def segRows (Ls : ℕ → ℕ) : ℕ :=
  2 ^ Ls 0 + 2 * 2 ^ Ls 1 + 4 * 2 ^ Ls 2 + 89 * 2 ^ Ls 3 + 4 * 2 ^ Ls 4 + 14 * 2 ^ Ls 5 + 2 * 2 ^ Ls 6 +
    8 * 2 ^ Ls 7 + 2 * 2 ^ Ls 8

/-- **The size condition**: every component has at most `2^24` rows and the site count is below `P`. -/
def SegSizeOk (Ls : ℕ → ℕ) : Prop := (∀ i < 9, Ls i ≤ 24) ∧ segRows Ls < P

/-- `set_rec`'s use multiplicities. -/
def recUseMults : List Expr := [.neg (Rec.k Rec.ON), .neg Rec.one, .neg Rec.cmp]

set_option maxRecDepth 20000 in
theorem rec_mult_cases : ∀ k < 89, isUse 3 k = true → (Rec.lookups.getD k ⟨0, .const 0, []⟩).mult ∈ recUseMults := by
  decide

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 9, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
include hL hsat

theorem bytes_sat : Block.bytes.air.Satisfied (Ls 0) pub (inst 0).main := by
  have := hsat.1 0 (by decide); rw [hL 0 (by decide)] at this; exact this

theorem tables_sat : Block.Tables.tables.air.Satisfied (Ls 1) pub (inst 1).main := by
  have := hsat.1 1 (by decide); rw [hL 1 (by decide)] at this; exact this

theorem pend_sat : Pend.pend.air.Satisfied (Ls 2) pub (inst 2).main := by
  have := hsat.1 2 (by decide); rw [hL 2 (by decide)] at this; exact this

theorem rec_sat : ∀ r < 2 ^ Ls 3, ∀ c ∈ Rec.constraints, c.eval (2 ^ Ls 3) Rec.preCols pub (inst 3).main r = 0 := by
  have := hsat.1 3 (by decide); rw [hL 3 (by decide)] at this; exact this

theorem fpwalk_sat :
    ∀ r < 2 ^ Ls 4, ∀ c ∈ Block.FpWalk.constraints, c.eval (2 ^ Ls 4) Block.FpWalk.preCols pub (inst 4).main r = 0 := by
  have := hsat.1 4 (by decide); rw [hL 4 (by decide)] at this; exact this

theorem b2w_sat : ∀ r < 2 ^ Ls 5, ∀ c ∈ B2w.constraints, c.eval (2 ^ Ls 5) B2w.preCols pub (inst 5).main r = 0 := by
  have := hsat.1 5 (by decide); rw [hL 5 (by decide)] at this; exact this

theorem b2c_sat : ∀ r < 2 ^ Ls 6, ∀ c ∈ B2c.constraints, c.eval (2 ^ Ls 6) B2c.preCols pub (inst 6).main r = 0 := by
  have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this

theorem tmsg_sat : ∀ r < 2 ^ Ls 7, ∀ c ∈ TMsg.constraints, c.eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main r = 0 := by
  have := hsat.1 7 (by decide); rw [hL 7 (by decide)] at this; exact this

theorem shac_sat : ∀ r < 2 ^ Ls 8, ∀ c ∈ ShaC.constraints, c.eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main r = 0 := by
  have := hsat.1 8 (by decide); rw [hL 8 (by decide)] at this; exact this

omit hsat in
theorem mem_sites {i r k : ℕ} : ((i, r, k) : Site) ∈ sites segSys inst ↔
    i < 9 ∧ r < 2 ^ Ls i ∧ k < (segSys.comp i).lookups.length := by
  simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
    exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
  · rintro ⟨hi, hr', hk'⟩
    exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩

omit hsat in
theorem sites_len : (sites segSys inst).length = segRows Ls := by
  have hl : ∀ i < 9, (segSys.comp i).lookups.length = [1, 2, 4, 89, 4, 14, 2, 8, 2].getD i 0 := lookups_len
  have hm : segSys.m = 9 := rfl
  simp only [sites, List.length_flatMap, List.length_map, List.length_range, hm]
  simp only [List.sum_range_succ, List.range_zero, List.map_nil, List.sum_nil, zero_add]
  simp only [List.map_const', List.sum_replicate, smul_eq_mul]
  rw [hl 0 (by decide), hl 1 (by decide), hl 2 (by decide), hl 3 (by decide), hl 4 (by decide), hl 5 (by decide),
    hl 6 (by decide), hl 7 (by decide), hl 8 (by decide), hL 0 (by decide), hL 1 (by decide), hL 2 (by decide),
    hL 3 (by decide), hL 4 (by decide), hL 5 (by decide), hL 6 (by decide), hL 7 (by decide), hL 8 (by decide)]
  simp only [segRows, List.getD_cons_zero, List.getD_cons_succ, List.length_range]
  ring

end System

end StarkedAir.SetPass
