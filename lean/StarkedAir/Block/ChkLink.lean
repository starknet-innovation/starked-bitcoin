/-
**The checks' lookups, linked (M3a.5).** In the block system, the fields component's byte slots and
auxiliary read read the block, and every range slot (fields, walker, context) holds a byte.
-/
import StarkedAir.Block.Link

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **Range uses are bytes.** A use of the range table with multiplicity `−1` looks up a value below 256. -/
theorem r8_lt {i r k : ℕ} (hs : ((i, r, k) : Site) ∈ sites hashSys inst) (hu : isUse i k = true)
    (hrel : siteRel hashSys (i, r, k) = Tables.REL_R8) (hm : siteMult hashSys inst pub (i, r, k) = -1)
    {v : F} (hv : siteVals hashSys inst pub (i, r, k) = [v]) : v.val < 256 := by
  obtain ⟨i', r', k', hr', hy, -, hsv⟩ := link hL hsat hL24 hs hu hm
  rw [hrel, show Tables.REL_R8 = 9 from rfl, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 5 ∧ k' = 0 := by omega
  have e : siteVals hashSys inst pub (5, r', 0) = [((r' % 256 : ℕ) : F)] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 5 (by decide), Tables.tables, Expr.eval, Tables.preCols,
      Tables.tab, PreCol.eval, wrap_zero hr', pre, List.getElem?_range (Nat.mod_lt r' (by norm_num : 0 < 256))]
  rw [e, hv] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  rw [← hsv, ZMod.val_natCast_of_lt (by unfold P; omega)]
  omega

/-- The fields site of check lookup `j` (`chkLookups` index `j`). -/
theorem fields_chk_site {r j : ℕ} (hr : r < 2 ^ L) (hj : j < 26) :
    ((1, r, 8 + j) : Site) ∈ sites hashSys inst ∧
    siteLookup hashSys ((1, r, 8 + j) : Site) = Fields.chkLookups.getD j ⟨0, .const 0, []⟩ := by
  refine ⟨site_mem hL (by decide) hr (by simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups]; omega), ?_⟩
  show (Fields.lookups ++ Fields.chkLookups).getD (8 + j) _ = _
  rw [getD_app_right _ (by rw [show Fields.lookups.length = 8 from rfl]; omega),
    show Fields.lookups.length = 8 from rfl, Nat.add_sub_cancel_left]

/-- **Fields range slots hold bytes.** -/
theorem fields_rg_lt {r j : ℕ} (hr : r < 2 ^ L) (hj : j < 13) : ((inst 1).main (Fields.RG j) r).val < 256 := by
  obtain ⟨hs, hl⟩ := fields_chk_site hL hsat hL24 hr (j := 9 + j) (by omega)
  have g : Fields.chkLookups.getD (9 + j) ⟨0, .const 0, []⟩ = ⟨Tables.REL_R8, .neg Fields.one, [Fields.rg j]⟩ := by
    interval_cases j <;> rfl
  rw [g] at hl
  apply r8_lt hL hsat hL24 hs (by simp [isUse]; omega) (by simp [siteRel, hl])
  · simp [siteMult, hl, siteEval, hL 1 (by decide), Expr.eval, Fields.one, StarkedAir.Sha256.eval_cst]
  · simp [siteVals, hl, siteEval, hL 1 (by decide), Fields.rg, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]

/-- **Fields byte slots read the block.** Byte slot `j` of fields row `r`, when its multiplicity is `−1`,
reads the block byte at `BASEC + j`. -/
theorem fields_by_read {r j : ℕ} (hr : r < 2 ^ L) (hj : j < 8)
    (hm : (Fields.chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Fields.preCols pub (inst 1).main r = -1) :
    ∃ r0, r0 < (pub 0).val ∧ (inst 1).main Fields.BASEC r + (j : F) = (r0 : F) ∧
      (inst 1).main (Fields.BY j) r = (inst 0).main BYTE r0 := by
  obtain ⟨hs, hl⟩ := fields_chk_site hL hsat hL24 hr (j := j) (by omega)
  have g : (Fields.chkLookups.getD j ⟨0, .const 0, []⟩).rel = REL_BYTE ∧
      (Fields.chkLookups.getD j ⟨0, .const 0, []⟩).vals = [.add (Fields.k Fields.BASEC) (Fields.c j), Fields.by4 j] := by
    interval_cases j <;> exact ⟨rfl, rfl⟩
  have hv : siteVals hashSys inst pub (1, r, 8 + j) = [(inst 1).main Fields.BASEC r + (j : F),
      (inst 1).main (Fields.BY j) r] := by
    rw [siteVals, hl, g.2]
    simp [siteEval, hL 1 (by decide), Expr.eval, Fields.k, Fields.c, Fields.by4,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr]
  obtain ⟨r0, hr0, hp, hb⟩ := hash_read hL hsat hL24 hs (by decide) (by rw [siteRel, hl]; exact g.1)
    (by simp only [siteMult, hl, siteEval, hL 1 (by decide)]; exact hm) hv
  exact ⟨r0, hr0, hp, hb⟩

/-- **The auxiliary read** (prevout or commitment-pattern byte) reads the block at `AQ`. -/
theorem fields_bq_read {r : ℕ} (hr : r < 2 ^ L) (hm : (inst 1).main Fields.GIN r + (inst 1).main Fields.MMB r = 1) :
    ∃ r0, r0 < (pub 0).val ∧ (inst 1).main Fields.AQ r = (r0 : F) ∧ (inst 1).main Fields.BQ r = (inst 0).main BYTE r0 := by
  obtain ⟨hs, hl⟩ := fields_chk_site hL hsat hL24 hr (j := 8) (by omega)
  have g : Fields.chkLookups.getD 8 ⟨0, .const 0, []⟩ =
      ⟨REL_BYTE, .neg (.add (Fields.k Fields.GIN) (Fields.k Fields.MMB)), [Fields.k Fields.AQ, Fields.k Fields.BQ]⟩ := rfl
  rw [g] at hl
  have hv : siteVals hashSys inst pub (1, r, 8 + 8) = [(inst 1).main Fields.AQ r, (inst 1).main Fields.BQ r] := by
    simp [siteVals, hl, siteEval, hL 1 (by decide), Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  exact hash_read hL hsat hL24 hs (by decide) (by simp [siteRel, hl])
    (by simp [siteMult, hl, siteEval, hL 1 (by decide), Expr.eval, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr, hm]) hv

end System

end StarkedAir.Block
