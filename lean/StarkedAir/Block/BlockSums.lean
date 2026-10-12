/-
**The block limits (M3a.5c–d), system level.** The block's weight is at most 4,000,000 (the context's
check, with the fields' witness-byte total) and its legacy sigops, times 4, at most 80,000 (the
context's check, with the walker's total over the fields' scripts).
-/
import StarkedAir.Block.BlockTxs

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)

theorem sumSig_toksFrom (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (m : ℕ) :
    Spec.Block.sumSig (toksFrom M R m 0) = ∑ i ∈ Finset.range m, Spec.Block.tokSig (tokOf M R i) := by
  rw [Spec.Block.sumSig, toksFrom, List.map_map, Nat.sub_zero, Fields.list_sum_range]; simp [Function.comp]

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : ∀ i < 15, Ls i ≤ 23)
include hL hsat hL24

/-- The rows' tokens serialize to the block's bytes. -/
theorem toks_bytes (S : Setup inst pub (Ls 1)) : Spec.Block.toksBytes (toksFrom (inst 1).main (Rb inst pub) S.m 0) = Rb inst pub := by
  have := S.cat S.m le_rfl
  rw [S.hSm, Fields.slice_zero] at this
  simpa [toksFrom, Spec.Block.toksBytes, List.flatMap_map] using this

theorem len_pub : pub 0 = (((Rb inst pub).length : ℕ) : F) := by
  rw [Fields.blockBytes_length, ZMod.natCast_zmod_val]

theorem ctx_seg_a0 (S : Setup inst pub (Ls 1)) :
    ((inst 7).main Ctx.SEG0 0 = 0 ∨ (inst 7).main Ctx.SEG0 0 = 1) ∧ ((inst 7).main Ctx.A0 0).val < 2 ^ 25 := by
  have fs := hash_fields_sat' hL hsat
  obtain ⟨ρ, t, hρ, -, -, -, hat, hta, hsg, -⟩ := tx0 hL hsat hL24 S
  obtain ⟨rh, hrh, ht, hnt, -⟩ := Fields.tx_rows fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hat hρ
  obtain ⟨hta', -⟩ := Fields.head_cols fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit S.hnp (hmk_R hL hsat hL24) hat hρ hrh ht hnt
  refine ⟨by rw [← hsg]; exact Fields.seg_bool fs (show ρ < 2 ^ Ls 1 by have := S.hmn; omega), ?_⟩
  rw [← hta, hta']; exact Fields.start_lt fs (show rh < 2 ^ Ls 1 by have := S.hmn; omega)

/-- **The weight limit.** -/
theorem weight_ok (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) : Spec.Block.weight S.b ≤ Spec.Block.MAX_BLOCK_WEIGHT := by
  have fs := hash_fields_sat' hL hsat
  have cs := hash_ctx_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have h256 := ctx_sat8 hL hsat hL24 hL8
  obtain ⟨hsw, hw⟩ := Spec.Block.toksBlock_weight S.htok
  rw [toks_bytes hL hsat hL24 S] at hsw hw
  have hlen := len_R hL hsat hL24 (inst := inst) (pub := pub)
  have hwb := Fields.wb_last fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit S.hnp (hmk_R hL hsat hL24)
  rw [← (tot_link hL hsat hL24).1] at hwb
  obtain ⟨D, hD, hDe⟩ := Ctx.weight_fact cs h256 (by omega) (ctx_ra hL hsat hL24)
  rw [hwb, len_pub hL hsat hL24] at hDe
  set sw := Spec.Block.sumW (toksFrom (inst 1).main (Rb inst pub) S.m 0)
  set len := (Rb inst pub).length
  have e : ((D + 4 * len : ℕ) : F) = ((4000000 + 3 * sw : ℕ) : F) := by push_cast; rw [hDe]; ring
  have := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
  unfold Spec.Block.MAX_BLOCK_WEIGHT; omega

/-- **Walker scripts are the fields' scripts**: a first row's remaining length is 1 to `2^25`. -/
theorem walk_rem (S : Setup inst pub (Ls 1)) : ∀ r < 2 ^ Ls 6, (inst 6).main Walk.FS r = 1 →
    1 ≤ ((inst 6).main Walk.REM r).val ∧ ((inst 6).main Walk.REM r).val ≤ 2 ^ 25 := by
  intro r hr hf
  have fs := hash_fields_sat' hL hsat
  have hs := site_mem hL (i := 6) (by decide) hr (k := 0) (by simp [hashSys, Walk.walk, Walk.lookups])
  have hm : siteMult hashSys inst pub (6, r, 0) = -1 := by rw [script_mult6 hL hsat hL24 hr, hf]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs rfl hm
  have e : siteRel hashSys (6, r, 0) = 11 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 1 ∧ k' = 30 := by omega
  rw [script_mult1 hL hsat hL24 hr'] at hsm
  rw [script_vals1 hL hsat hL24 hr', script_vals6 hL hsat hL24 hr] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  rw [← hsv.2]
  have := Fields.script_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr' hsm
  unfold Fields.MAXS at this; omega

/-- **The sigop limit.** -/
theorem sigops_ok (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) :
    (S.b.txs.map Spec.Block.legacySigOps).sum * 4 ≤ Spec.Block.MAX_BLOCK_SIGOPS_COST := by
  classical
  have fs := hash_fields_sat' hL hsat
  have cs := hash_ctx_sat' hL hsat
  have ws : ∀ r < 2 ^ Ls 6, ∀ c ∈ Walk.constraints, c.eval (2 ^ Ls 6) Walk.preCols pub (inst 6).main r = 0 := by
    have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have h256 := ctx_sat8 hL hsat hL24 hL8
  have hlen := len_R hL hsat hL24 (inst := inst) (pub := pub)
  set R := Rb inst pub
  -- the walker's total, over its first rows
  have htot := Walk.total ws (walk_opc hL hsat hL24) (walk_r8 hL hsat hL24) R (walk_read hL hsat hL24) (by omega)
    (walk_rem hL hsat hL24 S) (by positivity)
  -- equals the fields' scripts' sum
  have hss := script_sum hL hsat hL24 (fun v => Spec.Block.sigOps (slice R (v.getD 0 0).val (v.getD 1 0).val))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hss
  -- the fields' sum is the tokens'
  have hfs : ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => Fields.smult (inst 1).main r = 1),
      Spec.Block.sigOps (slice R ((inst 1).main Fields.SSC r).val ((inst 1).main Fields.VAL r).val) =
      Spec.Block.sumSig (toksFrom (inst 1).main R S.m 0) := by
    rw [Finset.sum_filter, sumSig_toksFrom, ← Finset.sum_range_add_sum_Ico _ (show S.m ≤ 2 ^ Ls 1 by have := S.hmn; omega)]
    have hz : ∑ r ∈ Finset.Ico S.m (2 ^ Ls 1), (if Fields.smult (inst 1).main r = 1 then
        Spec.Block.sigOps (slice R ((inst 1).main Fields.SSC r).val ((inst 1).main Fields.VAL r).val) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hr
      rw [Fields.script_pad fs R S.hcs S.hmn S.hpad S.hfit h2 h1, if_neg zero_ne_one]
    rw [hz, add_zero]
    exact Finset.sum_congr rfl (fun r hr => Fields.script_term fs R S.hcs S.hmn S.hpad S.hfit S.hnp
      (Finset.mem_range.mp hr))
  rw [hfs, Spec.Block.toksBlock_sig S.htok] at hss
  -- the context's check
  have hbound := Spec.Block.sumSig_le (toksFrom (inst 1).main R S.m 0)
  rw [toks_bytes hL hsat hL24 S, Spec.Block.toksBlock_sig S.htok] at hbound
  obtain ⟨D, hD, hDe⟩ := Ctx.sigops_fact cs h256 (by omega) (ctx_ra hL hsat hL24)
  rw [sigops_link hL hsat hL24, htot, ← Nat.cast_sum, ← hss] at hDe
  set s := (S.b.txs.map Spec.Block.legacySigOps).sum
  have hRR : (Rb inst pub).length = R.length := rfl
  have e : ((D + s : ℕ) : F) = ((20000 : ℕ) : F) := by push_cast; rw [hDe]; ring
  have := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) e
  unfold Spec.Block.MAX_BLOCK_SIGOPS_COST; omega

end System

end StarkedAir.Block
