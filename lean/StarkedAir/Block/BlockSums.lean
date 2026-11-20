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
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
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

/-- **Walker spans are the fields' spans**: a first row's remaining length is 1 to `2^25`. A script is a
fields script; an accurate span is a redeem script (below `2^24` bytes) or a witness item. -/
theorem walk_rem (S : Setup inst pub (Ls 1)) : ∀ r < 2 ^ Ls 6, (inst 6).main Walk.FS r = 1 →
    1 ≤ ((inst 6).main Walk.REM r).val ∧ ((inst 6).main Walk.REM r).val ≤ 2 ^ 25 := by
  intro r hr hf
  have fs := hash_fields_sat' hL hsat
  have ws := hash_walk_sat hL hsat
  have bAC : (inst 6).main Walk.AC r = 0 ∨ (inst 6).main Walk.AC r = 1 :=
    air_bool ws (c := Walk.AC) (by simp [Walk.walk, Walk.constraints, Walk.accC, Walk.k]) hr
  rcases bAC with a0 | a1
  · have hs := site_mem hL (i := 6) (by decide) hr (k := 0) (by simp [hashSys, Walk.walk, Walk.lookups])
    have hm : siteMult hashSys inst pub (6, r, 0) = -1 := by
      rw [script_mult6 hL hsat hL24 hr]; simp [wsm, hf, a0]
    obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs rfl hm
    have e : siteRel hashSys (6, r, 0) = 11 := rfl
    rw [e, yt] at hy
    obtain ⟨rfl, rfl⟩ : i' = 1 ∧ k' = 30 := by omega
    rw [script_mult1 hL hsat hL24 hr'] at hsm
    rw [script_vals1 hL hsat hL24 hr', script_vals6 hL hsat hL24 hr] at hsv
    simp only [List.cons.injEq, and_true] at hsv
    rw [← hsv.2.1]
    have := Fields.script_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr' hsm
    unfold Fields.MAXS at this; omega
  · have hs := site_mem hL (i := 6) (by decide) hr (k := 5) (by simp [hashSys, Walk.walk, Walk.lookups])
    have hm : siteMult hashSys inst pub (6, r, 5) = -1 := by
      simp [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Expr.eval, Walk.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr, hf, a1]
    obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs rfl hm
    have e : siteRel hashSys (6, r, 5) = 26 := rfl
    rw [e, yt] at hy
    have h6 : siteVals hashSys inst pub (6, r, 5) = [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r,
        (inst 6).main Walk.W4 r] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr]
    rw [h6] at hsv
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ : (i' = 1 ∧ k' = 42) ∨ (i' = 1 ∧ k' = 43) := by omega
    · have m42 : siteMult hashSys inst pub (1, r', 42) = (inst 1).main Fields.ARQ r' := by
        simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
        simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col,
          wrap_zero hr']
      have v42 : siteVals hashSys inst pub (1, r', 42) = [(inst 1).main Fields.SRS r', (inst 1).main Fields.SRL r', 1] := by
        simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
          Fields.chkLookups, Fields.k, Fields.c, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
          wrap_zero hr']
      rw [m42] at hsm; rw [v42] at hsv
      simp only [List.cons.injEq, and_true] at hsv
      rw [← hsv.2.1]
      have := Fields.arq_val fs hr' (fun j hj => fields_rg_lt hL hsat hL24 hr' hj) hsm
      omega
    · have m43 : siteMult hashSys inst pub (1, r', 43) =
          (inst 1).main Fields.WQ r' * (1 - (inst 1).main Fields.ZV r') := by
        simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
        simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, Fields.oneMinus, Fields.one,
          StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr']
      have v43 : siteVals hashSys inst pub (1, r', 43) = [(inst 1).main Fields.SSC r', (inst 1).main Fields.VAL r', 0] := by
        simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
          Fields.chkLookups, Fields.k, Fields.c, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
          wrap_zero hr']
      rw [m43] at hsm; rw [v43] at hsv
      simp only [List.cons.injEq, and_true] at hsv
      rw [← hsv.2.1]
      have := Fields.wq_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr' hsm
      unfold Fields.MAXS at this; omega

/-- **The legacy sum is the block's** and the context's check, as naturals: with `s` the block's legacy
sigops, `4·s + A + w + D = 80,000` for the walker's weighted accurate count `A`, the fields' P2WPKH count
`w` and a slack `D`. -/
theorem sigops_nat (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) :
    ∃ A w D : ℕ, 4 * (S.b.txs.map Spec.Block.legacySigOps).sum + A + w + D = 80000 ∧
      (inst 6).main Walk.SUMA (2 ^ Ls 6 - 1) = (A : F) ∧ (inst 1).main Fields.W20S (2 ^ Ls 1 - 1) = (w : F) := by
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
  -- only the scripts count
  have hsplit : ∑ f ∈ (Finset.range (2 ^ Ls 6)).filter (fun f => (inst 6).main Walk.FS f = 1),
      (1 - (inst 6).main Walk.AC f) *
        ((Spec.Block.sigOps (slice R ((inst 6).main Walk.POS f).val ((inst 6).main Walk.REM f).val) : ℕ) : F) =
      ((∑ f ∈ (Finset.range (2 ^ Ls 6)).filter (fun f => wsm (inst 6).main f = 1),
        Spec.Block.sigOps (slice R ((inst 6).main Walk.POS f).val ((inst 6).main Walk.REM f).val) : ℕ) : F) := by
    rw [Nat.cast_sum, Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f hf => ?_)
    have hfr := Finset.mem_range.mp hf
    have bFS := Walk.bool ws (c := Walk.FS) (by simp [Walk.bools]) hfr
    have bAC := Walk.acc_bool ws (c := Walk.AC) (by simp [Walk.accC]) hfr
    rcases bFS with a | a <;> rcases bAC with b | b <;> simp [wsm, a, b]
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
  have hbound := Spec.Block.sumSig_le (toksFrom (inst 1).main R S.m 0)
  rw [toks_bytes hL hsat hL24 S, Spec.Block.toksBlock_sig S.htok] at hbound
  set s := (S.b.txs.map Spec.Block.legacySigOps).sum
  have hRR : (Rb inst pub).length = R.length := rfl
  -- the walker's sums and the fields' count, as bounded naturals
  have hn6 : 2 ^ Ls 6 - 1 < 2 ^ Ls 6 := Nat.sub_lt (by positivity) (by norm_num)
  have hn1 : 2 ^ Ls 1 - 1 < 2 ^ Ls 1 := Nat.sub_lt (by positivity) (by norm_num)
  obtain ⟨S', A, hb, eS, eA⟩ := Walk.sums_nat ws (fun r hr ho => by
    obtain ⟨-, -, -, -, a5, -, -, a8, a9⟩ := walk_opc_all hL hsat hL24 r hr ho
    exact ⟨a5, a8, a9⟩) (2 ^ Ls 6 - 1) hn6
  obtain ⟨w, hw, ew⟩ := Fields.w20_nat fs (2 ^ Ls 1 - 1) hn1
  have h6 : 2 ^ Ls 6 ≤ 2 ^ 24 := rb6
  have h1 : 2 ^ Ls 1 ≤ 2 ^ 24 := rb1
  rw [show 2 ^ Ls 6 - 1 + 1 = 2 ^ Ls 6 by omega] at hb
  rw [show 2 ^ Ls 1 - 1 + 1 = 2 ^ Ls 1 by omega] at hw
  -- the legacy sum is `s`
  have eSs : S' = s := by
    have e : ((S' : ℕ) : F) = ((s : ℕ) : F) := by rw [← eS, htot, hsplit, ← hss]
    exact natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
  -- the context's check
  obtain ⟨D, hD, hDe⟩ := Ctx.sigops_fact cs h256 (by omega) (ctx_ra hL hsat hL24)
  rw [(sigops_link2 hL hsat hL24).1, (sigops_link2 hL hsat hL24).2, (tot_link4 hL hsat hL24).2.2.2, eS, eA, ew] at hDe
  have e : ((4 * S' + A + w + D : ℕ) : F) = ((80000 : ℕ) : F) := by push_cast; rw [hDe]; ring
  have := natCast_inj_of_lt (a := 4 * S' + A + w + D) (b := 80000) (by unfold P; omega) (by unfold P; norm_num) e
  exact ⟨A, w, D, by omega, eA, ew⟩

/-- **The sigop limit** (legacy part). -/
theorem sigops_ok (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) :
    (S.b.txs.map Spec.Block.legacySigOps).sum * 4 ≤ Spec.Block.MAX_BLOCK_SIGOPS_COST := by
  obtain ⟨A, w, D, h, -, -⟩ := sigops_nat hL hsat hL24 hL8 S
  unfold Spec.Block.MAX_BLOCK_SIGOPS_COST; omega

end System

end StarkedAir.Block
