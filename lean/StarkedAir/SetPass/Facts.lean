/-
**The segment system's cross-component facts.** Each use of the segment system, read through `link`:
what a record row reads (head and amount bytes, ranges, the fingerprint of its `ser` bytes), what the
`TxOutSer` stream reads (records, code bytes, segment bytes, pending bytes), what each compression reads
(its walker's words) and the end tokens (each walker's `m − 1` is a compression's last block, on its
period's last row).
-/
import StarkedAir.SetPass.LinkUse

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst)
open StarkedAir.Spec.QM31 (QM toQ emb)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
  (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls)
include hL hsat hHL hsz

omit hL hsat hHL hsz in
theorem site_lk {i r k : ℕ} : siteLookup segSys ((i, r, k) : Site) = (segSys.comp i).lookups.getD k ⟨0, .const 0, []⟩ :=
  rfl

/-! ### Record rows -/

omit hL hsat hHL hsz in
theorem rec_hb_lookup : ∀ j < 49, Rec.lookups.getD j ⟨0, .const 0, []⟩ =
    ⟨Block.REL_BYTE, .neg (Rec.k Rec.ON), [.add (Rec.k Rec.START) (cst j), Rec.hb j]⟩ := by
  intro j hj; interval_cases j <;> rfl

omit hL hsat hHL hsz in
theorem rec_ab_lookup : ∀ j < 8, Rec.lookups.getD (49 + j) ⟨0, .const 0, []⟩ =
    ⟨Block.REL_BYTE, .neg (Rec.k Rec.ON), [.add (Rec.k Rec.START) (cst (49 + j)), Rec.k (Rec.AB j)]⟩ := by
  intro j hj; interval_cases j <;> rfl

omit hL hsat hHL hsz in
theorem rec_len : Rec.lookups.length = 98 := by decide

/-- A record row's byte read at lookup `k`, column `c`, offset `o`. -/
theorem rec_byte_at {r k c o : ℕ} (hr : r < 2 ^ Ls 3) (hon : (inst 3).main Rec.ON r = 1) (hk : k < 57)
    (hl : Rec.lookups.getD k ⟨0, .const 0, []⟩ =
      ⟨Block.REL_BYTE, .neg (Rec.k Rec.ON), [.add (Rec.k Rec.START) (cst o), Rec.k c]⟩) :
    ∃ q, q < (pub PUB_LEN).val ∧ (inst 3).main Rec.START r + (o : F) = (q : F) ∧
      (inst 3).main c r = (inst 0).main Block.BYTE q := by
  have hsite := site_mem hL (i := 3) (by decide) hr (k := k) (by show k < Rec.lookups.length; rw [rec_len]; omega)
  have hpre : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hsl : siteLookup segSys ((3, r, k) : Site) = _ := hl
  obtain ⟨q, hq, hp, hb⟩ := byte_read hL hsat hHL hsz hsite (by simp [isUse]; omega) (by simp [siteRel, hsl])
    (by simp [siteMult, hsl, siteEval, hpre, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr, hon])
    (p := (inst 3).main Rec.START r + (o : F)) (b := (inst 3).main c r)
    (by simp [siteVals, hsl, siteEval, hpre, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hr])
  exact ⟨q, hq, hp, hb⟩

theorem rec_hb {r : ℕ} (hr : r < 2 ^ Ls 3) (hon : (inst 3).main Rec.ON r = 1) {j : ℕ} (hj : j < 49) :
    ∃ q, q < (pub PUB_LEN).val ∧ (inst 3).main Rec.START r + (j : F) = (q : F) ∧
      (inst 3).main (Rec.HB j) r = (inst 0).main Block.BYTE q :=
  rec_byte_at hL hsat hHL hsz hr hon (by omega) (rec_hb_lookup j hj)

theorem rec_ab {r : ℕ} (hr : r < 2 ^ Ls 3) (hon : (inst 3).main Rec.ON r = 1) {j : ℕ} (hj : j < 8) :
    ∃ q, q < (pub PUB_LEN).val ∧ (inst 3).main Rec.START r + ((49 + j : ℕ) : F) = (q : F) ∧
      (inst 3).main (Rec.AB j) r = (inst 0).main Block.BYTE q :=
  rec_byte_at hL hsat hHL hsz hr hon (by omega) (rec_ab_lookup j hj)

/-- A record row's range read at lookup `k` (`64 ≤ k`), of column `c`, gated by `m`. -/
theorem rec_r8_at {r k c : ℕ} {m : Expr} (hr : r < 2 ^ Ls 3) (hk : 64 ≤ k) (hk89 : k < 89)
    (hl : Rec.lookups.getD k ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k c) m)
    (hm : m.eval (2 ^ Ls 3) Rec.preCols pub (inst 3).main r = 1) : ((inst 3).main c r).val < 256 := by
  have hsite := site_mem hL (i := 3) (by decide) hr (k := k) (by show k < Rec.lookups.length; rw [rec_len]; omega)
  have hpre : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hsl : siteLookup segSys ((3, r, k) : Site) = _ := hl
  exact r8_read hL hsat hHL hsz hsite (by simp [isUse]; omega) (by simp [siteRel, hsl, Rec.r8])
    (by simp only [siteMult, hsl, siteEval, hpre, hL 3 (by decide), Rec.r8, Expr.eval, hm])
    (by simp [siteVals, hsl, siteEval, hpre, hL 3 (by decide), Rec.r8, Rec.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr])

omit hL hsat hHL hsz in
theorem rec_r8_lookups :
    (∀ i < 3, Rec.lookups.getD (64 + i) ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k (Rec.C i)) (Rec.k Rec.ON)) ∧
    (∀ i < 3, Rec.lookups.getD (67 + i) ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k (Rec.D i)) (Rec.k Rec.ON)) ∧
    (∀ i < 3, Rec.lookups.getD (70 + i) ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k (Rec.SB i)) (Rec.k Rec.ON)) ∧
    (∀ i < 3, Rec.lookups.getD (73 + i) ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k (Rec.MD i)) (Rec.k Rec.ON)) ∧
    (∀ j < 12, Rec.lookups.getD (76 + j) ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k (Rec.AM j)) Rec.one) ∧
    Rec.lookups.getD 88 ⟨0, .const 0, []⟩ = Rec.r8 (Rec.k Rec.DELTA) Rec.cmp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl⟩ <;> (intro i hi; interval_cases i <;> rfl)

/-- **A record row's ranges**: on rows the code, length, start and height-difference bytes; every row the
amount bytes; comparing rows the key difference. -/
theorem rec_ranges {r : ℕ} (hr : r < 2 ^ Ls 3) :
    ((inst 3).main Rec.ON r = 1 → ∀ i < 3, ((inst 3).main (Rec.C i) r).val < 256 ∧
      ((inst 3).main (Rec.D i) r).val < 256 ∧ ((inst 3).main (Rec.SB i) r).val < 256 ∧
      ((inst 3).main (Rec.MD i) r).val < 256) ∧
    (∀ j < 12, ((inst 3).main (Rec.AM j) r).val < 256) ∧
    (Rec.cmp.eval (2 ^ Ls 3) Rec.preCols pub (inst 3).main r = 1 → ((inst 3).main Rec.DELTA r).val < 256) := by
  obtain ⟨l1, l2, l3, l4, l5, l6⟩ := rec_r8_lookups
  have ev : ∀ c, (Rec.k c).eval (2 ^ Ls 3) Rec.preCols pub (inst 3).main r = (inst 3).main c r := fun c => by
    simp [Rec.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  refine ⟨fun hon i hi => ⟨?_, ?_, ?_, ?_⟩, fun j hj => ?_, fun hc => ?_⟩
  · exact rec_r8_at hL hsat hHL hsz hr (by omega) (by omega) (l1 i hi) (by rw [ev, hon])
  · exact rec_r8_at hL hsat hHL hsz hr (by omega) (by omega) (l2 i hi) (by rw [ev, hon])
  · exact rec_r8_at hL hsat hHL hsz hr (by omega) (by omega) (l3 i hi) (by rw [ev, hon])
  · exact rec_r8_at hL hsat hHL hsz hr (by omega) (by omega) (l4 i hi) (by rw [ev, hon])
  · exact rec_r8_at hL hsat hHL hsz hr (by omega) (by omega) (l5 j hj) (by simp [Rec.one, StarkedAir.Sha256.eval_cst])
  · exact rec_r8_at hL hsat hHL hsz hr (by omega) (by omega) l6 hc

omit hL hsat hHL hsz in
/-- A periodic preprocessed column's value. -/
theorem ev_periodic {n r i L : ℕ} {pc : List PreCol} {M : ℕ → ℕ → F} {f : ℕ → ℕ} (hL0 : 0 < L)
    (hi : pc.getD i (.periodic [0]) = .periodic ((List.range L).map f)) (hr : r < n) :
    (pre i).eval n pc pub M r = ((f (r % L) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  simp [PreCol.eval, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.mod_lt r hL0)]

/-! ### Fingerprints -/

/-- **A record's fingerprint** is the Horner fingerprint (at the public `γ`) of the segment bytes of its
`ser`: `len` bytes from `START + 49`, within the segment. -/
theorem rec_fp (hidx : ∀ r < 2 ^ Ls 3, (inst 3).main Rec.ON r = 1 → (inst 3).main Rec.IDX r = (r : F))
    (hst : ∀ r < 2 ^ Ls 3, (inst 3).main Rec.ON r = 1 → ((inst 3).main Rec.START r).val < 2 ^ 24)
    {r : ℕ} (hr : r < 2 ^ Ls 3) (hon : (inst 3).main Rec.ON r = 1) :
    ∃ len : ℕ, (inst 3).main Rec.LENC r = (len : F) ∧
      ((inst 3).main Rec.START r).val + 49 + len ≤ (pub PUB_LEN).val ∧
      toQ ⟨(inst 3).main Rec.FH r, (inst 3).main (Rec.FH + 1) r, (inst 3).main (Rec.FH + 2) r,
        (inst 3).main (Rec.FH + 3) r⟩ =
      Block.FpWalk.horner (Block.FpWalk.gQ pub) ((List.range len).map fun i =>
        emb ((inst 0).main Block.BYTE (((inst 3).main Rec.START r).val + 49 + i))) := by
  have fw := fpwalk_sat hL hsat
  have rs := rec_sat hL hsat
  have hP3 := rows_lt_P hL hsz (i := 3) (by decide)
  have hP4 := rows_lt_P hL hsz (i := 4) (by decide)
  have h24 : ∀ i < 12, 2 ^ Ls i ≤ 2 ^ 24 := fun i hi => Nat.pow_le_pow_right (by norm_num) (hsz.1 i hi)
  have hpre3 : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hpre4 : (segSys.comp 4).air.pre = Block.FpWalk.preCols := rfl
  -- the record's fingerprint use
  have hsite := site_mem hL (i := 3) (by decide) hr (k := 63) (by show 63 < Rec.lookups.length; rw [rec_len]; omega)
  have hl63 : siteLookup segSys ((3, r, 63) : Site) = ⟨Block.FpWalk.REL_FP, .neg (Rec.k Rec.ON),
      [cst 0, Rec.k Rec.IDX, Rec.k Rec.LENC, Rec.k Rec.FH, Rec.k (Rec.FH + 1), Rec.k (Rec.FH + 2),
        Rec.k (Rec.FH + 3)]⟩ := rfl
  have hm : siteMult segSys inst pub (3, r, 63) = -1 := by
    simp [siteMult, hl63, siteEval, hpre3, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr, hon]
  obtain ⟨i', e, k', he, hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse]) hm
  rw [show siteRel segSys ((3, r, 63) : Site) = 22 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i' = 4 ∧ k' = 3 := by omega
  have hlst : (inst 4).main Block.FpWalk.LST e = 1 := by
    have hm' : (inst 4).main Block.FpWalk.LST e ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, segSys, comps, hL 4 (by decide), Block.FpWalk.fpwalk,
        Block.FpWalk.lookups, Expr.eval, Block.FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero he] using hsm
    exact (Block.FpWalk.bool fw (c := Block.FpWalk.LST) (by simp) he).resolve_left hm'
  have hv1 : siteVals segSys inst pub (4, e, 3) = [(inst 4).main Block.FpWalk.STR e, (inst 4).main Block.FpWalk.SID e,
      (inst 4).main Block.FpWalk.LEN e, (inst 4).main Block.FpWalk.H e, (inst 4).main (Block.FpWalk.H + 1) e,
      (inst 4).main (Block.FpWalk.H + 2) e, (inst 4).main (Block.FpWalk.H + 3) e] := by
    simp [siteVals, siteEval, siteLookup, segSys, comps, hL 4 (by decide), Block.FpWalk.fpwalk, Block.FpWalk.lookups,
      Block.FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero he]
  have hv0 : siteVals segSys inst pub (3, r, 63) = [0, (inst 3).main Rec.IDX r, (inst 3).main Rec.LENC r,
      (inst 3).main Rec.FH r, (inst 3).main (Rec.FH + 1) r, (inst 3).main (Rec.FH + 2) r,
      (inst 3).main (Rec.FH + 3) r] := by
    simp [siteVals, hl63, siteEval, hpre3, hL 3 (by decide), Rec.k, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hr]
  rw [hv1, hv0] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨tstr, tsid, tlen, th0, th1, th2, th3⟩ := hsv
  -- the walked segment
  obtain ⟨s0, hse, hfs, hrow, -, hlen, hh⟩ := Block.FpWalk.seg_sound fw he hlst
  set len := e - s0 + 1 with hlendef
  -- its descriptor is the record's
  have hs0 : s0 < 2 ^ Ls 4 := by omega
  have hsite2 := site_mem hL (i := 4) (by decide) hs0 (k := 2) (by simp [segSys, comps, Block.FpWalk.fpwalk,
    Block.FpWalk.lookups])
  have hm2 : siteMult segSys inst pub (4, s0, 2) = -1 := by
    simp [siteMult, siteEval, siteLookup, segSys, comps, hL 4 (by decide), Block.FpWalk.fpwalk, Block.FpWalk.lookups,
      Expr.eval, Block.FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hs0, hfs]
  obtain ⟨i2, ρ, k2, hρ, hy2, hsm2, hsv2⟩ := link hL hsat hHL hsz hsite2 (by simp [isUse]) hm2
  rw [show siteRel segSys ((4, s0, 2) : Site) = 21 from rfl] at hy2
  replace hy2 := yt hy2; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy2
  obtain ⟨rfl, rfl⟩ : i2 = 3 ∧ k2 = 62 := by omega
  have hl62 : siteLookup segSys ((3, ρ, 62) : Site) = ⟨Block.FpWalk.REL_SEG, Rec.k Rec.ON,
      [cst 0, Rec.k Rec.IDX, .add (Rec.k Rec.START) (cst 49), Rec.k Rec.LENC]⟩ := rfl
  have hρon : (inst 3).main Rec.ON ρ = 1 := by
    have hm' : (inst 3).main Rec.ON ρ ≠ 0 := by
      simpa [siteMult, hl62, siteEval, hpre3, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
        wrap_zero hρ] using hsm2
    exact (Block.air_bool (air := Rec.rec.air) rs (c := Rec.ON) (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k])
      hρ).resolve_left hm'
  have hv2 : siteVals segSys inst pub (3, ρ, 62) = [0, (inst 3).main Rec.IDX ρ, (inst 3).main Rec.START ρ + 49,
      (inst 3).main Rec.LENC ρ] := by
    simp [siteVals, hl62, siteEval, hpre3, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hρ]
  have hv3 : siteVals segSys inst pub (4, s0, 2) = [(inst 4).main Block.FpWalk.STR s0, (inst 4).main Block.FpWalk.SID s0,
      (inst 4).main Block.FpWalk.POS s0, (inst 4).main Block.FpWalk.REM s0] := by
    simp [siteVals, siteEval, siteLookup, segSys, comps, hL 4 (by decide), Block.FpWalk.fpwalk, Block.FpWalk.lookups,
      Block.FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hs0]
  rw [hv2, hv3] at hsv2
  simp only [List.cons.injEq, and_true] at hsv2
  obtain ⟨-, hsid2, hpos2, -⟩ := hsv2
  have hρr : ρ = r := by
    have e1 : (inst 3).main Rec.IDX ρ = (inst 3).main Rec.IDX r := by
      rw [hsid2, (hrow s0 le_rfl hse).2.2.1, tsid]
    rw [hidx ρ hρ hρon, hidx r hr hon] at e1
    exact natCast_inj_of_lt (by omega) (by omega) e1
  subst hρr
  have hpos0 : (inst 4).main Block.FpWalk.POS s0 = (inst 3).main Rec.START ρ + 49 := hpos2.symm
  have hstv := hst ρ hr hon
  -- each byte
  have hbyte : ∀ i < len, ((inst 3).main Rec.START ρ).val + 49 + i < (pub PUB_LEN).val ∧
      (inst 4).main Block.FpWalk.B (s0 + i) = (inst 0).main Block.BYTE (((inst 3).main Rec.START ρ).val + 49 + i) := by
    intro i hi
    have hq : s0 + i ≤ e := by omega
    have hqn : s0 + i < 2 ^ Ls 4 := by omega
    obtain ⟨hon', hstr, -, -, hpos⟩ := hrow (s0 + i) (by omega) hq
    rw [tstr] at hstr
    have hsite3 := site_mem hL (i := 4) (by decide) hqn (k := 0) (by simp [segSys, comps, Block.FpWalk.fpwalk,
      Block.FpWalk.lookups])
    obtain ⟨q, hq', hp, hb⟩ := byte_read hL hsat hHL hsz hsite3 (by simp [isUse]) rfl
      (by simp [siteMult, siteEval, siteLookup, segSys, comps, hL 4 (by decide), Block.FpWalk.fpwalk,
        Block.FpWalk.lookups, Expr.eval, Block.FpWalk.k, Block.FpWalk.om, Block.FpWalk.one,
        StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hqn, hon', hstr])
      (p := (inst 4).main Block.FpWalk.POS (s0 + i)) (b := (inst 4).main Block.FpWalk.B (s0 + i))
      (by simp [siteVals, siteEval, siteLookup, segSys, comps, hL 4 (by decide), Block.FpWalk.fpwalk,
        Block.FpWalk.lookups, Block.FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hqn])
    have hlenb : len ≤ 2 ^ 24 := by have := h24 4 (by decide); omega
    have hqv : q = ((inst 3).main Rec.START ρ).val + 49 + i := by
      have e1 : ((q : ℕ) : F) = ((((inst 3).main Rec.START ρ).val + 49 + i : ℕ) : F) := by
        rw [← hp, hpos, hpos0, show s0 + i - s0 = i by omega]; push_cast
        rw [ZMod.natCast_zmod_val]
      have hqP : q < P := lt_trans hq' (ZMod.val_lt _)
      have hb1 : ((inst 3).main Rec.START ρ).val + 49 + i < 2 ^ 26 := by
        have := hstv; have := hlenb; omega
      exact natCast_inj_of_lt hqP (lt_of_lt_of_le hb1 (by unfold P; norm_num)) e1
    subst hqv
    exact ⟨hq', hb⟩
  refine ⟨len, by rw [← tlen, hlen], ?_, ?_⟩
  · have := (hbyte (len - 1) (by omega)).1; omega
  · have e1 : toQ ⟨(inst 3).main Rec.FH ρ, (inst 3).main (Rec.FH + 1) ρ, (inst 3).main (Rec.FH + 2) ρ,
        (inst 3).main (Rec.FH + 3) ρ⟩ = Block.FpWalk.hQ (inst 4).main e := by
      simp only [Block.FpWalk.hQ, th0, th1, th2, th3]
    rw [e1, hh]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [(hbyte i (List.mem_range.mp hi)).2]

/-! ### The `TxOutSer` stream -/

omit hL hsat hHL hsz in
theorem tmsg_ev {y c : ℕ} (hy : y < 2 ^ Ls 7) : (TMsg.k c).eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y =
    (inst 7).main c y := by
  simp [TMsg.k, StarkedAir.Sha256.eval_col, wrap_zero hy]

/-- A stream read with multiplicity `−(col)` at lookup `k`. -/
theorem tmsg_use {y k c : ℕ} (hy : y < 2 ^ Ls 7) (hk : k < 8) (hk6 : k ≠ 6)
    (hm : (TMsg.lookups.getD k ⟨0, .const 0, []⟩).mult = .neg (TMsg.k c)) (hc : (inst 7).main c y = 1) :
    ∃ i r' k', r' < 2 ^ Ls i ∧ (i, k', (TMsg.lookups.getD k ⟨0, .const 0, []⟩).rel) ∈ yieldTable ∧
      siteMult segSys inst pub (i, r', k') ≠ 0 ∧
      siteVals segSys inst pub (i, r', k') =
        (TMsg.lookups.getD k ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y) := by
  have hsite := site_mem hL (i := 7) (by decide) hy (k := k) (by simpa [segSys, comps, TMsg.tmsg, TMsg.lookups] using hk)
  have hpre : (segSys.comp 7).air.pre = TMsg.preCols := rfl
  have hsl : siteLookup segSys ((7, y, k) : Site) = TMsg.lookups.getD k ⟨0, .const 0, []⟩ := rfl
  have hmult : siteMult segSys inst pub (7, y, k) = -1 := by
    simp only [siteMult, hsl, siteEval, hpre, hL 7 (by decide), hm, Expr.eval]
    rw [tmsg_ev hy, hc]
  obtain ⟨i, r', k', hr', hy', hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse, hk6]) hmult
  refine ⟨i, r', k', hr', hy', hsm, ?_⟩
  rw [hsv]; simp only [siteVals, hsl]; congr 1
  funext e
  show e.eval (2 ^ (inst 7).logSize) (segSys.comp 7).air.pre pub (inst 7).main y = _
  rw [hpre, hL 7 (by decide)]

/-- **A record's first stream row reads its record**: `(R, RST, RLEN)` is a record row's `(IDX, START, LENC)`. -/
theorem tmsg_rec {y : ℕ} (hy : y < 2 ^ Ls 7) (hn : (inst 7).main TMsg.NEW y = 1) :
    ∃ ρ < 2 ^ Ls 3, (inst 3).main Rec.ON ρ = 1 ∧ (inst 7).main TMsg.R y = (inst 3).main Rec.IDX ρ ∧
      (inst 7).main TMsg.RST y = (inst 3).main Rec.START ρ ∧ (inst 7).main TMsg.RLEN y = (inst 3).main Rec.LENC ρ := by
  obtain ⟨i, ρ, k', hρ, hyt, hsm, hsv⟩ := tmsg_use hL hsat hHL hsz hy (k := 4) (c := TMsg.NEW) (by norm_num)
    (by norm_num) rfl hn
  rw [show (TMsg.lookups.getD 4 ⟨0, .const 0, []⟩).rel = 32 from rfl] at hyt
  replace hyt := yt hyt; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyt
  obtain ⟨rfl, rfl⟩ : i = 3 ∧ k' = 57 := by omega
  have rs := rec_sat hL hsat
  have hpre3 : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hl57 : siteLookup segSys ((3, ρ, 57) : Site) = ⟨REL_REC, .mul (cst 2) (Rec.k Rec.ON), [Rec.k Rec.IDX,
      Rec.k Rec.START, Rec.k Rec.LENC]⟩ := rfl
  have hon : (inst 3).main Rec.ON ρ = 1 := by
    have hm' : (inst 3).main Rec.ON ρ ≠ 0 := by
      have h2 : (2 : F) * (inst 3).main Rec.ON ρ ≠ 0 := by
        simpa [siteMult, hl57, siteEval, hpre3, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
          StarkedAir.Sha256.eval_cst, wrap_zero hρ] using hsm
      exact right_ne_zero_of_mul h2
    exact (Block.air_bool (air := Rec.rec.air) rs (c := Rec.ON) (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k])
      hρ).resolve_left hm'
  have e1 : siteVals segSys inst pub (3, ρ, 57) = [(inst 3).main Rec.IDX ρ, (inst 3).main Rec.START ρ,
      (inst 3).main Rec.LENC ρ] := by
    simp [siteVals, hl57, siteEval, hpre3, hL 3 (by decide), Rec.k, StarkedAir.Sha256.eval_col, wrap_zero hρ]
  rw [e1] at hsv
  simp only [TMsg.lookups, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil,
    tmsg_ev hy, List.cons.injEq, and_true] at hsv
  exact ⟨ρ, hρ, hon, hsv.1.symm, hsv.2.1.symm, hsv.2.2.symm⟩

/-- **A code row reads its record's code byte**: `(R, O − 36, B)` is a record row's `(IDX, i, C i)`. -/
theorem tmsg_code {y : ℕ} (hy : y < 2 ^ Ls 7) (hc : (inst 7).main TMsg.PC y = 1) :
    ∃ ρ < 2 ^ Ls 3, (inst 3).main Rec.ON ρ = 1 ∧ ∃ i : ℕ, i < 4 ∧ (inst 7).main TMsg.R y = (inst 3).main Rec.IDX ρ ∧
      (inst 7).main TMsg.O y - 36 = (i : F) ∧ (inst 7).main TMsg.B y = (inst 3).main (Rec.C i) ρ := by
  obtain ⟨i', ρ, k', hρ, hyt, hsm, hsv⟩ := tmsg_use hL hsat hHL hsz hy (k := 2) (c := TMsg.PC) (by norm_num)
    (by norm_num) rfl hc
  rw [show (TMsg.lookups.getD 2 ⟨0, .const 0, []⟩).rel = 33 from rfl] at hyt
  replace hyt := yt hyt; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyt
  obtain ⟨rfl, hk1, hk2⟩ : i' = 3 ∧ 58 ≤ k' ∧ k' ≤ 61 := by omega
  obtain ⟨i, hi, rfl⟩ : ∃ i, i < 4 ∧ k' = 58 + i := ⟨k' - 58, by omega, by omega⟩
  have rs := rec_sat hL hsat
  have hpre3 : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hl : siteLookup segSys ((3, ρ, 58 + i) : Site) = ⟨REL_CODE, Rec.k Rec.ON, [Rec.k Rec.IDX, cst i,
      Rec.k (Rec.C i)]⟩ := by
    show Rec.lookups.getD (58 + i) _ = _
    interval_cases i <;> rfl
  have hon : (inst 3).main Rec.ON ρ = 1 := by
    have hm' : (inst 3).main Rec.ON ρ ≠ 0 := by
      simpa [siteMult, hl, siteEval, hpre3, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
        wrap_zero hρ] using hsm
    exact (Block.air_bool (air := Rec.rec.air) rs (c := Rec.ON) (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k])
      hρ).resolve_left hm'
  have e1 : siteVals segSys inst pub (3, ρ, 58 + i) = [(inst 3).main Rec.IDX ρ, (i : F), (inst 3).main (Rec.C i) ρ] := by
    simp [siteVals, hl, siteEval, hpre3, hL 3 (by decide), Rec.k, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hρ]
  rw [e1] at hsv
  simp only [TMsg.lookups, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil, Expr.eval,
    tmsg_ev hy, StarkedAir.Sha256.eval_cst, List.cons.injEq, and_true] at hsv
  exact ⟨ρ, hρ, hon, i, hi, hsv.1.symm, by simpa using hsv.2.1.symm, hsv.2.2.symm⟩

/-- A stream byte read (lookup 1 for outpoint rows, 3 for `ser` rows). -/
theorem tmsg_byte {y k c : ℕ} (hy : y < 2 ^ Ls 7) (hk : k = 1 ∧ c = TMsg.P0 ∨ k = 3 ∧ c = TMsg.PS)
    (hc : (inst 7).main c y = 1) :
    ∃ q, q < (pub PUB_LEN).val ∧
      (inst 7).main TMsg.RST y + (inst 7).main TMsg.O y + (if k = 1 then 0 else 9) = (q : F) ∧
      (inst 7).main TMsg.B y = (inst 0).main Block.BYTE q := by
  have hpre : (segSys.comp 7).air.pre = TMsg.preCols := rfl
  have hk8 : k < 8 := by omega
  have hsite := site_mem hL (i := 7) (by decide) hy (k := k) (by simpa [segSys, comps, TMsg.tmsg, TMsg.lookups] using hk8)
  rcases hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨q, hq, hp, hb⟩ := byte_read hL hsat hHL hsz hsite (by simp [isUse]) rfl
      (by simp [siteMult, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups, Expr.eval,
        tmsg_ev hy, hc])
      (p := (inst 7).main TMsg.RST y + (inst 7).main TMsg.O y) (b := (inst 7).main TMsg.B y)
      (by simp [siteVals, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups, Expr.eval,
        tmsg_ev hy])
    exact ⟨q, hq, by simpa using hp, hb⟩
  · obtain ⟨q, hq, hp, hb⟩ := byte_read hL hsat hHL hsz hsite (by simp [isUse]) rfl
      (by simp [siteMult, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups, Expr.eval,
        tmsg_ev hy, hc])
      (p := (inst 7).main TMsg.RST y + (inst 7).main TMsg.O y + 9) (b := (inst 7).main TMsg.B y)
      (by simp [siteVals, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups, Expr.eval,
        tmsg_ev hy, StarkedAir.Sha256.eval_cst])
    exact ⟨q, hq, by simpa using hp, hb⟩

/-- **An incoming pending row reads the public pending byte at its position.** -/
theorem tmsg_pnd {y : ℕ} (hy : y < 2 ^ Ls 7) (hc : (inst 7).main TMsg.PND y = 1) :
    ∃ q : ℕ, q < 64 ∧ (inst 7).main TMsg.Y y = (q : F) ∧ (inst 7).main TMsg.B y = pub (H_PEND SHA_IN q) := by
  have hsite := site_mem hL (i := 7) (by decide) hy (k := 0) (by simp [segSys, comps, TMsg.tmsg, TMsg.lookups])
  exact pend_read hL hsat hHL hsz (j := 2) (by norm_num) hsite (by simp [isUse]) rfl
    (by simp [siteMult, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups, Expr.eval,
      tmsg_ev hy, hc])
    (by simp [siteVals, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups,
      tmsg_ev hy])

/-- **A tail row is the outgoing pending byte at its block offset.** -/
theorem tmsg_tail {y : ℕ} (hy : y < 2 ^ Ls 7) (hc : (inst 7).main TMsg.TAIL y = 1) :
    (inst 7).main TMsg.B y = pub (H_PEND SHA_OUT (y % 64)) := by
  have hsite := site_mem hL (i := 7) (by decide) hy (k := 5) (by simp [segSys, comps, TMsg.tmsg, TMsg.lookups])
  have hk64 : (TMsg.p TMsg.P_K64).eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y = ((y % 64 : ℕ) : F) :=
    ev_periodic (L := 64) (f := id) (by norm_num) rfl hy
  obtain ⟨q, hq, hp, hb⟩ := pend_read hL hsat hHL hsz (j := 3) (by norm_num) hsite (by simp [isUse]) rfl
    (by simp [siteMult, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups, Expr.eval,
      tmsg_ev hy, hc])
    (p := ((y % 64 : ℕ) : F)) (b := (inst 7).main TMsg.B y)
    (by simp only [siteVals, siteEval, siteLookup, segSys, comps, hL 7 (by decide), TMsg.tmsg, TMsg.lookups,
      List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.map_nil, tmsg_ev hy]
        exact congrArg (· :: _) hk64)
  have : y % 64 = q := natCast_inj_of_lt (by have := Nat.mod_lt y (by norm_num : 0 < 64); unfold P; omega)
    (by unfold P; omega) hp
  rw [hb, this]; rfl

/-! ### Blake2s words -/

omit hL hsat hHL hsz in
theorem b2w_ev {y c : ℕ} (hy : y < 2 ^ Ls 5) : (B2w.k c).eval (2 ^ Ls 5) B2w.preCols pub (inst 5).main y =
    (inst 5).main c y := by
  simp [B2w.k, StarkedAir.Sha256.eval_col, wrap_zero hy]

omit hL hsat hHL hsz in
theorem b2w_lookups : (∀ j < 4, B2w.lookups.getD j ⟨0, .const 0, []⟩ =
      ⟨REL_PB2I, .neg (B2w.k (B2w.N j)), [.add (B2w.k B2w.POS) (cst j), B2w.k (B2w.B j)]⟩) ∧
    (∀ j < 4, B2w.lookups.getD (4 + j) ⟨0, .const 0, []⟩ = ⟨Block.REL_BYTE, .neg (.sub (B2w.k (B2w.A j)) (B2w.k (B2w.N j))),
      [.sub (.add (B2w.k B2w.POS) (cst j)) B2w.plenIn, B2w.k (B2w.B j)]⟩) ∧
    (∀ j < 4, B2w.lookups.getD (8 + j) ⟨0, .const 0, []⟩ = ⟨REL_PB2O, .neg (.mul (B2w.k B2w.HELD) (B2w.k (B2w.A j))),
      [.add (.mul (cst 4) (B2w.p B2w.P_K)) (cst j), B2w.k (B2w.B j)]⟩) := by
  refine ⟨?_, ?_, ?_⟩ <;> (intro j hj; interval_cases j <;> rfl)

/-- **The Blake2s walker's reads**: incoming pending bytes, segment bytes, outgoing pending bytes. -/
theorem b2w_reads {r : ℕ} (hr : r < 2 ^ Ls 5) {j : ℕ} (hj : j < 4) :
    ((inst 5).main (B2w.N j) r = 1 → ∃ q : ℕ, q < 64 ∧ (inst 5).main B2w.POS r + (j : F) = (q : F) ∧
      (inst 5).main (B2w.B j) r = pub (H_PEND B2_IN q)) ∧
    ((inst 5).main (B2w.A j) r - (inst 5).main (B2w.N j) r = 1 → ∃ q, q < (pub PUB_LEN).val ∧
      (inst 5).main B2w.POS r + (j : F) - pub (H_PLEN B2_IN) = (q : F) ∧
      (inst 5).main (B2w.B j) r = (inst 0).main Block.BYTE q) ∧
    ((inst 5).main B2w.HELD r * (inst 5).main (B2w.A j) r = 1 → ∃ q : ℕ, q < 64 ∧
      4 * ((r % 16 : ℕ) : F) + (j : F) = (q : F) ∧ (inst 5).main (B2w.B j) r = pub (H_PEND B2_OUT q)) := by
  obtain ⟨l1, l2, l3⟩ := b2w_lookups
  have hpre : (segSys.comp 5).air.pre = B2w.preCols := rfl
  have hlen : (segSys.comp 5).lookups.length = 14 := rfl
  have hK : (B2w.p B2w.P_K).eval (2 ^ Ls 5) B2w.preCols pub (inst 5).main r = ((r % 16 : ℕ) : F) :=
    ev_periodic (L := 16) (f := id) (by norm_num) rfl hr
  refine ⟨fun hN => ?_, fun hA => ?_, fun hH => ?_⟩
  · have hsite := site_mem hL (i := 5) (by decide) hr (k := j) (by rw [hlen]; omega)
    have hsl : siteLookup segSys ((5, r, j) : Site) = _ := l1 j hj
    exact pend_read hL hsat hHL hsz (j := 0) (by norm_num) hsite (by simp [isUse]; omega)
      (by simp [siteRel, hsl, REL_PB2I])
      (by simp only [siteMult, hsl, siteEval, hpre, hL 5 (by decide), Expr.eval, b2w_ev hr, hN])
      (by simp [siteVals, hsl, siteEval, hpre, hL 5 (by decide), Expr.eval, b2w_ev hr,
        StarkedAir.Sha256.eval_cst])
  · have hsite := site_mem hL (i := 5) (by decide) hr (k := 4 + j) (by rw [hlen]; omega)
    have hsl : siteLookup segSys ((5, r, 4 + j) : Site) = _ := l2 j hj
    exact byte_read hL hsat hHL hsz hsite (by simp [isUse]; omega) (by simp [siteRel, hsl])
      (by simp only [siteMult, hsl, siteEval, hpre, hL 5 (by decide), Expr.eval, b2w_ev hr, hA])
      (by simp [siteVals, hsl, siteEval, hpre, hL 5 (by decide), Expr.eval, b2w_ev hr,
        StarkedAir.Sha256.eval_cst, B2w.plenIn])
  · have hsite := site_mem hL (i := 5) (by decide) hr (k := 8 + j) (by rw [hlen]; omega)
    have hsl : siteLookup segSys ((5, r, 8 + j) : Site) = _ := l3 j hj
    exact pend_read hL hsat hHL hsz (j := 1) (by norm_num) hsite (by simp [isUse]; omega)
      (by simp [siteRel, hsl, REL_PB2O])
      (by simp only [siteMult, hsl, siteEval, hpre, hL 5 (by decide), Expr.eval, b2w_ev hr, hH])
      (by simp [siteVals, hsl, siteEval, hpre, hL 5 (by decide), Expr.eval, b2w_ev hr,
        StarkedAir.Sha256.eval_cst, hK])

/-! ### Compressions -/

/-- **A Blake2s compression's word is its walker's**: a word row (`MU = 1`) reads `(BLKI, KR, WLO, WHI)`,
yielded by a word row of the walker as `(BLK, k, lo, hi)`. -/
theorem b2c_word {x : ℕ} (hx : x < 2 ^ Ls 6) (hmu : (inst 6).main B2c.MU x = 1) :
    ∃ y < 2 ^ Ls 5, (inst 5).main B2w.UW y ≠ 0 ∧ (inst 5).main B2w.BLK y = (inst 6).main B2c.BLKI x ∧
      ((y % 16 : ℕ) : F) = (B2c.p B2c.P_KR).eval (2 ^ Ls 6) B2c.preCols pub (inst 6).main x ∧
      (inst 5).main (B2w.B 0) y + 256 * (inst 5).main (B2w.B 1) y = (inst 6).main B2c.WLO x ∧
      (inst 5).main (B2w.B 2) y + 256 * (inst 5).main (B2w.B 3) y = (inst 6).main B2c.WHI x := by
  have hpre6 : (segSys.comp 6).air.pre = B2c.preCols := rfl
  have hpre5 : (segSys.comp 5).air.pre = B2w.preCols := rfl
  have hsite := site_mem hL (i := 6) (by decide) hx (k := 0) (by simp [segSys, comps, B2c.b2c, B2c.lookups])
  have hsl : siteLookup segSys ((6, x, 0) : Site) = ⟨REL_SB2W, .neg (B2c.k B2c.MU),
      [B2c.k B2c.BLKI, B2c.p B2c.P_KR, B2c.k B2c.WLO, B2c.k B2c.WHI]⟩ := rfl
  have ev6 : ∀ c, (B2c.k c).eval (2 ^ Ls 6) B2c.preCols pub (inst 6).main x = (inst 6).main c x := fun c => by
    simp [B2c.k, StarkedAir.Sha256.eval_col, wrap_zero hx]
  obtain ⟨i', y, k', hy, hyt, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse])
    (by simp only [siteMult, hsl, siteEval, hpre6, hL 6 (by decide), Expr.eval, ev6, hmu])
  rw [show siteRel segSys ((6, x, 0) : Site) = 30 from rfl] at hyt
  replace hyt := yt hyt; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyt
  obtain ⟨rfl, rfl⟩ : i' = 5 ∧ k' = 12 := by omega
  have hsl5 : siteLookup segSys ((5, y, 12) : Site) = ⟨REL_SB2W, B2w.k B2w.UW,
      [B2w.k B2w.BLK, B2w.p B2w.P_K, B2w.lo, B2w.hi]⟩ := rfl
  have hK : (B2w.p B2w.P_K).eval (2 ^ Ls 5) B2w.preCols pub (inst 5).main y = ((y % 16 : ℕ) : F) :=
    ev_periodic (L := 16) (f := id) (by norm_num) rfl hy
  refine ⟨y, hy, ?_, ?_⟩
  · simpa only [siteMult, hsl5, siteEval, hpre5, hL 5 (by decide), b2w_ev hy] using hsm
  · simp only [siteVals, hsl5, hsl, siteEval, hpre5, hpre6, hL 5 (by decide), hL 6 (by decide), List.map_cons,
      List.map_nil, b2w_ev hy, ev6, hK, B2w.lo, B2w.hi, Expr.eval, StarkedAir.Sha256.eval_cst,
      List.cons.injEq, and_true] at hsv
    obtain ⟨h1, h2, h3, h4⟩ := hsv
    exact ⟨h1, h2, by rw [← h3]; push_cast; ring, by rw [← h4]; push_cast; ring⟩

omit hL hsat hHL hsz in
theorem fin3_q : ∀ r < 88, Blake2s.preQ 15 r = true → r = 87 := by decide

/-- **The Blake2s end token**: the walker's `m − 1` is the last block of a compression whose period is
whole (its token is on the period's row 87). -/
theorem b2_end : ∃ x < 2 ^ Ls 6, x % 88 = 87 ∧ (inst 6).main B2c.LASTU x = 1 ∧
    (inst 6).main B2c.BLKI x = pub (H_NB B2_OUT) - pub (H_NB B2_IN) - 1 := by
  have h0 : 0 < 2 ^ Ls 5 := by positivity
  have hpre6 : (segSys.comp 6).air.pre = B2c.preCols := rfl
  have hpre5 : (segSys.comp 5).air.pre = B2w.preCols := rfl
  have hsite := site_mem hL (i := 5) (by decide) h0 (k := 13) (by simp [segSys, comps, B2w.b2w, B2w.lookups])
  have hsl : siteLookup segSys ((5, 0, 13) : Site) = ⟨REL_B2END, .neg B2w.first, [.sub B2w.m B2w.one]⟩ := rfl
  obtain ⟨i', x, k', hx, hyt, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse])
    (by simp [siteMult, hsl, siteEval, hpre5, hL 5 (by decide), Expr.eval, B2w.first, B2w.p, B2w.preCols,
      B2w.P_FIRST, PreCol.eval, wrap_zero h0, pre])
  rw [show siteRel segSys ((5, 0, 13) : Site) = 31 from rfl] at hyt
  replace hyt := yt hyt; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyt
  obtain ⟨rfl, rfl⟩ : i' = 6 ∧ k' = 1 := by omega
  have hsl6 : siteLookup segSys ((6, x, 1) : Site) = ⟨REL_B2END, .mul (B2c.k B2c.LASTU) (B2c.p (Blake2s.P_FIN 3)),
      [B2c.k B2c.BLKI]⟩ := rfl
  have ev6 : ∀ c, (B2c.k c).eval (2 ^ Ls 6) B2c.preCols pub (inst 6).main x = (inst 6).main c x := fun c => by
    simp [B2c.k, StarkedAir.Sha256.eval_col, wrap_zero hx]
  have hfin : (B2c.p (Blake2s.P_FIN 3)).eval (2 ^ Ls 6) B2c.preCols pub (inst 6).main x =
      ((if Blake2s.preQ 15 (x % 88) then 1 else 0 : ℕ) : F) := by
    refine ev_periodic (L := 88) (f := fun r => if Blake2s.preQ 15 r then 1 else 0) (by norm_num) ?_ hx
    rw [B2c.preCols, List.getD_append _ _ _ _ (by simp [Blake2s.preCols, Blake2s.P_FIN])]
    simp [Blake2s.preCols, Blake2s.P_FIN, Blake2s.PERIOD]
  have cs := b2c_sat hL hsat
  have bL := Block.air_bool (air := B2c.b2c.air) cs (c := B2c.LASTU) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (by
      simp only [B2c.flagC, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨B2c.LASTU, by simp, rfl⟩)))))))) hx
  simp only [siteMult, hsl6, siteEval, hpre6, hL 6 (by decide), Expr.eval, ev6, hfin] at hsm
  have hq : Blake2s.preQ 15 (x % 88) = true := by
    by_contra hc; simp [hc] at hsm
  have hL1 : (inst 6).main B2c.LASTU x = 1 := by
    rcases bL with h | h
    · simp [h] at hsm
    · exact h
  refine ⟨x, hx, fin3_q _ (Nat.mod_lt _ (by norm_num)) hq, hL1, ?_⟩
  simp only [siteVals, hsl6, hsl, siteEval, hpre5, hpre6, hL 5 (by decide), hL 6 (by decide), List.map_cons,
    List.map_nil, ev6, B2w.m, B2w.one, Expr.eval, StarkedAir.Sha256.eval_cst, Nat.cast_one, List.cons.injEq,
    and_true] at hsv
  exact hsv

/-- **A SHA-256 compression's word is the stream's**: a message row reads `(64·BLKI + 4·row − 16, W)`, yielded
by a stream row `y` with `NT·IS3 ≠ 0` as `(Y − 3, lo, hi)`. -/
theorem shac_word {x : ℕ} (hx : x < 2 ^ Ls 8)
    (hm : (Expr.mul (pre ShaC.MSGROW) (ShaC.k ShaC.USEW)).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main x = 1) :
    ∃ y < 2 ^ Ls 7, (Expr.mul (TMsg.k TMsg.NT) (TMsg.p TMsg.P_IS3)).eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y ≠ 0 ∧
      (Expr.sub (TMsg.k TMsg.Y) (cst 3)).eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y =
        (Expr.add (.mul (cst 64) (ShaC.k ShaC.BLKI)) (.sub (.mul (cst 4) (pre ShaC.ROWIDX)) (cst 16))).eval
          (2 ^ Ls 8) ShaC.preCols pub (inst 8).main x ∧
      TMsg.loW.eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y =
        (Sha256.limb Sha256.W 0).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main x ∧
      TMsg.hiW.eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main y =
        (Sha256.limb Sha256.W 1).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main x := by
  have hpre8 : (segSys.comp 8).air.pre = ShaC.preCols := rfl
  have hpre7 : (segSys.comp 7).air.pre = TMsg.preCols := rfl
  have hsite := site_mem hL (i := 8) (by decide) hx (k := 0) (by simp [segSys, comps, ShaC.shac, ShaC.lookups])
  have hsl : siteLookup segSys ((8, x, 0) : Site) = ShaC.lookups.getD 0 ⟨0, .const 0, []⟩ := rfl
  obtain ⟨i', y, k', hy, hyt, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse])
    (by simp only [siteMult, hsl, siteEval, hpre8, hL 8 (by decide), ShaC.lookups, List.getD_cons_zero, Expr.eval]
        simp only [Expr.eval] at hm; rw [hm])
  rw [show siteRel segSys ((8, x, 0) : Site) = 34 from rfl] at hyt
  replace hyt := yt hyt; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyt
  obtain ⟨rfl, rfl⟩ : i' = 7 ∧ k' = 6 := by omega
  have hsl7 : siteLookup segSys ((7, y, 6) : Site) = TMsg.lookups.getD 6 ⟨0, .const 0, []⟩ := rfl
  refine ⟨y, hy, ?_, ?_⟩
  · simpa only [siteMult, hsl7, siteEval, hpre7, hL 7 (by decide), TMsg.lookups, List.getD_cons_zero,
      List.getD_cons_succ] using hsm
  · simp only [siteVals, hsl7, hsl, siteEval, hpre7, hpre8, hL 7 (by decide), hL 8 (by decide), TMsg.lookups,
      ShaC.lookups, List.getD_cons_zero, List.getD_cons_succ, List.map_cons, List.map_nil, List.cons.injEq,
      and_true] at hsv
    exact hsv

/-- **The SHA-256 end token**: the stream's `m − 1` is the last block of a compression whose period is
whole (its token is on the period's row 71). -/
theorem sha_end : ∃ x < 2 ^ Ls 8, x % 72 = 71 ∧ (inst 8).main ShaC.LASTS x = 1 ∧
    (inst 8).main ShaC.BLKI x = pub (H_NB SHA_OUT) - pub (H_NB SHA_IN) - 1 := by
  have h0 : 0 < 2 ^ Ls 7 := by positivity
  have hpre8 : (segSys.comp 8).air.pre = ShaC.preCols := rfl
  have hpre7 : (segSys.comp 7).air.pre = TMsg.preCols := rfl
  have hsite := site_mem hL (i := 7) (by decide) h0 (k := 7) (by simp [segSys, comps, TMsg.tmsg, TMsg.lookups])
  have hsl : siteLookup segSys ((7, 0, 7) : Site) = ⟨REL_SHEND, .neg TMsg.first,
      [.sub (.sub (.pub (H_NB SHA_OUT)) (.pub (H_NB SHA_IN))) TMsg.one]⟩ := rfl
  obtain ⟨i', x, k', hx, hyt, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse])
    (by simp [siteMult, hsl, siteEval, hpre7, hL 7 (by decide), Expr.eval, TMsg.first, TMsg.p, TMsg.preCols,
      TMsg.P_FIRST, PreCol.eval, wrap_zero h0, pre])
  rw [show siteRel segSys ((7, 0, 7) : Site) = 35 from rfl] at hyt
  replace hyt := yt hyt; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hyt
  obtain ⟨rfl, rfl⟩ : i' = 8 ∧ k' = 1 := by omega
  have hsl8 : siteLookup segSys ((8, x, 1) : Site) = ⟨REL_SHEND, .mul (ShaC.k ShaC.LASTS) (pre ShaC.FIN3),
      [ShaC.k ShaC.BLKI]⟩ := rfl
  have ev8 : ∀ c, (ShaC.k c).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main x = (inst 8).main c x := fun c => by
    simp [ShaC.k, StarkedAir.Sha256.eval_col, wrap_zero hx]
  have hfin : (pre ShaC.FIN3).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main x =
      ((if x % 72 = 71 then 1 else 0 : ℕ) : F) :=
    ev_periodic (L := 72) (f := fun q => if q = 71 then 1 else 0) (by norm_num)
      (by simp [ShaC.preCols, ShaC.FIN3, Sha256.preCols, Block.Sha.per72, Sha256.PERIOD]) hx
  have cs := shac_sat hL hsat
  have bL := Block.air_bool (air := ShaC.shac.air) cs (c := ShaC.LASTS) (List.mem_append_left _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ (by
      simp only [ShaC.flagC, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨ShaC.LASTS, by simp, rfl⟩)))))) hx
  simp only [siteMult, hsl8, siteEval, hpre8, hL 8 (by decide), Expr.eval, ev8, hfin] at hsm
  have hq : x % 72 = 71 := by
    by_contra hc; simp [hc] at hsm
  have hL1 : (inst 8).main ShaC.LASTS x = 1 := by
    rcases bL with h | h
    · simp [h] at hsm
    · exact h
  refine ⟨x, hx, hq, hL1, ?_⟩
  simp only [siteVals, hsl8, hsl, siteEval, hpre7, hpre8, hL 7 (by decide), hL 8 (by decide), List.map_cons,
    List.map_nil, ev8, TMsg.one, Expr.eval, StarkedAir.Sha256.eval_cst, Nat.cast_one, List.cons.injEq,
    and_true] at hsv
  exact hsv

end System

end StarkedAir.SetPass
