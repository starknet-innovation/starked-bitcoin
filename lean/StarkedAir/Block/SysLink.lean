/-
**The block system's links (M3a.5).** The checks' read oracles, instantiated in the 9-component system
(context and walker reads are the block's bytes, range slots hold bytes, the walker's opcode facts are
the table's), and the tuples the components exchange: the coinbase's tuple, the block totals, the
sigop total, the commitment output and the finality cutoff.
-/
import StarkedAir.Block.ChkLink
import StarkedAir.Block.WMerkleLink
import StarkedAir.Block.TxWits
import StarkedAir.Block.WalkSound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : ∀ i < 15, Ls i ≤ 23)
include hL hsat hL24

/-- A byte position below the length is in the block, and its byte is the block's. -/
theorem read_R {r0 : ℕ} (hr0 : r0 < (pub 0).val) :
    r0 < (Fields.blockBytes (inst 0).main (pub 0).val).length ∧
    ((inst 0).main BYTE r0).val = ((Fields.blockBytes (inst 0).main (pub 0).val).getD r0 0).toNat := by
  have hb0 := hash_bytes_sat hL hsat
  have hP : 2 ^ Ls 0 < P := by have := rows_lt_P hL24 (i := 0) (by decide); omega
  have br := Block.bytes_rows (n := 2 ^ Ls 0) (pub := pub) (main := (inst 0).main) hb0 hP (by positivity)
  refine ⟨by rw [Fields.blockBytes_length]; exact hr0, ?_⟩
  rw [Fields.blockBytes_get hr0, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (br.1 r0 (by omega)).2]

/-- **A byte read, in terms of the block's bytes.** -/
theorem byte_read_R {i r k : ℕ} (hs0 : ((i, r, k) : Site) ∈ sites hashSys inst) (hi : i ≠ 0)
    (hrel : siteRel hashSys (i, r, k) = REL_BYTE) (hm : siteMult hashSys inst pub (i, r, k) = -1) {p b : F}
    (hv : siteVals hashSys inst pub (i, r, k) = [p, b]) :
    p.val < (Fields.blockBytes (inst 0).main (pub 0).val).length ∧
    b.val = ((Fields.blockBytes (inst 0).main (pub 0).val).getD p.val 0).toNat := by
  obtain ⟨r0, hr0, hp, hb⟩ := hash_read hL hsat hL24 hs0 hi hrel hm hv
  have hP : 2 ^ Ls 0 < P := by have := rows_lt_P hL24 (i := 0) (by decide); omega
  have h25 := (Block.bytes_rows (n := 2 ^ Ls 0) (pub := pub) (main := (inst 0).main) (hash_bytes_sat hL hsat) hP
    (by positivity)).2.1
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hpv : p.val = r0 := by rw [hp]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
  rw [hpv, hb]; exact read_R hL hsat hL24 hr0

/-- **Context reads** are the block's bytes. -/
theorem ctx_read : ∀ r < 2 ^ Ls 7, (inst 7).main Ctx.ACTR r = 1 →
    ((inst 7).main Ctx.ADDR r).val < (Fields.blockBytes (inst 0).main (pub 0).val).length ∧
    ((inst 7).main Ctx.B r).val = ((Fields.blockBytes (inst 0).main (pub 0).val).getD ((inst 7).main Ctx.ADDR r).val 0).toNat := by
  intro r hr ha
  have hs := site_mem hL (i := 7) (by decide) hr (k := 0) (by simp [hashSys, Ctx.ctx, Ctx.lookups])
  exact byte_read_R hL hsat hL24 hs (by decide) rfl
    (by simp [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr, ha])
    (by simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr])

/-- **Context range slots** hold bytes. -/
theorem ctx_ra : ∀ r < 2 ^ Ls 7, ((inst 7).main Ctx.RA r).val < 256 := by
  intro r hr
  have hs := site_mem hL (i := 7) (by decide) hr (k := 1) (by simp [hashSys, Ctx.ctx, Ctx.lookups])
  exact r8_lt hL hsat hL24 hs rfl rfl
    (by simp [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.one,
      StarkedAir.Sha256.eval_cst])
    (by simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr])

/-- **Walker reads** are the block's bytes. -/
theorem walk_read : ∀ r < 2 ^ Ls 6, (inst 6).main Walk.ACT r = 1 →
    ((inst 6).main Walk.POS r).val < (Fields.blockBytes (inst 0).main (pub 0).val).length ∧
    ((inst 6).main Walk.B r).val = ((Fields.blockBytes (inst 0).main (pub 0).val).getD ((inst 6).main Walk.POS r).val 0).toNat := by
  intro r hr ha
  have hs := site_mem hL (i := 6) (by decide) hr (k := 1) (by simp [hashSys, Walk.walk, Walk.lookups])
  exact byte_read_R hL hsat hL24 hs (by decide) rfl
    (by simp [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Expr.eval, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr, ha])
    (by simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr])

/-- **The walker's range use**: a pushed length's opcode minus 2 is a byte. -/
theorem walk_r8 : ∀ r < 2 ^ Ls 6, (inst 6).main Walk.TOPF r = 1 → ((inst 6).main Walk.B r - 2).val < 256 := by
  intro r hr ht
  have hs := site_mem hL (i := 6) (by decide) hr (k := 3) (by simp [hashSys, Walk.walk, Walk.lookups])
  exact r8_lt hL hsat hL24 hs rfl rfl
    (by simp [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Expr.eval, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr, ht])
    (by simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k, Expr.eval,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr])

/-- **The walker's opcode facts** are the opcode table's row for its byte. -/
theorem walk_opc : ∀ r < 2 ^ Ls 6, (inst 6).main Walk.OP r = 1 →
    (inst 6).main Walk.PN r = (Tables.pushN ((inst 6).main Walk.B r).val : F) ∧
    (inst 6).main Walk.K1 r = (Tables.isK 0x4c ((inst 6).main Walk.B r).val : F) ∧
    (inst 6).main Walk.K2 r = (Tables.isK 0x4d ((inst 6).main Walk.B r).val : F) ∧
    (inst 6).main Walk.K4 r = (Tables.isK 0x4e ((inst 6).main Walk.B r).val : F) ∧
    (inst 6).main Walk.SG r = (Tables.sigN ((inst 6).main Walk.B r).val : F) ∧
    (inst 6).main Walk.NZP r = (Tables.nzp ((inst 6).main Walk.B r).val : F) := by
  intro r hr ho
  have hs := site_mem hL (i := 6) (by decide) hr (k := 2) (by simp [hashSys, Walk.walk, Walk.lookups])
  have hm : siteMult hashSys inst pub (6, r, 2) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Expr.eval, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr, ho]
  obtain ⟨i', r', k', hr', hy, -, hsv⟩ := link hL hsat hL24 hs rfl hm
  have e : siteRel hashSys (6, r, 2) = 10 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 5 ∧ k' = 1 := by omega
  have h256 : r' % 256 < 256 := Nat.mod_lt _ (by norm_num)
  have ev : ∀ g : ℕ → ℕ, (Tables.tab g).eval (2 ^ Ls 5) r' = (g (r' % 256) : F) := by
    intro g
    simp [Tables.tab, PreCol.eval, List.getElem?_range h256]
  have hv5 : siteVals hashSys inst pub (5, r', 1) = [((r' % 256 : ℕ) : F), (Tables.pushN (r' % 256) : F),
      (Tables.isK 0x4c (r' % 256) : F), (Tables.isK 0x4d (r' % 256) : F), (Tables.isK 0x4e (r' % 256) : F),
      (Tables.sigN (r' % 256) : F), (Tables.nzp (r' % 256) : F)] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 5 (by decide), Tables.tables, Expr.eval,
      Tables.preCols, pre, wrap_zero hr', List.range_succ, ev]
  have hv6 : siteVals hashSys inst pub (6, r, 2) = [(inst 6).main Walk.B r, (inst 6).main Walk.PN r,
      (inst 6).main Walk.K1 r, (inst 6).main Walk.K2 r, (inst 6).main Walk.K4 r, (inst 6).main Walk.SG r,
      (inst 6).main Walk.NZP r] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]
  rw [hv5, hv6] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hsv
  have hb : ((inst 6).main Walk.B r).val = r' % 256 := by
    rw [← e0]; exact ZMod.val_natCast_of_lt (by unfold P; omega)
  rw [hb]
  exact ⟨e1.symm, e2.symm, e3.symm, e4.symm, e5.symm, e6.symm⟩

theorem ctx_site {r k : ℕ} (hr : r < 2 ^ Ls 7) (hk : k < 11) : ((7, r, k) : Site) ∈ sites hashSys inst :=
  site_mem hL (i := 7) (by decide) hr (by simp [hashSys, Ctx.ctx, Ctx.lookups]; omega)

theorem ctx_first_mult {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) : siteMult hashSys inst pub (7, 0, k) = -1 := by
  have hn0 : 0 < 2 ^ Ls 7 := by positivity
  rcases hk with rfl | rfl | rfl <;>
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
    simp [Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.ev_first (M := (inst 7).main) (pub := pub) hn0]

/-- **The coinbase tuple**: the context's `tx(0, A0, SEG0, W0, L0)` is the lock-time row of transaction 0. -/
theorem tx0_link : ∃ ρ < 2 ^ Ls 1, (inst 1).main Fields.K_LOCK ρ = 1 ∧ (inst 1).main Fields.TXI ρ = 0 ∧
    (inst 1).main Fields.TXA ρ = (inst 7).main Ctx.A0 0 ∧ (inst 1).main Fields.SEG ρ = (inst 7).main Ctx.SEG0 0 ∧
    (inst 1).main Fields.WST ρ = (inst 7).main Ctx.W0 0 ∧ (inst 1).main Fields.START ρ = (inst 7).main Ctx.L0 0 := by
  have hn0 : 0 < 2 ^ Ls 7 := by positivity
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 (ctx_site hL hsat hL24 hn0 (k := 2) (by norm_num)) rfl
    (ctx_first_mult hL hsat hL24 (Or.inl rfl))
  have e : siteRel hashSys (7, 0, 2) = 4 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 1 ∧ k' = 7 := by omega
  have fs := hash_fields_sat' hL hsat
  have hlm : (inst 1).main Fields.K_LOCK r' * (inst 1).main Fields.TXM r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Expr.eval,
      Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
  have hl : (inst 1).main Fields.K_LOCK r' = 1 := by
    rcases Fields.kind_bool fs (c := Fields.K_LOCK) (by simp [Fields.kinds]) hr' with h | h
    · rw [h, zero_mul] at hlm; exact absurd rfl hlm
    · exact h
  have h1 : siteVals hashSys inst pub (1, r', 7) = [(inst 1).main Fields.TXI r', (inst 1).main Fields.TXA r',
      (inst 1).main Fields.SEG r', (inst 1).main Fields.WST r', (inst 1).main Fields.START r'] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Fields.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr']
  have h7 : siteVals hashSys inst pub (7, 0, 2) = [0, (inst 7).main Ctx.A0 0, (inst 7).main Ctx.SEG0 0,
      (inst 7).main Ctx.W0 0, (inst 7).main Ctx.L0 0] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hn0]
  rw [h1, h7] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨r', hr', hl, hsv.1, hsv.2.1, hsv.2.2.1, hsv.2.2.2.1, hsv.2.2.2.2⟩

/-- **The block totals**: the context's `tot(WT, NSEG, HASC)` is the fields' last row. -/
theorem tot_link : (inst 7).main Ctx.WT 0 = (inst 1).main Fields.WB (2 ^ Ls 1 - 1) ∧
    (inst 7).main Ctx.NSEG 0 = (inst 1).main Fields.NS (2 ^ Ls 1 - 1) ∧
    (inst 7).main Ctx.HASC 0 = (inst 1).main Fields.HASC (2 ^ Ls 1 - 1) := by
  have hn0 : 0 < 2 ^ Ls 7 := by positivity
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 (ctx_site hL hsat hL24 hn0 (k := 3) (by norm_num)) rfl
    (ctx_first_mult hL hsat hL24 (Or.inr (Or.inl rfl)))
  have e : siteRel hashSys (7, 0, 3) = 12 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 1 ∧ k' = 31 := by omega
  have hlast : r' = 2 ^ Ls 1 - 1 := by
    by_contra h
    apply hsm
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Fields.ev_last (M := (inst 1).main) (pub := pub) hr',
      show r' + 1 < 2 ^ Ls 1 by omega]
  subst hlast
  have h1 : siteVals hashSys inst pub (1, 2 ^ Ls 1 - 1, 31) = [(inst 1).main Fields.WB (2 ^ Ls 1 - 1),
      (inst 1).main Fields.NS (2 ^ Ls 1 - 1), (inst 1).main Fields.HASC (2 ^ Ls 1 - 1)] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Fields.chkLookups,
      Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr']
  have h7 : siteVals hashSys inst pub (7, 0, 3) = [(inst 7).main Ctx.WT 0, (inst 7).main Ctx.NSEG 0,
      (inst 7).main Ctx.HASC 0] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hn0]
  rw [h1, h7] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨hsv.1.symm, hsv.2.1.symm, hsv.2.2.symm⟩

/-- **The sigop total**: the context's `SIGS` is the walker's last-row sum. -/
theorem sigops_link : (inst 7).main Ctx.SIGS 0 = (inst 6).main Walk.SUMS (2 ^ Ls 6 - 1) := by
  have hn0 : 0 < 2 ^ Ls 7 := by positivity
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 (ctx_site hL hsat hL24 hn0 (k := 4) (by norm_num)) rfl
    (ctx_first_mult hL hsat hL24 (Or.inr (Or.inr rfl)))
  have e : siteRel hashSys (7, 0, 4) = 15 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 6 ∧ k' = 4 := by omega
  have hlast : r' = 2 ^ Ls 6 - 1 := by
    by_contra h
    apply hsm
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide)]
    simp [Walk.walk, Walk.lookups, Walk.ev_last (M := (inst 6).main) (pub := pub) hr', show r' + 1 < 2 ^ Ls 6 by omega]
  subst hlast
  have h6 : siteVals hashSys inst pub (6, 2 ^ Ls 6 - 1, 4) = [(inst 6).main Walk.SUMS (2 ^ Ls 6 - 1)] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr']
  have h7 : siteVals hashSys inst pub (7, 0, 4) = [(inst 7).main Ctx.SIGS 0] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hn0]
  rw [h6, h7] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact hsv.symm

/-- **The commitment output**: with `HASC`, the context's `commit(CPOS, CLEN)` is a fields row's selected
output. -/
theorem commit_link (hh : (inst 7).main Ctx.HASC 0 = 1) :
    ∃ r < 2 ^ Ls 1, (inst 1).main Fields.ISC r ≠ 0 ∧ (inst 1).main Fields.SSC r = (inst 7).main Ctx.CPOS 0 ∧
      (inst 1).main Fields.VAL r = (inst 7).main Ctx.CLEN 0 := by
  have hn0 : 0 < 2 ^ Ls 7 := by positivity
  have hm : siteMult hashSys inst pub (7, 0, 5) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
    simp [Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.ev_first (M := (inst 7).main) (pub := pub) hn0,
      Ctx.ev_k (M := (inst 7).main) (pub := pub) hn0, hh]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 (ctx_site hL hsat hL24 hn0 (k := 5) (by norm_num)) rfl hm
  have e : siteRel hashSys (7, 0, 5) = 14 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 1 ∧ k' = 33 := by omega
  have hi : (inst 1).main Fields.ISC r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Fields.chkLookups,
      Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
  have h1 : siteVals hashSys inst pub (1, r', 33) = [(inst 1).main Fields.SSC r', (inst 1).main Fields.VAL r'] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Fields.chkLookups,
      Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr']
  have h7 : siteVals hashSys inst pub (7, 0, 5) = [(inst 7).main Ctx.CPOS 0, (inst 7).main Ctx.CLEN 0] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hn0]
  rw [h1, h7] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨r', hr', hi, hsv.1, hsv.2⟩

/-- **The finality cutoff**: the fields' `(CLO, CHI)` at row 0 is the context's. -/
theorem cutoff_link : (inst 1).main Fields.CLO 0 = (inst 7).main Ctx.CLO 0 ∧
    (inst 1).main Fields.CHI 0 = (inst 7).main Ctx.CHI 0 := by
  have hn0 : 0 < 2 ^ Ls 1 := by positivity
  have hn7 : 0 < 2 ^ Ls 7 := by positivity
  have hs := site_mem hL (i := 1) (by decide) hn0 (k := 32) (by
    simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups])
  have hm : siteMult hashSys inst pub (1, 0, 32) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval,
      Fields.ev_first (M := (inst 1).main) (pub := pub) hn0]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs rfl hm
  have e : siteRel hashSys (1, 0, 32) = 13 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 7 ∧ k' = 6 := by omega
  have h0 : r' = 0 := by
    by_contra h
    apply hsm
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
    simp [Ctx.ctx, Ctx.lookups, Ctx.ev_first (M := (inst 7).main) (pub := pub) hr', h]
  subst h0
  have h1 : siteVals hashSys inst pub (1, 0, 32) = [(inst 1).main Fields.CLO 0, (inst 1).main Fields.CHI 0] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Fields.chkLookups,
      Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hn0]
  have h7 : siteVals hashSys inst pub (7, 0, 6) = [(inst 7).main Ctx.CLO 0, (inst 7).main Ctx.CHI 0] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.k,
      StarkedAir.Sha256.eval_col, wrap_zero hn7]
  rw [h1, h7] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨hsv.1.symm, hsv.2.symm⟩

end System

end StarkedAir.Block
