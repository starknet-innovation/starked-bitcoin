/-
**The block commitment, system level (M3a.6, D-038).** In a satisfied 12-component block system, the
walker's reads are the two streams (the block's bytes and the undo bytes), each Blake2s period of a stream
compresses the stream's next block from the previous chaining value, a stream's last block outputs
`blake2s` of the stream, and the outer period's output, public inputs 9–24, is the commitment
`blake2s(blake2s(raw) ++ blake2s(undo))`.
-/
import StarkedAir.Block.BlockSetup
import StarkedAir.Block.B2MsgSound
import StarkedAir.Block.B2sSound
import StarkedAir.Spec.Blake2sBlocks
import StarkedAir.Spec.BlockCommit

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

/-- The undo bytes. -/
abbrev Ub (inst : ℕ → Inst) (pub : ℕ → F) : Spec.Block.Bytes := Fields.blockBytes (inst 9).main (pub 8).val

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 12, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 24)
include hL hsat hL24

theorem undo_bytes_sat : ∀ r < 2 ^ L, ∀ c ∈ Block.constraints,
    c.eval (2 ^ L) Block.preCols (pub ∘ Undo.remap) (inst 9).main r = 0 :=
  Undo.bytes_sat (hash_undo_sat hL hsat)

theorem undo_len : (pub 8).val ≤ 2 ^ L := by
  have hP : 2 ^ L < P := by have := hash_rows_lt_P hL24; omega
  have := (Block.bytes_rows (n := 2 ^ L) (pub := pub ∘ Undo.remap) (main := (inst 9).main) (undo_bytes_sat hL hsat hL24)
    hP (by positivity)).2.1
  simpa [Undo.remap, Undo.PUB_LEN] using this

/-- **Undo reads are the undo bytes.** A use of `REL_UBYTE` with multiplicity `−1` reads `(q, undo[q])`. -/
theorem undo_read {i r k : ℕ} (hs0 : ((i, r, k) : Site) ∈ sites hashSys inst) (huse : isUse i k = true)
    (hrel : siteRel hashSys (i, r, k) = Undo.REL_UBYTE) (hm : siteMult hashSys inst pub (i, r, k) = -1) {p b : F}
    (hv : siteVals hashSys inst pub (i, r, k) = [p, b]) :
    ∃ q, q < (pub 8).val ∧ p = (q : F) ∧ b.val = ((Ub inst pub).getD q 0).toNat := by
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs0 huse hm
  rw [hrel, show Undo.REL_UBYTE = 17 from rfl, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 9 ∧ k' = 0 := by omega
  have hP : 2 ^ L < P := by have := hash_rows_lt_P hL24; omega
  have ub := undo_bytes_sat hL hsat hL24
  have hm' : (Expr.mul (StarkedAir.Sha256.col ACTIVE) (StarkedAir.Sha256.col MULT)).eval (2 ^ L) preCols
      (pub ∘ Undo.remap) (inst 9).main r' ≠ 0 := by
    have e1 : ∀ pb : ℕ → F, (Expr.mul (StarkedAir.Sha256.col ACTIVE) (StarkedAir.Sha256.col MULT)).eval (2 ^ L) preCols pb
        (inst 9).main r' = (inst 9).main ACTIVE r' * (inst 9).main MULT r' := fun pb => by
      simp [Expr.eval, StarkedAir.Sha256.eval_col, wrap_zero hr']
    rw [e1]
    have e2 : siteMult hashSys inst pub (9, r', 0) = (inst 9).main ACTIVE r' * (inst 9).main MULT r' := by
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 9 (by decide)]
      simp [Undo.undo, e1]
    rwa [e2] at hsm
  obtain ⟨hlt, hvals⟩ := yield_sound ub hP hr' hm'
  have e : siteVals hashSys inst pub (9, r', 0) = [(r' : F), (inst 9).main BYTE r'] := by
    have : siteVals hashSys inst pub (9, r', 0) =
        [StarkedAir.Sha256.col POS, StarkedAir.Sha256.col BYTE].map (Expr.eval (2 ^ L) preCols (pub ∘ Undo.remap) (inst 9).main r') := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 9 (by decide), Undo.undo, StarkedAir.Sha256.eval_col]
    rw [this, hvals]
  rw [e, hv] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  have hlt8 : r' < (pub 8).val := by simpa [Undo.remap, Undo.PUB_LEN] using hlt
  refine ⟨r', hlt8, hsv.1.symm, ?_⟩
  have hb := (Block.bytes_rows (n := 2 ^ L) (pub := pub ∘ Undo.remap) (main := (inst 9).main) ub hP (by positivity)).1 r' hr'
  rw [← hsv.2, Fields.blockBytes_get hlt8, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hb.2]

omit hL hsat hL24 in
theorem rb_len : (Rb inst pub).length = (pub 0).val := Fields.blockBytes_length _ _
omit hL hsat hL24 in
theorem ub_len : (Ub inst pub).length = (pub 8).val := Fields.blockBytes_length _ _

theorem walker_site {r k : ℕ} (hr : r < 2 ^ L) (hk : k < 10) : ((10, r, k) : Site) ∈ sites hashSys inst :=
  site_mem hL (i := 10) (by decide) hr (by simp [hashSys, B2Msg.b2msg, B2Msg.lookups]; omega)

/-- **The walker's rows**, in the system: words of the block's bytes (stream 0) and of the undo bytes
(stream 1). -/
theorem walker_fact : ∀ r < 2 ^ L, (inst 10).main B2Msg.ON r = 1 → ∃ sv b : ℕ, (sv = 0 ∨ sv = 1) ∧
    (inst 10).main B2Msg.STR r = (sv : F) ∧ (inst 10).main B2Msg.BLK r = (b : F) ∧
    b < B2Msg.nbOf (if sv = 0 then Rb inst pub else Ub inst pub).length ∧
    (∀ j < 4, ((inst 10).main (B2Msg.B j) r).val =
      B2Msg.sbyte (if sv = 0 then Rb inst pub else Ub inst pub) (64 * b + 4 * (r % 16) + j)) ∧
    (r % 16 = 0 → ((inst 10).main B2Msg.LASTF r = 1 ↔ b + 1 = B2Msg.nbOf (if sv = 0 then Rb inst pub else Ub inst pub).length) ∧
      ((inst 10).main B2Msg.LASTF r = 0 ∨ (inst 10).main B2Msg.LASTF r = 1) ∧
      (inst 10).main B2Msg.T r = ((if b + 1 = B2Msg.nbOf (if sv = 0 then Rb inst pub else Ub inst pub).length then
        (if sv = 0 then Rb inst pub else Ub inst pub).length else 64 * (b + 1) : ℕ) : F)) := by
  have ws := hash_b2msg_sat hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  have hlen0 := len_R hL hsat hL24 (inst := inst) (pub := pub)
  have hlen1 := undo_len hL hsat hL24
  apply B2Msg.walker_sound ws (by positivity) (by omega) (Rb inst pub) (Ub inst pub)
    (by rw [rb_len, ZMod.natCast_zmod_val]) (by rw [ub_len, ZMod.natCast_zmod_val]; rfl)
    ⟨Fields.lt_P (by omega), by rw [ub_len]; exact Fields.lt_P (by omega)⟩
  intro r hr j hj ha
  have bstr := B2Msg.bool ws (c := B2Msg.STR) (by simp [B2Msg.boolCols]) hr
  have ev : ∀ c, (B2Msg.k c).eval (2 ^ L) B2Msg.preCols pub (inst 10).main r = (inst 10).main c r := fun c =>
    B2Msg.ev_k (pub := pub) (M := (inst 10).main) hr
  rcases bstr with h0 | h1
  · -- stream 0: the byte table
    have hm : siteMult hashSys inst pub (10, r, j) = -1 := by
      interval_cases j <;> simp [siteMult, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups,
        Expr.eval, ev, ha, h0, B2Msg.om, B2Msg.one, StarkedAir.Sha256.eval_cst]
    have hv : siteVals hashSys inst pub (10, r, j) = [(inst 10).main B2Msg.POS r + (j : F), (inst 10).main (B2Msg.B j) r] := by
      interval_cases j <;> simp [siteVals, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups,
        Expr.eval, ev, StarkedAir.Sha256.eval_cst, B2Msg.B]
    obtain ⟨r0, hr0, hp, hb⟩ := hash_read hL hsat hL24 (walker_site hL hsat hL24 hr (by omega)) (by decide)
      (by simp only [siteRel, siteLookup, hashSys]; interval_cases j <;> rfl) hm hv
    refine ⟨r0, hp, by rw [if_pos h0, rb_len]; exact hr0, ?_⟩
    rw [if_pos h0, hb]
    exact (read_R hL hsat hL24 hr0).2
  · -- stream 1: the undo table
    have hm : siteMult hashSys inst pub (10, r, 4 + j) = -1 := by
      interval_cases j <;> simp [siteMult, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups,
        Expr.eval, ev, ha, h1]
    have hv : siteVals hashSys inst pub (10, r, 4 + j) = [(inst 10).main B2Msg.POS r + (j : F), (inst 10).main (B2Msg.B j) r] := by
      interval_cases j <;> simp [siteVals, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups,
        Expr.eval, ev, StarkedAir.Sha256.eval_cst, B2Msg.B]
    obtain ⟨q, hq, hp, hb⟩ := undo_read hL hsat hL24 (walker_site hL hsat hL24 hr (by omega))
      (by simp [isUse]; omega) (by simp only [siteRel, siteLookup, hashSys]; interval_cases j <;> rfl) hm hv
    have hne : ¬ ((inst 10).main B2Msg.STR r = 0) := by rw [h1]; exact one_ne_zero
    refine ⟨q, hp, by rw [if_neg hne, ub_len]; exact hq, ?_⟩
    rw [if_neg hne, hb]; rfl

theorem b2s_site {r k : ℕ} (hr : r < 2 ^ L) (hk : k < 11) : ((11, r, k) : Site) ∈ sites hashSys inst :=
  site_mem hL (i := 11) (by decide) hr (by simp [hashSys, B2s.b2s, B2s.lookups]; omega)

/-- The stream a period hashes. -/
abbrev strm (inst : ℕ → Inst) (pub : ℕ → F) (sv : ℕ) : Spec.Block.Bytes := if sv = 0 then Rb inst pub else Ub inst pub

/-- **A stream period's block.** A period that hashes a stream block (`USEW`) reads its 16 message words
from the walker: they are the stream's words of its block, and its counter and last flag are Blake2s's. -/
theorem period_block {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ 2 ^ L) (hu : (inst 11).main B2s.USEW s = 1) :
    ∃ sv b : ℕ, (sv = 0 ∨ sv = 1) ∧ (inst 11).main B2s.STR s = (sv : F) ∧ (inst 11).main B2s.BLKI s = (b : F) ∧
      b < B2Msg.nbOf (strm inst pub sv).length ∧
      (∀ kk < 16, Blake2s.msgWord (inst 11).main kk s = Spec.Blake2s.wordAt (strm inst pub sv) b kk ∧
        ∀ h ≤ 1, ((inst 11).main (Blake2s.ML kk h) s).val < 65536) ∧
      ((inst 11).main B2s.LASTF s = 1 ↔ b + 1 = B2Msg.nbOf (strm inst pub sv).length) ∧
      ((inst 11).main B2s.LASTF s = 0 ∨ (inst 11).main B2s.LASTF s = 1) ∧
      (inst 11).main B2s.T s = ((if b + 1 = B2Msg.nbOf (strm inst pub sv).length then (strm inst pub sv).length
        else 64 * (b + 1) : ℕ) : F) := by
  have bs := hash_b2s_sat hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  have hsr : s < 2 ^ L := by omega
  have usew : ∀ q < 88, (inst 11).main B2s.USEW (s + q) = 1 := by
    intro q hq
    have e := B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC])
      (show s + q < 2 ^ L by omega)
    have e0 := B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC]) hsr
    simp only [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, B2s.ev_k (show s + q < 2 ^ L by omega),
      B2s.ev_k hsr] at e e0
    rw [e, B2s.per_const bs (X := B2s.NIL) (by simp [B2s.perConst]) hs q hq (by omega),
      B2s.outp_const (pub := pub) (M := (inst 11).main) hs hq (by omega), ← e0, hu]
  have ev : ∀ {r c}, r < 2 ^ L → (B2s.k c).eval (2 ^ L) B2s.preCols pub (inst 11).main r = (inst 11).main c r :=
    fun hr => B2s.ev_k (pub := pub) (M := (inst 11).main) hr
  have evw : ∀ {r c}, r < 2 ^ L → (B2Msg.k c).eval (2 ^ L) B2Msg.preCols pub (inst 10).main r = (inst 10).main c r :=
    fun hr => B2Msg.ev_k (pub := pub) (M := (inst 10).main) hr
  -- the block read (row `s`)
  have hmu2 : (inst 11).main B2s.MU2 s = 1 := by
    rw [B2s.defn bs (a := B2s.MU2) (e := .mul (B2s.k B2s.USEW) (B2s.p B2s.P_R0)) (by simp [B2s.flagC]) hsr]
    simp only [Expr.eval, ev hsr, B2s.ev_r0 (pub := pub) (M := (inst 11).main) hsr, hs, if_true, mul_one]
    simpa using usew 0 (by norm_num)
  have hm2 : siteMult hashSys inst pub (11, s, 2) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups, Expr.eval, ev hsr, hmu2]
  obtain ⟨i', r2, k', hr2, hy, hsm, hsv⟩ := link hL hsat hL24 (b2s_site hL hsat hL24 hsr (by norm_num)) rfl hm2
  have e19 : siteRel hashSys (11, s, 2) = 19 := rfl
  rw [e19, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 10 ∧ k' = 9 := by omega
  have hsm' : (inst 10).main B2Msg.ON r2 * (B2Msg.p B2Msg.P_K0).eval (2 ^ L) B2Msg.preCols pub (inst 10).main r2 ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups, Expr.eval, evw hr2]
      using hsm
  rw [B2Msg.ev_K0 hr2] at hsm'
  have hon2 : (inst 10).main B2Msg.ON r2 = 1 := by
    rcases B2Msg.bool (hash_b2msg_sat hL hsat) (c := B2Msg.ON) (by simp [B2Msg.boolCols]) hr2 with h | h
    · rw [h, zero_mul] at hsm'; exact absurd rfl hsm'
    · exact h
  have hk2 : r2 % 16 = 0 := by by_contra h; rw [if_neg h, mul_zero] at hsm'; exact hsm' rfl
  have hv2 : siteVals hashSys inst pub (10, r2, 9) = [(inst 10).main B2Msg.STR r2, (inst 10).main B2Msg.BLK r2,
      (inst 10).main B2Msg.LASTF r2, (inst 10).main B2Msg.T r2] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups, evw hr2]
  have hv11 : siteVals hashSys inst pub (11, s, 2) = [(inst 11).main B2s.STR s, (inst 11).main B2s.BLKI s,
      (inst 11).main B2s.LASTF s, (inst 11).main B2s.T s] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups, ev hsr]
  rw [hv2, hv11] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨es, eb, el, et⟩ := hsv
  obtain ⟨sv, b, hsv01, hstr, hblk, hb, hbytes, hk0⟩ := walker_fact hL hsat hL24 r2 hr2 hon2
  obtain ⟨hlast, hlb, ht⟩ := hk0 hk2
  refine ⟨sv, b, hsv01, by rw [← es, hstr], by rw [← eb, hblk], hb, fun kk hkk => ?_, by rw [← el]; exact hlast,
    by rw [← el]; exact hlb, by rw [← et, ht]⟩
  -- the words (rows `s + kk`)
  have hrk : s + kk < 2 ^ L := by omega
  have hmu0 : (inst 11).main B2s.MU0 (s + kk) = 1 := by
    rw [B2s.defn bs (a := B2s.MU0) (e := .mul (B2s.k B2s.USEW) (B2s.p B2s.P_LT16)) (by simp [B2s.flagC]) hrk]
    simp only [Expr.eval, ev hrk, B2s.ev_lt16 (pub := pub) (M := (inst 11).main) hrk,
      show (s + kk) % 88 < 16 by omega, if_true, mul_one]
    exact usew kk (by omega)
  have hm0 : siteMult hashSys inst pub (11, s + kk, 0) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups, Expr.eval, ev hrk, hmu0]
  obtain ⟨i', r1, k', hr1, hy, hsm, hsv⟩ := link hL hsat hL24 (b2s_site hL hsat hL24 hrk (by norm_num)) rfl hm0
  have e18 : siteRel hashSys (11, s + kk, 0) = 18 := rfl
  rw [e18, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 10 ∧ k' = 8 := by omega
  have hon1 : (inst 10).main B2Msg.ON r1 = 1 := by
    have : (inst 10).main B2Msg.ON r1 ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups, evw hr1] using hsm
    exact (B2Msg.bool (hash_b2msg_sat hL hsat) (c := B2Msg.ON) (by simp [B2Msg.boolCols]) hr1).resolve_left this
  have hv1 : siteVals hashSys inst pub (10, r1, 8) = [(inst 10).main B2Msg.STR r1, (inst 10).main B2Msg.BLK r1,
      ((r1 % 16 : ℕ) : F), (inst 10).main (B2Msg.B 0) r1 + 256 * (inst 10).main (B2Msg.B 1) r1,
      (inst 10).main (B2Msg.B 2) r1 + 256 * (inst 10).main (B2Msg.B 3) r1] := by
    have hK := B2Msg.ev_K (pub := pub) (M := (inst 10).main) hr1
    simp [siteVals, siteEval, siteLookup, hashSys, hL 10 (by decide), B2Msg.b2msg, B2Msg.lookups, evw hr1, B2Msg.lo,
      B2Msg.hi, Expr.eval, StarkedAir.Sha256.eval_cst, hK]
  have hKR : (B2s.p B2s.P_KR).eval (2 ^ L) B2s.preCols pub (inst 11).main (s + kk) = ((kk : ℕ) : F) := by
    rw [B2s.p, B2s.ev_per88 (f := fun r => if r < 16 then r else 0) (by simp [B2s.preCols, B2s.P_KR, Blake2s.preCols]) hrk,
      show (s + kk) % 88 = kk by omega, if_pos hkk]
  have hv0 : siteVals hashSys inst pub (11, s + kk, 0) = [(inst 11).main B2s.STR (s + kk), (inst 11).main B2s.BLKI (s + kk),
      ((kk : ℕ) : F), (inst 11).main B2s.WLO (s + kk), (inst 11).main B2s.WHI (s + kk)] := by
    have : siteVals hashSys inst pub (11, s + kk, 0) = [B2s.k B2s.STR, B2s.k B2s.BLKI, B2s.p B2s.P_KR, B2s.k B2s.WLO,
        B2s.k B2s.WHI].map (Expr.eval (2 ^ L) B2s.preCols pub (inst 11).main (s + kk)) := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups]
    rw [this]; simp [ev hrk, hKR]
  rw [hv1, hv0] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨es1, eb1, ek1, elo, ehi⟩ := hsv
  obtain ⟨sv', b', hsv01', hstr', hblk', hb', hbytes', -⟩ := walker_fact hL hsat hL24 r1 hr1 hon1
  rw [B2s.per_const bs (X := B2s.STR) (by simp [B2s.perConst]) hs kk (by omega) hrk, ← es, hstr] at es1
  rw [B2s.per_const bs (X := B2s.BLKI) (by simp [B2s.perConst]) hs kk (by omega) hrk, ← eb, hblk] at eb1
  rw [hstr'] at es1; rw [hblk'] at eb1
  have hnbp : ∀ x y, x < B2Msg.nbOf (strm inst pub y).length → x < P := by
    intro x y hx
    have : (strm inst pub y).length ≤ 2 ^ L := by
      simp only [strm]; split_ifs
      · exact len_R hL hsat hL24
      · rw [ub_len]; exact undo_len hL hsat hL24
    unfold B2Msg.nbOf at hx; unfold P; omega
  have esv : sv' = sv := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) es1
  subst esv
  have eb' : b' = b := natCast_inj_of_lt (hnbp b' sv' hb') (hnbp b sv' hb) eb1
  subst eb'
  have ekk : r1 % 16 = kk := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) ek1
  obtain ⟨wlo, whi⟩ := B2s.msg_word bs hs hsn hkk
  have byv : ∀ j < 4, ((inst 10).main (B2Msg.B j) r1).val < 256 := by
    intro j hj; rw [hbytes' j hj]; exact UInt8.toNat_lt _
  have v2 : ∀ x y : F, x.val < 256 → y.val < 256 → (x + 256 * y).val = x.val + 256 * y.val := by
    intro x y hx hy
    have hlt : x.val + 256 * y.val < P := lt_of_lt_of_le (show x.val + 256 * y.val < 65536 by omega) (by unfold P; norm_num)
    rw [show x + 256 * y = ((x.val + 256 * y.val : ℕ) : F) by push_cast; simp only [ZMod.natCast_zmod_val]]
    exact ZMod.val_natCast_of_lt hlt
  refine ⟨?_, fun h hh => ?_⟩
  swap
  · interval_cases h
    · rw [← wlo, ← elo, v2 _ _ (byv 0 (by norm_num)) (byv 1 (by norm_num))]
      have := byv 0 (by norm_num); have := byv 1 (by norm_num); omega
    · rw [← whi, ← ehi, v2 _ _ (byv 2 (by norm_num)) (byv 3 (by norm_num))]
      have := byv 2 (by norm_num); have := byv 3 (by norm_num); omega
  unfold Blake2s.msgWord Spec.Blake2s.wordAt
  rw [← wlo, ← whi, ← elo, ← ehi, v2 _ _ (byv 0 (by norm_num)) (byv 1 (by norm_num)),
    v2 _ _ (byv 2 (by norm_num)) (byv 3 (by norm_num)),
    hbytes' 0 (by norm_num), hbytes' 1 (by norm_num), hbytes' 2 (by norm_num), hbytes' 3 (by norm_num), ekk]
  simp only [B2Msg.sbyte, strm]
  congr 1; ring

/-- **A continuing period's predecessor** is a stream period of the same stream, one block earlier. -/
theorem prev_period {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ 2 ^ L) (h88 : 88 ≤ s) (hc : (inst 11).main B2s.CHN s = 1) :
    176 ≤ s ∧ (inst 11).main B2s.USEW (s - 88) = 1 ∧ (inst 11).main B2s.STR (s - 88) = (inst 11).main B2s.STR s ∧
      (inst 11).main B2s.BLKI s = (inst 11).main B2s.BLKI (s - 88) + 1 := by
  have bs := hash_b2s_sat hL hsat
  have hsr : s < 2 ^ L := by omega
  have hq : wrap (2 ^ L) s (-88) = s - 88 := by
    rw [show (-88 : ℤ) = -((88 : ℕ) : ℤ) by simp, StarkedAir.Sha256.wrap_back h88 hsr]
  have kq : ∀ c, (B2s.kq c).eval (2 ^ L) B2s.preCols pub (inst 11).main s = (inst 11).main c (s - 88) := by
    intro c; simp [B2s.kq, StarkedAir.Sha256.eval_col, hq]
  have hr0 : (B2s.p B2s.P_R0).eval (2 ^ L) B2s.preCols pub (inst 11).main s = 1 := by
    rw [B2s.ev_r0 (pub := pub) (M := (inst 11).main) hsr, if_pos hs]
  have c := fun (e : Expr) (h : e ∈ B2s.chainC) => B2s.sat bs (B2s.mem_chain h) hsr
  have c1 := c (.mul (B2s.p B2s.P_R0) (.mul (B2s.k B2s.CHN) (.sub (B2s.k B2s.STR) (B2s.kq B2s.STR)))) (by simp [B2s.chainC])
  have c2 := c (.mul (B2s.p B2s.P_R0) (.mul (B2s.k B2s.CHN) (.sub (.sub (B2s.k B2s.BLKI) (B2s.kq B2s.BLKI)) B2s.one)))
    (by simp [B2s.chainC])
  have c3 := c (.mul (B2s.p B2s.P_R0) (.mul (B2s.k B2s.CHN) (B2s.kq B2s.NIL))) (by simp [B2s.chainC])
  have c4 := c (.mul (B2s.p B2s.P_R0) (.mul (B2s.k B2s.CHN) (B2s.kq B2s.OQ))) (by simp [B2s.chainC])
  simp only [Expr.eval, hr0, one_mul, B2s.ev_k hsr, hc, kq, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one,
    sub_eq_zero] at c1 c2 c3 c4
  have hs' : s - 88 < 2 ^ L := by omega
  have hoq := B2s.defn bs (a := B2s.OQ) (e := B2s.outp) (by simp [B2s.flagC]) hs'
  rw [B2s.ev_outp (pub := pub) (M := (inst 11).main) hs', c4] at hoq
  have h176 : 176 ≤ s := by
    by_contra h
    rw [if_pos (by omega)] at hoq; exact zero_ne_one hoq
  refine ⟨h176, ?_, c1.symm, by linear_combination c2⟩
  rw [B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC]) hs']
  simp only [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, B2s.ev_k hs', c3,
    B2s.ev_outp (pub := pub) (M := (inst 11).main) hs', if_neg (show ¬ (s - 88 < 88) by omega)]
  ring

/-- A stream period after the outer one: not the outer, not unused. -/
theorem usew_facts {s : ℕ} (hsn : s + 88 ≤ 2 ^ L) (hu : (inst 11).main B2s.USEW s = 1) :
    88 ≤ s ∧ (inst 11).main B2s.NIL s = 0 ∧
      ((inst 11).main B2s.CHN s = 1 - (inst 11).main B2s.FST s) := by
  have bs := hash_b2s_sat hL hsat
  have hsr : s < 2 ^ L := by omega
  have e := B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC]) hsr
  simp only [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, B2s.ev_k hsr,
    B2s.ev_outp (pub := pub) (M := (inst 11).main) hsr] at e
  rw [hu] at e
  have h88 : 88 ≤ s := by
    by_contra h; rw [if_pos (by omega), sub_self, mul_zero] at e; exact one_ne_zero e
  rw [if_neg (by omega), sub_zero, mul_one] at e
  have hnil : (inst 11).main B2s.NIL s = 0 := by linear_combination e
  refine ⟨h88, hnil, ?_⟩
  rw [B2s.defn bs (a := B2s.CHN) (e := .mul (B2s.om (.add (B2s.k B2s.FST) (B2s.k B2s.NIL))) (B2s.om B2s.outp))
    (by simp [B2s.flagC]) hsr]
  simp only [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, B2s.ev_k hsr, hnil,
    B2s.ev_outp (pub := pub) (M := (inst 11).main) hsr, if_neg (show ¬ (s < 88) by omega)]
  ring

theorem strm_len_le (sv : ℕ) : (strm inst pub sv).length ≤ 2 ^ L := by
  simp only [strm]; split_ifs
  · exact len_R hL hsat hL24
  · rw [ub_len]; exact undo_len hL hsat hL24

/-- **The chain.** A stream period hashing block `b` starts from the spec's chaining value after `b` blocks. -/
theorem chain_state : ∀ b sv : ℕ, b + 1 < P → ∀ s, s % 88 = 0 → s + 88 ≤ 2 ^ L → (inst 11).main B2s.USEW s = 1 →
    (inst 11).main B2s.STR s = (sv : F) → (inst 11).main B2s.BLKI s = (b : F) → (sv = 0 ∨ sv = 1) →
    ∀ i < 8, Blake2s.diagSlot (inst 11).main s i = Spec.Blake2s.chainS Spec.Blake2s.h0 0 (strm inst pub sv) b i := by
  have bs := hash_b2s_sat hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  intro b
  induction b with
  | zero =>
    intro sv _ s hs hsn hu hstr hblk hsv i hi
    obtain ⟨h88, hnil, hchn⟩ := usew_facts hL hsat hL24 hsn hu
    rcases B2s.bool_flag bs (c := B2s.FST) (by simp) (show s < 2 ^ L by omega) with f0 | f1
    · exfalso
      rw [f0, sub_zero] at hchn
      obtain ⟨h176, hu', hstr', hblk'⟩ := prev_period hL hsat hL24 hs hsn h88 hchn
      obtain ⟨sv2, b2, -, -, hb2, hlt2, -⟩ := period_block hL hsat hL24 (s := s - 88) (by omega) (by omega) hu'
      rw [hblk, hb2] at hblk'
      have : ((b2 + 1 : ℕ) : F) = ((0 : ℕ) : F) := by push_cast; linear_combination -hblk'
      have hl2 := strm_len_le hL hsat hL24 sv2 (inst := inst) (pub := pub)
      have hb2 : b2 + 1 ≤ 2 ^ 30 := by unfold B2Msg.nbOf at hlt2; omega
      have := natCast_inj_of_lt (Fields.lt_P hb2) (Fields.lt_P (by norm_num)) this
      omega
    · have := B2s.h_first bs hs hsn (by
        rw [f1, B2s.ev_outp (pub := pub) (M := (inst 11).main) (show s < 2 ^ L by omega), if_neg (by omega), add_zero]
        exact one_ne_zero) i hi
      rw [this]; rfl
  | succ b ih =>
    intro sv hbP s hs hsn hu hstr hblk hsv i hi
    obtain ⟨h88, hnil, hchn⟩ := usew_facts hL hsat hL24 hsn hu
    have f0 : (inst 11).main B2s.FST s = 0 := by
      have := B2s.sat bs (B2s.mem_chain (c := .mul (B2s.p B2s.P_R0) (.mul (B2s.k B2s.FST) (B2s.k B2s.BLKI)))
        (by simp [B2s.chainC])) (show s < 2 ^ L by omega)
      simp only [Expr.eval, B2s.ev_r0 (pub := pub) (M := (inst 11).main) (show s < 2 ^ L by omega), if_pos hs, one_mul,
        B2s.ev_k (show s < 2 ^ L by omega), hblk] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exfalso
        have := natCast_inj_of_lt (a := b + 1) (b := 0) (by omega) (by unfold P; norm_num) (by simpa using h)
        omega
    rw [f0, sub_zero] at hchn
    obtain ⟨h176, hu', hstr', hblk'⟩ := prev_period hL hsat hL24 hs hsn h88 hchn
    have hs' : (s - 88) % 88 = 0 := by omega
    have hsn' : s - 88 + 88 ≤ 2 ^ L := by omega
    -- the previous period: block `b` of the same stream
    obtain ⟨sv2, b2, hsv2, hstr2, hblk2, hlt2, hwords2, hlast2, hlb2, ht2⟩ := period_block hL hsat hL24 hs' hsn' hu'
    obtain ⟨sv1, b1, hsv1, hstr1, hblk1, hlt1, -, -, -, -⟩ := period_block hL hsat hL24 hs hsn hu
    have e1 : sv = sv1 := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) (by rw [← hstr1, hstr])
    have e2 : sv = sv2 := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) (by rw [← hstr2, hstr', hstr])
    subst e1; subst e2
    have hlen := strm_len_le hL hsat hL24 sv (inst := inst) (pub := pub)
    have eb1 : b + 1 = b1 := natCast_inj_of_lt (by omega)
      (Fields.lt_P (by unfold B2Msg.nbOf at hlt1; omega)) (by rw [← hblk1, hblk])
    have eb2 : b = b2 := by
      have : ((b2 + 1 : ℕ) : F) = ((b + 1 : ℕ) : F) := by push_cast; rw [← hblk2, ← hblk', hblk]; push_cast; ring
      have := natCast_inj_of_lt (Fields.lt_P (by unfold B2Msg.nbOf at hlt2; omega))
        (Fields.lt_P (by unfold B2Msg.nbOf at hlt1; omega)) this
      omega
    subst eb1; subst eb2
    have ihs := ih sv (by omega) (s - 88) hs' hsn' hu' hstr2 hblk2 hsv
    -- not the last block, so the counter is `64·(b + 1)` and the flag is off
    have hnl : ¬ (b + 1 = B2Msg.nbOf (strm inst pub sv).length) := by omega
    have hl0 : (inst 11).main B2s.LASTF (s - 88) = 0 := by
      rcases hlb2 with h | h
      · exact h
      · exact absurd (hlast2.mp h) hnl
    obtain ⟨_, hnil2, -⟩ := usew_facts hL hsat hL24 hsn' hu'
    obtain ⟨htv, hfv⟩ := B2s.tf bs hs' (by omega) hnil2
    have htv' : (inst 11).main B2s.TV (s - 88) = (inst 11).main B2s.T (s - 88) := by
      rw [B2s.defn bs (a := B2s.TV) (e := .add (.mul B2s.outp (StarkedAir.Sha256.cst 64)) (.mul (B2s.om B2s.outp) (B2s.k B2s.T)))
        (by simp [B2s.flagC]) (show s - 88 < 2 ^ L by omega)]
      simp [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, B2s.ev_k (show s - 88 < 2 ^ L by omega),
        B2s.ev_outp (pub := pub) (M := (inst 11).main) (show s - 88 < 2 ^ L by omega), show ¬ (s - 88 < 88) by omega]
    have hfv' : (inst 11).main B2s.FV (s - 88) = 0 := by
      rw [B2s.defn bs (a := B2s.FV) (e := .add B2s.outp (.mul (B2s.om B2s.outp) (B2s.k B2s.LASTF)))
        (by simp [B2s.flagC]) (show s - 88 < 2 ^ L by omega)]
      simp [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, B2s.ev_k (show s - 88 < 2 ^ L by omega),
        B2s.ev_outp (pub := pub) (M := (inst 11).main) (show s - 88 < 2 ^ L by omega), show ¬ (s - 88 < 88) by omega, hl0]
    have hinT : Blake2s.inT (inst 11).main (s - 88) = 64 * (b + 1) := by
      rw [htv, htv', ht2, if_neg hnl, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold B2Msg.nbOf at hlt1; omega))]
    have hfb : Blake2s.fBit (inst 11).main (s - 88) = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      rw [hfv.mp h] at hfv'; exact one_ne_zero hfv'
    have hm : ∀ kk < 16, ∀ h ≤ 1, ((inst 11).main (Blake2s.ML kk h) (s - 88)).val < 65536 := fun kk hkk =>
      (hwords2 kk hkk).2
    have hcomp := B2s.period_compress bs hs' (by omega) hm
    rw [B2s.h_chain bs hs hsn h88 hchn i hi, ← hcomp i hi, hinT, hfb]
    simp only [Spec.Blake2s.chainS, if_pos hi, Nat.zero_add]
    exact Spec.Blake2s.compress_congr ihs (fun kk hkk => (hwords2 kk hkk).1) _ _ i hi

/-- **A stream's last block outputs its Blake2s hash** (as chaining words). -/
theorem last_digest {s sv : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ 2 ^ L) (hu : (inst 11).main B2s.USEW s = 1)
    (hl : (inst 11).main B2s.LASTF s = 1) (hstr : (inst 11).main B2s.STR s = (sv : F)) (hsv : sv = 0 ∨ sv = 1) :
    ∀ i < 8, Blake2s.outWord (inst 11).main s i = Spec.Blake2s.hashBlocks Spec.Blake2s.h0 0 (strm inst pub sv) i := by
  have bs := hash_b2s_sat hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  obtain ⟨sv1, b, hsv1, hstr1, hblk, hlt, hwords, hlast, -, ht⟩ := period_block hL hsat hL24 hs hsn hu
  have e1 : sv = sv1 := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) (by rw [← hstr1, hstr])
  subst e1
  have hlen := strm_len_le hL hsat hL24 sv (inst := inst) (pub := pub)
  have h24' := h24
  have hb : b + 1 = B2Msg.nbOf (strm inst pub sv).length := hlast.mp hl
  have hch := chain_state hL hsat hL24 b sv (by unfold B2Msg.nbOf at hb; unfold P; omega) s hs hsn hu hstr hblk hsv
  obtain ⟨-, hnil, -⟩ := usew_facts hL hsat hL24 hsn hu
  obtain ⟨htv, hfv⟩ := B2s.tf bs hs hsn hnil
  have hsr : s < 2 ^ L := by omega
  have h88 := (usew_facts hL hsat hL24 hsn hu).1
  have htv' : (inst 11).main B2s.TV s = (inst 11).main B2s.T s := by
    rw [B2s.defn bs (a := B2s.TV) (e := .add (.mul B2s.outp (StarkedAir.Sha256.cst 64)) (.mul (B2s.om B2s.outp) (B2s.k B2s.T)))
      (by simp [B2s.flagC]) hsr]
    simp [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, B2s.ev_k hsr,
      B2s.ev_outp (pub := pub) (M := (inst 11).main) hsr, show ¬ (s < 88) by omega]
  have hfv' : (inst 11).main B2s.FV s = 1 := by
    rw [B2s.defn bs (a := B2s.FV) (e := .add B2s.outp (.mul (B2s.om B2s.outp) (B2s.k B2s.LASTF))) (by simp [B2s.flagC]) hsr]
    simp [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, B2s.ev_k hsr,
      B2s.ev_outp (pub := pub) (M := (inst 11).main) hsr, show ¬ (s < 88) by omega, hl]
  have hinT : Blake2s.inT (inst 11).main s = (strm inst pub sv).length := by
    rw [htv, htv', ht, if_pos hb, ZMod.val_natCast_of_lt (Fields.lt_P (by omega))]
  have hfb : Blake2s.fBit (inst 11).main s = true := hfv.mpr hfv'
  have hcomp := B2s.period_compress bs hs hsn (fun kk hkk => (hwords kk hkk).2)
  intro i hi
  rw [← hcomp i hi, hinT, hfb, Spec.Blake2s.hashBlocks_eq b _ 0 _ (by unfold B2Msg.nbOf at hb; omega)
    (by unfold B2Msg.nbOf at hb; omega) i hi, Nat.zero_add]
  exact Spec.Blake2s.compress_congr hch (fun kk hkk => (hwords kk hkk).1) _ _ i hi

omit hL hsat hL24 in
theorem pow2_mod88 : ∀ L : ℕ, 2 ^ L % 88 ≤ 80 := by
  have closed : ∀ x ∈ ({1, 2, 4, 8, 16, 32, 64, 40, 80, 72, 56, 24, 48} : Finset ℕ),
      (x * 2) % 88 ∈ ({1, 2, 4, 8, 16, 32, 64, 40, 80, 72, 56, 24, 48} : Finset ℕ) := by decide
  have key : ∀ L : ℕ, 2 ^ L % 88 ∈ ({1, 2, 4, 8, 16, 32, 64, 40, 80, 72, 56, 24, 48} : Finset ℕ) := by
    intro L
    induction L with
    | zero => decide
    | succ L ih =>
      rw [pow_succ, Nat.mul_mod, Nat.mod_eq_of_lt (show 2 < 88 by norm_num)]
      exact closed _ ih
  intro L
  have := key L
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

omit hsat hL24 in
/-- A row at a period's final rows lies in a full period. -/
theorem full_period {r : ℕ} (hr : r < 2 ^ L) (h84 : 84 ≤ r % 88) : r - r % 88 + 88 ≤ 2 ^ L := by
  have := pow2_mod88 L
  by_contra hc
  have h1 : 2 ^ L - (r - r % 88) < 88 := by omega
  have h2 : (r - r % 88) % 88 = 0 := by omega
  have h3 : 2 ^ L % 88 = 2 ^ L - (r - r % 88) := by
    have : 2 ^ L = (r - r % 88) + (2 ^ L - (r - r % 88)) := by omega
    rw [this, Nat.add_mod, h2, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h1]
    omega
  omega

/-- The word index a digest yield carries: word `j` from `W0`, word `bidx j` from `W1`. -/
def widx (k : ℕ) : ℕ := if (k - 3) % 2 = 0 then (k - 3) / 2 else B2s.bidx ((k - 3) / 2)

/-- A stream's Blake2s chaining words. -/
abbrev hwords (inst : ℕ → Inst) (pub : ℕ → F) (sv : ℕ) : ℕ → Spec.Blake2s.Word :=
  Spec.Blake2s.hashBlocks Spec.Blake2s.h0 0 (strm inst pub sv)

omit hsat hL24 in
theorem yd_site {r k : ℕ} (hr : r < 2 ^ L) (hk3 : 3 ≤ k) (hk10 : k ≤ 10) :
    siteMult hashSys inst pub (11, r, k) = (inst 11).main B2s.YD r *
      (B2s.p (Blake2s.P_FIN ((k - 3) / 2))).eval (2 ^ L) B2s.preCols pub (inst 11).main r ∧
    siteVals hashSys inst pub (11, r, k) = [(inst 11).main B2s.STR r, ((widx k : ℕ) : F),
      (Blake2s.limb (if (k - 3) % 2 = 0 then 0 else 1) 0).eval (2 ^ L) B2s.preCols pub (inst 11).main r,
      (Blake2s.limb (if (k - 3) % 2 = 0 then 0 else 1) 1).eval (2 ^ L) B2s.preCols pub (inst 11).main r] := by
  have ev : ∀ c, (B2s.k c).eval (2 ^ L) B2s.preCols pub (inst 11).main r = (inst 11).main c r := fun c =>
    B2s.ev_k (pub := pub) (M := (inst 11).main) hr
  interval_cases k <;>
    simp [siteMult, siteVals, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups, Expr.eval, ev,
      widx, B2s.bidx, StarkedAir.Sha256.eval_cst, B2s.p, List.range_succ, List.flatMap_append]

/-- **A digest yield** is a full period's last block of a stream, and carries that stream's Blake2s
chaining word `widx k`, as limbs. -/
theorem digest_yield {r k : ℕ} (hr : r < 2 ^ L) (hk3 : 3 ≤ k) (hk10 : k ≤ 10)
    (hm : siteMult hashSys inst pub (11, r, k) ≠ 0) :
    ∃ sv : ℕ, (sv = 0 ∨ sv = 1) ∧ siteVals hashSys inst pub (11, r, k) = [(sv : F), ((widx k : ℕ) : F),
      ((Sha256.half16 (hwords inst pub sv (widx k)) 0 : ℕ) : F), ((Sha256.half16 (hwords inst pub sv (widx k)) 1 : ℕ) : F)] := by
  have bs := hash_b2s_sat hL hsat
  obtain ⟨em, ev⟩ := yd_site hL (pub := pub) (inst := inst) hr hk3 hk10
  set j := (k - 3) / 2 with hj
  have hj4 : j < 4 := by omega
  set s' := r - r % 88 with hs'
  have hp : r % 88 < 88 := Nat.mod_lt _ (by norm_num)
  have hrs : r = s' + r % 88 := by omega
  have hfin : (B2s.p (Blake2s.P_FIN j)).eval (2 ^ L) B2s.preCols pub (inst 11).main r =
      if r % 88 = 84 + j then 1 else 0 := by
    rw [B2s.p, B2s.eval_pre_gadget (by simp [Blake2s.P_FIN]; omega)]
    conv_lhs => rw [hrs]
    rw [Blake2s.pre_at (s := s') (by simp [Blake2s.PERIOD]; omega) (by simp [Blake2s.PERIOD]; omega) (by omega)
      (by simp [Blake2s.P_FIN]; omega), Blake2s.bPre_FIN hj4 (by simp [Blake2s.PERIOD]; omega)]
  rw [em, hfin] at hm
  have h84 : r % 88 = 84 + j := by by_contra h; rw [if_neg h, mul_zero] at hm; exact hm rfl
  rw [if_pos h84, mul_one] at hm
  have hfull := full_period hL (inst := inst) hr (by omega)
  have hs88 : s' % 88 = 0 := by omega
  have hrow : r = s' + (84 + j) := by omega
  -- the period is a stream's last block
  have yd := B2s.defn bs (a := B2s.YD) (e := .mul (B2s.k B2s.USEW) (B2s.k B2s.LASTF)) (by simp [B2s.flagC]) hr
  simp only [Expr.eval, B2s.ev_k hr] at yd
  have hus := B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC]) hr
  simp only [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, B2s.ev_k hr,
    B2s.ev_outp (pub := pub) (M := (inst 11).main) hr] at hus
  have hnil := B2s.bool_flag bs (c := B2s.NIL) (by simp) hr
  have hlast := B2s.bool_flag bs (c := B2s.LASTF) (by simp) hr
  have hu1 : (inst 11).main B2s.USEW r = 1 ∧ (inst 11).main B2s.LASTF r = 1 := by
    rw [yd] at hm
    rcases hnil with n0 | n1 <;> rcases hlast with l0 | l1
    · rw [l0, mul_zero] at hm; exact absurd rfl hm
    · refine ⟨?_, l1⟩
      rw [hus, n0]; split_ifs with h
      · rw [l1, mul_one, hus, n0] at hm; simp [h] at hm
      · simp
    · rw [l0, mul_zero] at hm; exact absurd rfl hm
    · exfalso; rw [hus, n1] at hm; simp at hm
  have hq : ∀ X ∈ B2s.perConst, (inst 11).main X r = (inst 11).main X s' := by
    intro X hX; rw [hrow]; exact B2s.per_const bs hX hs88 (84 + j) (by omega) (by omega)
  have husew : (inst 11).main B2s.USEW s' = 1 := by
    have e0 := B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC])
      (show s' < 2 ^ L by omega)
    have e1 := B2s.defn bs (a := B2s.USEW) (e := .mul (B2s.om (B2s.k B2s.NIL)) (B2s.om B2s.outp)) (by simp [B2s.flagC]) hr
    simp only [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, B2s.ev_k (show s' < 2 ^ L by omega),
      B2s.ev_k hr] at e0 e1
    have ho : B2s.outp.eval (2 ^ L) B2s.preCols pub (inst 11).main r = B2s.outp.eval (2 ^ L) B2s.preCols pub (inst 11).main s' := by
      conv_lhs => rw [hrow]
      exact B2s.outp_const (pub := pub) (M := (inst 11).main) hs88 (by omega) (by omega)
    rw [e0, ← hq B2s.NIL (by simp [B2s.perConst]), ← ho, ← e1, hu1.1]
  have hl' : (inst 11).main B2s.LASTF s' = 1 := by rw [← hq B2s.LASTF (by simp [B2s.perConst]), hu1.2]
  obtain ⟨sv, b, hsv, hstr, -⟩ := period_block hL hsat hL24 hs88 hfull husew
  have hdig := last_digest hL hsat hL24 hs88 hfull husew hl' hstr hsv
  refine ⟨sv, hsv, ?_⟩
  rw [ev, hq B2s.STR (by simp [B2s.perConst]), hstr]
  have hbits : ∀ w < 8, ∀ i < 32, ((inst 11).main (32 * w + i) r).val ≤ 1 := fun w hw =>
    B2s.bits4 bs hr w hw
  have lim : ∀ w < 2, ∀ h ≤ 1, (Blake2s.limb w h).eval (2 ^ L) B2s.preCols pub (inst 11).main r =
      ((Sha256.half16 (Sha256.word (inst 11).main (32 * w) r) h : ℕ) : F) := by
    intro w hw h hh
    exact StarkedAir.Sha256.eval_limb (wrap_zero hr) (hbits w (by omega)) hh
  by_cases h0 : (k - 3) % 2 = 0
  · rw [if_pos h0, lim 0 (by norm_num) 0 (by norm_num), lim 0 (by norm_num) 1 (by norm_num)]
    have : Sha256.word (inst 11).main (32 * 0) r = hwords inst pub sv (widx k) := by
      simp only [hwords]
      rw [show widx k = j by simp [widx, h0, hj], ← hdig j (by omega), Blake2s.outWord, if_pos hj4, hrow]; ring_nf
    rw [this]
  · rw [if_neg h0, lim 1 (by norm_num) 0 (by norm_num), lim 1 (by norm_num) 1 (by norm_num)]
    have hb : B2s.bidx j < 8 ∧ 4 ≤ B2s.bidx j ∧ (B2s.bidx j + 3) % 4 = j := by interval_cases j <;> decide
    have : Sha256.word (inst 11).main (32 * 1) r = hwords inst pub sv (widx k) := by
      simp only [hwords]
      rw [show widx k = B2s.bidx j by simp [widx, h0, hj], ← hdig _ hb.1, Blake2s.outWord, if_neg (by omega), hb.2.2, hrow]
      ring_nf
    rw [this]

omit hL hsat hL24 in
theorem word_of_limbs (w : Spec.Blake2s.Word) :
    BitVec.ofNat 32 (Sha256.half16 w 0 + 65536 * Sha256.half16 w 1) = w := by
  apply BitVec.eq_of_toNat_eq
  have := w.isLt
  simp [Sha256.half16]
  omega

/-- **The outer hash's message**: words 0–7 and 8–15 are the two streams' Blake2s chaining words. -/
theorem outer_words (hL8 : 8 ≤ L) {kk : ℕ} (hkk : kk < 16) :
    Blake2s.msgWord (inst 11).main kk 0 = (if kk < 8 then hwords inst pub 0 kk else hwords inst pub 1 (kk - 8)) ∧
    ∀ h ≤ 1, ((inst 11).main (Blake2s.ML kk h) 0).val < 65536 := by
  have bs := hash_b2s_sat hL hsat
  have h256 : 256 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL8)
  have hr : kk < 2 ^ L := by omega
  have ev : ∀ c, (B2s.k c).eval (2 ^ L) B2s.preCols pub (inst 11).main kk = (inst 11).main c kk := fun c =>
    B2s.ev_k (pub := pub) (M := (inst 11).main) hr
  have hmu1 : (inst 11).main B2s.MU1 kk = 1 := by
    rw [B2s.defn bs (a := B2s.MU1) (e := .mul B2s.outp (B2s.p B2s.P_LT16)) (by simp [B2s.flagC]) hr]
    simp only [Expr.eval, B2s.ev_outp (pub := pub) (M := (inst 11).main) hr, B2s.ev_lt16 (pub := pub) (M := (inst 11).main) hr,
      show kk < 88 by omega, show kk % 88 < 16 by omega, if_true, mul_one]
  have hm : siteMult hashSys inst pub (11, kk, 1) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups, Expr.eval, ev, hmu1]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 (b2s_site hL hsat hL24 hr (by norm_num)) rfl hm
  have e20 : siteRel hashSys (11, kk, 1) = 20 := rfl
  rw [e20, yt] at hy
  obtain ⟨rfl, hk3, hk10⟩ : i' = 11 ∧ 3 ≤ k' ∧ k' ≤ 10 := by omega
  obtain ⟨sv, hsv01, hvy⟩ := digest_yield hL hsat hL24 hr' hk3 hk10 hsm
  have hDS : (B2s.p B2s.P_DS).eval (2 ^ L) B2s.preCols pub (inst 11).main kk = ((kk / 8 : ℕ) : F) := by
    rw [B2s.p, B2s.ev_per88 (f := fun r => if r < 16 then r / 8 else 0) (by simp [B2s.preCols, B2s.P_DS, Blake2s.preCols]) hr,
      Nat.mod_eq_of_lt (show kk < 88 by omega), if_pos hkk]
  have hDK : (B2s.p B2s.P_DK).eval (2 ^ L) B2s.preCols pub (inst 11).main kk = ((kk % 8 : ℕ) : F) := by
    rw [B2s.p, B2s.ev_per88 (f := fun r => if r < 16 then r % 8 else 0) (by simp [B2s.preCols, B2s.P_DK, Blake2s.preCols]) hr,
      Nat.mod_eq_of_lt (show kk < 88 by omega), if_pos hkk]
  have hvu : siteVals hashSys inst pub (11, kk, 1) = [((kk / 8 : ℕ) : F), ((kk % 8 : ℕ) : F),
      (inst 11).main B2s.WLO kk, (inst 11).main B2s.WHI kk] := by
    have : siteVals hashSys inst pub (11, kk, 1) = [B2s.p B2s.P_DS, B2s.p B2s.P_DK, B2s.k B2s.WLO, B2s.k B2s.WHI].map
        (Expr.eval (2 ^ L) B2s.preCols pub (inst 11).main kk) := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups]
    rw [this]; simp [hDS, hDK, ev]
  rw [hvy, hvu] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨es, ew, elo, ehi⟩ := hsv
  have hwi : widx k' < 8 := by
    unfold widx
    have hj : (k' - 3) / 2 < 4 := by omega
    generalize (k' - 3) / 2 = j at hj ⊢
    split_ifs
    · omega
    · interval_cases j <;> decide
  have esv : sv = kk / 8 := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) es
  have ewi : widx k' = kk % 8 := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) ew
  obtain ⟨wlo, whi⟩ := B2s.msg_word bs (s := 0) (by norm_num) (by omega) hkk
  simp only [Nat.zero_add] at wlo whi
  have hl0 := Sha256.half16_lt (hwords inst pub sv (widx k')) 0
  have hl1 := Sha256.half16_lt (hwords inst pub sv (widx k')) 1
  refine ⟨?_, fun h hh => ?_⟩
  · unfold Blake2s.msgWord
    rw [← wlo, ← whi, ← elo, ← ehi, ZMod.val_natCast_of_lt (by unfold P; omega), ZMod.val_natCast_of_lt (by unfold P; omega),
      word_of_limbs, ewi, esv]
    split_ifs with h8
    · rw [show kk / 8 = 0 by omega, show kk % 8 = kk by omega]
    · rw [show kk / 8 = 1 by omega, show kk % 8 = kk - 8 by omega]
  · interval_cases h
    · rw [← wlo, ← elo, ZMod.val_natCast_of_lt (by unfold P; omega)]; omega
    · rw [← whi, ← ehi, ZMod.val_natCast_of_lt (by unfold P; omega)]; omega

/-- The commitment's chaining words: Blake2s of the two streams' digests. -/
abbrev cwords (inst : ℕ → Inst) (pub : ℕ → F) : ℕ → Spec.Blake2s.Word :=
  Spec.Blake2s.hashBlocks Spec.Blake2s.h0 0 (Spec.Blake2s.blake2s (Rb inst pub) ++ Spec.Blake2s.blake2s (Ub inst pub))

omit hL hsat hL24 in
theorem blockCommit_eq : Spec.Block.blockCommit (Rb inst pub) (Ub inst pub) = Spec.Blake2s.digest (cwords inst pub) := rfl

/-- **Block commitment soundness (M3a.6).** Public inputs 9–24 are the 16-bit limbs of the commitment's words:
`blockCommit raw undo = digest C` and `pub (9 + 2i + h) = half16 (C i) h`. -/
theorem commit_sound (hL8 : 8 ≤ L) :
    ∀ i < 8, ∀ h ≤ 1, pub (9 + 2 * i + h) = ((Sha256.half16 (cwords inst pub i) h : ℕ) : F) := by
  have bs := hash_b2s_sat hL hsat
  have h256 : 256 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL8)
  have h0r : 0 < 2 ^ L := by positivity
  -- the outer period's inputs
  have hfst : (inst 11).main B2s.FST 0 + B2s.outp.eval (2 ^ L) B2s.preCols pub (inst 11).main 0 ≠ 0 := by
    rw [B2s.ev_outp (pub := pub) (M := (inst 11).main) h0r, if_pos (by norm_num)]
    rcases B2s.bool_flag bs (c := B2s.FST) (by simp) h0r with h | h <;> rw [h]
    · simp
    · intro e
      have e2 : ((2 : ℕ) : F) = ((0 : ℕ) : F) := by push_cast; linear_combination e
      have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num) e2
      omega
  have hdiag := B2s.h_first bs (s := 0) (by norm_num) (by omega) hfst
  have hnil : (inst 11).main B2s.NIL 0 = 0 := by
    have := B2s.sat bs (B2s.mem_flag (c := .mul B2s.outp (B2s.k B2s.NIL)) (by simp [B2s.flagC])) h0r
    simpa [Expr.eval, B2s.ev_outp (pub := pub) (M := (inst 11).main) h0r, B2s.ev_k h0r] using this
  obtain ⟨htv, hfv⟩ := B2s.tf bs (s := 0) (by norm_num) (by omega) hnil
  have htv' : (inst 11).main B2s.TV 0 = 64 := by
    rw [B2s.defn bs (a := B2s.TV) (e := .add (.mul B2s.outp (StarkedAir.Sha256.cst 64)) (.mul (B2s.om B2s.outp) (B2s.k B2s.T)))
      (by simp [B2s.flagC]) h0r]
    simp [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, B2s.ev_k h0r,
      B2s.ev_outp (pub := pub) (M := (inst 11).main) h0r]
  have hfv' : (inst 11).main B2s.FV 0 = 1 := by
    rw [B2s.defn bs (a := B2s.FV) (e := .add B2s.outp (.mul (B2s.om B2s.outp) (B2s.k B2s.LASTF))) (by simp [B2s.flagC]) h0r]
    simp [Expr.eval, B2s.om, B2s.one, StarkedAir.Sha256.eval_cst, B2s.ev_k h0r,
      B2s.ev_outp (pub := pub) (M := (inst 11).main) h0r]
  have hinT : Blake2s.inT (inst 11).main 0 = 64 := by
    rw [htv, htv']; exact ZMod.val_natCast_of_lt (by unfold P; norm_num)
  have hfb : Blake2s.fBit (inst 11).main 0 = true := hfv.mpr hfv'
  have hcomp := B2s.period_compress bs (s := 0) (by norm_num) (by omega)
    (fun kk hkk => (outer_words hL hsat hL24 hL8 hkk).2)
  -- the outer output is the commitment's chaining value
  have hout : ∀ i < 8, Blake2s.outWord (inst 11).main 0 i = cwords inst pub i := by
    intro i hi
    rw [← hcomp i hi, hinT, hfb]
    have hlen : (Spec.Blake2s.blake2s (Rb inst pub) ++ Spec.Blake2s.blake2s (Ub inst pub)).length = 64 := by
      simp [Spec.Blake2s.blake2s, Spec.Blake2s.digest_length]
    have hb : ∀ w < 8, cwords inst pub w = Spec.Blake2s.compress (Spec.Blake2s.chainS Spec.Blake2s.h0 0 (Spec.Blake2s.blake2s (Rb inst pub) ++ Spec.Blake2s.blake2s (Ub inst pub)) 0)
        (Spec.Blake2s.wordAt (Spec.Blake2s.blake2s (Rb inst pub) ++ Spec.Blake2s.blake2s (Ub inst pub)) 0) (0 + 64) true w := by
      intro w hw
      have := Spec.Blake2s.hashBlocks_eq 0 Spec.Blake2s.h0 0 _ (by rw [hlen]) (Or.inl rfl) w hw
      rwa [hlen] at this
    rw [hb i hi, Nat.zero_add]
    apply Spec.Blake2s.compress_congr hdiag _ _ _ i hi
    intro kk hkk
    rw [(outer_words hL hsat hL24 hL8 hkk).1, ← Spec.Blake2s.leWord_pad _ 0 kk, List.replicate_zero, List.append_nil]
    unfold Spec.Blake2s.blake2s
    rw [Spec.Blake2s.leWord_digests _ _ hkk]
    simp [hwords, strm]
  -- the public limbs
  intro i hi h hh
  have hrow : ∀ j < 4, 84 + j < 2 ^ L := fun j hj => by omega
  have lim : ∀ j < 4, ∀ w < 2, (Blake2s.limb w h).eval (2 ^ L) B2s.preCols pub (inst 11).main (84 + j) =
      ((Sha256.half16 (Sha256.word (inst 11).main (32 * w) (84 + j)) h : ℕ) : F) := fun j hj w hw =>
    StarkedAir.Sha256.eval_limb (wrap_zero (hrow j hj)) (B2s.bits4 bs (hrow j hj) w (by omega)) hh
  have fin : ∀ j < 4, (B2s.p (Blake2s.P_FIN j)).eval (2 ^ L) B2s.preCols pub (inst 11).main (84 + j) = 1 := by
    intro j hj
    rw [B2s.p, B2s.eval_pre_gadget (by simp [Blake2s.P_FIN]; omega),
      show 84 + j = 0 + (84 + j) by ring, Blake2s.pre_at (s := 0) (by norm_num) (by simp [Blake2s.PERIOD]; omega)
        (by omega) (by simp [Blake2s.P_FIN]; omega), Blake2s.bPre_FIN hj (by simp [Blake2s.PERIOD]; omega), if_pos rfl]
  have outc : ∀ j < 4, ∀ e ∈ [Expr.mul B2s.outp (.mul (B2s.p (Blake2s.P_FIN j)) (.sub (Blake2s.limb 0 h) (.pub (B2s.PUB_OUT + 2 * j + h)))),
      Expr.mul B2s.outp (.mul (B2s.p (Blake2s.P_FIN j)) (.sub (Blake2s.limb 1 h) (.pub (B2s.PUB_OUT + 2 * B2s.bidx j + h))))],
      e.eval (2 ^ L) B2s.preCols pub (inst 11).main (84 + j) = 0 := by
    intro j hj e he
    apply B2s.sat bs (B2s.mem_out _) (hrow j hj)
    simp only [B2s.outC, List.mem_flatMap, List.mem_range]
    exact ⟨j, hj, h, by omega, by simpa using he⟩
  have pubw : ∀ j < 4, ∀ w < 2, ∀ idx, (Expr.mul B2s.outp (.mul (B2s.p (Blake2s.P_FIN j))
      (.sub (Blake2s.limb w h) (.pub (B2s.PUB_OUT + 2 * idx + h))))).eval (2 ^ L) B2s.preCols pub (inst 11).main (84 + j) = 0 →
      pub (9 + 2 * idx + h) = ((Sha256.half16 (Sha256.word (inst 11).main (32 * w) (84 + j)) h : ℕ) : F) := by
    intro j hj w hw idx he
    simp only [Expr.eval, B2s.ev_outp (pub := pub) (M := (inst 11).main) (hrow j hj), if_pos (show 84 + j < 88 by omega),
      one_mul, fin j hj, lim j hj w hw, sub_eq_zero] at he
    exact he.symm
  by_cases h4 : i < 4
  · rw [pubw i h4 0 (by norm_num) i (outc i h4 _ (by simp)), ← hout i hi, Blake2s.outWord, if_pos h4]
  · set j := (i + 3) % 4
    have hj : j < 4 := Nat.mod_lt _ (by norm_num)
    have hbj : B2s.bidx j = i := by simp only [j]; interval_cases i <;> rfl
    rw [← hbj, pubw j hj 1 (by norm_num) (B2s.bidx j) (outc j hj _ (by simp)), hbj, ← hout i hi, Blake2s.outWord,
      if_neg h4, show (i + 3) % 4 = j from rfl]

end System

end StarkedAir.Block
