/-
**The Merkle leaves in the system (D-050).** Record `ρ`'s leaf message (`leafMsg`) is its previous key's 36
bytes (`Rec.prevKey`), then its file bytes. Each walker row reads its record (`lw_rec`), and its word is the
message's (`lw_yield`); each used leaf compression reads its record's words, chains its blocks, and the
last block's digest yields are the message's Blake2s words (`leaf_yield`).
-/
import StarkedAir.SetPass.LWSound
import StarkedAir.SetPass.LCSound
import StarkedAir.SetPass.Facts
import StarkedAir.SetPass.MTLink
import StarkedAir.SetPass.RecSound
import StarkedAir.SetPass.Sound
import StarkedAir.Spec.Blake2sBlocks

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst half16)

/-- Record `ρ`'s leaf message: its previous key's bytes, then its encoding. -/
def leafMsg (pub : ℕ → F) (MR : ℕ → ℕ → F) (S : ℕ → ℕ) (ρ : ℕ) : Spec.Block.Bytes :=
  (List.range 36).map (fun j => UInt8.ofNat (Rec.prevKey pub MR S ρ j)) ++ Spec.SetFile.encRec (Rec.recR MR S ρ)

/-- A message word's halves, from its bytes. -/
theorem half16_wordAt (bs : Spec.Block.Bytes) (b k : ℕ) :
    half16 (Spec.Blake2s.wordAt bs b k) 0 = (bs.getD (64 * b + 4 * k) 0).toNat + 256 * (bs.getD (64 * b + 4 * k + 1) 0).toNat ∧
    half16 (Spec.Blake2s.wordAt bs b k) 1 = (bs.getD (64 * b + 4 * k + 2) 0).toNat + 256 * (bs.getD (64 * b + 4 * k + 3) 0).toNat := by
  have h0 := UInt8.toNat_lt (bs.getD (64 * b + 4 * k) 0)
  have h1 := UInt8.toNat_lt (bs.getD (64 * b + 4 * k + 1) 0)
  have h2 := UInt8.toNat_lt (bs.getD (64 * b + 4 * k + 2) 0)
  have h3 := UInt8.toNat_lt (bs.getD (64 * b + 4 * k + 3) 0)
  refine ⟨?_, ?_⟩ <;> simp only [half16, Spec.Blake2s.wordAt, BitVec.toNat_ofNat] <;> omega

/-- The leaf message's length and bytes. -/
theorem leafMsg_getD {pub : ℕ → F} {MR : ℕ → ℕ → F} {S : ℕ → ℕ} {ρ x : ℕ} :
    (leafMsg pub MR S ρ).getD x 0 = if x < 36 then UInt8.ofNat (Rec.prevKey pub MR S ρ x)
      else (Spec.SetFile.encRec (Rec.recR MR S ρ)).getD (x - 36) 0 := by
  unfold leafMsg
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]; simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simp; omega)]; simp


section Leaves

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
  (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls)
  {e : ℕ} (E : Rec.OnPre (2 ^ Ls 3) (inst 3).main e) (hidx : ∀ r < e, (inst 3).main Rec.IDX r = (r : F))
include hL hsat hHL hsz E hidx

omit hHL hsz E hidx in
theorem lw_lk {r k : ℕ} : siteLookup segSys ((9, r, k) : Site) = LW.lookups.getD k ⟨0, .const 0, []⟩ := rfl

omit hHL E hidx in
theorem lw_n : 2 ^ Ls 9 ≤ 2 ^ 25 := le_trans (Nat.pow_le_pow_right (by norm_num) (hsz.1 9 (by decide))) (by norm_num)

/-- **A walker record is a record row**: at its start row, its index, start and `length + 85`. -/
theorem rec_of_start {st : ℕ} (hsr : st < 2 ^ Ls 9) (hnw : (inst 9).main LW.NEWR st = 1) :
    ∃ ρ, ρ < e ∧ (inst 9).main LW.RI st = (ρ : F) ∧ (inst 9).main LW.START st = (inst 3).main Rec.START ρ ∧
      (inst 9).main LW.M st = (inst 3).main Rec.LENC ρ + 85 := by
  have hpre : (segSys.comp 9).air.pre = LW.preCols := rfl
  have hsite := site_mem hL (i := 9) (by decide) hsr (k := 1) (by simp [segSys, comps, LW.lw, LW.lookups])
  have hm : siteMult segSys inst pub (9, st, 1) = -1 := by
    simp [siteMult, siteEval, siteLookup, hpre, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups, Expr.eval,
      LW.ev_k (pub := pub) (W := (inst 9).main) hsr, hnw]
  obtain ⟨i, ρ, k', hρ, hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse]) hm
  rw [show siteRel segSys ((9, st, 1) : Site) = 32 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i = 3 ∧ k' = 57 := by omega
  have hpre3 : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hl57 : siteLookup segSys ((3, ρ, 57) : Site) = ⟨REL_REC, .mul (cst 2) (Rec.k Rec.ON), [Rec.k Rec.IDX,
      Rec.k Rec.START, Rec.k Rec.LENC]⟩ := rfl
  have hon3 : (inst 3).main Rec.ON ρ = 1 := by
    have h2 : (2 : F) * (inst 3).main Rec.ON ρ ≠ 0 := by
      simpa [siteMult, hl57, siteEval, hpre3, hL 3 (by decide), Expr.eval, Rec.k, StarkedAir.Sha256.eval_col,
        StarkedAir.Sha256.eval_cst, wrap_zero hρ] using hsm
    exact (Block.air_bool (air := Rec.rec.air) (rec_sat hL hsat) (c := Rec.ON)
      (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k]) hρ).resolve_left (right_ne_zero_of_mul h2)
  have hρe : ρ < e := by
    have := E.on ρ hρ; rw [hon3] at this; by_contra h; rw [if_neg h] at this; exact one_ne_zero this
  have e1 : siteVals segSys inst pub (3, ρ, 57) = [(inst 3).main Rec.IDX ρ, (inst 3).main Rec.START ρ,
      (inst 3).main Rec.LENC ρ] := by
    simp [siteVals, hl57, siteEval, hpre3, hL 3 (by decide), Rec.k, StarkedAir.Sha256.eval_col, wrap_zero hρ]
  have e2 : siteVals segSys inst pub (9, st, 1) = [(inst 9).main LW.RI st, (inst 9).main LW.START st,
      (inst 9).main LW.M st - 85] := by
    simp [siteVals, siteEval, siteLookup, hpre, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups, Expr.eval,
      LW.ev_k (pub := pub) (W := (inst 9).main) hsr, StarkedAir.Sha256.eval_cst]
  rw [e1, e2] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨a1, a2, a3⟩ := hsv
  exact ⟨ρ, hρe, by rw [← a1, hidx ρ hρe], a2.symm, by linear_combination -a3⟩

omit E hidx in
/-- **An active non-key byte is a segment byte**, at the record's start plus its message position − 36. -/
theorem lw_file_byte {r j : ℕ} (hr : r < 2 ^ Ls 9) (hj : j < 4) (hA : (inst 9).main (LW.A j) r = 1)
    (hpk : (inst 9).main LW.PKU r = 0) :
    ∃ q, q < (pub PUB_LEN).val ∧ (LW.filePos j).eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r = (q : F) ∧
      (inst 9).main (LW.B j) r = (inst 0).main Block.BYTE q := by
  have hpre : (segSys.comp 9).air.pre = LW.preCols := rfl
  have hl : LW.lookups.getD (2 + j) ⟨0, .const 0, []⟩ = ⟨Block.REL_BYTE, .neg (.mul (LW.k (LW.A j)) (LW.om (LW.k LW.PKU))),
      [LW.filePos j, LW.k (LW.B j)]⟩ := by interval_cases j <;> rfl
  have hsl : siteLookup segSys ((9, r, 2 + j) : Site) = _ := hl
  have hsite := site_mem hL (i := 9) (by decide) hr (k := 2 + j) (by simp [segSys, comps, LW.lw, LW.lookups]; omega)
  exact byte_read hL hsat hHL hsz hsite (by simp [isUse]; omega) (by simp [siteRel, hsl])
    (by simp [siteMult, hsl, siteEval, hpre, hL 9 (by decide), Expr.eval, LW.ev_k (pub := pub) (W := (inst 9).main) hr,
      LW.om, LW.one, StarkedAir.Sha256.eval_cst, hA, hpk])
    (by simp [siteVals, hsl, siteEval, hpre, hL 9 (by decide), LW.ev_k (pub := pub) (W := (inst 9).main) hr])

omit hidx in
/-- **A key word** (`PKU`) is a record row's previous-key word. -/
theorem lw_key_word {r : ℕ} (hr : r < 2 ^ Ls 9) (hpk : (inst 9).main LW.PKU r = 1) :
    ∃ ρ' : ℕ, ∃ w : ℕ, ρ' < e ∧ w < 9 ∧ (inst 9).main LW.RI r = (inst 3).main Rec.IDX ρ' ∧ ((r % 16 : ℕ) : F) = (w : F) ∧
      LW.lo.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r =
        (inst 3).main (Rec.PREV (4 * w)) ρ' + 256 * (inst 3).main (Rec.PREV (4 * w + 1)) ρ' ∧
      LW.hi.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r =
        (inst 3).main (Rec.PREV (4 * w + 2)) ρ' + 256 * (inst 3).main (Rec.PREV (4 * w + 3)) ρ' := by
  have hpre : (segSys.comp 9).air.pre = LW.preCols := rfl
  have hsite := site_mem hL (i := 9) (by decide) hr (k := 0) (by simp [segSys, comps, LW.lw, LW.lookups])
  have hm : siteMult segSys inst pub (9, r, 0) = -1 := by
    simp [siteMult, siteEval, siteLookup, hpre, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups, Expr.eval,
      LW.ev_k (pub := pub) (W := (inst 9).main) hr, hpk]
  obtain ⟨i, ρ', k', hρ, hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse]) hm
  rw [show siteRel segSys ((9, r, 0) : Site) = 36 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, h89, h98⟩ : i = 3 ∧ 89 ≤ k' ∧ k' < 98 := by omega
  set w := k' - 89 with hw
  have hpre3 : (segSys.comp 3).air.pre = Rec.preCols := rfl
  have hlk : siteLookup segSys ((3, ρ', k') : Site) = ⟨REL_PKEY, Rec.k Rec.ON, [Rec.k Rec.IDX, cst w,
      Rec.pair (Rec.k (Rec.PREV (4 * w))) (Rec.k (Rec.PREV (4 * w + 1))),
      Rec.pair (Rec.k (Rec.PREV (4 * w + 2))) (Rec.k (Rec.PREV (4 * w + 3)))]⟩ := by
    show Rec.lookups.getD k' _ = _
    rw [show k' = 89 + w by omega]
    have hw9 : w < 9 := by omega
    interval_cases w <;> rfl
  have hon3 : (inst 3).main Rec.ON ρ' ≠ 0 := by
    simpa [siteMult, hlk, siteEval, hpre3, hL 3 (by decide), Rec.k, StarkedAir.Sha256.eval_col, wrap_zero hρ] using hsm
  have hon3' := (Block.air_bool (air := Rec.rec.air) (rec_sat hL hsat) (c := Rec.ON)
    (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k]) hρ).resolve_left hon3
  have hρe : ρ' < e := by
    have := E.on ρ' hρ; rw [hon3'] at this; by_contra h; rw [if_neg h] at this; exact one_ne_zero this
  have e1 : siteVals segSys inst pub (3, ρ', k') = [(inst 3).main Rec.IDX ρ', (w : F),
      (inst 3).main (Rec.PREV (4 * w)) ρ' + 256 * (inst 3).main (Rec.PREV (4 * w + 1)) ρ',
      (inst 3).main (Rec.PREV (4 * w + 2)) ρ' + 256 * (inst 3).main (Rec.PREV (4 * w + 3)) ρ'] := by
    simp [siteVals, hlk, siteEval, hpre3, hL 3 (by decide), Rec.k, Rec.pair, Expr.eval, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hρ]
  have e2 : siteVals segSys inst pub (9, r, 0) = [(inst 9).main LW.RI r, ((r % 16 : ℕ) : F),
      LW.lo.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r, LW.hi.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r] := by
    simp [siteVals, siteEval, siteLookup, hpre, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups,
      LW.ev_k (pub := pub) (W := (inst 9).main) hr, LW.ev_K (pub := pub) (W := (inst 9).main) hr]
  rw [e1, e2] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨a1, a2, a3, a4⟩ := hsv
  exact ⟨ρ', w, hρe, by omega, a1.symm, a2.symm, a3.symm, a4.symm⟩

/-- **A walker word is the leaf message's word**, and a block's first row its last flag and counter. -/
theorem lw_yield (H : Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub)) {r : ℕ} (hr : r < 2 ^ Ls 9)
    (hon : (inst 9).main LW.ON r = 1) :
    ∃ ρ b, ρ < e ∧ b < Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length ∧
      (leafMsg pub (inst 3).main (Sb inst pub) ρ).length = (((inst 3).main Rec.LENC ρ).val + 85) ∧
      (inst 9).main LW.RI r = (ρ : F) ∧ (inst 9).main LW.BLK r = (b : F) ∧
      LW.lo.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r =
        ((half16 (Spec.Blake2s.wordAt (leafMsg pub (inst 3).main (Sb inst pub) ρ) b (r % 16)) 0 : ℕ) : F) ∧
      LW.hi.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r =
        ((half16 (Spec.Blake2s.wordAt (leafMsg pub (inst 3).main (Sb inst pub) ρ) b (r % 16)) 1 : ℕ) : F) ∧
      (r % 16 = 0 → ((inst 9).main LW.LASTF r = 1 ↔ b + 1 = Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length) ∧
        ((inst 9).main LW.LASTF r = 0 ∨ (inst 9).main LW.LASTF r = 1) ∧
        (inst 9).main LW.T r = ((if b + 1 = Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length
          then (leafMsg pub (inst 3).main (Sb inst pub) ρ).length else 64 * (b + 1) : ℕ) : F)) := by
  have ws := lw_sat hL hsat
  have rs := rec_sat hL hsat
  obtain ⟨st, hst, hst16, hnw, hlt, hcst, -, hblk, hA, hB0, hlast, hpku⟩ := LW.row_fact ws (lw_n hL hsat hsz) hr hon
  obtain ⟨ρ, hρe, hri, hstart, hM⟩ := rec_of_start hL hsat hHL hsz E hidx (show st < 2 ^ Ls 9 by omega) hnw
  set MR := (inst 3).main with hMR
  set S := Sb inst pub with hS
  set msg := leafMsg pub MR S ρ with hmsg
  set len := (MR Rec.LENC ρ).val with hlen
  have hlen24 : len < 2 ^ 24 := (Rec.fields rs E H hρe).2.2.2.1
  have hst24 : (MR Rec.START ρ).val < 2 ^ 24 := Rec.start_lt rs E H hρe
  have hmv : ((inst 9).main LW.M st).val = len + 85 := by
    rw [hM, show MR Rec.LENC ρ + 85 = ((len + 85 : ℕ) : F) by push_cast; rw [hlen, ZMod.natCast_zmod_val]]
    exact ZMod.val_natCast_of_lt (by unfold P; omega)
  have henc := Rec.recR_enc rs E H hρe
  have hLen : msg.length = len + 85 := by
    simp only [hmsg, leafMsg, List.length_append, List.length_map, List.length_range, henc, Rec.bytesAt_length]; omega
  rw [hmv] at hlt hA hlast
  set b := (r - st) / 16 with hb
  have hk : r % 16 = (r - st) % 16 := by omega
  have hx0 : 4 * (r - st) = 64 * b + 4 * (r % 16) := by omega
  have hbP : b < 2 ^ 24 := by have := lw_n hL hsat hsz; omega
  -- a non-key row's bytes
  have byteval : ∀ j < 4, 9 ≤ r - st → ((inst 9).main (LW.B j) r).val = (msg.getD (64 * b + 4 * (r % 16) + j) 0).toNat := by
    intro j hj h9
    have hpk : (inst 9).main LW.PKU r = 0 := by rw [hpku, if_neg (by omega)]
    obtain ⟨hiff, hbool⟩ := hA j hj
    rcases hbool with h0 | h1
    · rw [hB0 j hj h0, ZMod.val_zero, List.getD_eq_default _ _ (by rw [hLen]; rw [h0, ZMod.val_zero] at hiff; omega)]; rfl
    · have hxm : 64 * b + 4 * (r % 16) + j < len + 85 := by rw [h1, ZMod.val_one] at hiff; have := hiff.mp rfl; omega
      obtain ⟨q, hq, hpos, hbyte⟩ := lw_file_byte hL hsat hHL hsz hr hj h1 hpk
      have hst' : (inst 9).main LW.START r = (((MR Rec.START ρ).val : ℕ) : F) := by
        rw [hcst LW.START (Or.inr (Or.inl rfl)), hstart, ZMod.natCast_zmod_val]
      simp only [LW.filePos, Expr.eval, LW.ev_k (pub := pub) (W := (inst 9).main) hr, LW.ev_K (pub := pub) (W := (inst 9).main) hr,
        StarkedAir.Sha256.eval_cst, hst', hblk] at hpos
      have hq' : (MR Rec.START ρ).val + (64 * b + 4 * (r % 16) + j - 36) = q := by
        have h16 : r % 16 < 16 := Nat.mod_lt _ (by norm_num)
        have hqP : q < P := lt_of_lt_of_le hq (le_of_lt (ZMod.val_lt _))
        apply natCast_inj_of_lt (Block.Fields.lt_P (by omega)) hqP
        rw [← hpos]; push_cast [show 36 ≤ 64 * b + 4 * (r % 16) + j by omega]; ring
      have hx36 : ¬ (64 * b + 4 * (r % 16) + j < 36) := by rw [← hx0]; omega
      have hxl : 64 * b + 4 * (r % 16) + j - 36 < 49 + len := by omega
      rw [hbyte, hmsg, leafMsg_getD, if_neg hx36, henc, Rec.getD_bytesAt H.byte hxl, hq', hS, Sb, if_pos hq]
  -- a key row's words
  have keyval : r - st < 9 → ∀ h ≤ 1, ((if h = 0 then LW.lo else LW.hi).eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r) =
      (((msg.getD (4 * (r % 16) + 2 * h) 0).toNat + 256 * (msg.getD (4 * (r % 16) + 2 * h + 1) 0).toNat : ℕ) : F) := by
    intro h9 h hh
    have hpk : (inst 9).main LW.PKU r = 1 := by rw [hpku, if_pos h9]
    obtain ⟨ρ', w, hρ', hw9, hri', hw, hlo, hhi⟩ := lw_key_word hL hsat hHL hsz E hr hpk
    have eρ : ρ' = ρ := by
      have h1 : ((ρ' : ℕ) : F) = ((ρ : ℕ) : F) := by
        calc ((ρ' : ℕ) : F) = (inst 3).main Rec.IDX ρ' := (hidx ρ' hρ').symm
          _ = (inst 9).main LW.RI r := hri'.symm
          _ = (inst 9).main LW.RI st := hcst LW.RI (Or.inl rfl)
          _ = ρ := hri
      have hn3 := rows_lt_P hL hsz (i := 3) (by decide)
      have := E.lt
      exact natCast_inj_of_lt (by omega) (by omega) h1
    subst eρ
    have ew : w = r % 16 := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) hw.symm
    subst ew
    have pv := fun i (hi : i < 36) => Rec.prev_val rs E H hρ' i hi
    have mb : ∀ i < 36, (msg.getD i 0).toNat = (MR (Rec.PREV i) ρ').val := by
      intro i hi
      rw [hmsg, leafMsg_getD, if_pos hi, (pv i hi).1, Rec.toNat_ofNat_lt (by rw [← (pv i hi).1]; exact (pv i hi).2)]
    interval_cases h
    · simp only [if_true, hlo, Nat.mul_zero, Nat.add_zero, mb _ (show 4 * (r % 16) < 36 by omega),
        mb _ (show 4 * (r % 16) + 1 < 36 by omega)]
      push_cast; simp only [ZMod.natCast_zmod_val]; rfl
    · simp only [show (1 : ℕ) ≠ 0 by omega, if_false, hhi, Nat.mul_one, mb _ (show 4 * (r % 16) + 2 < 36 by omega),
        mb _ (show 4 * (r % 16) + 2 + 1 < 36 by omega)]
      push_cast; simp only [ZMod.natCast_zmod_val]; rfl
  have hw := half16_wordAt msg b (r % 16)
  refine ⟨ρ, b, hρe, by rw [hLen]; omega, hLen, by rw [hcst LW.RI (Or.inl rfl), hri], hblk, ?_, ?_, ?_⟩
  · rw [hw.1]
    by_cases h9 : r - st < 9
    · have := keyval h9 0 (by norm_num)
      simp only [if_true] at this
      rw [this, show b = 0 by omega]; simp
    · simp only [LW.lo, Expr.eval, LW.ev_k (pub := pub) (W := (inst 9).main) hr, StarkedAir.Sha256.eval_cst]
      rw [← ZMod.natCast_zmod_val ((inst 9).main (LW.B 0) r), ← ZMod.natCast_zmod_val ((inst 9).main (LW.B 1) r),
        byteval 0 (by norm_num) (by omega), byteval 1 (by norm_num) (by omega)]
      push_cast; ring_nf
  · rw [hw.2]
    by_cases h9 : r - st < 9
    · have := keyval h9 1 (by norm_num)
      simp only [show (1 : ℕ) ≠ 0 by omega, if_false] at this
      rw [this, show b = 0 by omega]; simp
    · simp only [LW.hi, Expr.eval, LW.ev_k (pub := pub) (W := (inst 9).main) hr, StarkedAir.Sha256.eval_cst]
      rw [← ZMod.natCast_zmod_val ((inst 9).main (LW.B 2) r), ← ZMod.natCast_zmod_val ((inst 9).main (LW.B 3) r),
        byteval 2 (by norm_num) (by omega), byteval 3 (by norm_num) (by omega)]
      push_cast; ring_nf
  · intro h0
    rw [hLen]
    exact hlast (by omega)

omit hHL hsz E hidx in
theorem lc_n : ∀ r < 2 ^ Ls 10, ∀ c ∈ Block.B2s.constraints,
    c.eval (2 ^ Ls 10) Block.B2s.preCols pub (inst 10).main r = 0 :=
  LC.b2s_sat (lc_sat hL hsat)

omit hHL hsz E hidx in
/-- `RI` is constant down a period. -/
theorem lc_ri_const {s : ℕ} (hs : s % 88 = 0) : ∀ q < 88, s + q < 2 ^ Ls 10 →
    (inst 10).main LC.RI (s + q) = (inst 10).main LC.RI s := by
  have cs := lc_sat hL hsat
  intro q
  induction q with
  | zero => intro _ _; rfl
  | succ q ih =>
    intro hq hr
    have hr' : s + q + 1 < 2 ^ Ls 10 := by omega
    have hmem : Expr.mul (Block.B2s.om (Block.B2s.p Block.B2s.P_R0)) (.sub (Block.B2s.k LC.RI) (Block.B2s.kp LC.RI)) ∈
        LC.constraints :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ (by
          simp only [LC.flagC, List.mem_append, List.mem_map]
          exact Or.inr ⟨LC.RI, by simp [LC.perConst], rfl⟩)))))
    have := cs (s + q + 1) hr' _ hmem
    rw [show LC.preCols = Block.B2s.preCols from rfl] at this
    simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one,
      Block.B2s.ev_r0 (pub := pub) (M := (inst 10).main) hr', show ¬ ((s + q + 1) % 88 = 0) by omega, if_false,
      sub_zero, one_mul, Block.B2s.ev_k hr', Block.B2s.ev_kp hr', sub_eq_zero] at this
    rw [show s + (q + 1) = s + q + 1 by ring, this, ih (by omega) (by omega)]

/-- **A used leaf period's block**: its record's message block `b`, words, last flag and counter. -/
theorem lc_block (H : Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub)) {s : ℕ} (hs : s % 88 = 0)
    (hsn : s + 88 ≤ 2 ^ Ls 10) (hu : (inst 10).main LC.USEW s = 1) :
    ∃ ρ b : ℕ, ρ < e ∧ (inst 10).main LC.RI s = (ρ : F) ∧ (inst 10).main LC.BLKI s = (b : F) ∧
      b < Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length ∧
      (leafMsg pub (inst 3).main (Sb inst pub) ρ).length < 2 ^ 25 ∧
      (∀ kk < 16, Blake2s.msgWord (inst 10).main kk s = Spec.Blake2s.wordAt (leafMsg pub (inst 3).main (Sb inst pub) ρ) b kk ∧
        ∀ h ≤ 1, ((inst 10).main (Blake2s.ML kk h) s).val < 65536) ∧
      ((inst 10).main LC.LASTF s = 1 ↔ b + 1 = Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length) ∧
      ((inst 10).main LC.LASTF s = 0 ∨ (inst 10).main LC.LASTF s = 1) ∧
      (inst 10).main LC.T s = ((if b + 1 = Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length
        then (leafMsg pub (inst 3).main (Sb inst pub) ρ).length else 64 * (b + 1) : ℕ) : F) := by
  have bs := lc_n hL hsat
  have hsr : s < 2 ^ Ls 10 := by omega
  have hpre : (segSys.comp 10).air.pre = LC.preCols := rfl
  have hpre9 : (segSys.comp 9).air.pre = LW.preCols := rfl
  have ev : ∀ {r c}, r < 2 ^ Ls 10 → (LC.k c).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r = (inst 10).main c r :=
    fun hr => Block.B2s.ev_k (pub := pub) (M := (inst 10).main) hr
  have usew : ∀ q < 88, (inst 10).main LC.USEW (s + q) = 1 := by
    intro q hq
    have e := Block.B2s.defn bs (a := Block.B2s.USEW) (e := Block.B2s.om (Block.B2s.k Block.B2s.NIL)) (by simp [Block.B2s.flagC]) (show s + q < 2 ^ Ls 10 by omega)
    have e0 := Block.B2s.defn bs (a := Block.B2s.USEW) (e := Block.B2s.om (Block.B2s.k Block.B2s.NIL)) (by simp [Block.B2s.flagC]) hsr
    simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, Block.B2s.ev_k (show s + q < 2 ^ Ls 10 by omega),
      Block.B2s.ev_k hsr] at e e0
    show (inst 10).main Block.B2s.USEW (s + q) = 1
    rw [e, Block.B2s.per_const bs (X := Block.B2s.NIL) (by simp [Block.B2s.perConst]) hs q hq (by omega), ← e0]; exact hu
  -- the block read (row `s`)
  have hmu1 : (inst 10).main LC.MU1 s = 1 := by
    show (inst 10).main Block.B2s.MU1 s = 1
    rw [Block.B2s.defn bs (a := Block.B2s.MU1) (e := .mul (Block.B2s.k Block.B2s.USEW) (Block.B2s.p Block.B2s.P_R0)) (by simp [Block.B2s.flagC]) hsr]
    simp only [Expr.eval, Block.B2s.ev_k hsr, Block.B2s.ev_r0 (pub := pub) (M := (inst 10).main) hsr, hs, if_true, mul_one]
    exact usew 0 (by norm_num)
  have hsite1 := site_mem hL (i := 10) (by decide) hsr (k := 1) (by simp [segSys, comps, LC.lc, LC.lookups])
  have hm2 : siteMult segSys inst pub (10, s, 1) = -1 := by
    simp [siteMult, siteEval, siteLookup, hpre, hL 10 (by decide), segSys, comps, LC.lc, LC.lookups, Expr.eval, ev hsr, hmu1]
  obtain ⟨i', r2, k', hr2, hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite1 (by simp [isUse]) hm2
  rw [show siteRel segSys ((10, s, 1) : Site) = 38 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i' = 9 ∧ k' = 7 := by omega
  have ws := lw_sat hL hsat
  have hsm' : (inst 9).main LW.ON r2 * (LW.p LW.P_K0).eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r2 ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hpre9, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups, Expr.eval,
      LW.ev_k (pub := pub) (W := (inst 9).main) hr2] using hsm
  rw [LW.ev_K0 hr2] at hsm'
  have hon2 : (inst 9).main LW.ON r2 = 1 := by
    rcases LW.bool ws (c := LW.ON) (by simp [LW.boolCols]) hr2 with h | h
    · rw [h, zero_mul] at hsm'; exact absurd rfl hsm'
    · exact h
  have hk2 : r2 % 16 = 0 := by by_contra h; rw [if_neg h, mul_zero] at hsm'; exact hsm' rfl
  have hv2 : siteVals segSys inst pub (9, r2, 7) = [(inst 9).main LW.RI r2, (inst 9).main LW.BLK r2,
      (inst 9).main LW.LASTF r2, (inst 9).main LW.T r2] := by
    simp [siteVals, siteEval, siteLookup, hpre9, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups,
      LW.ev_k (pub := pub) (W := (inst 9).main) hr2]
  have hv10 : siteVals segSys inst pub (10, s, 1) = [(inst 10).main LC.RI s, (inst 10).main LC.BLKI s,
      (inst 10).main LC.LASTF s, (inst 10).main LC.T s] := by
    simp [siteVals, siteEval, siteLookup, hpre, hL 10 (by decide), segSys, comps, LC.lc, LC.lookups, ev hsr]
  rw [hv2, hv10] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨eri, eb, el, et⟩ := hsv
  obtain ⟨ρ, b, hρe, hb, hLen, hri, hblk, -, -, hk0⟩ := lw_yield hL hsat hHL hsz E hidx H hr2 hon2
  obtain ⟨hlast, hlb, ht⟩ := hk0 hk2
  have hlen24 : ((inst 3).main Rec.LENC ρ).val < 2 ^ 24 := (Rec.fields (rec_sat hL hsat) E H hρe).2.2.2.1
  refine ⟨ρ, b, hρe, by rw [← eri, hri], by rw [← eb, hblk], hb, by omega, fun kk hkk => ?_, by rw [← el]; exact hlast,
    by rw [← el]; exact hlb, by rw [← et, ht]⟩
  -- the words (rows `s + kk`)
  have hrk : s + kk < 2 ^ Ls 10 := by omega
  have hmu0 : (inst 10).main LC.MU0 (s + kk) = 1 := by
    show (inst 10).main Block.B2s.MU0 (s + kk) = 1
    rw [Block.B2s.defn bs (a := Block.B2s.MU0) (e := .mul (Block.B2s.k Block.B2s.USEW) (Block.B2s.p Block.B2s.P_LT16)) (by simp [Block.B2s.flagC]) hrk]
    simp only [Expr.eval, Block.B2s.ev_k hrk, Block.B2s.ev_lt16 (pub := pub) (M := (inst 10).main) hrk,
      show (s + kk) % 88 < 16 by omega, if_true, mul_one]
    exact usew kk (by omega)
  have hsite0 := site_mem hL (i := 10) (by decide) hrk (k := 0) (by simp [segSys, comps, LC.lc, LC.lookups])
  have hm0 : siteMult segSys inst pub (10, s + kk, 0) = -1 := by
    simp [siteMult, siteEval, siteLookup, hpre, hL 10 (by decide), segSys, comps, LC.lc, LC.lookups, Expr.eval, ev hrk, hmu0]
  obtain ⟨i', r1, k', hr1, hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite0 (by simp [isUse]) hm0
  rw [show siteRel segSys ((10, s + kk, 0) : Site) = 37 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i' = 9 ∧ k' = 6 := by omega
  have hon1 : (inst 9).main LW.ON r1 = 1 := by
    have : (inst 9).main LW.ON r1 ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hpre9, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups,
        LW.ev_k (pub := pub) (W := (inst 9).main) hr1] using hsm
    exact (LW.bool ws (c := LW.ON) (by simp [LW.boolCols]) hr1).resolve_left this
  obtain ⟨ρ1, b1, hρ1, hb1, hLen1, hri1, hblk1, hlo1, hhi1, -⟩ := lw_yield hL hsat hHL hsz E hidx H hr1 hon1
  have hv1 : siteVals segSys inst pub (9, r1, 6) = [(inst 9).main LW.RI r1, (inst 9).main LW.BLK r1,
      ((r1 % 16 : ℕ) : F), LW.lo.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r1,
      LW.hi.eval (2 ^ Ls 9) LW.preCols pub (inst 9).main r1] := by
    simp [siteVals, siteEval, siteLookup, hpre9, hL 9 (by decide), segSys, comps, LW.lw, LW.lookups,
      LW.ev_k (pub := pub) (W := (inst 9).main) hr1, LW.ev_K (pub := pub) (W := (inst 9).main) hr1]
  have hKR : (LC.p LC.P_KR).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main (s + kk) = ((kk : ℕ) : F) := by
    rw [LC.p, show LC.preCols = Block.B2s.preCols from rfl, Block.B2s.ev_per88 (f := fun r => if r < 16 then r else 0) (by simp [Block.B2s.preCols, LC.P_KR, Blake2s.preCols]) hrk,
      show (s + kk) % 88 = kk by omega, if_pos hkk]
  have hv0 : siteVals segSys inst pub (10, s + kk, 0) = [(inst 10).main LC.RI (s + kk), (inst 10).main LC.BLKI (s + kk),
      ((kk : ℕ) : F), (inst 10).main LC.WLO (s + kk), (inst 10).main LC.WHI (s + kk)] := by
    have : siteVals segSys inst pub (10, s + kk, 0) = [LC.k LC.RI, LC.k LC.BLKI, LC.p LC.P_KR, LC.k LC.WLO,
        LC.k LC.WHI].map (Expr.eval (2 ^ Ls 10) LC.preCols pub (inst 10).main (s + kk)) := by
      simp [siteVals, siteEval, siteLookup, hpre, hL 10 (by decide), segSys, comps, LC.lc, LC.lookups]
    rw [this]; simp [ev hrk, hKR]
  rw [hv1, hv0] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨er1, eb1, ek1, elo, ehi⟩ := hsv
  -- the same record and block
  have hP3 := rows_lt_P hL hsz (i := 3) (by decide)
  have hEl := E.lt
  have eρ : ρ1 = ρ := by
    have : ((ρ1 : ℕ) : F) = ((ρ : ℕ) : F) :=
      calc ((ρ1 : ℕ) : F) = (inst 9).main LW.RI r1 := hri1.symm
        _ = (inst 10).main LC.RI (s + kk) := er1
        _ = (inst 10).main LC.RI s := lc_ri_const hL hsat hs kk (by omega) hrk
        _ = (inst 9).main LW.RI r2 := eri.symm
        _ = ρ := hri
    exact natCast_inj_of_lt (by omega) (by omega) this
  subst eρ
  have eb' : b1 = b := by
    have : ((b1 : ℕ) : F) = ((b : ℕ) : F) :=
      calc ((b1 : ℕ) : F) = (inst 9).main LW.BLK r1 := hblk1.symm
        _ = (inst 10).main LC.BLKI (s + kk) := eb1
        _ = (inst 10).main LC.BLKI s :=
          Block.B2s.per_const bs (X := Block.B2s.BLKI) (by simp [Block.B2s.perConst]) hs kk (by omega) hrk
        _ = (inst 9).main LW.BLK r2 := eb.symm
        _ = b := hblk
    unfold Block.B2Msg.nbOf at hb hb1
    exact natCast_inj_of_lt (Block.Fields.lt_P (by omega)) (Block.Fields.lt_P (by omega)) this
  subst eb'
  have ekk : r1 % 16 = kk := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) ek1
  rw [ekk] at hlo1 hhi1
  obtain ⟨wlo, whi⟩ := Block.B2s.msg_word bs hs hsn hkk
  have m0 : (inst 10).main (Blake2s.ML kk 0) s = ((half16 (Spec.Blake2s.wordAt (leafMsg pub (inst 3).main (Sb inst pub) ρ1) b1 kk) 0 : ℕ) : F) := by
    rw [← wlo]; show (inst 10).main LC.WLO (s + kk) = _; rw [← elo, hlo1]
  have m1 : (inst 10).main (Blake2s.ML kk 1) s = ((half16 (Spec.Blake2s.wordAt (leafMsg pub (inst 3).main (Sb inst pub) ρ1) b1 kk) 1 : ℕ) : F) := by
    rw [← whi]; show (inst 10).main LC.WHI (s + kk) = _; rw [← ehi, hhi1]
  refine ⟨MT.msgWord_halves m0 m1, fun h hh => ?_⟩
  have v : ∀ x, (((half16 x h : ℕ) : F)).val < 65536 := fun x => by
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (Sha256.half16_lt x h) (by unfold P; norm_num))]
    exact Sha256.half16_lt x h
  interval_cases h
  · rw [m0]; exact v _
  · rw [m1]; exact v _

omit hHL hsz E hidx in
/-- A used period: not unused, and it continues unless it is a first block. -/
theorem lc_usew {s : ℕ} (hsn : s + 88 ≤ 2 ^ Ls 10) (hu : (inst 10).main LC.USEW s = 1) :
    (inst 10).main LC.NIL s = 0 ∧ ((inst 10).main LC.CHN s = 1 - (inst 10).main LC.FST s) := by
  have bs := lc_n hL hsat
  have hsr : s < 2 ^ Ls 10 := by omega
  have e := Block.B2s.defn bs (a := Block.B2s.USEW) (e := Block.B2s.om (Block.B2s.k Block.B2s.NIL)) (by simp [Block.B2s.flagC]) hsr
  simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, Block.B2s.ev_k hsr] at e
  rw [show Block.B2s.USEW = LC.USEW from rfl, hu] at e
  have hnil : (inst 10).main LC.NIL s = 0 := by show (inst 10).main Block.B2s.NIL s = 0; linear_combination e
  refine ⟨hnil, ?_⟩
  show (inst 10).main Block.B2s.CHN s = 1 - (inst 10).main Block.B2s.FST s
  rw [Block.B2s.defn bs (a := Block.B2s.CHN) (e := Block.B2s.om (.add (Block.B2s.k Block.B2s.FST) (Block.B2s.k Block.B2s.NIL))) (by simp [Block.B2s.flagC]) hsr]
  simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, Block.B2s.ev_k hsr,
    show Block.B2s.NIL = LC.NIL from rfl, hnil]
  ring

omit hHL hsz E hidx in
/-- **A continuing period's predecessor** is a used period of the same record, one block earlier. -/
theorem lc_prev {s : ℕ} (hs : s % 88 = 0) (hsn : s + 88 ≤ 2 ^ Ls 10) (hc : (inst 10).main LC.CHN s = 1) :
    88 ≤ s ∧ (inst 10).main LC.USEW (s - 88) = 1 ∧
      (inst 10).main LC.BLKI s = (inst 10).main LC.BLKI (s - 88) + 1 ∧
      (inst 10).main LC.RI s = (inst 10).main LC.RI (s - 88) := by
  have bs := lc_n hL hsat
  have cs := lc_sat hL hsat
  have hsr : s < 2 ^ Ls 10 := by omega
  have h88 : 88 ≤ s := by
    have := Block.B2s.sat bs (Block.B2s.mem_chain (c := .mul (Block.B2s.p Block.B2s.P_OUT8) (Block.B2s.k Block.B2s.CHN))
      (by simp [Block.B2s.chainC])) hsr
    simp only [Expr.eval, Block.B2s.ev_out8 (pub := pub) (M := (inst 10).main) hsr, Block.B2s.ev_k hsr,
      show Block.B2s.CHN = LC.CHN from rfl, hc, mul_one] at this
    by_contra h
    rw [if_pos (by omega)] at this; exact one_ne_zero this
  have hq : wrap (2 ^ Ls 10) s (-88) = s - 88 := by
    rw [show (-88 : ℤ) = -((88 : ℕ) : ℤ) by simp, StarkedAir.Sha256.wrap_back h88 hsr]
  have kq : ∀ c, (Block.B2s.kq c).eval (2 ^ Ls 10) Block.B2s.preCols pub (inst 10).main s = (inst 10).main c (s - 88) := by
    intro c; simp [Block.B2s.kq, StarkedAir.Sha256.eval_col, hq]
  have hr0 : (Block.B2s.p Block.B2s.P_R0).eval (2 ^ Ls 10) Block.B2s.preCols pub (inst 10).main s = 1 := by
    rw [Block.B2s.ev_r0 (pub := pub) (M := (inst 10).main) hsr, if_pos hs]
  have c := fun (e : Expr) (h : e ∈ Block.B2s.chainC) => Block.B2s.sat bs (Block.B2s.mem_chain h) hsr
  have c2 := c (.mul (Block.B2s.p Block.B2s.P_R0) (.mul (Block.B2s.k Block.B2s.CHN) (.sub (.sub (Block.B2s.k Block.B2s.BLKI)
    (Block.B2s.kq Block.B2s.BLKI)) Block.B2s.one))) (by simp [Block.B2s.chainC])
  have c3 := c (.mul (Block.B2s.p Block.B2s.P_R0) (.mul (Block.B2s.k Block.B2s.CHN) (Block.B2s.kq Block.B2s.NIL)))
    (by simp [Block.B2s.chainC])
  have cri := cs s hsr (.mul (Block.B2s.p Block.B2s.P_R0) (.mul (Block.B2s.k LC.CHN) (.sub (Block.B2s.k LC.RI)
    (Block.B2s.kq LC.RI)))) (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ (by simp [LC.chainC, LC.p, LC.k, LC.kq, Block.B2s.p, Block.B2s.k, Block.B2s.kq, LC.P_R0, Block.B2s.P_R0])))))
  rw [show LC.preCols = Block.B2s.preCols from rfl] at cri
  simp only [Expr.eval, hr0, one_mul, Block.B2s.ev_k hsr, show Block.B2s.CHN = LC.CHN from rfl, hc, kq, Block.B2s.one,
    StarkedAir.Sha256.eval_cst, Nat.cast_one, sub_eq_zero] at c2 c3 cri
  have hs' : s - 88 < 2 ^ Ls 10 := by omega
  refine ⟨h88, ?_, by show (inst 10).main Block.B2s.BLKI s = (inst 10).main Block.B2s.BLKI (s - 88) + 1; linear_combination c2, cri⟩
  show (inst 10).main Block.B2s.USEW (s - 88) = 1
  rw [Block.B2s.defn bs (a := Block.B2s.USEW) (e := Block.B2s.om (Block.B2s.k Block.B2s.NIL)) (by simp [Block.B2s.flagC]) hs']
  simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, Block.B2s.ev_k hs', c3]
  ring

/-- **The chain.** A used period of record `ρ` hashing block `b` starts from the spec's chaining value of
`ρ`'s leaf message after `b` blocks. -/
theorem lc_chain (H : Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub)) {ρ : ℕ} (hρe : ρ < e) :
    ∀ b : ℕ, b + 1 < P → ∀ s, s % 88 = 0 → s + 88 ≤ 2 ^ Ls 10 → (inst 10).main LC.USEW s = 1 →
    (inst 10).main LC.RI s = (ρ : F) → (inst 10).main LC.BLKI s = (b : F) →
    ∀ i < 8, Blake2s.diagSlot (inst 10).main s i =
      Spec.Blake2s.chainS Spec.Blake2s.h0 0 (leafMsg pub (inst 3).main (Sb inst pub) ρ) b i := by
  have bs := lc_n hL hsat
  have hP3 := rows_lt_P hL hsz (i := 3) (by decide)
  have hEl := E.lt
  intro b
  induction b with
  | zero =>
    intro _ s hs hsn hu _ hblk i hi
    obtain ⟨hnil, hchn⟩ := lc_usew hL hsat hsn hu
    rcases Block.B2s.bool_flag bs (c := Block.B2s.FST) (by simp) (show s < 2 ^ Ls 10 by omega) with f0 | f1
    · exfalso
      rw [show LC.FST = Block.B2s.FST from rfl, f0, sub_zero] at hchn
      obtain ⟨h88, hu', hblk', -⟩ := lc_prev hL hsat hs hsn hchn
      obtain ⟨ρ2, b2, -, -, hb2, hlt2, hl25, -⟩ := lc_block hL hsat hHL hsz E hidx H (s := s - 88) (by omega) (by omega) hu'
      rw [hblk, hb2] at hblk'
      have : ((b2 + 1 : ℕ) : F) = ((0 : ℕ) : F) := by push_cast; linear_combination -hblk'
      have hb2' : b2 + 1 ≤ 2 ^ 30 := by unfold Block.B2Msg.nbOf at hlt2; omega
      have := natCast_inj_of_lt (Block.Fields.lt_P hb2') (Block.Fields.lt_P (by norm_num)) this
      omega
    · have := Block.B2s.h_first bs hs hsn (by rw [f1]; exact one_ne_zero) i hi
      rw [this]; rfl
  | succ b ih =>
    intro hbP s hs hsn hu hri hblk i hi
    obtain ⟨hnil, hchn⟩ := lc_usew hL hsat hsn hu
    have f0 : (inst 10).main LC.FST s = 0 := by
      have := Block.B2s.sat bs (Block.B2s.mem_chain (c := .mul (Block.B2s.p Block.B2s.P_R0) (.mul (Block.B2s.k Block.B2s.FST)
        (Block.B2s.k Block.B2s.BLKI))) (by simp [Block.B2s.chainC])) (show s < 2 ^ Ls 10 by omega)
      simp only [Expr.eval, Block.B2s.ev_r0 (pub := pub) (M := (inst 10).main) (show s < 2 ^ Ls 10 by omega), if_pos hs,
        one_mul, Block.B2s.ev_k (show s < 2 ^ Ls 10 by omega), show Block.B2s.BLKI = LC.BLKI from rfl, hblk] at this
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · exfalso
        have := natCast_inj_of_lt (a := b + 1) (b := 0) (by omega) (by unfold P; norm_num) (by simpa using h)
        omega
    rw [f0, sub_zero] at hchn
    obtain ⟨h88, hu', hblk', hri'⟩ := lc_prev hL hsat hs hsn hchn
    have hs' : (s - 88) % 88 = 0 := by omega
    have hsn' : s - 88 + 88 ≤ 2 ^ Ls 10 := by omega
    obtain ⟨ρ2, b2, hρ2, hri2, hblk2, hlt2, hl2, hwords2, hlast2, hlb2, ht2⟩ :=
      lc_block hL hsat hHL hsz E hidx H hs' hsn' hu'
    obtain ⟨ρ1, b1, hρ1, hri1, hblk1, hlt1, hl1, -, -, -, -⟩ := lc_block hL hsat hHL hsz E hidx H hs hsn hu
    have eρ1 : ρ = ρ1 := (natCast_inj_of_lt (by omega) (by omega) (by rw [← hri1, hri])).symm
    have eρ2 : ρ = ρ2 := (natCast_inj_of_lt (by omega) (by omega) (by rw [← hri2, ← hri', hri])).symm
    subst eρ1; subst eρ2
    have eb1 : b + 1 = b1 := natCast_inj_of_lt (by omega)
      (Block.Fields.lt_P (by unfold Block.B2Msg.nbOf at hlt1; omega)) (by rw [← hblk1, hblk])
    have eb2 : b = b2 := by
      have : ((b2 + 1 : ℕ) : F) = ((b + 1 : ℕ) : F) := by push_cast; rw [← hblk2, ← hblk', hblk]; push_cast; ring
      have := natCast_inj_of_lt (Block.Fields.lt_P (by unfold Block.B2Msg.nbOf at hlt2; omega))
        (Block.Fields.lt_P (by unfold Block.B2Msg.nbOf at hlt1; omega)) this
      omega
    subst eb1; subst eb2
    have ihs := ih (by omega) (s - 88) hs' hsn' hu' hri2 hblk2
    have hnl : ¬ (b + 1 = Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length) := by omega
    have hl0 : (inst 10).main LC.LASTF (s - 88) = 0 := by
      rcases hlb2 with h | h
      · exact h
      · exact absurd (hlast2.mp h) hnl
    obtain ⟨hnil2, -⟩ := lc_usew hL hsat hsn' hu'
    obtain ⟨htv, hfv⟩ := Block.B2s.tf bs hs' (by omega) hnil2
    have hinT : Blake2s.inT (inst 10).main (s - 88) = 64 * (b + 1) := by
      rw [htv, show Block.B2s.T = LC.T from rfl, ht2, if_neg hnl,
        ZMod.val_natCast_of_lt (Block.Fields.lt_P (by unfold Block.B2Msg.nbOf at hlt1; omega))]
    have hfb : Blake2s.fBit (inst 10).main (s - 88) = false := by
      by_contra h
      rw [Bool.not_eq_false] at h
      rw [show LC.LASTF = Block.B2s.LASTF from rfl, hfv.mp h] at hl0; exact one_ne_zero hl0
    have hm : ∀ kk < 16, ∀ h ≤ 1, ((inst 10).main (Blake2s.ML kk h) (s - 88)).val < 65536 := fun kk hkk =>
      (hwords2 kk hkk).2
    have hcomp := Block.B2s.period_compress bs hs' (by omega) hm
    rw [Block.B2s.h_chain bs hs hsn h88 hchn i hi, ← hcomp i hi, hinT, hfb]
    simp only [Spec.Blake2s.chainS, if_pos hi, Nat.zero_add]
    exact Spec.Blake2s.compress_congr ihs (fun kk hkk => (hwords2 kk hkk).1) _ _ i hi

/-- **A record's last block outputs its leaf message's Blake2s hash** (as chaining words). -/
theorem lc_last (H : Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub)) {s : ℕ} (hs : s % 88 = 0)
    (hsn : s + 88 ≤ 2 ^ Ls 10) (hu : (inst 10).main LC.USEW s = 1) (hl : (inst 10).main LC.LASTF s = 1) :
    ∃ ρ, ρ < e ∧ (inst 10).main LC.RI s = (ρ : F) ∧ ∀ i < 8, Blake2s.outWord (inst 10).main s i =
      Spec.Blake2s.hashBlocks Spec.Blake2s.h0 0 (leafMsg pub (inst 3).main (Sb inst pub) ρ) i := by
  have bs := lc_n hL hsat
  obtain ⟨ρ, b, hρe, hri, hblk, hlt, hl25, hwords, hlast, -, ht⟩ := lc_block hL hsat hHL hsz E hidx H hs hsn hu
  have hb : b + 1 = Block.B2Msg.nbOf (leafMsg pub (inst 3).main (Sb inst pub) ρ).length := hlast.mp hl
  have hch := lc_chain hL hsat hHL hsz E hidx H hρe b (by unfold Block.B2Msg.nbOf at hb; unfold P; omega) s hs hsn hu hri hblk
  obtain ⟨hnil, -⟩ := lc_usew hL hsat hsn hu
  obtain ⟨htv, hfv⟩ := Block.B2s.tf bs hs hsn hnil
  have hinT : Blake2s.inT (inst 10).main s = (leafMsg pub (inst 3).main (Sb inst pub) ρ).length := by
    rw [htv, show Block.B2s.T = LC.T from rfl, ht, if_pos hb, ZMod.val_natCast_of_lt (Block.Fields.lt_P (by omega))]
  have hfb : Blake2s.fBit (inst 10).main s = true := hfv.mpr hl
  have hcomp := Block.B2s.period_compress bs hs hsn (fun kk hkk => (hwords kk hkk).2)
  refine ⟨ρ, hρe, hri, fun i hi => ?_⟩
  rw [← hcomp i hi, hinT, hfb, Spec.Blake2s.hashBlocks_eq b _ 0 _ (by unfold Block.B2Msg.nbOf at hb; omega)
    (by unfold Block.B2Msg.nbOf at hb; omega) i hi, Nat.zero_add]
  exact Spec.Blake2s.compress_congr hch (fun kk hkk => (hwords kk hkk).1) _ _ i hi

omit hHL hsz E hidx in
theorem lc_ysite {r k : ℕ} (hr : r < 2 ^ Ls 10) (hk2 : 2 ≤ k) (hk10 : k < 10) :
    siteMult segSys inst pub (10, r, k) = (inst 10).main LC.YD r *
      (LC.p (Blake2s.P_FIN ((k - 2) / 2))).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r ∧
    siteVals segSys inst pub (10, r, k) = [(inst 10).main LC.RI r, ((MT.widx k : ℕ) : F),
      (Blake2s.limb (if (k - 2) % 2 = 0 then 0 else 1) 0).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r,
      (Blake2s.limb (if (k - 2) % 2 = 0 then 0 else 1) 1).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r] := by
  have ev : ∀ c, (LC.k c).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r = (inst 10).main c r := fun c =>
    Block.B2s.ev_k (pub := pub) (M := (inst 10).main) hr
  interval_cases k <;>
    simp [siteMult, siteVals, siteEval, siteLookup, segSys, comps, hL 10 (by decide), LC.lc, LC.lookups, Expr.eval, ev,
      MT.widx, Block.B2s.bidx, StarkedAir.Sha256.eval_cst, LC.p, List.range_succ]

omit hL hsat hHL hsz E hidx in
theorem stWord_toState (f : ℕ → Spec.Blake2s.Word) {w : ℕ} (hw : w < 8) :
    Spec.HeaderTree.stWord (Spec.HeaderTree.toState f) w = f w := by
  interval_cases w <;> rfl

/-- **A leaf yield** carries a record's leaf words: `Blake2s-256` of its leaf message. -/
theorem leaf_yield (H : Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub)) {r k : ℕ} (hr : r < 2 ^ Ls 10)
    (hk2 : 2 ≤ k) (hk10 : k < 10) (hm : siteMult segSys inst pub (10, r, k) ≠ 0) :
    ∃ s < e, siteVals segSys inst pub (10, r, k) = [(s : F), ((MT.widx k : ℕ) : F),
      ((half16 (Spec.HeaderTree.stWord (Spec.SetMerkle.leafHash (leafMsg pub (inst 3).main (Sb inst pub) s))
        (MT.widx k)) 0 : ℕ) : F),
      ((half16 (Spec.HeaderTree.stWord (Spec.SetMerkle.leafHash (leafMsg pub (inst 3).main (Sb inst pub) s))
        (MT.widx k)) 1 : ℕ) : F)] := by
  have bs := lc_n hL hsat
  obtain ⟨em, ev⟩ := lc_ysite hL hsat (pub := pub) (inst := inst) hr hk2 hk10
  set j := (k - 2) / 2 with hj
  have hj4 : j < 4 := by omega
  set s' := r - r % 88 with hs'
  have hrs : r = s' + r % 88 := by omega
  have hfin : (LC.p (Blake2s.P_FIN j)).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r =
      if r % 88 = 84 + j then 1 else 0 := by
    rw [LC.p, show LC.preCols = Block.B2s.preCols from rfl, Block.B2s.eval_pre_gadget (by simp [Blake2s.P_FIN]; omega)]
    conv_lhs => rw [hrs]
    rw [Blake2s.pre_at (s := s') (by simp [Blake2s.PERIOD]; omega) (by simp [Blake2s.PERIOD]; omega) (by omega)
      (by simp [Blake2s.P_FIN]; omega), Blake2s.bPre_FIN hj4 (by simp [Blake2s.PERIOD]; omega)]
  rw [em, hfin] at hm
  have h84 : r % 88 = 84 + j := by by_contra h; rw [if_neg h, mul_zero] at hm; exact hm rfl
  rw [if_pos h84, mul_one] at hm
  have hfull := MT.full_period hr (by omega)
  have hs88 : s' % 88 = 0 := by omega
  have hrow : r = s' + (84 + j) := by omega
  have yd := Block.B2s.defn bs (a := Block.B2s.YD) (e := .mul (Block.B2s.k Block.B2s.USEW) (Block.B2s.k Block.B2s.LASTF))
    (by simp [Block.B2s.flagC]) hr
  simp only [Expr.eval, Block.B2s.ev_k hr] at yd
  have hus := Block.B2s.defn bs (a := Block.B2s.USEW) (e := Block.B2s.om (Block.B2s.k Block.B2s.NIL)) (by simp [Block.B2s.flagC]) hr
  simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, Block.B2s.ev_k hr] at hus
  have hnil := Block.B2s.bool_flag bs (c := Block.B2s.NIL) (by simp) hr
  have hlast := Block.B2s.bool_flag bs (c := Block.B2s.LASTF) (by simp) hr
  have hu1 : (inst 10).main Block.B2s.USEW r = 1 ∧ (inst 10).main Block.B2s.LASTF r = 1 := by
    rw [show LC.YD = Block.B2s.YD from rfl, yd, hus] at hm
    rcases hnil with n0 | n1 <;> rcases hlast with l0 | l1
    · rw [l0, mul_zero] at hm; exact absurd rfl hm
    · exact ⟨by rw [hus, n0]; ring, l1⟩
    · rw [l0, mul_zero] at hm; exact absurd rfl hm
    · exfalso; rw [n1, sub_self, zero_mul] at hm; exact hm rfl
  have hq : ∀ X ∈ Block.B2s.perConst, (inst 10).main X r = (inst 10).main X s' := by
    intro X hX; rw [hrow]; exact Block.B2s.per_const bs hX hs88 (84 + j) (by omega) (by omega)
  have husew : (inst 10).main LC.USEW s' = 1 := by
    have e0 := Block.B2s.defn bs (a := Block.B2s.USEW) (e := Block.B2s.om (Block.B2s.k Block.B2s.NIL)) (by simp [Block.B2s.flagC])
      (show s' < 2 ^ Ls 10 by omega)
    simp only [Expr.eval, Block.B2s.om, Block.B2s.one, StarkedAir.Sha256.eval_cst, Nat.cast_one,
      Block.B2s.ev_k (show s' < 2 ^ Ls 10 by omega)] at e0
    show (inst 10).main Block.B2s.USEW s' = 1
    rw [e0, ← hq Block.B2s.NIL (by simp [Block.B2s.perConst]), ← hus, hu1.1]
  have hl' : (inst 10).main LC.LASTF s' = 1 := by
    show (inst 10).main Block.B2s.LASTF s' = 1
    rw [← hq Block.B2s.LASTF (by simp [Block.B2s.perConst]), hu1.2]
  obtain ⟨ρ, hρe, hri, hdig⟩ := lc_last hL hsat hHL hsz E hidx H hs88 hfull husew hl'
  refine ⟨ρ, hρe, ?_⟩
  rw [ev, show (inst 10).main LC.RI r = (inst 10).main LC.RI s' by rw [hrow]; exact lc_ri_const hL hsat hs88 _ (by omega) (by omega), hri]
  have hbits : ∀ w < 8, ∀ i < 32, ((inst 10).main (32 * w + i) r).val ≤ 1 := fun w hw => Block.B2s.bits4 bs hr w hw
  have lim : ∀ w < 2, ∀ h ≤ 1, (Blake2s.limb w h).eval (2 ^ Ls 10) LC.preCols pub (inst 10).main r =
      ((half16 (Sha256.word (inst 10).main (32 * w) r) h : ℕ) : F) := by
    intro w hw h hh
    exact StarkedAir.Sha256.eval_limb (wrap_zero hr) (hbits w (by omega)) hh
  have hwx := MT.widx_lt hk2 hk10
  rw [Spec.SetMerkle.leafHash, stWord_toState _ hwx]
  by_cases h0 : (k - 2) % 2 = 0
  · rw [if_pos h0, lim 0 (by norm_num) 0 (by norm_num), lim 0 (by norm_num) 1 (by norm_num)]
    have : Sha256.word (inst 10).main (32 * 0) r = Spec.Blake2s.hashBlocks Spec.Blake2s.h0 0
        (leafMsg pub (inst 3).main (Sb inst pub) ρ) (MT.widx k) := by
      rw [show MT.widx k = j by simp [MT.widx, h0, hj], ← hdig j (by omega), Blake2s.outWord, if_pos hj4, hrow]; ring_nf
    rw [this]
  · rw [if_neg h0, lim 1 (by norm_num) 0 (by norm_num), lim 1 (by norm_num) 1 (by norm_num)]
    have hb : Block.B2s.bidx j < 8 ∧ 4 ≤ Block.B2s.bidx j ∧ (Block.B2s.bidx j + 3) % 4 = j := by
      interval_cases j <;> decide
    have : Sha256.word (inst 10).main (32 * 1) r = Spec.Blake2s.hashBlocks Spec.Blake2s.h0 0
        (leafMsg pub (inst 3).main (Sb inst pub) ρ) (MT.widx k) := by
      rw [show MT.widx k = Block.B2s.bidx j by simp [MT.widx, h0, hj], ← hdig _ hb.1, Blake2s.outWord, if_neg (by omega),
        hb.2.2, hrow]
      ring_nf
    rw [this]

end Leaves

end StarkedAir.SetPass
