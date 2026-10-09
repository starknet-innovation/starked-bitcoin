/-
**Merkle tree soundness, system level (M3a.4).** In a satisfied system (bytes, fields, msg, sha, merkle),
each Merkle node id's second hash outputs SHA256d of its children's digests, and the root matches the
header's Merkle field.
-/
import StarkedAir.Block.HashSound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst limb word messageAt outputAt)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 5, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub [])
include hL hsat

/-- The digest tuple of a second-hash period: its id and the limbs of its output state's words. -/
theorem digest_vals {q : ℕ} (hn : 72 * q + 72 ≤ 2 ^ L) :
    siteVals hashSys inst pub (3, 72 * q + 71, 2) = (inst 3).main Sha.MID (72 * q) ::
      (List.range 16).map (fun j =>
        ((Sha256.half16 (Spec.Bitcoin.stateWord (outputAt (inst 3).main (72 * q)) (j / 2)) (j % 2) : ℕ) : F)) := by
  have ss := hash_sha_sat hL hsat
  have hr : 72 * q + 71 < 2 ^ L := by omega
  have e : siteVals hashSys inst pub (3, 72 * q + 71, 2) =
      (Sha.k Sha.MID :: Sha.digestLimbs).map (Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main (72 * q + 71)) := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups]
  rw [e, List.map_cons]
  congr 1
  · simp only [Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
    exact Sha.per_const ss (X := Sha.MID) (by simp) (s := 72 * q) (by omega) 71 (by norm_num) hr
  · apply List.ext_getElem
    · simp [Sha.digestLimbs]
    · intro j h1 h2
      have hj : j < 16 := by simpa [Sha.digestLimbs] using h1
      simp only [List.getElem_map, List.getElem_range]
      have := Sha.digest_tuple ss (s := 72 * q) hn hj
      rw [List.getD_eq_getElem _ _ (by simp [Sha.digestLimbs]; exact hj)] at this
      exact this

/-- Message ids are small: below `2^26 + 2`, hence below `NB`. -/
theorem msg_mid_lt (hL25 : L ≤ 25) {r0 : ℕ} (h0 : r0 < 2 ^ L) (f0 : (inst 2).main Msg.FIRSTM r0 = 1) :
    ((inst 2).main Msg.MID r0).val < Merkle.NB := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  rw [Msg.mid_eq ms h0]
  rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h0 with h | h
  · obtain ⟨ρ, hρ, -, ti, -⟩ := msg_tuple_row hL hsat hL25 h0 f0 h
    have hw := Fields.bool_val (Msg.bool_col ms (e := Msg.WTX) (by simp) h0)
    rw [h, sub_zero, one_mul, ← ti, Fields.txi_count fs ρ hρ, hw.1]
    have := Fields.locks_le (M := (inst 1).main) ρ
    rw [show (1 : F) + 2 * ((Fields.locks (inst 1).main ρ : ℕ) : F) + (((inst 2).main Msg.WTX r0).val : F) =
      ((1 + 2 * Fields.locks (inst 1).main ρ + ((inst 2).main Msg.WTX r0).val : ℕ) : F) by push_cast; ring,
      ZMod.val_natCast_of_lt (Fields.lt_P (by omega))]
    unfold Merkle.NB; omega
  · rw [h, sub_self, zero_mul]; simp [Merkle.NB]

/-- **A node id's second hash** finishes a node block and its padding block (same id). -/
theorem node_period (hL25 : L ≤ 25) {q : ℕ} (hn : 72 * q + 72 ≤ 2 ^ L) (hd : (inst 3).main Sha.DBL (72 * q) = 1)
    (hmid : Merkle.NB ≤ ((inst 3).main Sha.MID (72 * q)).val) :
    2 ≤ q ∧ (inst 3).main Sha.NPAD (72 * (q - 1)) = 1 ∧ (inst 3).main Sha.NODE (72 * (q - 2)) = 1 ∧
      (inst 3).main Sha.MID (72 * (q - 2)) = (inst 3).main Sha.MID (72 * q) := by
  have ss := hash_sha_sat hL hsat
  have ms := hash_msg_sat hL hsat
  have hx : 72 * q < 2 ^ L := by omega
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  have r0q : (pre Sha.ROW0).eval (2 ^ L) Sha.preCols pub (inst 3).main (72 * q) = 1 := Sha.row0_at ss hx
  -- not period 0
  have hq1 : 1 ≤ q := by
    by_contra h
    have e : q = 0 := by omega
    subst e
    have := Sha.order_sat ss (c := .mul (pre Sha.FIRST) (.add (Sha.k Sha.CHN) (Sha.k Sha.DBL))) (by simp [Sha.orderC])
      (show 0 < 2 ^ L by omega)
    have hfirst : (pre Sha.FIRST).eval (2 ^ L) Sha.preCols pub (inst 3).main 0 = 1 := by
      simp only [pre, Expr.eval, wrap_zero (show 0 < 2 ^ L by omega)]
      rw [show Sha.preCols.getD Sha.FIRST (.periodic [0]) = .isFirst from rfl]; simp [PreCol.eval]
    simp only [Nat.mul_zero] at hd
    simp only [Expr.eval, hfirst, one_mul, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero (show 0 < 2 ^ L by omega), hd] at this
    have hc := Sha.chn_eq ss (show 0 < 2 ^ L by omega)
    rw [hd] at hc
    obtain ⟨-, -, -, -, e5, -, -, -, e9, -⟩ := Sha.kinds_excl ss (show 0 < 2 ^ L by omega)
    rw [hd, mul_one] at e5 e9
    obtain ⟨e1, -, e3, -⟩ := Sha.kinds_excl ss (show 0 < 2 ^ L by omega)
    rw [hd, mul_one] at e1; rw [hd, one_mul] at e3
    rw [hc, e1, e3, e5, e9] at this
    norm_num at this
  -- the length check reads a Merkle node's length 128: the previous period is block 1
  have hm' : siteMult hashSys inst pub (3, 72 * q, 1) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide)]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
    simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval]
    rw [r0q, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hx, hd]; ring
  have hv3 : siteVals hashSys inst pub (3, 72 * q, 1) = [(inst 3).main Sha.MID (72 * q),
      (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main (72 * q)] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  obtain ⟨r', hr', hlink⟩ := sha_use_linked hL hsat hL25 hx (kk := 1) (by norm_num) hm'
  have hb1 : (inst 3).main Sha.BLKI (72 * (q - 1)) = 1 := by
    rcases hlink with ⟨hym, hyv⟩ | ⟨-, hym, hyv⟩
    · exfalso
      have hmult : (inst 2).main Msg.LN r' * (inst 2).main Msg.MM r' ≠ 0 := by
        simpa [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr'] using hym
      obtain ⟨r0, d, f0, -, -, heq, hm0, -⟩ := Msg.len_yield ms hr' hmult
      have hv2 : siteVals hashSys inst pub (2, r', 1 + 2) = [(inst 2).main Msg.MID r', (inst 2).main Msg.IDX r' + 1] := by
        simp [siteVals, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Msg.k, Msg.one,
          StarkedAir.Sha256.eval_col, wrap_zero hr', Expr.eval, StarkedAir.Sha256.eval_cst]
      rw [hv2, hv3] at hyv
      simp only [List.cons.injEq] at hyv
      have h0 : r0 < 2 ^ L := by omega
      have := msg_mid_lt hL hsat hL25 h0 f0
      rw [← hm0, hyv.1] at this; omega
    · have hv4 : siteVals hashSys inst pub (4, r', 1) = [(Merkle.NB : F) + (inst 4).main Merkle.RIX r', 128] := by
        simp [siteVals, siteEval, siteLookup, hashSys, hL 4 (by decide), Merkle.merkle, Merkle.lookups,
          Merkle.nodeId, Merkle.k, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
      rw [hv4, hv3] at hyv
      simp only [List.cons.injEq, and_true] at hyv
      have e2 := hyv.2
      simp only [Expr.eval, Sha.kp, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst] at e2
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, StarkedAir.Sha256.wrap_back (by omega) hx,
        show 72 * q - 1 = 72 * (q - 1) + 71 by omega,
        Sha.per_const ss (X := Sha.BLKI) (by simp) (s := 72 * (q - 1)) (by omega) 71 (by norm_num) (by omega)] at e2
      have h64 : (64 : F) ≠ 0 := by
        intro h; have := natCast_inj_of_lt (a := 64) (b := 0) (Fields.lt_P (by norm_num)) (Fields.lt_P (by norm_num))
          (by simpa using h); omega
      have : (64 : F) * ((inst 3).main Sha.BLKI (72 * (q - 1)) - 1) = 0 := by
        push_cast at e2; linear_combination -e2
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h h64
      · exact sub_eq_zero.mp h
  -- the previous period's kind
  have hp := (Sha.prev_facts ss hq1 hn).2 hd
  obtain ⟨hpd, hpn⟩ := Sha.not_dn ss (by omega) hp.2
  have hpr : 72 * (q - 1) < 2 ^ L := by omega
  have fst0 : (inst 3).main Sha.FST (72 * (q - 1)) = 0 := by
    rcases Sha.kbool ss (c := Sha.FST) (by simp) hpr with h | h
    · exact h
    · have := Sha.order_sat ss (c := .mul (Sha.k Sha.FST) (Sha.k Sha.BLKI)) (by simp [Sha.orderC]) hpr
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hpr, h, hb1, mul_one] at this
      exact absurd this one_ne_zero
  have node0 : (inst 3).main Sha.NODE (72 * (q - 1)) = 0 := by
    rcases Sha.kbool ss (c := Sha.NODE) (by simp) hpr with h | h
    · exact h
    · have := hsat.1 3 (by decide) (72 * (q - 1)) (by rw [hL 3 (by decide)]; exact hpr) (.mul (Sha.k Sha.NODE) (Sha.k Sha.BLKI))
        (by have hm : Expr.mul (Sha.k Sha.NODE) (Sha.k Sha.BLKI) ∈ Sha.nodeOrderC := by simp [Sha.nodeOrderC]
            simp only [hashSys, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
              ↓reduceIte, Sha.sha, Sha.constraints, List.mem_append]; tauto)
      simp only [hashSys, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide,
        ↓reduceIte, Sha.sha, hL 3 (by decide)] at this
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hpr, h, hb1, mul_one] at this
      exact absurd this one_ne_zero
  rcases Sha.kbool ss (c := Sha.NPAD) (by simp) hpr with hnp | hnp
  · -- a continuation reads message words: its id is a message id, too small
    exfalso
    have hchn : (inst 3).main Sha.CHN (72 * (q - 1)) = 1 := by
      rw [Sha.chn_eq ss hpr, fst0, hpd, hpn, node0, hnp]; ring
    have hs : (72 * (q - 1)) % 72 = 0 := by omega
    have hu : (inst 3).main Sha.USEW (72 * (q - 1) + 4) = 1 := by
      rw [Sha.usew_eq ss (by omega)]
      rw [show 72 * (q - 1) + 4 = 72 * (q - 1) + 4 by rfl,
        Sha.per_const ss (X := Sha.DBL) (by simp) hs 4 (by norm_num) (by omega),
        Sha.per_const ss (X := Sha.NILS) (by simp) hs 4 (by norm_num) (by omega),
        Sha.per_const ss (X := Sha.NODE) (by simp) hs 4 (by norm_num) (by omega),
        Sha.per_const ss (X := Sha.NPAD) (by simp) hs 4 (by norm_num) (by omega), hpd, hpn, node0, hnp]; ring
    have hrow : (Expr.mul (pre Sha.MSGROW) (Sha.k Sha.USEW)).eval (2 ^ L) Sha.preCols pub (inst 3).main
        (72 * (q - 1) + 4) = 1 := by
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero (show 72 * (q - 1) + 4 < 2 ^ L by omega), hu,
        mul_one]
      rw [Sha.eval_per72 ss (i := Sha.MSGROW) (f := fun q => if 4 ≤ q ∧ q < 20 then 1 else 0) rfl (by omega),
        show (72 * (q - 1) + 4) % 72 = 4 by omega]; simp
    obtain ⟨r0, j, hr0, -, -, f0, -, m1, -⟩ := sha_word hL hsat hL25 (by omega) hrow
    have := msg_mid_lt hL hsat hL25 (by omega) f0
    rw [m1, Sha.per_const ss (X := Sha.MID) (by simp) hs 4 (by norm_num) (by omega), hp.1.symm] at this
    omega
  · obtain ⟨hq2, hno, hme⟩ := Sha.npad_prev ss (q := q - 1) (by omega) hnp
    refine ⟨by omega, hnp, by rw [show q - 2 = q - 1 - 1 by omega]; exact hno, ?_⟩
    rw [show q - 2 = q - 1 - 1 by omega, hme, ← hp.1]

end System

end StarkedAir.Block
