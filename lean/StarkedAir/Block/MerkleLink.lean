/-
**Merkle tree soundness, system level (M3a.4).** In a satisfied system (bytes, fields, msg, sha, merkle),
each Merkle node id's second hash outputs SHA256d of its children's digests, and the root matches the
header's Merkle field.
-/
import StarkedAir.Block.HashSound
import StarkedAir.Spec.MerkleLevels

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst limb word messageAt outputAt)

/-- A word is its two 16-bit limbs. -/
theorem word_of_halves {y z : Spec.Sha256.Word} (h0 : Sha256.half16 y 0 = Sha256.half16 z 0)
    (h1 : Sha256.half16 y 1 = Sha256.half16 z 1) : y = z := by
  apply BitVec.eq_of_toNat_eq
  simp only [Sha256.half16] at h0 h1
  have := y.isLt; have := z.isLt
  omega

theorem half16_lt (y : Spec.Sha256.Word) (h : ℕ) : Sha256.half16 y h < 2 ^ 16 := by
  have := y.isLt
  rcases h with _ | h <;> simp only [Sha256.half16] <;> omega

theorem lvs_len (l0 : List Spec.Block.Bytes) : ∀ k, (Spec.Block.lvs l0 k).length = Merkle.cntL l0.length k
  | 0 => rfl
  | k + 1 => by rw [Spec.Block.lvs_length, lvs_len l0 k]; rfl

theorem npad_eq : Sha.npadBlock = HashSpec.npadBlk := by
  funext t
  unfold Sha.npadBlock HashSpec.npadBlk Sha.npadWord
  by_cases h0 : t = 0
  · subst h0; rfl
  · by_cases h15 : t = 15
    · subst h15; rfl
    · simp [h0, h15]

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

/-- **A node block's children.** Words `0..7` (`8..15`) of a node block at `s` are the output state of a
second hash whose id is the node's left (right) child. -/
theorem node_children (hL25 : L ≤ 25) {p : ℕ} (hp : 72 * p + 72 ≤ 2 ^ L) (ho : (inst 3).main Sha.NODE (72 * p) = 1) :
    ∀ half ≤ 1, ∃ q', 72 * q' + 72 ≤ 2 ^ L ∧ (inst 3).main Sha.DBL (72 * q') = 1 ∧
      (inst 3).main Sha.MID (72 * q') = (if half = 0 then (inst 3).main Sha.LID (72 * p) else (inst 3).main Sha.RID (72 * p)) ∧
      ∀ t < 8, messageAt (inst 3).main (72 * p) (8 * half + t) = Spec.Bitcoin.stateWord (outputAt (inst 3).main (72 * q')) t := by
  intro half hh
  have ss := hash_sha_sat hL hsat
  have hs : (72 * p) % 72 = 0 := by omega
  set x := 72 * p + 11 + 8 * half with hx
  have hxr : x < 2 ^ L := by omega
  have hxs : x = 72 * p + (11 + 8 * half) := by omega
  have hnode : (inst 3).main Sha.NODE x = 1 := by
    rw [hxs, Sha.per_const ss (X := Sha.NODE) (by simp) hs _ (by omega) (by omega), ho]
  have hm : siteMult hashSys inst pub (3, x, 4 + half) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide)]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
    interval_cases half
    · simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, Sha.k,
        StarkedAir.Sha256.eval_col, wrap_zero hxr, hnode, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.DLR) (f := fun q => if q = 11 then 1 else 0) rfl hxr,
        show x % 72 = 11 by omega]; simp
    · simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, Sha.k,
        StarkedAir.Sha256.eval_col, wrap_zero hxr, hnode, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.DRR) (f := fun q => if q = 19 then 1 else 0) rfl hxr,
        show x % 72 = 19 by omega]; simp
  obtain ⟨q', hq', hd', hv⟩ := digest_linked hL hsat hL25 (i := 3) (k := 4 + half)
    (Or.inl ⟨rfl, by interval_cases half <;> simp⟩) hxr hm
  have hu : siteVals hashSys inst pub (3, x, 4 + half) =
      ((if half = 0 then Sha.k Sha.LID else Sha.k Sha.RID) :: Sha.nodeWordLimbs).map
        (Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x) := by
    interval_cases half <;> simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups]
  rw [digest_vals hL hsat hq', hu, List.map_cons] at hv
  simp only [List.cons.injEq] at hv
  obtain ⟨hmid, hlimbs⟩ := hv
  refine ⟨q', hq', hd', ?_, fun t ht => ?_⟩
  · rw [hmid]
    interval_cases half
    · simp only [if_true, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hxr]
      rw [hxs, Sha.per_const ss (X := Sha.LID) (by simp) hs (11 + 8 * 0) (by omega) (by omega)]
    · simp only [show (1 : ℕ) ≠ 0 by decide, if_false, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hxr]
      rw [hxs, Sha.per_const ss (X := Sha.RID) (by simp) hs (11 + 8 * 1) (by omega) (by omega)]
  · -- compare limbs `2t` and `2t + 1`
    have lj : ∀ j < 16, ((Sha256.half16 (Spec.Bitcoin.stateWord (outputAt (inst 3).main (72 * q')) (j / 2)) (j % 2) : ℕ) : F)
        = ((Sha256.half16 (messageAt (inst 3).main (72 * p) (8 * half + j / 2)) (j % 2) : ℕ) : F) := by
      intro j hj
      have e := congrArg (fun l => l[j]?) hlimbs
      have hjl : j < Sha.nodeWordLimbs.length := by simp [Sha.nodeWordLimbs]; exact hj
      simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, List.getElem?_eq_getElem hjl,
        Option.some.injEq] at e
      rw [e, ← List.getD_eq_getElem _ (cst 0) hjl, show x = 72 * p + 11 + 8 * half by rfl,
        Sha.node_tuple ss (s := 72 * p) (by omega) hj half hh]
    have h0 := lj (2 * t) (by omega)
    have h1 := lj (2 * t + 1) (by omega)
    rw [show 2 * t / 2 = t by omega, show 2 * t % 2 = 0 by omega] at h0
    rw [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1) % 2 = 1 by omega] at h1
    symm
    have hb : ∀ (y : Spec.Sha256.Word) (h : ℕ), Sha256.half16 y h < P := fun y h =>
      Fields.lt_P (by have := half16_lt y h; omega)
    exact word_of_halves (natCast_inj_of_lt (hb _ 0) (hb _ 0) h0) (natCast_inj_of_lt (hb _ 1) (hb _ 1) h1)

/-- **Every tree entry's second hash.** With `b` the parsed block (`N` transactions, public input 1), a
second hash whose id is tree entry `(l, i)` outputs entry `i` of level `l` of the txid Merkle tree. -/
theorem id_digest (hL25 : L ≤ 25) {b : Spec.Block.Blk}
    (hb : Spec.Block.parseBlock (Fields.blockBytes (inst 0).main (pub 0).val) = some b)
    (hN : pub 1 = (b.txs.length : F)) (hN1 : 1 ≤ b.txs.length) (hN25 : b.txs.length < 2 ^ L) :
    ∀ l, (l = 0 ∨ (1 ≤ l ∧ 2 ≤ Merkle.cntL b.txs.length (l - 1))) → ∀ i < Merkle.cntL b.txs.length l,
      ∀ q, 72 * q + 72 ≤ 2 ^ L → (inst 3).main Sha.DBL (72 * q) = 1 →
        (inst 3).main Sha.MID (72 * q) = (Merkle.idOf b.txs.length l i : F) →
        Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) =
          (Spec.Block.lvs (b.txs.map Spec.Block.txid) l).getD i [] := by
  have ms := hash_msg_sat hL hsat
  have ss := hash_sha_sat hL hsat
  have ks := hash_merkle_sat hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  set N := b.txs.length with hNdef
  have tr := Merkle.tree_rows ks (show 0 < 2 ^ L by positivity) (by omega) hN hN1 (by omega)
  intro l
  induction l with
  | zero =>
    intro _ i hi q hq hd hm
    simp only [Merkle.cntL] at hi
    simp only [Merkle.idOf, if_true] at hm
    have hmid : ((inst 3).main Sha.MID (72 * q)).val < Merkle.NB := by
      rw [hm, ZMod.val_natCast_of_lt (Fields.lt_P (m := 1 + 2 * i) (by omega))]; unfold Merkle.NB; omega
    obtain ⟨b', hp', r0, h0, f0, hm0, -, hnh⟩ := digest_tx hL hsat hL25 (Sha.dbl_pos ss hq hd) hq hd hmid
    rw [hb] at hp'; cases hp'
    -- the message is a txid message of transaction `i`
    have hh : (inst 2).main Msg.HDR r0 = 0 := by
      rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h0 with h | h
      · exact h
      · exfalso
        rw [Msg.mid_eq ms h0, h, sub_self, zero_mul, hm] at hm0
        have := natCast_inj_of_lt (a := 0) (b := 1 + 2 * i) (Fields.lt_P (by norm_num)) (Fields.lt_P (by omega))
          (by simpa using hm0)
        omega
    obtain ⟨i', tx, hti, hget, hout⟩ := hnh hh
    have hi' : i' < N := by
      have := List.getElem?_eq_some_iff.mp hget; exact this.1
    have hw := Fields.bool_val (Msg.bool_col ms (e := Msg.WTX) (by simp) h0)
    rw [Msg.mid_eq ms h0, hh, sub_zero, one_mul, hti, hw.1, hm] at hm0
    have e : ((1 + 2 * i' + ((inst 2).main Msg.WTX r0).val : ℕ) : F) = ((1 + 2 * i : ℕ) : F) := by
      push_cast at hm0 ⊢; linear_combination hm0
    have en := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
    have hw0 : (inst 2).main Msg.WTX r0 = 0 := by
      rw [hw.1, show ((inst 2).main Msg.WTX r0).val = 0 by omega]; simp
    have hii : i' = i := by omega
    subst hii
    rw [hout, if_neg (by rw [hw0]; exact zero_ne_one)]
    simp [Spec.Block.lvs, List.getD_eq_getElem?_getD, hget]
  | succ l ih =>
    intro hl i hi q hq hd hm
    have hc2 : 2 ≤ Merkle.cntL N l := by rcases hl with h | ⟨-, h⟩ <;> simp_all
    have hil : i < (Merkle.cntL N l + 1) / 2 := hi
    -- the node's second hash, padding block and node block
    have hmv : ((inst 3).main Sha.MID (72 * q)).val = Merkle.NB + Merkle.baseL N (l + 1) + i := by
      rw [hm, Merkle.idOf, if_neg (by omega), ZMod.val_natCast_of_lt (Fields.lt_P (by
        have := (tr.1 (l + 1) (by omega) (by simpa using hc2)).1; unfold Merkle.NB; omega))]
    obtain ⟨hq2, hnp, hno, hme⟩ := node_period hL hsat hL25 hq hd (by omega)
    set s := 72 * (q - 2) with hs
    have hsr : s < 2 ^ L := by omega
    obtain ⟨r', hr', ha', hmr, hlr, hrr, hdr⟩ := node_row hL hsat hL25 hsr (by
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hsr, hno, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hsr,
        show s % 72 = 0 by omega]; simp)
    -- the Merkle row is entry `(l + 1, i)`
    obtain ⟨hlt, rows⟩ := tr.1 (l + 1) (by omega) (by simpa using hc2)
    have hrow : r' = Merkle.baseL N (l + 1) + i := by
      have e : ((Merkle.NB + r' : ℕ) : F) = ((Merkle.NB + Merkle.baseL N (l + 1) + i : ℕ) : F) := by
        rw [← hmr, hme, hm, Merkle.idOf, if_neg (by omega)]
      have := natCast_inj_of_lt (Fields.lt_P (by unfold Merkle.NB; omega)) (Fields.lt_P (by unfold Merkle.NB; omega)) e
      omega
    subst hrow
    obtain ⟨-, rI, -, rL1, rPB, rOdd, rLast, -⟩ := rows i hi
    obtain ⟨kd, kl, kr⟩ := Merkle.kids ks hr' (show 1 ≤ l + 1 by omega) (rfl : Merkle.cntL N l = Merkle.cntL N (l + 1 - 1))
      hil (by simpa using rL1) (fun h => by simpa using rPB h) rI (by simpa using rOdd) (by
        rw [rLast]; rfl)
    simp only [Nat.add_sub_cancel] at kl kr
    -- the children's digests
    have ihl : l = 0 ∨ (1 ≤ l ∧ 2 ≤ Merkle.cntL N (l - 1)) := by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact Or.inl h
      · right; refine ⟨h, ?_⟩
        have := Merkle.cntL_le (N := N) (l - 1); rw [show l - 1 + 1 = l by omega] at this; omega
    have child : ∀ half ≤ 1, ∃ o : Spec.Sha256.State,
        (∀ t < 8, messageAt (inst 3).main s (8 * half + t) = Spec.Bitcoin.stateWord o t) ∧
        Spec.Block.stateBytes o = (Spec.Block.lvs (b.txs.map Spec.Block.txid) l).getD
          (if half = 0 then 2 * i else min (2 * i + 1) (Merkle.cntL N l - 1)) [] := by
      intro half hh
      obtain ⟨q', hq', hd', hmid', hw⟩ := node_children hL hsat hL25 (p := q - 2) (by omega) hno half hh
      refine ⟨outputAt (inst 3).main (72 * q'), hw, ?_⟩
      apply ih ihl _ (by split_ifs <;> omega) q' hq' hd'
      rw [hmid']
      interval_cases half
      · simp only [if_true]; rw [hlr, kl]
      · simp only [show (1 : ℕ) ≠ 0 by decide, if_false]; rw [hrr, kr]
    obtain ⟨oL, wL, bL⟩ := child 0 (by norm_num)
    obtain ⟨oR, wR, bR⟩ := child 1 (by norm_num)
    simp only [if_true, show (1 : ℕ) ≠ 0 by decide, if_false] at bL bR
    -- the node's output
    have hout := Sha.node_out ss hq2 hq hd (by rw [show q - 1 = q - 1 by rfl]; exact hnp) hno
    have hmsg : Spec.Sha256.compress Spec.Sha256.IV (messageAt (inst 3).main s) =
        Spec.Sha256.compress Spec.Sha256.IV (HashSpec.pairWords oL oR) := by
      apply StarkedAir.HeaderChain.compress_congr
      intro t ht
      unfold HashSpec.pairWords
      split_ifs with h8
      · have := wL t h8; simpa using this
      · have := wR (t - 8) (by omega); rw [show 8 * 1 + (t - 8) = t by omega] at this; exact this
    rw [hout, hmsg, npad_eq, dbl_digest, ← HashSpec.sha256d_pair, bL, bR]
    have hlen := lvs_len (b.txs.map Spec.Block.txid) l
    simp only [List.length_map] at hlen
    have hg := Spec.Block.level_get (Spec.Block.lvs (b.txs.map Spec.Block.txid) l) i (by rw [hlen]; exact hil)
    simp only [Spec.Block.lvs, List.getD_eq_getElem?_getD, hg, Option.getD_some]
    rw [hlen]

end System

end StarkedAir.Block
