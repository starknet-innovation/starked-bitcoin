/-
**Block hashing soundness (M3a.3).** In a satisfied hashing system (bytes, fields, messages, SHA), every
second-hash digest is `Spec.Block.sha256d` of a message's data bytes.
-/
import StarkedAir.Block.Link
import StarkedAir.Block.HashSpec
import StarkedAir.Block.TxBytes

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst limb word messageAt outputAt)

namespace Sha

section Words

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

/-- A message word is its two 16-bit limbs. -/
theorem word_limbs {x : ℕ} (hx : x < n) :
    word M StarkedAir.Sha256.W x = BitVec.ofNat 32 (((limb StarkedAir.Sha256.W 0).eval n preCols pub M x).val +
      65536 * ((limb StarkedAir.Sha256.W 1).eval n preCols pub M x).val) := by
  have l0 := StarkedAir.Sha256.limbs_back (sha_sat hsat) hx (Nat.zero_le _) (base := StarkedAir.Sha256.W)
    (by simp [StarkedAir.Sha256.W]) (h := 0) (by norm_num)
  have l1 := StarkedAir.Sha256.limbs_back (sha_sat hsat) hx (Nat.zero_le _) (base := StarkedAir.Sha256.W)
    (by simp [StarkedAir.Sha256.W]) (h := 1) (by norm_num)
  simp only [Nat.cast_zero, neg_zero, Nat.sub_zero] at l0 l1
  rw [l0, l1]
  set w := word M StarkedAir.Sha256.W x
  have hw := w.isLt
  rw [ZMod.val_natCast_of_lt (by simp [StarkedAir.Sha256.half16]; unfold P; omega),
    ZMod.val_natCast_of_lt (by simp [StarkedAir.Sha256.half16]; unfold P; omega)]
  apply BitVec.eq_of_toNat_eq
  simp [StarkedAir.Sha256.half16]; omega

/-- A period that starts or continues a message reads words. -/
theorem usew_one {r : ℕ} (hr : r < n) (h : M FST r = 1 ∨ M CHN r = 1) : M USEW r = 1 := by
  rw [usew_eq hsat hr]
  rcases h with h | h
  · obtain ⟨e1, e2, -, e4, -, -, -, e8, -, -⟩ := kinds_excl hsat hr
    rw [h, one_mul] at e1 e2; rw [h, mul_one] at e4 e8
    rw [e1, e2, e4, e8]; ring
  · obtain ⟨-, b, c, d, g⟩ := chn_one hsat hr h
    rw [b, c, d, g]; ring

end Words

end Sha

/-- Word `t` of block `b` of a byte string: bytes `64b + 4t .. + 3`, big-endian. -/
theorem chunk_get (l : Spec.Block.Bytes) (b t : ℕ) (ht : t < 16) :
    Spec.Block.chunkWords ((l.drop (64 * b)).take 64) t =
      BitVec.ofNat 32 ((l.getD (64 * b + 4 * t) 0).toNat * 2 ^ 24 + (l.getD (64 * b + 4 * t + 1) 0).toNat * 2 ^ 16 +
        (l.getD (64 * b + 4 * t + 2) 0).toNat * 2 ^ 8 + (l.getD (64 * b + 4 * t + 3) 0).toNat) := by
  have g : ∀ i < 64, ((l.drop (64 * b)).take 64).toArray.getD i 0 = l.getD (64 * b + i) 0 := by
    intro i hi
    simp [Array.getD, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop, hi]
    split_ifs with h
    · rw [List.getElem?_eq_getElem (by omega)]; rfl
    · rw [List.getElem?_eq_none (by omega)]; rfl
  simp only [Spec.Block.chunkWords, g (4 * t) (by omega), g (4 * t + 1) (by omega), g (4 * t + 2) (by omega),
    g (4 * t + 3) (by omega), add_assoc]

theorem val2 {x y : F} (hx : x.val < 256) (hy : y.val < 256) : (256 * x + y).val = 256 * x.val + y.val := by
  refine Fields.val_lt_of_eq_cast ?_ (Fields.lt_P (m := 256 * x.val + y.val) (by omega))
  push_cast; simp

theorem slice_bb (Mb : ℕ → ℕ → F) {len a k : ℕ} (h : a + k ≤ len) :
    Fields.slice (Fields.blockBytes Mb len) a k = (List.range k).map (fun j => UInt8.ofNat (Mb BYTE (a + j)).val) := by
  apply List.ext_getElem
  · simp [Fields.slice, Fields.blockBytes]; omega
  · intro i h1 h2
    simp [Fields.slice, Fields.blockBytes]

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 5, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub [])
include hL hsat

/-- The data bytes of the message starting at message row `r0` (data rows `0..d`). -/
def msgData (inst : ℕ → Inst) (r0 d : ℕ) : Spec.Block.Bytes :=
  (List.range (d + 1)).map (fun j => UInt8.ofNat ((inst 2).main Msg.BYTE (r0 + j)).val)

/-- **Every message with a given id is the padded data of one reference message.** -/
theorem msg_rows_pad (hL25 : L ≤ 25) {r0 d r1 : ℕ} (h0 : r0 < 2 ^ L) (h1 : r1 < 2 ^ L)
    (f0 : (inst 2).main Msg.FIRSTM r0 = 1) (f1 : (inst 2).main Msg.FIRSTM r1 = 1)
    (hc0 : ∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d) = 1)
    (hm : (inst 2).main Msg.MID r1 = (inst 2).main Msg.MID r0) :
    r1 + (Spec.Block.pad (msgData inst r0 d)).length ≤ 2 ^ L ∧
      ∀ i < (Spec.Block.pad (msgData inst r0 d)).length,
        ((inst 2).main Msg.BYTE (r1 + i)).val = ((Spec.Block.pad (msgData inst r0 d)).getD i 0).toNat := by
  have ms := hash_msg_sat hL hsat
  have h27 : 2 ^ L ≤ 2 ^ 27 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨d1, hc1, he1⟩ := Msg.data_exit ms h1 f1
  obtain ⟨hd, hb⟩ := same_bytes hL hsat hL25 h1 h0 f1 f0 hm hc1 he1 hc0 he0
  subst hd
  have e : msgData inst r0 d1 = (List.range (d1 + 1)).map (fun j => UInt8.ofNat ((inst 2).main Msg.BYTE (r1 + j)).val) := by
    unfold msgData
    refine List.map_congr_left (fun j hj => ?_)
    rw [hb j (by simp at hj; omega)]
  rw [e]
  exact Msg.msg_pad ms h1 f1 hc1 he1 h27

theorem byte_val_lt {r : ℕ} (hr : r < 2 ^ L) : ((inst 2).main Msg.BYTE r).val < 256 :=
  Msg.byte_lt (hash_msg_sat hL hsat) hr

/-- **SHA's message words are the padded message's words.** Word `t` of a period that starts or continues
the message with id `MID r0`, as its block `b`, is word `t` of block `b` of `pad (msgData r0 d)`. -/
theorem block_word (hL25 : L ≤ 25) {r0 d : ℕ} (h0 : r0 < 2 ^ L) (f0 : (inst 2).main Msg.FIRSTM r0 = 1)
    (hc0 : ∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d) = 1)
    {s b t : ℕ} (hs : s % 72 = 0) (hsn : s + 72 ≤ 2 ^ L) (ht : t < 16)
    (hfc : (inst 3).main Sha.FST s = 1 ∨ (inst 3).main Sha.CHN s = 1)
    (hmid : (inst 3).main Sha.MID s = (inst 2).main Msg.MID r0) (hbk : (inst 3).main Sha.BLKI s = (b : F))
    (hlen : 64 * b + 64 ≤ (Spec.Block.pad (msgData inst r0 d)).length) :
    messageAt (inst 3).main s t =
      Spec.Block.chunkWords (((Spec.Block.pad (msgData inst r0 d)).drop (64 * b)).take 64) t := by
  have ss := hash_sha_sat hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  set x := s + 4 + t with hxdef
  have hx : x < 2 ^ L := by omega
  have hxs : x = s + (4 + t) := by omega
  -- the row reads a word
  have hdbl : (inst 3).main Sha.DBL x = (inst 3).main Sha.DBL s := by
    rw [hxs]; exact Sha.per_const ss (by simp) hs (4 + t) (by omega) (by omega)
  have hnil : (inst 3).main Sha.NILS x = (inst 3).main Sha.NILS s := by
    rw [hxs]; exact Sha.per_const ss (by simp) hs (4 + t) (by omega) (by omega)
  have hnod : (inst 3).main Sha.NODE x = (inst 3).main Sha.NODE s := by
    rw [hxs]; exact Sha.per_const ss (by simp) hs (4 + t) (by omega) (by omega)
  have hnpd : (inst 3).main Sha.NPAD x = (inst 3).main Sha.NPAD s := by
    rw [hxs]; exact Sha.per_const ss (by simp) hs (4 + t) (by omega) (by omega)
  have hu : (inst 3).main Sha.USEW x = 1 := by
    rw [Sha.usew_eq ss hx, hdbl, hnil, hnod, hnpd, ← Sha.usew_eq ss (by omega)]; exact Sha.usew_one ss (by omega) hfc
  have hrow : (Expr.mul (pre Sha.MSGROW) (Sha.k Sha.USEW)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1 := by
    simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hx, hu, mul_one]
    rw [Sha.eval_per72 ss (i := Sha.MSGROW) (f := fun q => if 4 ≤ q ∧ q < 20 then 1 else 0) rfl hx]
    have : x % 72 = 4 + t := by omega
    simp [this]; omega
  obtain ⟨r1, j, hr1, hj, -, f1, -, m1, hidx, lo, hi⟩ := sha_word hL hsat hL25 hx hrow
  -- same message: index `j − 3 = 64 b + 4 t`
  have hm1 : (inst 2).main Msg.MID r1 = (inst 2).main Msg.MID r0 := by
    rw [m1, hxs, Sha.per_const ss (by simp) hs (4 + t) (by omega) (by omega), hmid]
  obtain ⟨hbound, rows⟩ := msg_rows_pad hL hsat hL25 h0 (by omega) f0 f1 hc0 he0 hm1
  have hj' : j - 3 = 64 * b + 4 * t := by
    have e : (Expr.add (.mul (cst 64) (Sha.k Sha.BLKI)) (.sub (.mul (cst 4) (pre Sha.ROWIDX)) (cst 16))).eval
        (2 ^ L) Sha.preCols pub (inst 3).main x = ((64 * b + 4 * t : ℕ) : F) := by
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hx, StarkedAir.Sha256.eval_cst]
      rw [Sha.eval_per72 ss (i := Sha.ROWIDX) (f := fun q => q) rfl hx, show x % 72 = 4 + t by omega]
      rw [show (inst 3).main Sha.BLKI x = (b : F) by
        rw [hxs, Sha.per_const ss (by simp) hs (4 + t) (by omega) (by omega), hbk]]
      push_cast; ring
    rw [e] at hidx
    exact natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) hidx
  have bv : ∀ k < 4, ((inst 2).main Msg.BYTE (r1 + (64 * b + 4 * t + k))).val =
      ((Spec.Block.pad (msgData inst r0 d)).getD (64 * b + 4 * t + k) 0).toNat :=
    fun k hk => rows _ (by omega)
  -- assemble the word
  unfold messageAt
  rw [Sha.word_limbs ss hx, chunk_get _ b t ht, lo, hi]
  have bl := fun r (hr : r < 2 ^ L) => byte_val_lt hL hsat hr
  have v2 : ∀ {a c : ℕ}, a < 2 ^ L → c < 2 ^ L →
      (256 * (inst 2).main Msg.BYTE a + (inst 2).main Msg.BYTE c).val =
        256 * ((inst 2).main Msg.BYTE a).val + ((inst 2).main Msg.BYTE c).val := by
    intro a c ha hc
    exact val2 (bl a ha) (bl c hc)
  rw [v2 (by omega) (by omega), v2 (by omega) (by omega)]
  have i0 := bv 0 (by norm_num); have i1 := bv 1 (by norm_num); have i2 := bv 2 (by norm_num)
  have i3 := bv 3 (by norm_num)
  rw [show r1 + j - 3 = r1 + (64 * b + 4 * t + 0) by omega, show r1 + j - 2 = r1 + (64 * b + 4 * t + 1) by omega,
    show r1 + j - 1 = r1 + (64 * b + 4 * t + 2) by omega, show r1 + j = r1 + (64 * b + 4 * t + 3) by omega,
    i0, i1, i2, i3]
  simp only [add_zero]
  congr 1; ring

omit hL hsat in
theorem dbl_digest (h : Spec.Sha256.State) : Sha.dblBlock h = Spec.Bitcoin.digestBlock h := by
  funext t
  unfold Sha.dblBlock Spec.Bitcoin.digestBlock Sha.dblWord
  by_cases h8 : t < 8
  · simp [h8]
  · by_cases e8 : t = 8
    · subst e8; rfl
    · by_cases e15 : t = 15
      · subst e15; rfl
      · simp [h8, e8, e15]

/-- **Block hashing soundness.** In a satisfied hashing system with at most `2^25` rows, a second-hash
period `q` outputs `SHA256d` of the data bytes of a message with the period's id. -/
theorem digest_sha256d (hL25 : L ≤ 25) {q : ℕ} (hq : 1 ≤ q) (hn : 72 * q + 72 ≤ 2 ^ L)
    (hd : (inst 3).main Sha.DBL (72 * q) = 1) (hmid : ((inst 3).main Sha.MID (72 * q)).val < Merkle.NB) :
    ∃ r0 d, r0 < 2 ^ L ∧ (inst 2).main Msg.FIRSTM r0 = 1 ∧ (inst 2).main Msg.MID r0 = (inst 3).main Sha.MID (72 * q) ∧
      (∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1) ∧
      (inst 2).main Msg.ENDD (r0 + d) = 1 ∧
      Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) = Spec.Block.sha256d (msgData inst r0 d) := by
  have ss := hash_sha_sat hL hsat
  have ms := hash_msg_sat hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  -- the period before is no node block: node ids are at least `NB`
  have hpm : (inst 3).main Sha.MID (72 * (q - 1)) = (inst 3).main Sha.MID (72 * q) :=
    ((Sha.prev_facts ss hq hn).2 hd).1.symm
  have nodeAt : ∀ p, 72 * p + 72 ≤ 2 ^ L → (inst 3).main Sha.NODE (72 * p) = 1 →
      (inst 3).main Sha.MID (72 * p) = (inst 3).main Sha.MID (72 * q) → False := by
    intro p hp hno he
    have hx' : 72 * p < 2 ^ L := by omega
    have := node_mid hL hsat hL25 hx' (by
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hx', hno, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hx']; simp)
    rw [he] at this; omega
  have hpo : (inst 3).main Sha.NODE (72 * (q - 1)) = 0 := by
    rcases Sha.kbool ss (c := Sha.NODE) (by simp) (show 72 * (q - 1) < 2 ^ L by omega) with h | h
    · exact h
    · exact (nodeAt (q - 1) (by omega) h hpm).elim
  have hpp : (inst 3).main Sha.NPAD (72 * (q - 1)) = 0 := by
    rcases Sha.kbool ss (c := Sha.NPAD) (by simp) (show 72 * (q - 1) < 2 ^ L by omega) with h | h
    · exact h
    · obtain ⟨hq1, hno, hme⟩ := Sha.npad_prev ss (q := q - 1) (by omega) h
      exact (nodeAt (q - 1 - 1) (by omega) hno (hme.trans hpm)).elim
  obtain ⟨q0, hq0, f0, chn, vals, hout⟩ := Sha.digest_sound ss hq hn hd hpo hpp
  -- the length check of the second hash
  have hx : 72 * q < 2 ^ L := by omega
  have hrow : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.DBL)).eval (2 ^ L) Sha.preCols pub (inst 3).main (72 * q) = 1 := by
    simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hx, hd, mul_one]
    rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hx]
    simp
  obtain ⟨r0, d, f, he, hc, hmid', hlt, hlen⟩ := sha_len hL hsat hL25 hx hrow hmid
  have hr0 : r0 < 2 ^ L := by omega
  have hal := Msg.first_align ms hr0 f
  -- the padded length is `64 (q − q0)`
  have hprev : (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main (72 * q) =
      ((64 * (q - q0) : ℕ) : F) := by
    simp only [Expr.eval, Sha.kp, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst]
    rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, StarkedAir.Sha256.wrap_back (by omega) hx]
    have e := Sha.per_const ss (X := Sha.BLKI) (by simp) (s := 72 * (q - 1)) (by omega) 71 (by norm_num) (by omega)
    rw [show 72 * q - 1 = 72 * (q - 1) + 71 by omega, e, (vals (q - 1) (by omega) (by omega)).2]
    rw [show q - 1 - q0 = (q - q0) - 1 by omega, Nat.cast_sub (by omega)]
    push_cast; ring
  rw [hprev] at hlen
  have hplen := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) hlen
  have hpl : (Spec.Block.pad (msgData inst r0 d)).length = 64 * (q - q0) := by
    rw [HashSpec.pad_length, show (msgData inst r0 d).length = d + 1 by simp [msgData]]
    omega
  -- the message blocks
  have hfold : ∀ b ≤ q - q0, Sha.fold (inst 3).main (72 * q0) b = HashSpec.chunkFold Spec.Sha256.IV
      (Spec.Block.pad (msgData inst r0 d)) b := by
    intro b hb
    induction b with
    | zero => rfl
    | succ b ih =>
      simp only [Sha.fold, HashSpec.chunkFold]
      rw [ih (by omega)]
      apply StarkedAir.HeaderChain.compress_congr
      intro t ht
      have hs : (72 * q0 + 72 * b) % 72 = 0 := by omega
      have hfc : (inst 3).main Sha.FST (72 * q0 + 72 * b) = 1 ∨ (inst 3).main Sha.CHN (72 * q0 + 72 * b) = 1 := by
        rcases Nat.eq_zero_or_pos b with h | h
        · left; rw [h, mul_zero, add_zero]; exact f0
        · right; rw [show 72 * q0 + 72 * b = 72 * (q0 + b) by ring]; exact chn _ (by omega) (by omega)
      have vj := vals (q0 + b) (by omega) (by omega)
      rw [show 72 * (q0 + b) = 72 * q0 + 72 * b by ring, show q0 + b - q0 = b by omega] at vj
      exact block_word hL hsat hL25 hr0 f hc he hs (by omega) ht hfc (vj.1.trans hmid'.symm) vj.2 (by omega)
  refine ⟨r0, d, hr0, f, hmid', hc, he, ?_⟩
  rw [hout, hfold _ le_rfl, dbl_digest, HashSpec.sha256d_eq _ _ hpl]

/-- **A whole message's data is a block slice**: `msgData = R[TA, TA + d]`, and `TA + d = TL + 3`. -/
theorem whole_data (hL25 : L ≤ 25) {r0 d : ℕ} (h0 : r0 < 2 ^ L) (f0 : (inst 2).main Msg.FIRSTM r0 = 1)
    (hc0 : ∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d) = 1) (hmt : (inst 2).main Msg.MT r0 = 0) :
    ((inst 2).main Msg.TA r0).val + d < (pub 0).val ∧
      msgData inst r0 d = Fields.slice (Fields.blockBytes (inst 0).main (pub 0).val) ((inst 2).main Msg.TA r0).val (d + 1) ∧
      ((((inst 2).main Msg.TA r0).val + d : ℕ) : F) = (inst 2).main Msg.TL r0 + 3 := by
  have ms := hash_msg_sat hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  have hLEN : (pub 0).val ≤ 2 ^ 25 :=
    Fields.len_le hL25 (hash_fields_sat' hL hsat) (hash_bytes_sat hL hsat) (hash_fields_read hL hsat hL25)
  have rows := Msg.whole_rows ms h0 f0 hmt hc0 he0
  have rd : ∀ j ≤ d, ((inst 2).main Msg.TA r0).val + j < (pub 0).val ∧
      (inst 2).main Msg.BYTE (r0 + j) = (inst 0).main BYTE (((inst 2).main Msg.TA r0).val + j) := by
    have r00 := rows 0 (Nat.zero_le _)
    obtain ⟨l0, -⟩ := Msg.data_walk ms h0 f0 0 (fun i hi => absurd hi (Nat.not_lt_zero _))
    obtain ⟨ρ0, hρ0, p0, -⟩ := msg_read hL hsat hL25 l0 r00.1
    have hta : ((inst 2).main Msg.TA r0).val = ρ0 := by
      rw [r00.2.2.1] at p0; simp at p0
      exact Fields.val_lt_of_eq_cast p0 (by unfold P; omega)
    intro j hj
    obtain ⟨hd, -, hpos, -⟩ := rows j hj
    obtain ⟨lj, -⟩ := Msg.data_walk ms h0 f0 j (fun i hi => hc0 i (by omega))
    obtain ⟨ρ, hρ, pj, bj⟩ := msg_read hL hsat hL25 lj hd
    have e : ((inst 2).main Msg.TA r0).val + j = ρ := by
      refine natCast_inj_of_lt (a := ((inst 2).main Msg.TA r0).val + j) (b := ρ) (by rw [hta]; unfold P; omega)
        (lt_of_lt_of_le hρ (hLEN.trans (by unfold P; norm_num))) ?_
      rw [← pj, hpos]; push_cast; rw [ZMod.natCast_zmod_val]
    exact ⟨by omega, by rw [bj, e]⟩
  have hb := (rd d le_rfl).1
  refine ⟨hb, ?_, ?_⟩
  · rw [slice_bb _ (by omega)]
    unfold msgData
    refine List.map_congr_left (fun j hj => ?_)
    rw [(rd j (by simp at hj; omega)).2]
  · have := ((rows d le_rfl).2.2.2).mpr rfl
    push_cast; rw [ZMod.natCast_zmod_val]; exact this

/-- **wtxid and legacy txid messages are `serWit`.** A non-header message start whose message is whole
(`MT = 0`: a wtxid, or the txid of a transaction without the segwit flag) reads a transaction's
`serWit`; for a txid message (`WTX = 0`) that is also its `serNoWit`. -/
theorem whole_tx (hL25 : L ≤ 25) {m : ℕ} (hmn : m < 2 ^ L) (hnp : ∀ r < m, (inst 1).main Fields.K_PAD r = 0)
    (hpad : ∀ r < 2 ^ L, m ≤ r → (inst 1).main Fields.K_PAD r = 1)
    (hfit : ∀ r < m, ((inst 1).main Fields.START r).val + ((inst 1).main Fields.LEN r).val ≤ (Fields.blockBytes (inst 0).main (pub 0).val).length)
    (hcs : ∀ r < 2 ^ L, (inst 1).main Fields.K_LOCK r + (inst 1).main Fields.K_PAD r = 0 → ∀ o : ℕ,
      (inst 1).main Fields.OFF r = (o : F) → o ≤ 86 →
      ((inst 1).main Fields.START r).val + o + Fields.prefOf (inst 1).main r ≤ (Fields.blockBytes (inst 0).main (pub 0).val).length ∧
      ((inst 1).main Fields.VAL r).val ≤ Fields.MAXS ∧
      Spec.Block.serCompact ((inst 1).main Fields.VAL r).val =
        Fields.slice (Fields.blockBytes (inst 0).main (pub 0).val) (((inst 1).main Fields.START r).val + o) (Fields.prefOf (inst 1).main r))
    (cat : ∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (Fields.tokOf (inst 1).main (Fields.blockBytes (inst 0).main (pub 0).val) r)) =
        Fields.slice (Fields.blockBytes (inst 0).main (pub 0).val) 0 ((inst 1).main Fields.START k).val)
    (mono : ∀ k j, k ≤ j → j ≤ m → ((inst 1).main Fields.START k).val ≤ ((inst 1).main Fields.START j).val)
    (hSm : ((inst 1).main Fields.START m).val = (Fields.blockBytes (inst 0).main (pub 0).val).length)
    {r0 d : ℕ} (h0 : r0 < 2 ^ L) (f0 : (inst 2).main Msg.FIRSTM r0 = 1)
    (hh : (inst 2).main Msg.HDR r0 = 0)
    (hc0 : ∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d) = 1) (hmt : (inst 2).main Msg.MT r0 = 0) :
    ∃ tx ρ, ρ < 2 ^ L ∧ (inst 1).main Fields.K_LOCK ρ = 1 ∧
      (inst 2).main Msg.TI r0 = ((Fields.locks (inst 1).main ρ : ℕ) : F) ∧ Fields.TxAt (inst 1).main (Fields.blockBytes (inst 0).main (pub 0).val) m ρ tx ∧ msgData inst r0 d = Spec.Block.serWit tx ∧
      ((inst 2).main Msg.WTX r0 = 0 → msgData inst r0 d = Spec.Block.serNoWit tx) := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have hb0 := hash_bytes_sat hL hsat
  obtain ⟨ρ, hρ, hl, ti, ta, sg, tw, tl⟩ := msg_tuple_row hL hsat hL25 h0 f0 hh
  obtain ⟨tx, hat, hw, -, hnn⟩ := Fields.lock_tx hL25 fs hb0 (hash_fields_read hL hsat hL25) hmn hnp hpad hfit hcs cat mono hSm hρ hl
  obtain ⟨hb, hdata, hend⟩ := whole_data hL hsat hL25 h0 f0 hc0 he0 hmt
  have hst := Fields.start_lt fs hρ
  have hLEN : (pub 0).val ≤ 2 ^ 25 := Fields.len_le hL25 fs hb0 (hash_fields_read hL hsat hL25)
  -- `TA + d = TL + 3` as naturals
  have hta : ((inst 2).main Msg.TA r0).val = ((inst 1).main Fields.TXA ρ).val := by rw [ta]
  have hn : ((inst 2).main Msg.TA r0).val + d = ((inst 1).main Fields.START ρ).val + 3 := by
    refine natCast_inj_of_lt (a := ((inst 2).main Msg.TA r0).val + d) (b := ((inst 1).main Fields.START ρ).val + 3)
      (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) ?_
    rw [hend, ← tl]; push_cast; rw [ZMod.natCast_zmod_val]
  have hdat : msgData inst r0 d = Spec.Block.serWit tx := by
    rw [hdata, hw, ← hta, show ((inst 1).main Fields.START ρ).val + 4 - ((inst 2).main Msg.TA r0).val = d + 1 by omega]
  refine ⟨tx, ρ, hρ, hl, by rw [← ti, Fields.txi_count fs ρ hρ], hat, hdat, fun hw0 => ?_⟩
  -- a txid message is whole only without the segwit flag
  have hseg : (inst 1).main Fields.SEG ρ ≠ 1 := by
    intro h1
    rw [Msg.mt_eq ms h0, hw0, hh, ← sg, h1] at hmt; simp at hmt
  rw [hdat, hnn hseg]

omit hL hsat in
theorem map_range_add {α : Type} (f : ℕ → α) (x y : ℕ) :
    (List.range (x + y)).map f = (List.range x).map f ++ (List.range y).map (fun i => f (x + i)) := by
  rw [List.range_add, List.map_append, List.map_map]; rfl

/-- **Segwit txid messages are `serNoWit`.** -/
theorem split_tx (hL25 : L ≤ 25) {m : ℕ} (hmn : m < 2 ^ L) (hnp : ∀ r < m, (inst 1).main Fields.K_PAD r = 0)
    (hpad : ∀ r < 2 ^ L, m ≤ r → (inst 1).main Fields.K_PAD r = 1)
    (hfit : ∀ r < m, ((inst 1).main Fields.START r).val + ((inst 1).main Fields.LEN r).val ≤ (Fields.blockBytes (inst 0).main (pub 0).val).length)
    (hcs : ∀ r < 2 ^ L, (inst 1).main Fields.K_LOCK r + (inst 1).main Fields.K_PAD r = 0 → ∀ o : ℕ,
      (inst 1).main Fields.OFF r = (o : F) → o ≤ 86 →
      ((inst 1).main Fields.START r).val + o + Fields.prefOf (inst 1).main r ≤ (Fields.blockBytes (inst 0).main (pub 0).val).length ∧
      ((inst 1).main Fields.VAL r).val ≤ Fields.MAXS ∧
      Spec.Block.serCompact ((inst 1).main Fields.VAL r).val =
        Fields.slice (Fields.blockBytes (inst 0).main (pub 0).val) (((inst 1).main Fields.START r).val + o) (Fields.prefOf (inst 1).main r))
    (cat : ∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (Fields.tokOf (inst 1).main (Fields.blockBytes (inst 0).main (pub 0).val) r)) =
        Fields.slice (Fields.blockBytes (inst 0).main (pub 0).val) 0 ((inst 1).main Fields.START k).val)
    (mono : ∀ k j, k ≤ j → j ≤ m → ((inst 1).main Fields.START k).val ≤ ((inst 1).main Fields.START j).val)
    (hSm : ((inst 1).main Fields.START m).val = (Fields.blockBytes (inst 0).main (pub 0).val).length)
    {r0 d : ℕ} (h0 : r0 < 2 ^ L) (f0 : (inst 2).main Msg.FIRSTM r0 = 1)
    (hh : (inst 2).main Msg.HDR r0 = 0)
    (hc0 : ∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d) = 1) (hmt : (inst 2).main Msg.MT r0 = 1) :
    ∃ tx ρ, ρ < 2 ^ L ∧ (inst 1).main Fields.K_LOCK ρ = 1 ∧
      (inst 2).main Msg.TI r0 = ((Fields.locks (inst 1).main ρ : ℕ) : F) ∧ Fields.TxAt (inst 1).main (Fields.blockBytes (inst 0).main (pub 0).val) m ρ tx ∧
      (inst 2).main Msg.WTX r0 = 0 ∧ msgData inst r0 d = Spec.Block.serNoWit tx := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have hb0 := hash_bytes_sat hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  norm_num at h25
  have hLEN : (pub 0).val ≤ 2 ^ 25 := Fields.len_le hL25 fs hb0 (hash_fields_read hL hsat hL25)
  -- the flags: a txid message of a segwit transaction
  have hwseg : (inst 2).main Msg.WTX r0 = 0 ∧ (inst 2).main Msg.SEG r0 = 1 := by
    rw [Msg.mt_eq ms h0, hh] at hmt
    rcases Msg.bool_col ms (e := Msg.WTX) (by simp) h0 with w | w <;>
      rcases Msg.bool_col ms (e := Msg.SEG) (by simp) h0 with g | g <;> simp_all
  obtain ⟨ρ, hρ, hl, ti, ta, sg, tw, tl⟩ := msg_tuple_row hL hsat hL25 h0 f0 hh
  obtain ⟨tx, hat, -, hnw, -⟩ := Fields.lock_tx hL25 fs hb0 (hash_fields_read hL hsat hL25) hmn hnp hpad hfit hcs cat mono hSm hρ hl
  have hsegρ : (inst 1).main Fields.SEG ρ = 1 := sg.trans hwseg.2
  obtain ⟨d1, h4, hd1, rowsD, pos0, pos1, hsw, pos2, hend⟩ := Msg.split_pieces ms h0 f0 hmt hc0 he0
  -- every data row reads the block byte at its position
  have rd : ∀ j ≤ d, ∀ p : ℕ, (inst 2).main Msg.POS (r0 + j) = (p : F) → p < 2 ^ 26 →
      p < (pub 0).val ∧ (inst 2).main Msg.BYTE (r0 + j) = (inst 0).main BYTE p := by
    intro j hj p hp hp26
    obtain ⟨hl', hd'⟩ := rowsD j hj
    obtain ⟨ρ', hρ', p', b'⟩ := msg_read hL hsat hL25 hl' hd'
    have e : p = ρ' := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) (hp.symm.trans p')
    subst e; exact ⟨hρ', b'⟩
  set a := ((inst 2).main Msg.TA r0).val with ha
  set l := ((inst 2).main Msg.TL r0).val with hlv
  have hTA : (inst 2).main Msg.TA r0 = (a : F) := by rw [ha, ZMod.natCast_zmod_val]
  have hTL : (inst 2).main Msg.TL r0 = (l : F) := by rw [hlv, ZMod.natCast_zmod_val]
  have hl25 : l < 2 ^ 25 := by rw [hlv, ← tl]; exact Fields.start_lt fs hρ
  -- `a` is small: row 0 reads it
  have ha25 : a < 2 ^ 25 := by
    obtain ⟨hl', hd'⟩ := rowsD 0 (by omega)
    obtain ⟨ρ', hρ', p', -⟩ := msg_read hL hsat hL25 hl' hd'
    rw [pos0 0 (by norm_num), Nat.cast_zero, add_zero] at p'
    have : a = ρ' := by rw [ha, p']; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
    omega
  have hdL : r0 + d < 2 ^ L := (rowsD d le_rfl).1
  -- the witness start and the data length
  have hTW : (inst 2).main Msg.TW r0 = ((a + d1 + 3 : ℕ) : F) := by
    rw [hTA] at hsw
    rw [show ((a + d1 + 3 : ℕ) : F) = (a : F) + d1 + 3 by push_cast; ring]
    linear_combination -hsw
  have hdd : d = d1 + 4 := by
    rw [hTA, hTW, hTL] at hend
    push_cast at hend
    have e : ((d : ℕ) : F) = ((d1 + 4 : ℕ) : F) := by push_cast; linear_combination hend
    exact natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
  subst hdd
  -- positions as naturals
  have b0' : ∀ j < 4, (inst 2).main Msg.BYTE (r0 + j) = (inst 0).main BYTE (a + j) ∧ a + j < (pub 0).val := by
    intro j hj
    obtain ⟨x, y⟩ := rd j (by omega) (a + j) (by rw [pos0 j (by omega), hTA]; push_cast; ring) (by omega)
    exact ⟨y, x⟩
  have b1' : ∀ i < d1 - 3, (inst 2).main Msg.BYTE (r0 + (4 + i)) = (inst 0).main BYTE (a + 6 + i) ∧
      a + 6 + i < (pub 0).val := by
    intro i hi
    obtain ⟨x, y⟩ := rd (4 + i) (by omega) (a + 6 + i)
      (by rw [pos1 (4 + i) (by omega) (by omega), hTA]; push_cast; ring) (by omega)
    exact ⟨y, x⟩
  have b2' : ∀ i < 4, (inst 2).main Msg.BYTE (r0 + (d1 + 1 + i)) = (inst 0).main BYTE (l + i) ∧ l + i < (pub 0).val := by
    intro i hi
    obtain ⟨x, y⟩ := rd (d1 + 1 + i) (by omega) (l + i)
      (by rw [pos2 (d1 + 1 + i) (by omega) (by omega), hTA, hTW, hTL]; push_cast; ring) (by omega)
    exact ⟨y, x⟩
  refine ⟨tx, ρ, hρ, hl, by rw [← ti, Fields.txi_count fs ρ hρ], hat, hwseg.1, ?_⟩
  rw [hnw hsegρ]
  have eTXA : ((inst 1).main Fields.TXA ρ).val = a := by rw [ta]
  have eWST : ((inst 1).main Fields.WST ρ).val = a + d1 + 3 := by
    rw [tw, hTW]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
  have eST : ((inst 1).main Fields.START ρ).val = l := by rw [tl]
  rw [eTXA, eWST, eST, show a + d1 + 3 - (a + 6) = d1 - 3 by omega,
    slice_bb _ (by have := (b0' 3 (by norm_num)).2; omega),
    slice_bb _ (by have := (b1' (d1 - 3 - 1) (by omega)).2; omega),
    slice_bb _ (by have := (b2' 3 (by norm_num)).2; omega)]
  unfold msgData
  rw [show d1 + 4 + 1 = 4 + ((d1 - 3) + 4) by omega, map_range_add, map_range_add]
  simp only [List.append_assoc]
  congr 1
  · refine List.map_congr_left (fun j hj => ?_)
    rw [(b0' j (by simpa using hj)).1]
  · congr 1
    · refine List.map_congr_left (fun i hi => ?_)
      rw [(b1' i (by simpa using hi)).1]
    · refine List.map_congr_left (fun i hi => ?_)
      rw [show 4 + (d1 - 3 + i) = d1 + 1 + i by omega, (b2' i (by simpa using hi)).1]

/-- **Block hashing soundness (M3a.3).** In a satisfied hashing system with at most `2^25` rows, the
block's bytes parse as a block `b`, and each second-hash period `q` outputs `SHA256d` of `b.header` (for
the header message) or, for a transaction message with index `TI = i`, the `wtxid` (`WTX = 1`) or the
`txid` (`WTX = 0`) of `b.txs[i]`. -/
theorem digest_tx (hL25 : L ≤ 25) {q : ℕ} (hq : 1 ≤ q) (hn : 72 * q + 72 ≤ 2 ^ L)
    (hd : (inst 3).main Sha.DBL (72 * q) = 1) (hmid : ((inst 3).main Sha.MID (72 * q)).val < Merkle.NB) :
    ∃ b, Spec.Block.parseBlock (Fields.blockBytes (inst 0).main (pub 0).val) = some b ∧
      ∃ r0, r0 < 2 ^ L ∧ (inst 2).main Msg.FIRSTM r0 = 1 ∧ (inst 2).main Msg.MID r0 = (inst 3).main Sha.MID (72 * q) ∧
      ((inst 2).main Msg.HDR r0 = 1 → Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) =
        Spec.Block.sha256d b.header) ∧
      ((inst 2).main Msg.HDR r0 = 0 → ∃ (i : ℕ) (tx : Spec.Block.Tx), (inst 2).main Msg.TI r0 = (i : F) ∧ b.txs[i]? = some tx ∧
        Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) =
          if (inst 2).main Msg.WTX r0 = 1 then Spec.Block.wtxid tx else Spec.Block.txid tx) := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have hb0 := hash_bytes_sat hL hsat
  obtain ⟨m, hmn, hnp, hpad, hfit, hcs, cat, mono, hSm⟩ :=
    Fields.block_ctx hL25 fs hb0 (hash_fields_read hL hsat hL25)
  obtain ⟨b, hparse, hhead, -, -, hidx⟩ :=
    Fields.block_index hL25 fs hb0 (hash_fields_read hL hsat hL25) hmn hnp hpad hfit hcs cat mono hSm
  obtain ⟨r0, d, h0, f, hmid', hc, he, hdig⟩ := digest_sha256d hL hsat hL25 hq hn hd hmid
  refine ⟨b, hparse, r0, h0, f, hmid', fun hh => ?_, fun hh => ?_⟩
  · -- the header message: bytes `[0, 80)`
    obtain ⟨ta, tl, w0⟩ := hdr_tuple hL hsat h0 hh
    have hmt : (inst 2).main Msg.MT r0 = 0 := by rw [Msg.mt_eq ms h0, w0, hh]; ring
    obtain ⟨hb, hdata, hend⟩ := whole_data hL hsat hL25 h0 f hc he hmt
    have ha : ((inst 2).main Msg.TA r0).val = 0 := by rw [ta]; rfl
    rw [ha, tl] at hend; rw [ha] at hdata hb
    have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
    have hd79 : d = 79 := by
      have hdL : r0 + d < 2 ^ L := (Msg.data_walk ms h0 f d hc).1
      have e : ((0 + d : ℕ) : F) = ((79 : ℕ) : F) := by rw [hend]; norm_num
      have := natCast_inj_of_lt (Fields.lt_P (by norm_num at h25 ⊢; omega)) (Fields.lt_P (by norm_num)) e
      omega
    subst hd79
    rw [hdig, hdata, hhead]
  · rcases Msg.mt_bool ms h0 with mt | mt
    · obtain ⟨tx, ρ, hρ, hl, hti, hat, hw, hnw⟩ :=
        whole_tx hL hsat hL25 hmn hnp hpad hfit hcs cat mono hSm h0 f hh hc he mt
      refine ⟨_, tx, hti, hidx ρ hρ hl tx hat, ?_⟩
      rw [hdig]
      rcases Msg.bool_col ms (e := Msg.WTX) (by simp) h0 with w | w
      · rw [if_neg (by rw [w]; exact zero_ne_one), Spec.Block.txid, hnw w]
      · rw [if_pos w, Spec.Block.wtxid, hw]
    · obtain ⟨tx, ρ, hρ, hl, hti, hat, w, hnw⟩ :=
        split_tx hL hsat hL25 hmn hnp hpad hfit hcs cat mono hSm h0 f hh hc he mt
      refine ⟨_, tx, hti, hidx ρ hρ hl tx hat, ?_⟩
      rw [hdig, if_neg (by rw [w]; exact zero_ne_one), Spec.Block.txid, hnw]

end System

end StarkedAir.Block
