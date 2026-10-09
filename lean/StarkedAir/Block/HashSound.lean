/-
**Block hashing soundness (M3a.3).** In a satisfied hashing system (bytes, fields, messages, SHA), every
second-hash digest is `Spec.Block.sha256d` of a message's data bytes.
-/
import StarkedAir.Block.Link
import StarkedAir.Block.HashSpec

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
  obtain ⟨e1, e2, e3⟩ := flags_excl hsat hr
  have cq := chn_eq hsat hr
  rcases fbool hsat (c := FST) (by simp) hr with a | a <;> rcases fbool hsat (c := DBL) (by simp) hr with b | b <;>
    rcases fbool hsat (c := NILS) (by simp) hr with c | c <;> simp_all

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

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 4, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub [])
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
  have hu : (inst 3).main Sha.USEW x = 1 := by
    rw [Sha.usew_eq ss hx, hdbl, hnil, ← Sha.usew_eq ss (by omega)]; exact Sha.usew_one ss (by omega) hfc
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

end System

end StarkedAir.Block
