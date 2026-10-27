/-
**The segment system is sound (`set_seg_sound`, set-pass step 3).** A satisfied, balanced segment
system below the size bound, whose public incoming state encodes a pass state `s` (`EncIn`), has
outgoing public values encoding `seg.foldl step s` (`EncOut`), for the records `seg` its bytes encode
(nonempty, well formed); the checks hold after it iff they held before (the records are sorted after
`s`'s last one). The fraction is the coin tuple's `1/(z − φ)` (`Rec.frac`), with the challenges public.

The parts: `set_rec` parses the bytes and advances the count, last key, amount, highest height and sum
(`Rec.rec_sound`); `set_b2w`/`set_b2c` feed Blake2s (`b2w_sound`, `b2c_sound`, `b2Feed_chain`);
`set_tmsg`/`set_shac` feed SHA-256 (`tmsg_sound`, `shac_sound`, `shaFeed_eq`); `Facts` links them.
-/
import StarkedAir.SetPass.Facts
import StarkedAir.SetPass.RecSound
import StarkedAir.SetPass.B2wSound
import StarkedAir.SetPass.B2cSound
import StarkedAir.SetPass.TMsgSound
import StarkedAir.SetPass.ShaCSound
import StarkedAir.SetPass.Fold
import StarkedAir.Gadgets.StateSound

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst half16)
open StarkedAir.Spec.QM31 (QM toQ emb)

/-! ### The encoding of a pass state in public inputs -/

/-- A Blake2s state at public block `bs`: the chaining value's limbs, the block count (`t = 64·nb`,
`nb < 2^30`), the pending bytes. -/
def EncB2 (pub : ℕ → F) (bs : ℕ) (s : Spec.SetFile.B2) : Prop :=
  (∀ w < 8, ∀ h ≤ 1, pub (H_LIMB bs (2 * w + h)) = ((half16 (s.h w) h : ℕ) : F)) ∧
  (pub (H_NB bs)).val < 2 ^ 30 ∧ s.t = 64 * (pub (H_NB bs)).val ∧
  (pub (H_PLEN bs)).val = s.pend.length ∧ s.pend.length ≤ 64 ∧
  ∀ q < s.pend.length, (pub (H_PEND bs q)).val = (s.pend.getD q 0).toNat

/-- A SHA-256 state at public block `bs`: the chaining value's limbs, the length as whole blocks and
pending bytes. -/
def EncSha (pub : ℕ → F) (bs : ℕ) (s : Spec.SetFile.Sha) : Prop :=
  (∀ w < 8, ∀ h ≤ 1, pub (H_LIMB bs (2 * w + h)) = ((half16 (Spec.Bitcoin.stateWord s.H w) h : ℕ) : F)) ∧
  pub (H_NB bs) = ((s.len / 64 : ℕ) : F) ∧ (pub (H_PLEN bs)).val = s.len % 64 ∧ s.pend.length = s.len % 64 ∧
  ∀ q < s.pend.length, (pub (H_PEND bs q)).val = (s.pend.getD q 0).toNat

/-- **The incoming state.** -/
structure EncIn (pub : ℕ → F) (s : Spec.SetFile.St QM) : Prop where
  i : pub PUB_I_IN = (s.i : F)
  last : (pub PUB_HASLAST = 0 ∧ s.last = none) ∨
    (pub PUB_HASLAST = 1 ∧ ∃ p, s.last = some p ∧ Spec.SetFile.RecOk p ∧
      ∀ j < 36, (pub (PUB_LAST_IN j)).val = Rec.keyB p j)
  lastB : ∀ j < 36, (pub (PUB_LAST_IN j)).val < 256
  maxh : (pub PUB_MAXH_IN).val = s.maxHeight
  maxh_lt : s.maxHeight < 2 ^ 24
  amtB : ∀ j < 12, (pub (PUB_AMT_IN j)).val < 256
  amt : Rec.pubAmt pub PUB_AMT_IN = s.amount
  sums : s.sums = [Block.RunSum.pQ pub PUB_SUM_IN]
  b2 : EncB2 pub B2_IN s.b2
  sha : EncSha pub SHA_IN s.sha

/-- **The outgoing state.** -/
structure EncOut (pub : ℕ → F) (s : Spec.SetFile.St QM) : Prop where
  i : pub PUB_I_OUT = (s.i : F)
  last : ∃ p, s.last = some p ∧ Spec.SetFile.RecOk p ∧ ∀ j < 36, (pub (PUB_LAST_OUT j)).val = Rec.keyB p j
  maxh : (pub PUB_MAXH_OUT).val = s.maxHeight
  maxh_lt : s.maxHeight < 2 ^ 24
  amtB : ∀ j < 12, (pub (PUB_AMT_OUT j)).val < 256
  amt : Rec.pubAmt pub PUB_AMT_OUT = s.amount
  sums : s.sums = [Block.RunSum.pQ pub PUB_SUM_OUT]
  b2 : EncB2 pub B2_OUT s.b2
  sha : EncSha pub SHA_OUT s.sha

/-- The segment's byte values (zero past its length). -/
def Sb (inst : ℕ → Inst) (pub : ℕ → F) (q : ℕ) : ℕ :=
  if q < (pub PUB_LEN).val then ((inst 0).main Block.BYTE q).val else 0

/-- The segment's bytes. -/
def segBytes (inst : ℕ → Inst) (pub : ℕ → F) : Spec.Block.Bytes :=
  (List.range (pub PUB_LEN).val).map fun q => UInt8.ofNat ((inst 0).main Block.BYTE q).val

theorem segBytes_eq (inst : ℕ → Inst) (pub : ℕ → F) :
    segBytes inst pub = (List.range (pub PUB_LEN).val).map fun q => UInt8.ofNat (Sb inst pub q) := by
  unfold segBytes
  apply List.map_congr_left
  intro q hq
  rw [Sb, if_pos (List.mem_range.mp hq)]

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub []) (hsz : SegSizeOk Ls)
include hL hsat hsz

theorem len_le : (pub PUB_LEN).val ≤ 2 ^ Ls 0 :=
  (Block.bytes_rows (bytes_sat hL hsat) (rows_lt_P hL hsz (by decide)) (by positivity)).2.1

theorem byte_lt {q : ℕ} (hq : q < (pub PUB_LEN).val) : ((inst 0).main Block.BYTE q).val < 256 :=
  ((Block.bytes_rows (bytes_sat hL hsat) (rows_lt_P hL hsz (by decide)) (by positivity)).1 q
    (by have := len_le hL hsat hsz; omega)).2

theorem Sb_lt (q : ℕ) : Sb inst pub q < 256 := by
  unfold Sb; split_ifs with h
  · exact byte_lt hL hsat hsz h
  · norm_num

theorem byte_eq {q : ℕ} (hq : q < (pub PUB_LEN).val) : (inst 0).main Block.BYTE q = ((Sb inst pub q : ℕ) : F) := by
  rw [Sb, if_pos hq, ZMod.natCast_zmod_val]

theorem len_lt : (pub PUB_LEN).val < 2 ^ 25 := by
  have := len_le hL hsat hsz
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (hsz.1 0 (by decide)); omega

/-! ### Records -/

theorem rec_rows : ∃ e, Rec.OnPre (2 ^ Ls 3) (inst 3).main e ∧ ∀ r < e, (inst 3).main Rec.IDX r = (r : F) := by
  obtain ⟨e, E⟩ := Rec.on_prefix (rec_sat hL hsat) (by positivity)
  exact ⟨e, E, (Rec.rows_sound (rec_sat hL hsat) E).1⟩

theorem rec_on_lt {e : ℕ} (E : Rec.OnPre (2 ^ Ls 3) (inst 3).main e) {r : ℕ} (hr : r < 2 ^ Ls 3)
    (hon : (inst 3).main Rec.ON r = 1) : r < e := by
  rw [E.on r hr] at hon
  by_contra h; rw [if_neg h] at hon; exact zero_ne_one hon

theorem rec_start_lt (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) {r : ℕ} (hr : r < 2 ^ Ls 3)
    (hon : (inst 3).main Rec.ON r = 1) : ((inst 3).main Rec.START r).val < 2 ^ 24 := by
  have := Rec.lc (rec_sat hL hsat) hr (c := .mul (Rec.k Rec.ON) (.sub (Rec.k Rec.START) (Rec.b3 Rec.SB)))
    (Rec.memE (by simp))
  simp only [Expr.eval, Rec.ev_k hr, Rec.ev_b3 hr, hon, one_mul, sub_eq_zero] at this
  obtain ⟨hr8, -, -⟩ := rec_ranges hL hsat hHL hsz hr
  obtain ⟨-, -, b0, -⟩ := hr8 hon 0 (by norm_num)
  obtain ⟨-, -, b1, -⟩ := hr8 hon 1 (by norm_num)
  obtain ⟨-, -, b2, -⟩ := hr8 hon 2 (by norm_num)
  have e1 : (inst 3).main Rec.START r = ((((inst 3).main (Rec.SB 0) r).val + 256 * ((inst 3).main (Rec.SB 1) r).val +
      65536 * ((inst 3).main (Rec.SB 2) r).val : ℕ) : F) := by
    rw [this]; push_cast; simp only [Rec.cast_val]
  rw [Rec.val_of_eq e1 (by have := Rec.P_big; omega)]; omega

/-- **The record component's lookups are answered** (`Rec.Hyp`), given the incoming public bytes. -/
theorem rec_hyp (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hLI : ∀ j < 36, (pub (PUB_LAST_IN j)).val < 256)
    (hAI : ∀ j < 12, (pub (PUB_AMT_IN j)).val < 256) (hMI : (pub PUB_MAXH_IN).val < 2 ^ 24) :
    Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub) := by
  obtain ⟨e, E, hidx⟩ := rec_rows hL hsat hsz
  refine ⟨Sb_lt hL hsat hsz, ?_, ?_, ?_, ?_, ?_, ?_, hHL, hLI, hAI, hMI⟩
  · intro r hr hon j hj
    obtain ⟨q, hq, hp, hb⟩ := rec_hb hL hsat hHL hsz hr hon hj
    exact ⟨q, hq, hp, by rw [hb, byte_eq hL hsat hsz hq, ZMod.val_natCast_of_lt (by have := Sb_lt hL hsat hsz q; unfold P; omega)]⟩
  · intro r hr hon j hj
    obtain ⟨q, hq, hp, hb⟩ := rec_ab hL hsat hHL hsz hr hon hj
    exact ⟨q, hq, hp, by rw [hb, byte_eq hL hsat hsz hq, ZMod.val_natCast_of_lt (by have := Sb_lt hL hsat hsz q; unfold P; omega)]⟩
  · intro r hr hon i hi
    exact (rec_ranges hL hsat hHL hsz hr).1 hon i hi
  · intro r hr j hj
    exact (rec_ranges hL hsat hHL hsz hr).2.1 j hj
  · intro r hr hon hc
    apply (rec_ranges hL hsat hHL hsz hr).2.2
    simp only [Rec.cmp, Expr.eval, Rec.ev_k hr, Rec.ev_first hr, hon]
    by_cases h0 : r = 0
    · simp only [h0, if_true, sub_self, zero_add, one_mul]
      rcases hc with h | h
      · exact absurd h0 h
      · exact h
    · simp [h0]
  · intro r hr hon
    obtain ⟨len, hlen, hle, hfp⟩ := rec_fp hL hsat hHL hsz
      (fun r hr hon => hidx r (rec_on_lt hL hsat hsz E hr hon)) (fun r hr hon => rec_start_lt hL hsat hsz hHL hr hon)
      hr hon
    have hLEN := len_lt hL hsat hsz
    have hlv : ((inst 3).main Rec.LENC r).val = len := by
      rw [hlen, ZMod.val_natCast_of_lt (by have := Rec.P_big; omega)]
    refine ⟨((inst 3).main Rec.START r).val + 49, by have := Rec.P_big; omega, by push_cast; rw [Rec.cast_val], ?_⟩
    rw [hfp, hlv]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [byte_eq hL hsat hsz (by have := List.mem_range.mp hi; omega)]

/-! ### Blake2s -/

omit hL hsat hsz in
/-- A word from its limbs (public inputs `b`, `b + 1`). -/
theorem word_of_limbs {x : Spec.Blake2s.Word} {b : ℕ} (h0 : pub b = ((half16 x 0 : ℕ) : F))
    (h1 : pub (b + 1) = ((half16 x 1 : ℕ) : F)) : x = HeaderChain.pubWord pub b :=
  HeaderChain.word_of_pubs h0.symm h1.symm

omit hL hsat hsz in
theorem toNat_ofNat_lt {x : ℕ} (h : x < 256) : (UInt8.ofNat x).toNat = x := Rec.toNat_ofNat_lt h

/-- The Blake2s stream byte `i`: the incoming pending bytes, then the segment's. -/
theorem xb_eq {s : Spec.SetFile.B2} (hb : EncB2 pub B2_IN s) (i : ℕ) :
    B2w.xb pub (Sb inst pub) i = ((s.pend ++ segBytes inst pub).getD i 0).toNat := by
  obtain ⟨-, -, -, hpl, -, hpb⟩ := hb
  unfold B2w.xb
  rw [hpl]
  split_ifs with h
  · rw [hpb i h, List.getD_append _ _ _ _ h]
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD]
    unfold segBytes Sb
    by_cases h2 : i - s.pend.length < (pub PUB_LEN).val
    · rw [if_pos h2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h2]
      simp only [Option.map_some, Option.getD_some]
      rw [toNat_ofNat_lt (byte_lt hL hsat hsz h2)]
    · rw [if_neg h2, List.getD_eq_default _ _ (by simp; omega)]; rfl

/-- **The Blake2s side.** The outgoing Blake2s state is the incoming one fed the segment's bytes. -/
theorem b2_side (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) {s : Spec.SetFile.B2} (hb : EncB2 pub B2_IN s) :
    EncB2 pub B2_OUT (Spec.SetFile.b2Feed s (segBytes inst pub)) := by
  have ws := b2w_sat hL hsat
  have h25 : 2 ^ Ls 5 ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) (by have := hsz.1 5 (by decide); omega)
  have hLEN := len_lt hL hsat hsz
  obtain ⟨m, hm1, h16, hmF, hpli, hplo1, hplo2, harith, hUW, hwords, hpo⟩ := B2w.b2w_sound ws (by positivity) h25
    (Sb inst pub) (by omega)
    (fun r hr j hj hN => (b2w_reads hL hsat hHL hsz hr hj).1 hN)
    (fun r hr j hj hA => by
      obtain ⟨q, hq, hp, hbq⟩ := (b2w_reads hL hsat hHL hsz hr hj).2.1 hA
      exact ⟨q, hq, hp, by rw [hbq, byte_eq hL hsat hsz hq, ZMod.val_natCast_of_lt
        (by have := Sb_lt hL hsat hsz q; have := Rec.P_big; omega)]⟩)
    (fun r hr j hj hH => (b2w_reads hL hsat hHL hsz hr hj).2.2 hH)
  set X := s.pend ++ segBytes inst pub with hX
  have hxb := xb_eq hL hsat hsz hb
  obtain ⟨hlimb, hnb, ht, hpl, -, -⟩ := hb
  have hXl : X.length = 64 * m + (pub (H_PLEN B2_OUT)).val := by
    rw [hX, List.length_append, ← hpl, segBytes, List.length_map, List.length_range]; omega
  have hXb : ∀ i, (X.getD i 0).toNat < 256 := fun i => (X.getD i 0).toNat_lt
  -- the compressions
  have cs := b2c_sat hL hsat
  have hmn : m ≤ 2 ^ 25 := by omega
  obtain ⟨hnbm, hout⟩ := B2c.b2c_sound cs X hm1 hmn hmF hnb (by
    intro r hr hmu
    have hlt : r % 88 < 16 := by
      have := B2c.defn cs (a := B2c.MU) (e := .mul (B2c.k B2c.USEW) (B2c.p B2c.P_LT16)) (by simp [B2c.flagC]) hr
      rw [hmu] at this
      simp only [Expr.eval, B2c.ev_k hr, B2c.ev_lt16 hr] at this
      by_contra hc; rw [if_neg hc, mul_zero] at this; exact one_ne_zero this
    obtain ⟨y, hy, huw, hblk, hk, hlo, hhi⟩ := b2c_word hL hsat hHL hsz hr hmu
    have hy16 : y < 16 * m := by
      rw [hUW y hy] at huw; by_contra hc; rw [if_neg hc] at huw; exact huw rfl
    obtain ⟨hbk, hB⟩ := hwords y hy16
    have hyk : y % 16 = r % 88 := by
      rw [B2c.ev_kr hr, if_pos hlt] at hk
      exact natCast_inj_of_lt (by have := Rec.P_big; omega) (by have := Rec.P_big; omega) hk
    refine ⟨y / 16, by omega, by rw [← hblk, hbk], ?_, ?_⟩
    · have hw : (Spec.Blake2s.wordAt X (y / 16) (r % 88)).toNat = (X.getD (4 * y) 0).toNat +
          256 * (X.getD (4 * y + 1) 0).toNat + 65536 * (X.getD (4 * y + 2) 0).toNat +
          16777216 * (X.getD (4 * y + 3) 0).toNat := by
        unfold Spec.Blake2s.wordAt
        rw [show 64 * (y / 16) + 4 * (r % 88) = 4 * y by omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := hXb (4 * y); have := hXb (4 * y + 1); have := hXb (4 * y + 2); have := hXb (4 * y + 3); omega)]
      rw [← hlo, hB 0 (by norm_num), hB 1 (by norm_num), hw, hxb, hxb]
      have := hXb (4 * y); have := hXb (4 * y + 1); have := hXb (4 * y + 2); have := hXb (4 * y + 3)
      rw [show (X.getD (4 * y) 0).toNat + 256 * (X.getD (4 * y + 1) 0).toNat + 65536 * (X.getD (4 * y + 2) 0).toNat +
          16777216 * (X.getD (4 * y + 3) 0).toNat = ((X.getD (4 * y) 0).toNat + 256 * (X.getD (4 * y + 1) 0).toNat) +
          65536 * ((X.getD (4 * y + 2) 0).toNat + 256 * (X.getD (4 * y + 3) 0).toNat) by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
      simp only [Nat.add_zero]; push_cast; ring
    · have hw : (Spec.Blake2s.wordAt X (y / 16) (r % 88)).toNat = (X.getD (4 * y) 0).toNat +
          256 * (X.getD (4 * y + 1) 0).toNat + 65536 * (X.getD (4 * y + 2) 0).toNat +
          16777216 * (X.getD (4 * y + 3) 0).toNat := by
        unfold Spec.Blake2s.wordAt
        rw [show 64 * (y / 16) + 4 * (r % 88) = 4 * y by omega, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
          have := hXb (4 * y); have := hXb (4 * y + 1); have := hXb (4 * y + 2); have := hXb (4 * y + 3); omega)]
      rw [← hhi, hB 2 (by norm_num), hB 3 (by norm_num), hw, hxb, hxb]
      have := hXb (4 * y); have := hXb (4 * y + 1); have := hXb (4 * y + 2); have := hXb (4 * y + 3)
      rw [show (X.getD (4 * y) 0).toNat + 256 * (X.getD (4 * y + 1) 0).toNat + 65536 * (X.getD (4 * y + 2) 0).toNat +
          16777216 * (X.getD (4 * y + 3) 0).toNat = ((X.getD (4 * y) 0).toNat + 256 * (X.getD (4 * y + 1) 0).toNat) +
          65536 * ((X.getD (4 * y + 2) 0).toNat + 256 * (X.getD (4 * y + 3) 0).toNat) by ring,
        Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega)]
      simp only [Nat.zero_add]; push_cast; ring)
    (by obtain ⟨x, hx, hx87, hl, -⟩ := b2_end hL hsat hHL hsz; exact ⟨x, hx, hx87, hl⟩)
  -- the spec feed
  obtain ⟨ft, fp, fh⟩ := Spec.SetFile.b2Feed_chain s (segBytes inst pub) m (pub (H_PLEN B2_OUT)).val hXl hplo1 hplo2
  have hin : ∀ w < 8, s.h w = B2c.hIn pub w := by
    intro w hw
    rw [word_of_limbs (b := H_LIMB B2_IN (2 * w)) (hlimb w hw 0 (by norm_num))
      (by rw [show H_LIMB B2_IN (2 * w) + 1 = H_LIMB B2_IN (2 * w + 1) by simp [H_LIMB]; ring]; exact hlimb w hw 1 le_rfl)]
    rfl
  have hnbo : (pub (H_NB B2_OUT)).val = (pub (H_NB B2_IN)).val + m := by
    have e1 : pub (H_NB B2_OUT) = (((pub (H_NB B2_IN)).val + m : ℕ) : F) := by
      rw [Nat.cast_add, Rec.cast_val, ← hmF]; ring
    rw [e1, ZMod.val_natCast_of_lt (by have := Rec.P_big; omega)]
  refine ⟨fun w hw h hh => ?_, by omega, by rw [ft, ht, hnbo]; ring, ?_, ?_, ?_⟩
  · rw [hout w hw h hh, fh w hw, ← hX, ht,
      Spec.SetFile.chainS_congr (fun w hw => (hin w hw).symm) _ _ m w hw]
  · rw [fp, List.length_drop, ← hX]; omega
  · rw [fp, List.length_drop, ← hX]; omega
  · intro q hq
    rw [fp, ← hX] at hq ⊢
    rw [List.length_drop] at hq
    rw [hpo q (by have := hXl; omega), ZMod.val_natCast_of_lt (by
        rw [hxb]; exact lt_of_lt_of_le (UInt8.toNat_lt _) (by have := Rec.P_big; omega)), hxb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop, hX]

/-! ### SHA-256 -/

omit hL hsat hsz in
theorem ofNat_mod256 (x : ℕ) : UInt8.ofNat (x % 256) = UInt8.ofNat x := by
  apply UInt8.toNat_inj.mp; simp [UInt8.toNat_ofNat]

omit hL hsat hsz in
/-- A record's stream bytes are its `TxOutSer`. -/
theorem recSer_bytes {S : ℕ → ℕ} {cb : ℕ → ℕ → ℕ} {st ln : ℕ → ℕ} {ρ : ℕ}
    (hcb : ∀ i < 4, cb ρ i = Spec.SetFile.code (Rec.recAt S (st ρ) (ln ρ)) / 256 ^ i % 256) :
    (TMsg.recSer S cb st ln ρ).map UInt8.ofNat = Spec.SetFile.txOutSer (Rec.recAt S (st ρ) (ln ρ)) := by
  have h36 : (List.range 36).map (fun j => UInt8.ofNat (S (st ρ + j))) =
      Rec.bytesAt S (st ρ) 32 ++ Rec.bytesAt S (st ρ + 32) 4 := by
    rw [← Rec.bytesAt_add]; rfl
  have h4 : (List.range 4).map (fun i => UInt8.ofNat (cb ρ i)) =
      Spec.Block.leBytes 4 (Spec.SetFile.code (Rec.recAt S (st ρ) (ln ρ))) := by
    unfold Spec.Block.leBytes
    apply List.map_congr_left
    intro i hi
    rw [hcb i (List.mem_range.mp hi), ofNat_mod256, pow_mul]; norm_num
  simp only [TMsg.recSer, List.map_append, List.map_map, Function.comp_def, h36, h4]
  simp only [Spec.SetFile.txOutSer, Spec.SetFile.txid, Spec.SetFile.vout, Spec.SetFile.ser, Rec.recAt,
    Rec.leBytes_bytesAt, List.append_assoc]
  rfl

omit hL hsat hsz in
theorem list_eq_range (l : Spec.Block.Bytes) : (List.range l.length).map (fun q => l.getD q 0) = l := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]


omit hL hsat hsz in
/-- A used SHA period `q` (whole or not) is block `q`. -/
theorem shac_blki {n : ℕ} {M : ℕ → ℕ → F} (cs : ∀ r < n, ∀ c ∈ ShaC.constraints, c.eval n ShaC.preCols pub M r = 0)
    (hn : 0 < n) : ∀ q, 72 * q < n → M ShaC.NIL (72 * q) = 0 → M ShaC.BLKI (72 * q) = (q : F)
  | 0, _, _ => by simpa using ShaC.p0_blki cs hn
  | q + 1, h, hnil => by
    obtain ⟨-, hb, hnp⟩ := ShaC.prev_period cs (s := 72 * (q + 1)) (by omega) (by omega) h hnil
    rw [show 72 * (q + 1) - 72 = 72 * q by omega] at hb hnp
    rw [hb, shac_blki cs hn q (by omega) hnp]; push_cast; ring

/-- **The SHA-256 side.** The outgoing SHA-256 state is the incoming one fed the records' `TxOutSer`. -/
theorem sha_side (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) {sh : Spec.SetFile.Sha}
    (hs : EncSha pub SHA_IN sh) {e : ℕ} (E : Rec.OnPre (2 ^ Ls 3) (inst 3).main e)
    (H : Rec.Hyp (2 ^ Ls 3) pub (inst 3).main (Sb inst pub)) :
    EncSha pub SHA_OUT (Spec.SetFile.shaFeed sh
      ((Rec.recs (inst 3).main (Sb inst pub) e).flatMap Spec.SetFile.txOutSer)) := by
  have rs := rec_sat hL hsat
  obtain ⟨hidx, hcnt⟩ := Rec.rows_sound rs E
  obtain ⟨-, c1, c2⟩ := Rec.chain rs E H
  have hen := E.lt
  have hP3 := rows_lt_P hL hsz (i := 3) (by decide)
  have hLEN := len_lt hL hsat hsz
  have hcv : (pub PUB_I_OUT - pub PUB_I_IN).val = e := by
    rw [hcnt, ZMod.val_natCast_of_lt (by omega)]
  obtain ⟨hlimb, hnbI, hplI, hpendL, hpendB⟩ := hs
  -- the records' ends are within the segment
  have hend : ∀ d ρ, ρ + d + 1 = e → ((inst 3).main Rec.START ρ).val + 49 + ((inst 3).main Rec.LENC ρ).val ≤
      (pub PUB_LEN).val := by
    intro d
    induction d with
    | zero => intro ρ h; rw [show ρ = e - 1 by omega]; exact c2.le
    | succ d ih =>
      intro ρ h
      have := ih (ρ + 1) (by omega); have := c1 ρ (by omega)
      have := (Rec.fields rs E H (r := ρ + 1) (by omega)).2.2.1; omega
  have ts := tmsg_sat hL hsat
  have h7 : 2 ^ Ls 7 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (hsz.1 7 (by decide))
  have T := TMsg.tmsg_sound ts (by positivity) (by omega) (S := Sb inst pub)
    (cb := fun ρ i => ((inst 3).main (Rec.C i) ρ).val) (LEN := (pub PUB_LEN).val)
    (st := fun ρ => ((inst 3).main Rec.START ρ).val) (ln := fun ρ => ((inst 3).main Rec.LENC ρ).val) (by omega)
    (by
      intro ρ hρ; rw [hcv] at hρ
      exact ⟨by have := (Rec.fields rs E H hρ).2.2.1; omega, hend (e - 1 - ρ) ρ (by omega)⟩)
    (fun r hr h => tmsg_pnd hL hsat hHL hsz hr h)
    (fun r hr h => by
      obtain ⟨q, hq, hp, hb⟩ := tmsg_byte hL hsat hHL hsz hr (k := 1) (Or.inl ⟨rfl, rfl⟩) h
      exact ⟨q, hq, by simpa using hp, by rw [hb, byte_eq hL hsat hsz hq, ZMod.val_natCast_of_lt
        (by have := Sb_lt hL hsat hsz q; have := Rec.P_big; omega)]⟩)
    (fun r hr h => by
      obtain ⟨q, hq, hp, hb⟩ := tmsg_byte hL hsat hHL hsz hr (k := 3) (Or.inr ⟨rfl, rfl⟩) h
      exact ⟨q, hq, by simpa using hp, by rw [hb, byte_eq hL hsat hsz hq, ZMod.val_natCast_of_lt
        (by have := Sb_lt hL hsat hsz q; have := Rec.P_big; omega)]⟩)
    (fun r hr h => by
      obtain ⟨ρ, hρ, hon, i, hi, hR, hO, hB⟩ := tmsg_code hL hsat hHL hsz hr h
      have hρe := rec_on_lt hL hsat hsz E hρ hon
      exact ⟨ρ, by rw [hcv]; exact hρe, i, hi, by rw [hR, hidx ρ hρe], hO, by rw [hB]⟩)
    (fun r hr h => by
      obtain ⟨ρ, hρ, hon, hR, hS, hN⟩ := tmsg_rec hL hsat hHL hsz hr h
      have hρe := rec_on_lt hL hsat hsz E hρ hon
      exact ⟨ρ, by rw [hcv]; exact hρe, by rw [hR, hidx ρ hρe], by rw [hS, Rec.cast_val], by rw [hN, Rec.cast_val]⟩)
    (fun r hr h => ⟨r % 64, Nat.mod_lt _ (by norm_num), rfl, tmsg_tail hL hsat hHL hsz hr h⟩)
  simp only [hcv] at T
  set seg := (Rec.recs (inst 3).main (Sb inst pub) e).flatMap Spec.SetFile.txOutSer with hseg
  set x := TMsg.stream (fun q => (pub (H_PEND SHA_IN q)).val) (pub (H_PLEN SHA_IN)).val e (Sb inst pub)
    (fun ρ i => ((inst 3).main (Rec.C i) ρ).val) (fun ρ => ((inst 3).main Rec.START ρ).val)
    (fun ρ => ((inst 3).main Rec.LENC ρ).val) with hx
  obtain ⟨-, hxn, hnbD, hplO, hpoB, hsw⟩ := T
  set Xb := sh.pend ++ seg with hXb
  have hql : (pub (H_PLEN SHA_IN)).val = sh.pend.length := by rw [hplI, hpendL]
  -- the stream's bytes are the state's pending bytes, then the records' `TxOutSer`
  have hrecser : ∀ ρ < e, (TMsg.recSer (Sb inst pub) (fun ρ i => ((inst 3).main (Rec.C i) ρ).val)
      (fun ρ => ((inst 3).main Rec.START ρ).val) (fun ρ => ((inst 3).main Rec.LENC ρ).val) ρ).map UInt8.ofNat =
      Spec.SetFile.txOutSer (Rec.recR (inst 3).main (Sb inst pub) ρ) := fun ρ hρ =>
    recSer_bytes (fun i hi => Rec.code_bytes rs E H hρ hi)
  have hX : x.map UInt8.ofNat = Xb := by
    rw [hx, hXb, hseg, TMsg.stream, List.map_append, List.map_flatMap, hql, Rec.recs, List.flatMap_map]
    congr 1
    · conv_rhs => rw [← list_eq_range sh.pend]
      rw [List.map_map]
      apply List.map_congr_left
      intro q hq
      simp only [Function.comp]
      rw [hpendB q (List.mem_range.mp hq), UInt8.ofNat_toNat]
    · apply List.flatMap_congr
      intro ρ hρ; exact hrecser ρ (List.mem_range.mp hρ)
  have hxlt : ∀ v ∈ x, v < 256 := by
    intro v hv
    rw [hx, TMsg.stream, List.mem_append, List.mem_map, List.mem_flatMap] at hv
    rcases hv with ⟨q, hq, rfl⟩ | ⟨ρ, hρ, hv⟩
    · rw [hql] at hq; rw [hpendB q (List.mem_range.mp hq)]; exact UInt8.toNat_lt _
    · simp only [TMsg.recSer, List.mem_append, List.mem_map] at hv
      rcases hv with (⟨j, -, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨j, -, rfl⟩
      · exact Sb_lt hL hsat hsz _
      · rw [Rec.code_bytes rs E H (List.mem_range.mp hρ) (List.mem_range.mp hi)]; exact Nat.mod_lt _ (by norm_num)
      · exact Sb_lt hL hsat hsz _
  have hgx : ∀ i, (Xb.getD i 0).toNat = x.getD i 0 := by
    intro i
    rw [← hX, List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
    cases h : x[i]? with
    | none => rfl
    | some v => exact toNat_ofNat_lt (hxlt v (List.mem_of_getElem? h))
  have hlen : Xb.length = x.length := by rw [← hX, List.length_map]
  have hXl : Xb.length = sh.len % 64 + seg.length := by rw [hXb, List.length_append, hpendL]
  -- the state's chaining value is the public incoming one
  have hH : sh.H = HeaderChain.pubState pub SHA_IN := by
    have hw : ∀ w < 8, Spec.Bitcoin.stateWord sh.H w = HeaderChain.pubWord pub (SHA_IN + 2 * w) := fun w hw =>
      word_of_limbs (hlimb w hw 0 (by norm_num))
        (by rw [show SHA_IN + 2 * w + 1 = H_LIMB SHA_IN (2 * w + 1) by simp [H_LIMB]; ring]; exact hlimb w hw 1 le_rfl)
    have key : ∀ S0 : Spec.Sha256.State, (∀ w < 8, Spec.Bitcoin.stateWord S0 w =
        HeaderChain.pubWord pub (SHA_IN + 2 * w)) → S0 = HeaderChain.pubState pub SHA_IN := by
      rintro ⟨a, b, c, d, e', f, g, h⟩ hw
      have h0 := hw 0 (by norm_num); have h1 := hw 1 (by norm_num); have h2 := hw 2 (by norm_num)
      have h3 := hw 3 (by norm_num); have h4 := hw 4 (by norm_num); have h5 := hw 5 (by norm_num)
      have h6 := hw 6 (by norm_num); have h7 := hw 7 (by norm_num)
      simp only [Spec.Bitcoin.stateWord] at h0 h1 h2 h3 h4 h5 h6 h7
      subst h0 h1 h2 h3 h4 h5 h6 h7; rfl
    exact key _ hw
  -- the compressions
  have cs := shac_sat hL hsat
  have h8 : 2 ^ Ls 8 ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) (hsz.1 8 (by decide))
  have hmS : (pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)).val = x.length / 64 := by
    rw [hnbD, ZMod.val_natCast_of_lt (by have := Rec.P_big; omega)]
  have htok : ∃ r < 2 ^ Ls 8, r % 72 = 71 ∧ (inst 8).main ShaC.LASTS r = 1 := by
    obtain ⟨r, hr, h71, hl, -⟩ := sha_end hL hsat hHL hsz; exact ⟨r, hr, h71, hl⟩
  have hmsg : ∀ s0 t, s0 % 72 = 0 → t < 16 → s0 + 4 + t < 2 ^ Ls 8 → (inst 8).main ShaC.USEW s0 = 1 →
      ∃ b : ℕ, (inst 8).main ShaC.BLKI s0 = (b : F) ∧ b < (pub (H_NB SHA_OUT) - pub (H_NB SHA_IN)).val ∧
        ∀ h ≤ 1, (Sha256.limb Sha256.W h).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main (s0 + 4 + t) =
          ((half16 (blockWords Xb b t) h : ℕ) : F) := by
    intro s0 t hs0 ht hx0 hu
    have hs0n : s0 < 2 ^ Ls 8 := by omega
    have hnil : (inst 8).main ShaC.NIL s0 = 0 := by
      have := ShaC.usew_eq cs hs0n; rw [hu] at this; linear_combination this
    obtain ⟨q, rfl⟩ : ∃ q, s0 = 72 * q := ⟨s0 / 72, by omega⟩
    have hbq := shac_blki cs (by positivity) q hs0n hnil
    have hbx : (inst 8).main ShaC.BLKI (72 * q + (4 + t)) = (q : F) := by
      rw [ShaC.per_const cs (X := ShaC.BLKI) (by simp) hs0 (4 + t) (by omega) (by omega), hbq]
    have hux : (inst 8).main ShaC.USEW (72 * q + (4 + t)) = 1 := by
      rw [ShaC.usew_eq cs (by omega), ShaC.per_const cs (X := ShaC.NIL) (by simp) hs0 (4 + t) (by omega) (by omega),
        hnil, sub_zero]
    have hx0' : 72 * q + 4 + t = 72 * q + (4 + t) := by ring
    have hm : (Expr.mul (pre ShaC.MSGROW) (ShaC.k ShaC.USEW)).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main
        (72 * q + 4 + t) = 1 := by
      rw [hx0']
      simp only [Expr.eval, ShaC.ev_k (by omega : 72 * q + (4 + t) < 2 ^ Ls 8), hux, mul_one]
      rw [ShaC.eval_per72 (f := fun q => if 4 ≤ q ∧ q < 20 then 1 else 0) rfl (by omega)]
      rw [if_pos (by omega)]; simp
    obtain ⟨y, hy, hNT, hY, hlo, hhi⟩ := shac_word hL hsat hHL hsz (by omega) hm
    obtain ⟨hy4, hyM, hY3, hloY, hhiY⟩ := hsw y hy hNT
    have hrow : (pre ShaC.ROWIDX).eval (2 ^ Ls 8) ShaC.preCols pub (inst 8).main (72 * q + 4 + t) = ((4 + t : ℕ) : F) := by
      rw [ShaC.eval_per72 (f := id) rfl (by omega)]; congr 1; simp only [id]; omega
    have hYeq : y - 3 = 64 * q + 4 * t := by
      rw [hY3] at hY
      simp only [Expr.eval, ShaC.ev_k (by omega : 72 * q + 4 + t < 2 ^ Ls 8), hrow, StarkedAir.Sha256.eval_cst] at hY
      rw [hx0', hbx] at hY
      have h2 : ((y - 3 : ℕ) : F) = ((64 * q + 4 * t : ℕ) : F) := by rw [hY]; push_cast; ring
      have : 72 * q < 2 ^ 24 := by omega
      exact natCast_inj_of_lt (by have := Rec.P_big; omega) (by have := Rec.P_big; omega) h2
    have hy3 : 3 ≤ y := by omega
    refine ⟨q, hbq, by rw [hmS]; omega, fun h hh => ?_⟩
    have hgd : ∀ j < 64, ((Xb.drop (64 * q)).take 64).getD j 0 = Xb.getD (64 * q + j) 0 := by
      intro j hj
      simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, List.getElem?_drop]
    obtain ⟨k0, k1⟩ := chunkWords_half ((Xb.drop (64 * q)).take 64) t
    rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl
    · rw [← hlo, hloY, blockWords, k0, hgd (4 * t + 2) (by omega), hgd (4 * t + 3) (by omega), hgx, hgx, show 64 * q + (4 * t + 2) = y - 1 by omega, show 64 * q + (4 * t + 3) = y by omega]
    · rw [← hhi, hhiY, blockWords, k1, hgd (4 * t) (by omega), hgd (4 * t + 1) (by omega), hgx, hgx,
        show 64 * q + 4 * t = y - 3 by omega, show 64 * q + (4 * t + 1) = y - 2 by omega]
  obtain ⟨-, hout⟩ := ShaC.shac_sound cs (by positivity) (by omega) (blockWords Xb) hmsg htok
  have hxl : x.length = sh.len % 64 + seg.length := by rw [← hlen, hXl]
  rw [shaFeed_eq]
  refine ⟨fun w hw h hh => ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Rec.cast_val (pub (H_LIMB SHA_OUT (2 * w + h))), hout w hw h hh, hmS, hH, hlen]
  · show pub (H_NB SHA_OUT) = (((sh.len + seg.length) / 64 : ℕ) : F)
    have e1 : pub (H_NB SHA_OUT) = pub (H_NB SHA_IN) + ((x.length / 64 : ℕ) : F) := by rw [← hnbD]; ring
    rw [e1, hnbI, ← Nat.cast_add]
    congr 1; omega
  · show (pub (H_PLEN SHA_OUT)).val = (sh.len + seg.length) % 64
    rw [hplO, ZMod.val_natCast_of_lt (by have := Rec.P_big; omega)]; omega
  · show (Xb.drop (64 * (Xb.length / 64))).length = (sh.len + seg.length) % 64
    rw [List.length_drop]; omega
  · intro q hq
    show (pub (H_PEND SHA_OUT q)).val = ((Xb.drop (64 * (Xb.length / 64))).getD q 0).toNat
    have hq' : q < x.length % 64 := by
      have : (Xb.drop (64 * (Xb.length / 64))).length = x.length % 64 := by rw [List.length_drop, hlen]; omega
      exact this ▸ hq
    rw [hpoB q hq', ← hgx, hlen]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]


/-! ### Together -/

omit hL hsat hsz in
theorem keyLex_congr {a a' b : ℕ → ℕ} (h : ∀ j < 36, a j = a' j) (hl : Rec.KeyLex a b) : Rec.KeyLex a' b := by
  obtain ⟨d, hd, heq, hlt⟩ := hl
  exact ⟨d, hd, fun i hi => by rw [← h i (by omega)]; exact heq i hi, by rw [← h d hd]; exact hlt⟩

/-- **The segment system is sound.** A satisfied, balanced segment system below the size bound whose
public incoming state encodes `s` proves the records `seg` its bytes encode (nonempty, well formed),
and its public outgoing state encodes `seg.foldl step s`, whose checks hold iff `s`'s did. -/
theorem set_seg_sound (s : Spec.SetFile.St QM) (hin : EncIn pub s) :
    ∃ seg : List Spec.CoinEpoch.CEv, seg ≠ [] ∧ seg.flatMap Spec.SetFile.encRec = segBytes inst pub ∧
      (∀ x ∈ seg, Spec.SetFile.RecOk x) ∧
      EncOut pub (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s) ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s).n = s.n ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s).ok = s.ok := by
  have hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1 := by
    rcases hin.last with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have H := rec_hyp hL hsat hsz hHL hin.lastB hin.amtB (by rw [hin.maxh]; exact hin.maxh_lt)
  have rs := rec_sat hL hsat
  obtain ⟨e, E, -, hcnt, hparse, hok, hsorted, hfirst, hlastout, hamt, hamtB, hmax, hmaxlt, hsum⟩ :=
    Rec.rec_sound rs (by positivity) H
  set seg := Rec.recs (inst 3).main (Sb inst pub) e with hseg
  have he1 := E.pos
  have hne : seg ≠ [] := by
    rw [hseg, Rec.recs]; intro h
    rw [List.map_eq_nil_iff, List.range_eq_nil] at h; omega
  have hlen : seg.length = e := by simp [hseg, Rec.recs]
  have hbytes : seg.flatMap Spec.SetFile.encRec = segBytes inst pub := by rw [hparse, segBytes_eq]
  have hrok : ∀ x ∈ seg, Spec.SetFile.RecOk x := fun x hx => (hok x hx).1
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := Spec.SetFile.fold_step [Rec.frac pub] seg s hne
  have hlast : seg.getLast? = some (Rec.recR (inst 3).main (Sb inst pub) (e - 1)) := by
    rw [List.getLast?_eq_getElem?, hlen, hseg, Rec.recs, List.getElem?_map, List.getElem?_range (by omega)]; rfl
  have hr0 : seg = Rec.recR (inst 3).main (Sb inst pub) 0 :: (List.range (e - 1)).map
      (fun r => Rec.recR (inst 3).main (Sb inst pub) (r + 1)) := by
    rw [hseg, Rec.recs, show e = (e - 1) + 1 by omega, List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [show e - 1 + 1 - 1 = e - 1 by omega]; rfl
  -- the checks
  have hchain : Spec.SetFile.chainOk s.last seg = true := by
    rcases hin.last with ⟨-, hn⟩ | ⟨h1, p, hp, hpok, hpk⟩
    · rw [hn, Spec.SetFile.chainOk_none]; exact hsorted
    · rw [hp, Spec.SetFile.chainOk_some]
      have hs := hsorted
      rw [hr0] at hs ⊢
      unfold Spec.SetFile.Sorted at hs ⊢
      rw [List.isChain_cons_cons]
      refine ⟨?_, hs⟩
      have h0ok := hrok (Rec.recR (inst 3).main (Sb inst pub) 0) (by rw [hr0]; exact List.mem_cons_self ..)
      exact Rec.keyLt_of_lex hpok.1 h0ok.1 hpok.2.1 h0ok.2.1 (keyLex_congr hpk (hfirst h1))
  refine ⟨seg, hne, hbytes, hrok, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, f1, ?_⟩
  · rw [f2, hlen, Nat.cast_add, ← hin.i, ← hcnt]; ring
  · refine ⟨_, by rw [f8, hlast], (hok _ (by rw [hseg, Rec.recs]; exact List.mem_map.mpr ⟨e - 1,
      List.mem_range.mpr (by omega), rfl⟩)).1, hlastout⟩
  · rw [f7, hmax, hin.maxh]
  · rw [f7, ← hin.maxh, ← hmax]; exact hmaxlt
  · exact hamtB
  · rw [f6, hamt, hin.amt]
  · rw [f5, hin.sums, hsum]; simp
  · rw [f3, hbytes]; exact b2_side hL hsat hsz hHL hin.b2
  · rw [f4]; exact sha_side hL hsat hsz hHL hin.sha E H
  · have := f9
    cases hok' : s.ok <;> cases h' : (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s).ok <;> simp_all

end System

end StarkedAir.SetPass
