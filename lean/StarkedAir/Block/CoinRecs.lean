/-
**Input claims are the undo stream's records (D-041, steps 1–3 of utxo.md's plan).** The undo stream
`Ub` (committed in `C_h`, `commit_sound`) is a sequence of records `code(4) ‖ ctx(3) ‖ tl(2) ‖ script(tl)`
from offset 1. `recStart`/`recAt` parse it sequentially. `rec_starts`: URec's record starts are exactly
that parse (`rows_sound`, `tl_bytes`, `urec_bytes`). `claim_is_record`: every input claim the coin
component uses (`ClaimAt`) is the record at its URec row, so the claims are a function of the committed
stream and the row index — no choice is left to the prover.
-/
import StarkedAir.Block.CoinEpochSound

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch

/-- The script length in the header of the record at `s`. -/
def tlAt (u : Spec.Block.Bytes) (s : ℕ) : ℕ := Spec.Block.le ((List.range 2).map fun k => u.getD (s + 7 + k) 0)

/-- Where record `r` starts, parsing from offset 1. -/
def recStart (u : Spec.Block.Bytes) : ℕ → ℕ
  | 0 => 1
  | r + 1 => recStart u r + 9 + tlAt u (recStart u r)

/-- Record `r` as a claim: its code, script and creating transaction's index. -/
def recAt (u : Spec.Block.Bytes) (r : ℕ) : Claim :=
  let s := recStart u r
  ⟨Spec.Block.le ((List.range 4).map fun k => u.getD (s + k) 0),
   (List.range (tlAt u s)).map fun k => u.getD (s + 9 + k) 0,
   Spec.Block.le ((List.range 3).map fun k => u.getD (s + 4 + k) 0)⟩

theorem le2_lt (f : ℕ → UInt8) : Spec.Block.le ((List.range 2).map f) < 2 ^ 16 := by
  have := UInt8.toNat_lt (f 0); have := UInt8.toNat_lt (f 1)
  simp [Spec.Block.le, List.range_succ]; omega

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- A URec byte column at an on row, as a stream byte at `S + c`, with `S + c` a natural below the
stream's length. -/
theorem urec_byte_at {r c : ℕ} (hr : r < 2 ^ L) (hon : (inst 13).main URec.ON r = 1) (hc : c < 17) :
    ((inst 13).main URec.S r).val + c < (pub 8).val ∧
      ((inst 13).main (URec.ucol c) r).val = ((Ub inst pub).getD (((inst 13).main URec.S r).val + c) 0).toNat := by
  have hU := undo_len hL hsat hL24
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have hP : P = 2147483647 := rfl
  -- `S` itself is a stream position (c = 0), so `S + c` does not wrap
  obtain ⟨u0, hu0, hpu0, -⟩ := urec_bytes hL hsat hL24 hr hon (c := 0) (by norm_num)
  have hS : ((inst 13).main URec.S r).val = u0 := by
    apply Coin.lift _ (ZMod.val_lt _) (by omega)
    rw [ZMod.natCast_zmod_val]; simpa using hpu0
  obtain ⟨u, hu, hpu, hb⟩ := urec_bytes hL hsat hL24 hr hon hc
  have e : ((inst 13).main URec.S r).val + c = u := by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; rw [ZMod.natCast_zmod_val, hpu]
  rw [e]; exact ⟨hu, hb⟩

/-- **Record starts are the stream's parse.** -/
theorem rec_starts : ∃ e < 2 ^ L, (∀ r < 2 ^ L, ((inst 13).main URec.ON r = 1 ↔ r < e)) ∧
    ∀ r < e, ((inst 13).main URec.S r).val = recStart (Ub inst pub) r := by
  obtain ⟨e, hen, hon, -, hS0, hstep, -, -⟩ := URec.rows_sound (urec_sat' hL hsat hL24) (n := 2 ^ L) (by positivity)
  refine ⟨e, hen, hon, fun r => ?_⟩
  induction r with
  | zero => intro _; rw [hS0]; rfl
  | succ r ih =>
    intro hr
    have hr0 : r < 2 ^ L := by omega
    have hon0 : (inst 13).main URec.ON r = 1 := (hon r hr0).mpr (by omega)
    have hon1 : (inst 13).main URec.ON (r + 1) = 1 := (hon (r + 1) (by omega)).mpr hr
    have htl := URec.tl_bytes (urec_sat' hL hsat hL24) (n := 2 ^ L) hr0 hon0
    obtain ⟨-, b7⟩ := urec_byte_at hL hsat hL24 hr0 hon0 (c := 7) (by norm_num)
    obtain ⟨hlt8, b8⟩ := urec_byte_at hL hsat hL24 hr0 hon0 (c := 8) (by norm_num)
    obtain ⟨hlt1, -⟩ := urec_byte_at hL hsat hL24 (by omega) hon1 (c := 0) (by norm_num)
    simp only [URec.ucol, show ¬ (7 < 4) by norm_num, show ¬ (7 < 7) by norm_num, show 7 < 9 by norm_num,
      show ¬ (8 < 4) by norm_num, show ¬ (8 < 7) by norm_num, show 8 < 9 by norm_num, if_false, if_true] at b7 b8
    have hS := hstep r hr
    rw [ih (by omega)] at b7 b8 hlt8
    have hP8 : (pub 8).val < P := ZMod.val_lt _
    rw [recStart]
    apply Coin.lift _ (by omega) (by
      have : tlAt (Ub inst pub) (recStart (Ub inst pub) r) < 65536 := le2_lt (fun k => (Ub inst pub).getD (recStart (Ub inst pub) r + 7 + k) 0)
      have hU := undo_len hL hsat hL24
      have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
      unfold P; omega)
    rw [ZMod.natCast_zmod_val, hS, htl]
    rw [← ZMod.natCast_zmod_val ((inst 13).main URec.S r), ih (by omega),
      ← ZMod.natCast_zmod_val ((inst 13).main (URec.T 0) r), ← ZMod.natCast_zmod_val ((inst 13).main (URec.T 1) r),
      show URec.T 0 = 19 from rfl, show URec.T 1 = 20 from rfl]
    simp only [URec.T] at b7 b8
    rw [b7, b8]
    unfold tlAt
    simp [Spec.Block.le, List.range_succ]

/-- **A claim is its record.** Every input claim the coin component uses is the stream's record at its
URec row: code, script (of the record's length) and creating transaction's index. -/
theorem claim_is_record {j : ℕ} {c : Claim} (hc : ClaimAt inst pub L j c) :
    ∃ rj < 2 ^ L, (inst 13).main URec.ON rj = 1 ∧ (inst 14).main Coin.J j = (inst 13).main URec.J rj ∧
      c = recAt (Ub inst pub) rj := by
  obtain ⟨-, -, rj, hrj, honj, hJ, htl, u0, hu0, h9, hlen, hser, hcodeb, hctxb⟩ := hc
  obtain ⟨e, -, hon, hst⟩ := rec_starts hL hsat hL24
  have hs : ((inst 13).main URec.S rj).val = recStart (Ub inst pub) rj := hst rj ((hon rj hrj).mp honj)
  have hU := undo_len hL hsat hL24
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have hP : P = 2147483647 := rfl
  obtain ⟨hlt0, -⟩ := urec_byte_at hL hsat hL24 hrj honj (c := 0) (by norm_num)
  have hu : u0 = recStart (Ub inst pub) rj + 9 := by
    apply Coin.lift _ (by omega) (by omega)
    rw [← hu0, ← hs]; push_cast; rw [ZMod.natCast_zmod_val]
  -- the script's length is the record's
  have htl2 := URec.tl_bytes (urec_sat' hL hsat hL24) (n := 2 ^ L) hrj honj
  obtain ⟨-, b7⟩ := urec_byte_at hL hsat hL24 hrj honj (c := 7) (by norm_num)
  obtain ⟨-, b8⟩ := urec_byte_at hL hsat hL24 hrj honj (c := 8) (by norm_num)
  simp only [URec.ucol, show ¬ (7 < 4) by norm_num, show ¬ (7 < 7) by norm_num, show 7 < 9 by norm_num,
    show ¬ (8 < 4) by norm_num, show ¬ (8 < 7) by norm_num, show 8 < 9 by norm_num, if_false, if_true] at b7 b8
  rw [hs] at b7 b8
  have hlenEq : c.ser.length = tlAt (Ub inst pub) (recStart (Ub inst pub) rj) := by
    apply Coin.lift _ (by omega) (by have := le2_lt (fun k => (Ub inst pub).getD (recStart (Ub inst pub) rj + 7 + k) 0); unfold tlAt; omega)
    rw [← htl, htl2, ← ZMod.natCast_zmod_val ((inst 13).main (URec.T 0) rj),
      ← ZMod.natCast_zmod_val ((inst 13).main (URec.T 1) rj)]
    have b7' : ((inst 13).main (URec.T 0) rj).val = ((Ub inst pub).getD (recStart (Ub inst pub) rj + 7) 0).toNat := b7
    have b8' : ((inst 13).main (URec.T 1) rj).val = ((Ub inst pub).getD (recStart (Ub inst pub) rj + 8) 0).toNat := b8
    rw [b7', b8']
    unfold tlAt
    simp [Spec.Block.le, List.range_succ]
  refine ⟨rj, hrj, honj, hJ, ?_⟩
  cases c with
  | mk code ser ctx =>
    simp only at hser hcodeb hctxb hlenEq
    simp only [recAt]
    congr 1
    · rw [hcodeb, hu, Nat.add_sub_cancel]
    · rw [hser, hlenEq, hu]
    · rw [hctxb, hu, show recStart (Ub inst pub) rj + 9 - 5 = recStart (Ub inst pub) rj + 4 by omega]

/-- **The claim of the input at coin row `j` is the stream's record `J j`** (the number of inputs
before it): no choice is left to the prover beyond the committed stream. -/
theorem claim_is_record_at {j : ℕ} {c : Claim} (hc : ClaimAt inst pub L j c) :
    c = recAt (Ub inst pub) ((inst 14).main Coin.J j).val := by
  obtain ⟨rj, hrj, honj, hJ, rfl⟩ := claim_is_record hL hsat hL24 hc
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  rw [hJ, urec_j hL hsat hL24 hrj honj, ZMod.val_natCast_of_lt (by unfold P; omega)]

end System

end StarkedAir.Block
