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

theorem insBefore_succ (txs : List Spec.Block.Tx) (t : ℕ) (tx : Spec.Block.Tx) (htx : txs[t]? = some tx) :
    insBefore txs (t + 1) = insBefore txs t + if 1 ≤ t then tx.vin.length else 0 := by
  unfold insBefore
  rw [List.range_succ, List.map_append, List.sum_append]
  simp [htx]


/-- The inputs before transaction `t` are at most its parts' rows before it. -/
theorem insBefore_le {txs : List Spec.Block.Tx} {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx txs parts) :
    ∀ t ≤ txs.length, insBefore txs t ≤ ((parts.take t).map List.length).sum
  | 0, _ => by simp [insBefore]
  | t + 1, ht => by
    obtain ⟨tx, htx⟩ : ∃ tx, txs[t]? = some tx := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hpl, hpe⟩ := part_len hf htx
    rw [insBefore_succ _ t tx htx, List.take_add_one, List.map_append, List.sum_append]
    have ih := insBefore_le hf t (by omega)
    have : (List.map List.length (parts[t]?.toList)).sum = tx.vin.length + tx.vout.length := by
      rw [← hpe]; simp [List.getElem?_eq_getElem hpl, List.getD_eq_getElem _ _ hpl]
    rw [this]; split <;> omega

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
include hL hsat hL24

/-- A URec byte column at an on row, as a stream byte at `S + c`, with `S + c` a natural below the
stream's length. -/
theorem urec_byte_at {r c : ℕ} (hr : r < 2 ^ Ls 13) (hon : (inst 13).main URec.ON r = 1) (hc : c < 17) :
    ((inst 13).main URec.S r).val + c < (pub 8).val ∧
      ((inst 13).main (URec.ucol c) r).val = ((Ub inst pub).getD (((inst 13).main URec.S r).val + c) 0).toNat := by
  have hU := undo_len hL hsat hL24
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
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
theorem rec_starts : ∃ e < 2 ^ Ls 13, (∀ r < 2 ^ Ls 13, ((inst 13).main URec.ON r = 1 ↔ r < e)) ∧
    ∀ r < e, ((inst 13).main URec.S r).val = recStart (Ub inst pub) r := by
  obtain ⟨e, hen, hon, -, hS0, hstep, -, -⟩ := URec.rows_sound (urec_sat' hL hsat hL24) (n := 2 ^ Ls 13) (by positivity)
  refine ⟨e, hen, hon, fun r => ?_⟩
  induction r with
  | zero => intro _; rw [hS0]; rfl
  | succ r ih =>
    intro hr
    have hr0 : r < 2 ^ Ls 13 := by omega
    have hon0 : (inst 13).main URec.ON r = 1 := (hon r hr0).mpr (by omega)
    have hon1 : (inst 13).main URec.ON (r + 1) = 1 := (hon (r + 1) (by omega)).mpr hr
    have htl := URec.tl_bytes (urec_sat' hL hsat hL24) (n := 2 ^ Ls 13) hr0 hon0
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
      obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
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
theorem claim_is_record {j : ℕ} {c : Claim} (hc : ClaimAt inst pub (Ls 13) j c) :
    ∃ rj < 2 ^ Ls 13, (inst 13).main URec.ON rj = 1 ∧ (inst 14).main Coin.J j = (inst 13).main URec.J rj ∧
      c = recAt (Ub inst pub) rj := by
  obtain ⟨-, -, rj, hrj, honj, hJ, htl, u0, hu0, h9, hlen, hser, hcodeb, hctxb⟩ := hc
  obtain ⟨e, -, hon, hst⟩ := rec_starts hL hsat hL24
  have hs : ((inst 13).main URec.S rj).val = recStart (Ub inst pub) rj := hst rj ((hon rj hrj).mp honj)
  have hU := undo_len hL hsat hL24
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hP : P = 2147483647 := rfl
  obtain ⟨hlt0, -⟩ := urec_byte_at hL hsat hL24 hrj honj (c := 0) (by norm_num)
  have hu : u0 = recStart (Ub inst pub) rj + 9 := by
    apply Coin.lift _ (by omega) (by omega)
    rw [← hu0, ← hs]; push_cast; rw [ZMod.natCast_zmod_val]
  -- the script's length is the record's
  have htl2 := URec.tl_bytes (urec_sat' hL hsat hL24) (n := 2 ^ Ls 13) hrj honj
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
theorem claim_is_record_at {j : ℕ} {c : Claim} (hc : ClaimAt inst pub (Ls 13) j c) :
    c = recAt (Ub inst pub) ((inst 14).main Coin.J j).val := by
  obtain ⟨rj, hrj, honj, hJ, rfl⟩ := claim_is_record hL hsat hL24 hc
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  rw [hJ, urec_j hL hsat hL24 hrj honj, ZMod.val_natCast_of_lt (by unfold P; omega)]

/-! ### The record index is the input's position in the block -/

variable (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
include he hon hlen hst hf htg

/-- **Input rows before transaction `t`** number the inputs of the non-coinbase transactions before it. -/
theorem ki_count : ∀ t ≤ S.b.txs.length,
    ∑ q ∈ Finset.range ((parts.take t).map List.length).sum, (inst 14).main Coin.KI q = ((insBefore S.b.txs t : ℕ) : F)
  | 0, _ => by simp [insBefore]
  | t + 1, ht => by
    have cs := coin_sat hL hsat hL24
    obtain ⟨tx, htx⟩ : ∃ tx, S.b.txs[t]? = some tx := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hpl, hpe⟩ := part_len hf htx
    have hft := fields_tagged hL hsat hL24 S
    rw [htg] at hft
    have he' : e = (parts.map List.length).sum := by rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
    have hpre1 : ((parts.take (t + 1)).map List.length).sum = ((parts.take t).map List.length).sum +
        (tx.vin.length + tx.vout.length) := by
      rw [List.take_add_one, List.map_append, List.sum_append, ← hpe]
      simp [List.getElem?_eq_getElem hpl, List.getD_eq_getElem _ _ hpl]
    have hle : ((parts.take (t + 1)).map List.length).sum ≤ e := by
      rw [he']
      have := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
      rwa [List.take_length] at this
    rw [hpre1, Finset.sum_range_add, ki_count t (by omega), insBefore_succ _ t tx htx]
    have hrow : ∀ q < tx.vin.length + tx.vout.length,
        (inst 14).main Coin.KI (((parts.take t).map List.length).sum + q) = if q < tx.vin.length ∧ 1 ≤ t then 1 else 0 := by
      intro q hq
      have hj : ((parts.take t).map List.length).sum + q < e := by omega
      have hk := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg hj htx rfl hq).2.1
      split_ifs with hc
      · exact hk.mpr hc
      · rcases Coin.bool_col cs (c := Coin.KI) (r := ((parts.take t).map List.length).sum + q) (by simp)
          (by omega) with h0 | h1
        · exact h0
        · exact absurd (hk.mp h1) hc
    rw [Finset.sum_congr rfl fun q hq => hrow q (Finset.mem_range.mp hq)]
    push_cast
    congr 1
    by_cases ht1 : 1 ≤ t
    · simp only [ht1, and_true, if_true]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      rw [show (Finset.range (tx.vin.length + tx.vout.length)).filter (· < tx.vin.length) = Finset.range tx.vin.length by
        ext x; simp; omega]
      simp
    · simp [ht1]

/-- **The claim of input `k` of transaction `t ≥ 1` is the stream's record `insBefore t + k`**: a
function of the block and the committed undo stream only (D-041, step 4 of utxo.md's plan). -/
theorem claim_at_input {t k : ℕ} {tx : Spec.Block.Tx} (htx : S.b.txs[t]? = some tx) (ht1 : 1 ≤ t)
    (hk : k < tx.vin.length) {c : Claim} (hc : ClaimAt inst pub (Ls 13) (((parts.take t).map List.length).sum + k) c) :
    c = recAt (Ub inst pub) (insBefore S.b.txs t + k) := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  have hft := fields_tagged hL hsat hL24 S
  rw [htg] at hft
  have he' : e = (parts.map List.length).sum := by rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
  have hle : ((parts.take (t + 1)).map List.length).sum ≤ e := by
    rw [he']
    have := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
    rwa [List.take_length] at this
  have hpre1 : ((parts.take (t + 1)).map List.length).sum = ((parts.take t).map List.length).sum +
      (tx.vin.length + tx.vout.length) := by
    rw [List.take_add_one, List.map_append, List.sum_append, ← hpe]
    simp [List.getElem?_eq_getElem hpl, List.getD_eq_getElem _ _ hpl]
  set j := ((parts.take t).map List.length).sum + k with hj
  have hjL : j < 2 ^ Ls 14 := by omega
  rw [claim_is_record_at hL hsat hL24 hc]
  congr 1
  -- J j = KI rows before j = insBefore t + k
  have hJ := Coin.j_spec cs j hjL
  rw [hj, Finset.sum_range_add, ki_count hL hsat hL24 S he hon hlen hst hf htg t
    (by have := (List.getElem?_eq_some_iff.mp htx).1; omega)] at hJ
  have hrow : ∀ q < k, (inst 14).main Coin.KI (((parts.take t).map List.length).sum + q) = 1 := fun q hq =>
    (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (show _ < e by omega) htx rfl (by omega)).2.1.mpr ⟨by omega, ht1⟩
  rw [Finset.sum_congr rfl fun q hq => hrow q (Finset.mem_range.mp hq)] at hJ
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hJ
  rw [hJ]
  have hib : insBefore S.b.txs t + k < P := by
    have := insBefore_le hf t (by have := (List.getElem?_eq_some_iff.mp htx).1; omega)
    obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
    unfold P; omega
  rw [← Nat.cast_add, ZMod.val_natCast_of_lt hib]

end System

end StarkedAir.Block
