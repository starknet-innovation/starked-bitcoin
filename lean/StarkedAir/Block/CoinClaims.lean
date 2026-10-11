/-
**The coin component's amounts, per transaction (M3b, layer 5).** The circuit's per-row amounts are
Core's: an output row's limbs `VL`, `VH` are its output's value (`out_amount`), and an input row's are
its claim's amount, the first bytes of the claimed `serTxOut` (`in_amount`). Summed over a
transaction's rows (`in_nat`, `out_nat`, `tend_nat`), they give `ClaimsOK`'s amount conditions.
-/
import StarkedAir.Block.CoinEpochSound
import StarkedAir.Block.ValueSound

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **An output row's amount is its output's value.** -/
theorem out_amount (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {j t q : ℕ} {tx : Spec.Block.Tx} {o : Spec.Block.TxOut} (hj : j < e) (hko : (inst 14).main Coin.KO j = 1)
    (htx : S.b.txs[t]? = some tx) (hjq : j = ((parts.take t).map List.length).sum + q)
    (hq : q < tx.vin.length + tx.vout.length) (ho : tx.vout[q - tx.vin.length]? = some o) :
    ((inst 14).main Coin.VL j).val < 2 ^ 24 ∧ ((inst 14).main Coin.VH j).val < 2 ^ 27 ∧
      0 ≤ o.value ∧ o.value < 2 ^ 51 ∧
      ((((inst 14).main Coin.VH j).val * 2 ^ 24 + ((inst 14).main Coin.VL j).val : ℕ) : ℤ) = o.value := by
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ L := by omega
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  obtain ⟨t0, q0, tx0, htx0, -, hjq0, hq0, hko0, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  obtain ⟨-, o0, ho0, hot⟩ := hko0 hko
  rw [ho] at ho0; obtain rfl := Option.some.inj ho0
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : ρ < 2 ^ L := by have := S.hmn; omega
  obtain ⟨hkout, hT⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hj).1 hko
  have hVL : (inst 14).main Coin.VL j = Fields.vlo.eval (2 ^ L) Fields.preCols pub (inst 1).main ρ := by
    have := congrArg (fun l => l.getD 5 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  have hVH : (inst 14).main Coin.VH j = Fields.vhi.eval (2 ^ L) Fields.preCols pub (inst 1).main ρ := by
    have := congrArg (fun l => l.getD 6 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  obtain ⟨hv51, hlo, hhi, hvsum⟩ := Fields.out_value fs (Rb inst pub) (hby_R hL hsat hL24 S)
    (fun r hr j hj => fields_rg_lt hL hsat hL24 hr hj) (by omega) hρn hkout
  have htok : Fields.tokOf (inst 1).main (Rb inst pub) ρ = .out (Fields.slice (Rb inst pub) ((inst 1).main Fields.START ρ).val 8)
      (Fields.slice (Rb inst pub) (((inst 1).main Fields.START ρ).val + 8 + Fields.prefOf (inst 1).main ρ)
        ((inst 1).main Fields.VAL ρ).val) := by
    have kat := Fields.kinds_at fs hρn (a := Fields.K_OUT) (by decide) hkout
    unfold Fields.tokOf
    rw [if_neg (by rw [kat Fields.K_BLK (by decide)]; simp [Fields.K_BLK, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_TXH (by decide)]; simp [Fields.K_TXH, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_IN (by decide)]; simp [Fields.K_IN, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_NOUT (by decide)]; simp [Fields.K_NOUT, Fields.K_OUT]), if_pos hkout]
  rw [htok] at hot
  obtain ⟨-, hval, -⟩ := hot
  rw [Fields.signed64_of_lt (by omega)] at hval
  rw [hVL, hVH]
  refine ⟨hlo, hhi, by rw [hval]; positivity, by rw [hval]; exact_mod_cast hv51, ?_⟩
  rw [hval, hvsum]; push_cast; ring

omit hL hsat hL24 in
/-- The first 8 bytes' little-endian value, byte by byte. -/
theorem le_take8 {s : Spec.Block.Bytes} (hs : 8 ≤ s.length) :
    Spec.Block.le (s.take 8) = ∑ i ∈ Finset.range 8, (s.getD i 0).toNat * 256 ^ i := by
  rw [← Fields.le_range_map 8 (fun i => s.getD i 0)]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

omit hL hsat hL24 in
/-- An amount within `MAX_MONEY` has its top byte zero and its seventh byte below 8. -/
theorem amount_bytes {b : ℕ → ℕ} (hb : ∀ i, b i < 256)
    (hv : ∑ i ∈ Finset.range 8, b i * 256 ^ i ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO) : b 7 = 0 ∧ b 6 < 8 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fields.MAXHI, Fields.MAXLO] at hv
  have := hb 0; have := hb 1; have := hb 2; have := hb 3; have := hb 4; have := hb 5; have := hb 6; have := hb 7
  constructor <;> omega

/-- **An input row's amount is its claim's.** For input row `j` with claim `c` (its undo record), the
amount limbs are the claim's first seven `serTxOut` bytes; with the claimed amount (the first 8 bytes)
within `MAX_MONEY`, they are in range and sum to it. -/
theorem in_amount {j : ℕ} (hj : j < 2 ^ L) {c : Claim} (hc : ClaimAt inst pub L j c) (h8 : 8 ≤ c.ser.length)
    (hmax : Spec.Block.le (c.ser.take 8) ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO) :
    ((inst 14).main Coin.VL j).val < 2 ^ 24 ∧ ((inst 14).main Coin.VH j).val < 2 ^ 27 ∧
      ((inst 14).main Coin.VH j).val * 2 ^ 24 + ((inst 14).main Coin.VL j).val = Spec.Block.le (c.ser.take 8) := by
  obtain ⟨hki, rj, hrj, honj, hJ, u0, hu0, -, hu0l, hser, -, -⟩ := hc
  obtain ⟨rj', hrj', hon', hJ', -, -, hvl, hvh, -⟩ := coin_urec hL hsat hL24 hj hki
  have hrr : rj' = rj := urec_j_inj hL hsat hL24 hrj' hrj hon' honj (by rw [← hJ', hJ])
  rw [hrr] at hvl hvh
  have hU := undo_len hL hsat hL24
  have hPv : (pub 8).val < P := ZMod.val_lt _
  -- the amount bytes
  have hb : ∀ i < 8, ((inst 13).main (URec.V i) rj).val = (c.ser.getD i 0).toNat := by
    intro i hi
    obtain ⟨u, hu, hpu, hbu⟩ := urec_bytes hL hsat hL24 hrj honj (c := 7 + i) (by omega)
    have hcol : URec.ucol (7 + i) = URec.V i := by simp [URec.ucol]; omega
    rw [hcol] at hbu
    have hue : u = u0 + i := by
      apply Coin.lift _ (lt_of_lt_of_le hu (le_of_lt hPv)) (by omega)
      push_cast; rw [← hpu, show ((7 + i : ℕ) : F) = 7 + (i : F) by push_cast; ring, ← add_assoc, hu0]
    have hgi : c.ser.getD i 0 = (Ub inst pub).getD (u0 + i) 0 := by
      conv_lhs => rw [hser]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    rw [hbu, hue, hgi]
  rw [le_take8 h8] at hmax ⊢
  have hb256 : ∀ i, (c.ser.getD i 0).toNat < 256 := fun i => UInt8.toNat_lt _
  obtain ⟨h7, h6⟩ := amount_bytes hb256 hmax
  have hVF : ∀ i < 8, (inst 13).main (URec.V i) rj = (((c.ser.getD i 0).toNat : ℕ) : F) := by
    intro i hi; rw [← Coin.cast_val ((inst 13).main (URec.V i) rj), hb i hi]
  have hlo : (inst 14).main Coin.VL j = (((c.ser.getD 0 0).toNat + 256 * (c.ser.getD 1 0).toNat +
      65536 * (c.ser.getD 2 0).toNat : ℕ) : F) := by
    rw [hvl, hVF 0 (by norm_num), hVF 1 (by norm_num), hVF 2 (by norm_num)]; push_cast; ring
  have hhi : (inst 14).main Coin.VH j = (((c.ser.getD 3 0).toNat + 256 * (c.ser.getD 4 0).toNat +
      65536 * (c.ser.getD 5 0).toNat + 16777216 * (c.ser.getD 6 0).toNat : ℕ) : F) := by
    rw [hvh, hVF 3 (by norm_num), hVF 4 (by norm_num), hVF 5 (by norm_num), hVF 6 (by norm_num)]; push_cast; ring
  have b0 := hb256 0; have b1 := hb256 1; have b2 := hb256 2; have b3 := hb256 3; have b4 := hb256 4
  have b5 := hb256 5
  rw [hlo, hhi, ZMod.val_natCast_of_lt (lt_of_lt_of_le (show _ < 2 ^ 24 by omega) (by unfold P; norm_num)),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (show _ < 2 ^ 27 by omega) (by unfold P; norm_num))]
  refine ⟨by omega, by omega, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h7]; ring

end System

end StarkedAir.Block
