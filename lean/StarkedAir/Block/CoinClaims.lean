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

end System

end StarkedAir.Block
