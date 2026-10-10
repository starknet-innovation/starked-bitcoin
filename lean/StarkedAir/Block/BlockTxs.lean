/-
**The block's transactions (M3a.5b–c), system level.** Every transaction has inputs and outputs and
valid output values; transactions after the coinbase spend no null prevout; and transaction 0, read
by the context component, is a coinbase with a 2–100-byte scriptSig (starting with the BIP34 height
push when BIP34 is active).
-/
import StarkedAir.Block.BlockSetup

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- A transaction of the block is at a lock-time row. -/
theorem tx_at (S : Setup inst pub L) {t : Spec.Block.Tx} (ht : t ∈ S.b.txs) :
    ∃ j ρ, j < S.b.txs.length ∧ S.b.txs[j]? = some t ∧ ρ < S.m ∧ (inst 1).main Fields.K_LOCK ρ = 1 ∧
      locks (inst 1).main ρ = j ∧ TxAt (inst 1).main (Rb inst pub) S.m ρ t := by
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem ht
  obtain ⟨ρ, tx, hρ, hl, hlk, hget, hat⟩ := S.hsurj j hj
  rw [List.getElem?_eq_getElem hj, Option.some.injEq] at hget
  exact ⟨j, ρ, hj, List.getElem?_eq_getElem hj, hρ, hl, hlk, hget ▸ hat⟩

/-- **Inputs, outputs and output values.** -/
theorem txs_basic (S : Setup inst pub L) : ∀ t ∈ S.b.txs, t.vin ≠ [] ∧ t.vout ≠ [] ∧
    (∀ o ∈ t.vout, 0 ≤ o.value) ∧ (t.vout.map (·.value)).sum ≤ Spec.Block.MAX_MONEY := by
  intro t ht
  have fs := hash_fields_sat' hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨j, ρ, -, -, hρ, hl, -, hat⟩ := tx_at hL hsat hL24 S ht
  obtain ⟨rh, -, -, -, -, h1, -⟩ := Fields.tx_rows fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hat hρ
  refine ⟨fun h => by rw [h] at h1; simp at h1, Fields.tx_vout_ne fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hat hρ, ?_⟩
  exact Fields.tx_values fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (hby_R hL hsat hL24 S)
    (fun r hr j hj => fields_rg_lt hL hsat hL24 hr hj) h25 hat hρ hl

/-- **Later transactions spend no null prevout.** -/
theorem txs_later (S : Setup inst pub L) {j : ℕ} (hj1 : 1 ≤ j) (hj : j < S.b.txs.length) {t : Spec.Block.Tx}
    (ht : S.b.txs[j]? = some t) : ∀ i ∈ t.vin, i.prevout.isNull = false := by
  have fs := hash_fields_sat' hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨ρ, tx, hρ, hl, hlk, hget, hat⟩ := S.hsurj j hj
  rw [ht, Option.some.injEq] at hget
  subst hget
  exact Fields.tx_prevouts fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (hbq_R hL hsat hL24) h25 hat hρ (by omega)

/-- **Transaction 0 is the context's coinbase**: its lock-time row carries the context's tuple. -/
theorem tx0 (S : Setup inst pub L) : ∃ ρ t, ρ < S.m ∧ (inst 1).main Fields.K_LOCK ρ = 1 ∧ locks (inst 1).main ρ = 0 ∧
    S.b.txs[0]? = some t ∧ TxAt (inst 1).main (Rb inst pub) S.m ρ t ∧
    (inst 1).main Fields.TXA ρ = (inst 7).main Ctx.A0 0 ∧ (inst 1).main Fields.SEG ρ = (inst 7).main Ctx.SEG0 0 ∧
    (inst 1).main Fields.WST ρ = (inst 7).main Ctx.W0 0 ∧ (inst 1).main Fields.START ρ = (inst 7).main Ctx.L0 0 := by
  have fs := hash_fields_sat' hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  obtain ⟨ρ0, hρ0, hl0, hti, hta, hsg, hws, hst⟩ := tx0_link hL hsat hL24
  obtain ⟨ρ, t, hρ, hl, hlk, hget, hat⟩ := S.hsurj 0 S.hN1
  have hP : 2 ^ L < P := by have := hash_rows_lt_P hL24; omega
  obtain rfl : ρ0 = ρ := Fields.lock_unique fs hP hρ0 (by have := S.hmn; omega) hl0 hl (by
    rw [hti, Fields.txi_count fs ρ (by have := S.hmn; omega), hlk]; simp)
  exact ⟨ρ0, t, hρ, hl, hlk, hget, hat, hta, hsg, hws, hst⟩

theorem ctx_sat8 (hL8 : 8 ≤ L) : 256 ≤ 2 ^ L := by
  calc 256 = 2 ^ 8 := by norm_num
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL8

/-- **The coinbase**: transaction 0 has one input, with a null prevout and a 2–100-byte scriptSig
(`cbase = A0 + 2·SEG0` is where the context reads it); with BIP34 its first bytes push the height. -/
theorem cb_facts (hL8 : 8 ≤ L) (S : Setup inst pub L) :
    ∃ ρ t inp, ρ < S.m ∧ (inst 1).main Fields.K_LOCK ρ = 1 ∧ locks (inst 1).main ρ = 0 ∧ S.b.txs[0]? = some t ∧
      TxAt (inst 1).main (Rb inst pub) S.m ρ t ∧
      (inst 1).main Fields.TXA ρ = (inst 7).main Ctx.A0 0 ∧ (inst 1).main Fields.SEG ρ = (inst 7).main Ctx.SEG0 0 ∧
      (inst 1).main Fields.WST ρ = (inst 7).main Ctx.W0 0 ∧ (inst 1).main Fields.START ρ = (inst 7).main Ctx.L0 0 ∧
      t.vin = [inp] ∧ inp.prevout.isNull = true ∧
      inp.scriptSig = slice (Rb inst pub) (Ctx.cbase (inst 7).main + 42)
        ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 41) 0).toNat ∧
      Ctx.cbase (inst 7).main + 42 + ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 41) 0).toNat ≤ (Rb inst pub).length ∧
      Ctx.cbase (inst 7).main + 41 < (Rb inst pub).length ∧
      2 + 2 * (pub 4).val ≤ ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 41) 0).toNat ∧
      ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 41) 0).toNat ≤ 100 ∧
      (pub 4 = 1 → Ctx.cbase (inst 7).main + 45 < (Rb inst pub).length ∧
        ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 42) 0).toNat = 3 ∧
        ((((Rb inst pub).getD (Ctx.cbase (inst 7).main + 43) 0).toNat +
          256 * ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 44) 0).toNat +
          65536 * ((Rb inst pub).getD (Ctx.cbase (inst 7).main + 45) 0).toNat : ℕ) : F) = pub 2) := by
  have fs := hash_fields_sat' hL hsat
  have cs := hash_ctx_sat' hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  have h256 := ctx_sat8 hL hsat hL24 hL8
  obtain ⟨ρ, t, hρ, hl, hlk, hget, hat, hta, hsg, hws, hst⟩ := tx0 hL hsat hL24 S
  obtain ⟨rh, hrh, ht, hnt, -⟩ := Fields.tx_rows fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hat hρ
  obtain ⟨hta', hsg'⟩ := Fields.head_cols fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit S.hnp (hmk_R hL hsat hL24) hat hρ hrh
    ht hnt
  have hseg : (inst 7).main Ctx.SEG0 0 = 0 ∨ (inst 7).main Ctx.SEG0 0 = 1 := by
    rw [← hsg]; exact Fields.seg_bool fs (show ρ < 2 ^ L by have := S.hmn; omega)
  have ha0 : ((inst 7).main Ctx.A0 0).val < 2 ^ 25 := by
    rw [← hta, hta']; exact Fields.start_lt fs (show rh < 2 ^ L by have := S.hmn; omega)
  have fc := fun r (hr : r ≤ 36) =>
    Ctx.cb_read cs h256 (by omega) (Rb inst pub) (ctx_read hL hsat hL24) (ctx_ra hL hsat hL24) hseg ha0 hr
  obtain ⟨hs1, hs2, hs3⟩ := Ctx.slen_fact cs h256 (by omega) (Rb inst pub) (ctx_read hL hsat hL24) (ctx_ra hL hsat hL24)
    hseg ha0
  have hcb : Ctx.cbase (inst 7).main = ((inst 1).main Fields.TXA ρ).val + 2 * ((inst 1).main Fields.SEG ρ).val := by
    rw [hta, hsg]; rfl
  obtain ⟨inp, hv, hnull, hss, hfss⟩ := Fields.cb_tx fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit S.hnp (hmk_R hL hsat hL24) hat hρ
    hcb fc ⟨hs1, hs3⟩
  refine ⟨ρ, t, inp, hρ, hl, hlk, hget, hat, hta, hsg, hws, hst, hv, hnull, hss, hfss, hs1, hs2, hs3, fun h4 => ?_⟩
  exact Ctx.bip34_fact cs h256 (by omega) (Rb inst pub) (ctx_read hL hsat hL24) (ctx_ra hL hsat hL24) hseg ha0 h4

end System

end StarkedAir.Block
