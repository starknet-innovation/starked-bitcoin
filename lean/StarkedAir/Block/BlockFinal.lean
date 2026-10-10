/-
**Finality and BIP34 (M3a.5b–c), system level.** Every transaction is final for the height and the
cutoff (the previous MTP once CSV is active, else the block's time), whose 16-bit limbs the context
yields; and with BIP34 active the coinbase's scriptSig starts with the height push.
-/
import StarkedAir.Block.BlockSums
import StarkedAir.Spec.PushHeight

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)

theorem Fields.same_const {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
    (hsat : ∀ r < n, ∀ c ∈ Fields.constraints, c.eval n Fields.preCols pub M r = 0) {X : ℕ}
    (hX : Fields.same X ∈ Fields.chkC) : ∀ r < n, M X r = M X 0 := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
    have := Fields.sat hsat (Fields.mem_chk hX) hr
    simp only [Fields.same, Expr.eval, Fields.ev_notFirst (pub := pub) (M := M) hr, one_mul, Fields.ev_k hr,
      Fields.ev_kp hr, sub_eq_zero] at this
    rw [this, ih (by omega)]

theorem le4_slice {R : Spec.Block.Bytes} {a : ℕ} (h : a + 4 ≤ R.length) :
    Spec.Block.le (slice R a 4) = (R.getD a 0).toNat + 256 * (R.getD (a + 1) 0).toNat +
      65536 * (R.getD (a + 2) 0).toNat + 16777216 * (R.getD (a + 3) 0).toNat := by
  have e : slice R a 4 = [R.getD a 0, R.getD (a + 1) 0, R.getD (a + 2) 0, R.getD (a + 3) 0] := by
    apply List.ext_getElem
    · rw [Fields.slice_length h]; rfl
    · intro i h1 h2
      have hi : i < 4 := by simpa using h2
      rw [← List.getD_eq_getElem _ (0 : UInt8) h1, Fields.slice_getD hi h]
      interval_cases i <;> rfl
  rw [e]; simp [Spec.Block.le]; ring

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **Finality.** -/
theorem final_ok (hL8 : 8 ≤ L) (S : Setup inst pub L) {c : Spec.Block.Ctx} (hh : c.height < 2 ^ 23)
    (hmtp : c.prevMtp < 2 ^ 32) (p2 : pub 2 = (c.height : F)) (p3 : pub 3 = ((c.prevMtp % 65536 : ℕ) : F))
    (p5 : pub 5 = if Spec.Block.CSV_HEIGHT ≤ c.height then 1 else 0) (p7 : pub 7 = ((c.prevMtp / 65536 : ℕ) : F)) :
    ∀ t ∈ S.b.txs, Spec.Block.isFinal t c.height (Spec.Block.cutoffOf c S.b) = true := by
  intro t ht
  have fs := hash_fields_sat' hL hsat
  have cs := hash_ctx_sat' hL hsat
  have h24 := rows_le hL hsat hL24
  norm_num at h24
  have h256 := ctx_sat8 hL hsat hL24 hL8
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨j, ρ, -, -, hρ, hl, -, hat⟩ := tx_at hL hsat hL24 S ht
  have hρn : ρ < 2 ^ L := by have := S.hmn; omega
  -- the cutoff's limbs on the lock-time row are the context's
  have hclo : (inst 1).main Fields.CLO ρ = (inst 7).main Ctx.CLO 0 := by
    rw [Fields.same_const fs (X := Fields.CLO) (by simp [Fields.chkC, Fields.finalC]) ρ hρn, (cutoff_link hL hsat hL24).1]
  have hchi : (inst 1).main Fields.CHI ρ = (inst 7).main Ctx.CHI 0 := by
    rw [Fields.same_const fs (X := Fields.CHI) (by simp [Fields.chkC, Fields.finalC]) ρ hρn, (cutoff_link hL hsat hL24).2]
  obtain ⟨-, -, -, hmlo, hmhi, hcl, hch⟩ := Ctx.glob_eqs cs (by positivity)
  obtain ⟨hseg, ha0⟩ := ctx_seg_a0 hL hsat hL24 S
  obtain ⟨h72, htl, hth⟩ := Ctx.time_fact cs h256 (by omega) (Rb inst pub) (ctx_read hL hsat hL24) (ctx_ra hL hsat hL24)
    hseg ha0
  have hco : (inst 1).main Fields.CLO ρ = ((Spec.Block.cutoffOf c S.b % 65536 : ℕ) : F) ∧
      (inst 1).main Fields.CHI ρ = ((Spec.Block.cutoffOf c S.b / 65536 : ℕ) : F) ∧ Spec.Block.cutoffOf c S.b < 2 ^ 32 := by
    rw [hclo, hchi, hcl, hch, p5]
    unfold Spec.Block.cutoffOf
    by_cases hcsv : Spec.Block.CSV_HEIGHT ≤ c.height
    · rw [if_pos hcsv, if_pos (by simpa using hcsv), hmlo, hmhi, p3, p7]
      exact ⟨by ring, by ring, hmtp⟩
    · rw [if_neg hcsv, if_neg (by simpa using hcsv), htl, hth]
      have ht4 : S.b.time = ((Rb inst pub).getD 68 0).toNat +
          256 * ((Rb inst pub).getD 69 0).toNat + 65536 * ((Rb inst pub).getD 70 0).toNat +
          16777216 * ((Rb inst pub).getD 71 0).toNat := by
        unfold Spec.Block.Blk.time
        rw [S.hhead]
        have e : ((slice (Rb inst pub) 0 80).drop 68).take 4 = slice (Rb inst pub) 68 4 := by
          simp [slice, List.drop_take, List.take_take]
        rw [e, le4_slice (by omega)]
      rw [ht4]
      have b0 := UInt8.toNat_lt ((Rb inst pub).getD 68 0); have b1 := UInt8.toNat_lt ((Rb inst pub).getD 69 0)
      have b2 := UInt8.toNat_lt ((Rb inst pub).getD 70 0); have b3 := UInt8.toNat_lt ((Rb inst pub).getD 71 0)
      set T := ((Rb inst pub).getD 68 0).toNat + 256 * ((Rb inst pub).getD 69 0).toNat +
        65536 * ((Rb inst pub).getD 70 0).toNat + 16777216 * ((Rb inst pub).getD 71 0).toNat
      have e1 : T % 65536 = ((Rb inst pub).getD 68 0).toNat + 256 * ((Rb inst pub).getD 69 0).toNat := by omega
      have e2 : T / 65536 = ((Rb inst pub).getD 70 0).toNat + 256 * ((Rb inst pub).getD 71 0).toNat := by omega
      refine ⟨by rw [e1]; push_cast; ring, by rw [e2]; push_cast; ring, by omega⟩
  exact Fields.tx_final fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (hby_R hL hsat hL24 S)
    (fun r hr j hj => fields_rg_lt hL hsat hL24 hr hj) h25 hat hρ hl p2 hh ⟨hco.1, hco.2.1⟩ hco.2.2

/-- **BIP34.** -/
theorem bip34_ok (hL8 : 8 ≤ L) (S : Setup inst pub L) {c : Spec.Block.Ctx} (hh : c.height < 2 ^ 23)
    (p2 : pub 2 = (c.height : F)) (p4 : pub 4 = if Spec.Block.BIP34_HEIGHT ≤ c.height then 1 else 0) :
    c.height ≥ Spec.Block.BIP34_HEIGHT →
      (Spec.Block.ssOf S.b).take (Spec.Block.pushHeight c.height).length = Spec.Block.pushHeight c.height := by
  intro hb
  obtain ⟨ρ, t, inp, -, -, -, hget, -, -, -, -, -, hv, -, hss, -, hs41, hslo, -, h34⟩ := cb_facts hL hsat hL24 hL8 S
  have h4 : pub 4 = 1 := by rw [p4, if_pos hb]
  obtain ⟨h45, h42, hsum⟩ := h34 h4
  set R := Rb inst pub
  set cb := Ctx.cbase (inst 7).main
  rw [h4, ZMod.val_one] at hslo
  have hcb : Spec.Block.cbOf S.b = t := by
    unfold Spec.Block.cbOf
    match h : S.b.txs, hget with
    | a :: _, hg => simp at hg; simp [hg]
  have hs : Spec.Block.ssOf S.b = slice R (cb + 42) (R.getD (cb + 41) 0).toNat := by
    unfold Spec.Block.ssOf; rw [hcb, hv]; exact hss
  rw [Spec.Block.pushHeight_3 (by unfold Spec.Block.BIP34_HEIGHT at hb; omega) hh, hs]
  -- the height's bytes
  have b3 := UInt8.toNat_lt (R.getD (cb + 43) 0); have b4 := UInt8.toNat_lt (R.getD (cb + 44) 0)
  have b5 := UInt8.toNat_lt (R.getD (cb + 45) 0)
  rw [p2] at hsum
  have hn := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) hsum
  have ht4 : (slice R (cb + 42) (R.getD (cb + 41) 0).toNat).take 4 = slice R (cb + 42) 4 := by
    simp only [slice, List.take_take]; congr 1; omega
  rw [show [(3 : UInt8), UInt8.ofNat c.height, UInt8.ofNat (c.height / 256), UInt8.ofNat (c.height / 65536)].length = 4
    from rfl, ht4]
  apply List.ext_getElem
  · rw [Fields.slice_length (by omega)]; rfl
  · intro i h1 h2
    have hi : i < 4 := by simpa using h2
    rw [← List.getD_eq_getElem _ (0 : UInt8) h1, Fields.slice_getD hi (by omega)]
    apply UInt8.toNat_inj.mp
    interval_cases i
    · simp only [Nat.add_zero, List.getElem_cons_zero]; rw [h42]; rfl
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, UInt8.toNat_ofNat']
      rw [show cb + 42 + 1 = cb + 43 by ring]; omega
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, UInt8.toNat_ofNat']
      rw [show cb + 42 + 2 = cb + 44 by ring]; omega
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero, UInt8.toNat_ofNat']
      rw [show cb + 42 + 3 = cb + 45 by ring]; omega

end System

end StarkedAir.Block
