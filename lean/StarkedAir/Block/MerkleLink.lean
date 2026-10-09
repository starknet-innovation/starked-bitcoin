/-
**Merkle tree soundness, system level (M3a.4).** In a satisfied system (bytes, fields, msg, sha, merkle),
each Merkle node id's second hash outputs SHA256d of its children's digests, and the root matches the
header's Merkle field.
-/
import StarkedAir.Block.HashSound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst limb word messageAt outputAt)

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

end System

end StarkedAir.Block
