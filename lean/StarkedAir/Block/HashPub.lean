/-
**The block hash as public inputs (BLOCK-DATA).** The context component reads the digest `(0, pub 25 … pub 40)`
at row 0. In a satisfied block system that read is the header message's second hash: public inputs 25–40
are the 16-bit limbs of `SHA256d(b.header)`, so a verifier can check the block proof against the header
chain's commitment at the block's height.
-/
import StarkedAir.Block.WMerkleLink

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst outputAt)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 12, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 24)
include hL hsat hL24

/-- A message start with id 0 is the header message. -/
theorem mid_zero_hdr {r0 : ℕ} (h0 : r0 < 2 ^ L) (f0 : (inst 2).main Msg.FIRSTM r0 = 1)
    (hz : (inst 2).main Msg.MID r0 = 0) : (inst 2).main Msg.HDR r0 = 1 := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have h25 : 2 ^ L ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hL24
  norm_num at h25
  rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h0 with h | h
  · exfalso
    rw [Msg.mid_eq ms h0] at hz
    obtain ⟨ρ, hρ, -, ti, -⟩ := msg_tuple_row hL hsat hL24 h0 f0 h
    have hw := Fields.bool_val (Msg.bool_col ms (e := Msg.WTX) (by simp) h0)
    rw [h, sub_zero, one_mul, ← ti, Fields.txi_count fs ρ hρ, hw.1] at hz
    have := Fields.locks_le (M := (inst 1).main) ρ
    rw [show (1 : F) + 2 * ((Fields.locks (inst 1).main ρ : ℕ) : F) + (((inst 2).main Msg.WTX r0).val : F) =
      ((1 + 2 * Fields.locks (inst 1).main ρ + ((inst 2).main Msg.WTX r0).val : ℕ) : F) by push_cast; ring] at hz
    have := natCast_inj_of_lt (Fields.lt_P (by omega)) (by unfold P; norm_num) (hz.trans Nat.cast_zero.symm)
    omega
  · exact h

/-- **The public block hash**: the block parses as `b`, and public inputs 25–40 are the 16-bit limbs of a
SHA-256 state whose bytes are `SHA256d(b.header)` (limb `2w + h` is half `h` of word `w`). -/
theorem hash_pub :
    ∃ b, Spec.Block.parseBlock (Fields.blockBytes (inst 0).main (pub 0).val) = some b ∧
      ∃ S, Spec.Block.stateBytes S = Spec.Block.sha256d b.header ∧
        ∀ j < 16, pub (Ctx.PUB_HASH + j) = ((Sha256.half16 (Spec.Bitcoin.stateWord S (j / 2)) (j % 2) : ℕ) : F) := by
  have ss := hash_sha_sat hL hsat
  have hn0 : 0 < 2 ^ L := by positivity
  have hm : siteMult hashSys inst pub (7, 0, 11) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
    simp [Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.ev_first (M := (inst 7).main) (pub := pub) hn0]
  have hv : siteVals hashSys inst pub (7, 0, 11) = (0 : F) :: (List.range 16).map (fun j => pub (Ctx.PUB_HASH + j)) := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Expr.eval,
      StarkedAir.Sha256.eval_cst]
  rcases digest_any hL hsat hL24 (i := 7) (k := 11) (Or.inr (Or.inr ⟨rfl, Or.inr rfl⟩)) hn0 hm with
    ⟨q, hq, hd, hyq⟩ | hz | ⟨-, -, hn⟩
  rotate_left
  · rw [hv] at hz; simp only [List.cons.injEq] at hz
    have := natCast_inj_of_lt (a := 0) (b := Ctx.ZERO_ID) (by unfold P; norm_num) (by unfold Ctx.ZERO_ID P; norm_num)
      (by simpa using hz.1)
    unfold Ctx.ZERO_ID at this; omega
  · rw [hv] at hn; simp only [List.cons.injEq] at hn
    have := natCast_inj_of_lt (a := 0) (b := Ctx.NONCE_ID) (by unfold P; norm_num) (by unfold Ctx.NONCE_ID P; norm_num)
      (by simpa using hn.1)
    unfold Ctx.NONCE_ID at this; omega
  rw [digest_vals hL hsat hq, hv] at hyq
  simp only [List.cons.injEq] at hyq
  obtain ⟨hmq, hlimbs⟩ := hyq
  have hq1 := Sha.dbl_pos ss hq hd
  obtain ⟨b, hparse, r0, h0, f0, hmid, hhdr, -⟩ :=
    digest_tx hL hsat hL24 hq1 hq hd (by rw [hmq]; simp [Merkle.NB])
  have hh := mid_zero_hdr hL hsat hL24 h0 f0 (by rw [hmid, hmq])
  refine ⟨b, hparse, outputAt (inst 3).main (72 * q), hhdr hh, fun j hj => ?_⟩
  have := congrArg (fun l => l.getD j 0) hlimbs
  simpa [List.getD_eq_getElem?_getD, hj] using this.symm

end System

end StarkedAir.Block
