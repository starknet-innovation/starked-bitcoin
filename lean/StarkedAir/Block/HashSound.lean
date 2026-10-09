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

end StarkedAir.Block
