/-
Bits ↔ naturals ↔ `BitVec`, as used by bit-decomposed AIR soundness proofs.

`ofBits g k = Σ_{i<k} 2^i · g i` is the value an AIR assembles from boolean
columns. These lemmas tie it to `Nat.testBit` and to `BitVec.toNat`, so that
word-level facts (rotations, xor, addition mod 2^32) can be read off columns.
-/
import Mathlib

namespace StarkedAir

/-- `Σ_{i<k} 2^i · (g i).toNat`. -/
def ofBits (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => ofBits g k + 2 ^ k * (g k).toNat

theorem ofBits_lt (g : ℕ → Bool) (k : ℕ) : ofBits g k < 2 ^ k := by
  induction k with
  | zero => simp [ofBits]
  | succ k ih =>
    simp only [ofBits, pow_succ]
    have : (g k).toNat ≤ 1 := Bool.toNat_le _
    nlinarith [Nat.one_le_two_pow (n := k)]

theorem testBit_ofBits (g : ℕ → Bool) (k i : ℕ) :
    (ofBits g k).testBit i = (decide (i < k) && g i) := by
  induction k with
  | zero => simp [ofBits]
  | succ k ih =>
    rw [ofBits, Nat.add_comm, Nat.testBit_two_pow_mul_add _ (ofBits_lt g k)]
    by_cases hik : i < k
    · simp [hik, ih, Nat.lt_succ_of_lt hik]
    · simp only [hik, if_false]
      by_cases hk : i = k
      · subst hk; cases g i <;> simp
      · obtain ⟨m, hm⟩ : ∃ m, i - k = m + 1 := ⟨i - k - 1, by omega⟩
        have : ¬ i < k + 1 := by omega
        rw [hm]; cases g k <;> simp [this, Nat.testBit_succ]

/-- Splitting at bit 16: `ofBits g (16 + k) = ofBits g 16 + 2^16 · ofBits (g ∘ (16 + ·)) k`. -/
theorem ofBits_split16 (g : ℕ → Bool) (k : ℕ) :
    ofBits g (16 + k) = ofBits g 16 + 2 ^ 16 * ofBits (fun i => g (16 + i)) k := by
  induction k with
  | zero => simp [ofBits]
  | succ k ih =>
    rw [show 16 + (k + 1) = (16 + k) + 1 by omega]
    show ofBits g (16 + k) + 2 ^ (16 + k) * (g (16 + k)).toNat =
      ofBits g 16 + 2 ^ 16 * (ofBits (fun i => g (16 + i)) k + 2 ^ k * (g (16 + k)).toNat)
    rw [ih, pow_add]; ring

theorem ofBits_congr {g h : ℕ → Bool} {k : ℕ} (e : ∀ i < k, g i = h i) : ofBits g k = ofBits h k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ofBits, ih (fun i hi => e i (Nat.lt_succ_of_lt hi)), e k (Nat.lt_succ_self k)]

/-- A 32-bit vector is the value of its bits. -/
theorem toNat_eq_ofBits (y : BitVec 32) : y.toNat = ofBits (fun i => y.getLsbD i) 32 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofBits]
  by_cases hi : i < 32
  · simp [hi, BitVec.getLsbD]
  · simp only [hi, decide_false, Bool.false_and]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The 32-bit vector with bits `g 0, …, g 31`. -/
def bv32 (g : ℕ → Bool) : BitVec 32 := BitVec.ofNat 32 (ofBits g 32)

theorem bv32_toNat (g : ℕ → Bool) : (bv32 g).toNat = ofBits g 32 := by
  rw [bv32, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (ofBits_lt g 32)]

theorem bv32_getLsbD (g : ℕ → Bool) {i : ℕ} (hi : i < 32) : (bv32 g).getLsbD i = g i := by
  simp [BitVec.getLsbD, bv32_toNat, testBit_ofBits, hi]

theorem bv32_ext {x y : BitVec 32} (h : ∀ i < 32, x.getLsbD i = y.getLsbD i) : x = y := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_eq_ofBits x, toNat_eq_ofBits y]
  exact ofBits_congr h

/-- Low and high 16-bit halves of a 32-bit vector, from its bits. -/
theorem toNat_split (y : BitVec 32) :
    y.toNat = ofBits (fun i => y.getLsbD i) 16 + 2 ^ 16 * ofBits (fun i => y.getLsbD (16 + i)) 16 := by
  rw [toNat_eq_ofBits]
  exact ofBits_split16 (fun i => y.getLsbD i) 16

end StarkedAir
