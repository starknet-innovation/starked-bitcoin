/-
Soundness of the SHA-256 compression AIR against FIPS 180-4.

Main theorem (`compress_sound`): if a trace satisfies `Sha256.air`, then for
every 72-row block that starts at a multiple of 72 and lies inside the
trace, the words in its finalize rows equal
`Spec.Sha256.compress H M`, where `H` is read from the init rows and `M`
from the first 16 round rows.
-/
import StarkedAir.Gadgets.Sha256
import StarkedAir.Bits

namespace StarkedAir.Sha256

open StarkedAir Spec.Sha256

/-! ## Layer 1: evaluation lemmas -/

section Eval

variable {n : ℕ} {main : ℕ → ℕ → F} {r : ℕ}

theorem cast_ofBits (g : ℕ → Bool) (k : ℕ) :
    ((ofBits g k : ℕ) : F) = ∑ j ∈ Finset.range k, (2 : F) ^ j * ((g j).toNat : F) := by
  induction k with
  | zero => simp [ofBits]
  | succ k ih => simp [ofBits, ih, Finset.sum_range_succ]

theorem eval_sumPow (f : ℕ → Expr) (k : ℕ) :
    (sumPow f k).eval n preCols main r =
      ∑ j ∈ Finset.range k, (2 : F) ^ j * (f j).eval n preCols main r := by
  induction k with
  | zero => simp [sumPow, cst, Expr.eval]
  | succ k ih => simp [sumPow, cst, Expr.eval, ih, Finset.sum_range_succ]

/-- A weighted sum of boolean-valued expressions is the value of those bits. -/
theorem eval_sumPow_bits (f : ℕ → Expr) (g : ℕ → Bool) (k : ℕ)
    (h : ∀ j < k, (f j).eval n preCols main r = ((g j).toNat : F)) :
    (sumPow f k).eval n preCols main r = ((ofBits g k : ℕ) : F) := by
  rw [eval_sumPow, cast_ofBits]
  exact Finset.sum_congr rfl (fun j hj => by rw [h j (Finset.mem_range.mp hj)])

theorem eval_col (i : ℕ) (off : ℤ) :
    (col i off).eval n preCols main r = main i (wrap n r off) := by
  simp [col, Expr.eval]

theorem eval_cst (v : ℕ) : (cst v).eval n preCols main r = (v : F) := by
  simp [cst, Expr.eval]

/-- The boolean held by a column cell (meaningful once booleanity holds). -/
def bit (main : ℕ → ℕ → F) (c r : ℕ) : Bool := decide ((main c r).val = 1)

theorem eq_bit {c r' : ℕ} (h : (main c r').val ≤ 1) : main c r' = ((bit main c r').toNat : F) := by
  rw [← ZMod.natCast_zmod_val (main c r')]
  unfold bit
  congr 1
  rcases (by omega : (main c r').val = 0 ∨ (main c r').val = 1) with h0 | h1
  · simp [h0]
  · simp [h1]

/-! Boolean polynomials. -/

theorem xor2_poly (a b : Bool) :
    ((a.toNat : F) + b.toNat) - 2 * ((a.toNat : F) * b.toNat) = ((a ^^ b).toNat : F) := by
  cases a <;> cases b <;> norm_num

theorem xor3_poly (a b c : Bool) :
    ((a.toNat : F) + b.toNat + c.toNat) -
        2 * ((a.toNat : F) * b.toNat + (b.toNat : F) * c.toNat + (c.toNat : F) * a.toNat) +
      4 * ((a.toNat : F) * b.toNat * c.toNat) = ((a ^^ b ^^ c).toNat : F) := by
  cases a <;> cases b <;> cases c <;> norm_num

theorem ch_poly (a b c : Bool) :
    (a.toNat : F) * b.toNat + c.toNat - (a.toNat : F) * c.toNat =
      (((a && b) ^^ (!a && c)).toNat : F) := by
  cases a <;> cases b <;> cases c <;> norm_num

theorem maj_poly (a b c : Bool) :
    (a.toNat : F) * b.toNat + (b.toNat : F) * c.toNat + (c.toNat : F) * a.toNat -
        2 * ((a.toNat : F) * b.toNat * c.toNat) =
      (((a && b) ^^ (a && c) ^^ (b && c)).toNat : F) := by
  cases a <;> cases b <;> cases c <;> norm_num

section
variable {x y z : Expr} {a b c : Bool}
  (hx : x.eval n preCols main r = (a.toNat : F))
  (hy : y.eval n preCols main r = (b.toNat : F))
  (hz : z.eval n preCols main r = (c.toNat : F))
include hx hy

theorem eval_xor2 : (xor2 x y).eval n preCols main r = ((a ^^ b).toNat : F) := by
  simp only [xor2, Expr.eval, eval_cst, hx, hy]; rw [← xor2_poly]; norm_num

include hz

theorem eval_xor3 : (xor3 x y z).eval n preCols main r = ((a ^^ b ^^ c).toNat : F) := by
  simp only [xor3, Expr.eval, eval_cst, hx, hy, hz]; rw [← xor3_poly]; norm_num

theorem eval_ch : (chE x y z).eval n preCols main r = (((a && b) ^^ (!a && c)).toNat : F) := by
  simp only [chE, Expr.eval, hx, hy, hz]; exact ch_poly a b c

theorem eval_maj :
    (majE x y z).eval n preCols main r = (((a && b) ^^ (a && c) ^^ (b && c)).toNat : F) := by
  simp only [majE, Expr.eval, eval_cst, hx, hy, hz]; rw [← maj_poly]; norm_num
end

/-! Row offsets. -/

theorem wrap_eq {n' r' : ℕ} {off : ℤ} (h0 : 0 ≤ (r' : ℤ) + off) (h1 : (r' : ℤ) + off < n') :
    wrap n' r' off = ((r' : ℤ) + off).toNat := by
  unfold wrap; rw [Int.emod_eq_of_lt h0 h1]

theorem wrap_back {n' r' k : ℕ} (hk : k ≤ r') (hr : r' < n') : wrap n' r' (-(k : ℤ)) = r' - k := by
  rw [wrap_eq (by omega) (by omega)]; omega

end Eval

/-! ## Layer 2: bit-level facts about the spec functions -/

theorem rotr_getLsbD (x : Word) {k i : ℕ} (hk : k < 32) (hi : i < 32) :
    (x.rotateRight k).getLsbD i = x.getLsbD ((i + k) % 32) := by
  rw [BitVec.getLsbD_rotateRight_of_lt hk]
  by_cases h : i < 32 - k
  · simp only [h, decide_true, cond_true]
    rw [Nat.mod_eq_of_lt (by omega : i + k < 32), Nat.add_comm]
  · simp only [h, decide_false, cond_false, decide_true, hi, Bool.true_and]
    congr 1; omega

theorem shr_getLsbD (x : Word) (s i : ℕ) :
    (x >>> s).getLsbD i = (decide (s + i < 32) && x.getLsbD (s + i)) := by
  rw [BitVec.getLsbD_ushiftRight]
  by_cases h : s + i < 32
  · simp [h]
  · simp [h, BitVec.getLsbD_of_ge x (s + i) (by omega)]

/-! ## Layer 3: limbs and words -/

theorem ofBits_lo (y : Word) : ofBits (fun j => y.getLsbD (16 * 0 + j)) 16 = y.toNat % 65536 := by
  have h := toNat_split y
  have b1 := ofBits_lt (fun i => y.getLsbD i) 16
  simp only [Nat.mul_zero, Nat.zero_add]
  norm_num at h b1 ⊢; omega

theorem ofBits_hi (y : Word) : ofBits (fun j => y.getLsbD (16 * 1 + j)) 16 = y.toNat / 65536 := by
  have h := toNat_split y
  have b1 := ofBits_lt (fun i => y.getLsbD i) 16
  simp only [Nat.mul_one]
  norm_num at h b1 ⊢; omega

/-- The value a limb takes, from a word: low half for `half = 0`, high half for `half = 1`. -/
def half16 (y : Word) : ℕ → ℕ
  | 0 => y.toNat % 65536
  | _ => y.toNat / 65536

theorem half16_lt (y : Word) (h : ℕ) : half16 y h < 65536 := by
  have := y.isLt
  cases h <;> simp [half16] <;> omega

section
variable {n : ℕ} {main : ℕ → ℕ → F} {r : ℕ}

/-- A limb of bit-expressions that encode word `y` evaluates to that half of `y`. -/
theorem eval_limbOf (f : ℕ → Expr) (y : Word) {half : ℕ} (hh : half ≤ 1)
    (h : ∀ i < 32, (f i).eval n preCols main r = ((y.getLsbD i).toNat : F)) :
    (limbOf f half).eval n preCols main r = ((half16 y half : ℕ) : F) := by
  unfold limbOf
  rw [eval_sumPow_bits _ (fun j => y.getLsbD (16 * half + j)) 16
    (fun j hj => h _ (by omega))]
  rcases (by omega : half = 0 ∨ half = 1) with rfl | rfl
  · rw [ofBits_lo]; rfl
  · rw [ofBits_hi]; rfl

/-- The word encoded by the 32 bit columns starting at `base`, at row `r`. -/
def word (main : ℕ → ℕ → F) (base r : ℕ) : Word := bv32 (fun i => bit main (base + i) r)

theorem word_getLsbD (base r' : ℕ) {i : ℕ} (hi : i < 32) :
    (word main base r').getLsbD i = bit main (base + i) r' := bv32_getLsbD _ hi

/-- Bit columns, read through an offset that lands on row `r'`. -/
theorem eval_bitcol {base r' : ℕ} {off : ℤ} (hw : wrap n r off = r')
    (hb : ∀ i < 32, (main (base + i) r').val ≤ 1) {i : ℕ} (hi : i < 32) :
    (col (base + i) off).eval n preCols main r = (((word main base r').getLsbD i).toNat : F) := by
  rw [eval_col, hw, word_getLsbD _ _ hi]; exact eq_bit (hb i hi)

theorem eval_limb {base r' : ℕ} {off : ℤ} (hw : wrap n r off = r')
    (hb : ∀ i < 32, (main (base + i) r').val ≤ 1) {half : ℕ} (hh : half ≤ 1) :
    (limb base half off).eval n preCols main r = ((half16 (word main base r') half : ℕ) : F) :=
  eval_limbOf _ _ hh (fun _ hi => eval_bitcol hw hb hi)

/-- A column pinned to a limb expression by `col D − limbOf f half = 0` holds that half. -/
theorem limbcol_val {D : ℕ} (f : ℕ → Expr) (y : Word) {half : ℕ} (hh : half ≤ 1) (hr : r < n)
    (hc : (Expr.sub (col D) (limbOf f half)).eval n preCols main r = 0)
    (h : ∀ i < 32, (f i).eval n preCols main r = ((y.getLsbD i).toNat : F)) :
    (main D r).val = half16 y half := by
  simp only [Expr.eval, eval_col, wrap_zero hr, eval_limbOf f y hh h, sub_eq_zero] at hc
  rw [hc, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans (half16_lt y half) (by norm_num [P]))]

end

/-! ## Layer 4: facts at a row of a satisfying trace -/

theorem Kn_lt (t : ℕ) : Kn.getD t 0 < 2 ^ 32 := by
  have hall : Kn.all (· < 2 ^ 32) = true := by decide
  rw [List.all_eq_true] at hall
  rw [List.getD_eq_getElem?_getD]
  cases h : Kn[t]? with
  | none => simp
  | some v => simpa using hall v (List.mem_of_getElem? h)

theorem K_toNat (t : ℕ) : (Spec.Sha256.K t).toNat = Kn.getD t 0 := by
  rw [Spec.Sha256.K, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Kn_lt t)]

section Row

variable {logSize : ℕ} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize main)
include hsat

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < 2 ^ logSize) :
    c.eval (2 ^ logSize) preCols main r = 0 := hsat r hr c hc

/-- Every bit and carry column is boolean at every row. -/
theorem bool_val {c r : ℕ} (hr : r < 2 ^ logSize) (hc : c < 96 ∨ (108 ≤ c ∧ c < 124)) :
    (main c r).val ≤ 1 := by
  have hm : boolC (col c) ∈ constraints := by
    simp only [constraints, List.mem_append]
    left; left; left; left
    simp only [booleans, List.mem_map, List.mem_filter, List.mem_range, Function.comp]
    refine ⟨c, ⟨?_, ?_⟩, rfl⟩
    · show c < 124; omega
    · have : c < 96 ∨ 108 ≤ c := by omega
      exact decide_eq_true (by simpa only [CA_LO] using this)
  have := sat hsat hm hr
  simp only [boolC, Expr.eval, eval_col, eval_cst, wrap_zero hr, Nat.cast_one] at this
  exact val_le_one_of_bool this

theorem word_bits {base r : ℕ} (hr : r < 2 ^ logSize) (hbase : base + 32 ≤ 96) :
    ∀ i < 32, (main (base + i) r).val ≤ 1 :=
  fun i hi => bool_val hsat hr (Or.inl (by omega))

/-! Preprocessed columns. -/

omit hsat in
theorem eval_pre_periodic {i r : ℕ} (hr : r < 2 ^ logSize) {vals : List ℕ}
    (hi : preCols.getD i (.periodic [0]) = .periodic vals) :
    (pre i).eval (2 ^ logSize) preCols main r = ((vals.getD (r % vals.length) 0 : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]; simp [PreCol.eval]

end Row

/-! ## Layer 5: the bitwise columns -/

section Bitwise

variable {n : ℕ} {main : ℕ → ℕ → F} {r : ℕ}

theorem eval_bigSigmaBit {base r' : ℕ} {off : ℤ} (hw : wrap n r off = r')
    (hb : ∀ i < 32, (main (base + i) r').val ≤ 1) {r1 r2 r3 i : ℕ}
    (h1 : r1 < 32) (h2 : r2 < 32) (h3 : r3 < 32) (hi : i < 32) :
    (bigSigmaBit base off r1 r2 r3 i).eval n preCols main r =
      ((((word main base r').rotateRight r1 ^^^ (word main base r').rotateRight r2 ^^^
        (word main base r').rotateRight r3).getLsbD i).toNat : F) := by
  unfold bigSigmaBit
  rw [eval_xor3 (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num)))
    (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num))) (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num)))]
  simp [BitVec.getLsbD_xor, rotr_getLsbD _ h1 hi, rotr_getLsbD _ h2 hi, rotr_getLsbD _ h3 hi]

theorem eval_smallSigmaBit {base r' : ℕ} {off : ℤ} (hw : wrap n r off = r')
    (hb : ∀ i < 32, (main (base + i) r').val ≤ 1) {r1 r2 sh i : ℕ}
    (h1 : r1 < 32) (h2 : r2 < 32) (hi : i < 32) :
    (smallSigmaBit base off r1 r2 sh i).eval n preCols main r =
      ((((word main base r').rotateRight r1 ^^^ (word main base r').rotateRight r2 ^^^
        (word main base r' >>> sh)).getLsbD i).toNat : F) := by
  unfold smallSigmaBit
  simp only
  split
  · rename_i hs
    have h3 : (col (base + i + sh) off).eval n preCols main r =
        (((word main base r').getLsbD (i + sh)).toNat : F) := by
      rw [Nat.add_assoc]; exact eval_bitcol hw hb hs
    rw [eval_xor3 (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num)))
      (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num))) h3]
    simp [BitVec.getLsbD_xor, rotr_getLsbD _ h1 hi, rotr_getLsbD _ h2 hi, shr_getLsbD,
      show sh + i < 32 by omega, Nat.add_comm sh i]
  · rename_i hs
    rw [eval_xor2 (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num)))
      (eval_bitcol hw hb (Nat.mod_lt _ (by norm_num)))]
    simp only [BitVec.getLsbD_xor, rotr_getLsbD _ h1 hi, rotr_getLsbD _ h2 hi, shr_getLsbD,
      show ¬ sh + i < 32 by omega, decide_false, Bool.false_and, Bool.xor_false]

theorem eval_chBit {base r1 r2 r3 : ℕ} {o1 o2 o3 : ℤ} (hw1 : wrap n r o1 = r1)
    (hw2 : wrap n r o2 = r2) (hw3 : wrap n r o3 = r3)
    (hb1 : ∀ i < 32, (main (base + i) r1).val ≤ 1) (hb2 : ∀ i < 32, (main (base + i) r2).val ≤ 1)
    (hb3 : ∀ i < 32, (main (base + i) r3).val ≤ 1) {i : ℕ} (hi : i < 32) :
    (chE (col (base + i) o1) (col (base + i) o2) (col (base + i) o3)).eval n preCols main r =
      (((ch (word main base r1) (word main base r2) (word main base r3)).getLsbD i).toNat : F) := by
  rw [eval_ch (eval_bitcol hw1 hb1 hi) (eval_bitcol hw2 hb2 hi) (eval_bitcol hw3 hb3 hi)]
  simp [ch, BitVec.getLsbD_xor, BitVec.getLsbD_and, BitVec.getLsbD_not, hi]

theorem eval_majBit {base r1 r2 r3 : ℕ} {o1 o2 o3 : ℤ} (hw1 : wrap n r o1 = r1)
    (hw2 : wrap n r o2 = r2) (hw3 : wrap n r o3 = r3)
    (hb1 : ∀ i < 32, (main (base + i) r1).val ≤ 1) (hb2 : ∀ i < 32, (main (base + i) r2).val ≤ 1)
    (hb3 : ∀ i < 32, (main (base + i) r3).val ≤ 1) {i : ℕ} (hi : i < 32) :
    (majE (col (base + i) o1) (col (base + i) o2) (col (base + i) o3)).eval n preCols main r =
      (((maj (word main base r1) (word main base r2) (word main base r3)).getLsbD i).toNat : F) := by
  rw [eval_maj (eval_bitcol hw1 hb1 hi) (eval_bitcol hw2 hb2 hi) (eval_bitcol hw3 hb3 hi)]
  simp [maj, BitVec.getLsbD_xor, BitVec.getLsbD_and]

end Bitwise

section Subsets
theorem sub_S0 : defineLimbs S0 (bigSigmaBit A (-1) 2 13 22) ⊆ bitwise :=
  fun x hx => by simp only [bitwise, List.mem_append]; tauto
theorem sub_S1 : defineLimbs S1 (bigSigmaBit E (-1) 6 11 25) ⊆ bitwise :=
  fun x hx => by simp only [bitwise, List.mem_append]; tauto
theorem sub_CH : defineLimbs CH (fun i => chE (col (E + i) (-1)) (col (E + i) (-2)) (col (E + i) (-3)))
    ⊆ bitwise := fun x hx => by simp only [bitwise, List.mem_append]; tauto
theorem sub_MJ : defineLimbs MJ (fun i => majE (col (A + i) (-1)) (col (A + i) (-2)) (col (A + i) (-3)))
    ⊆ bitwise := fun x hx => by simp only [bitwise, List.mem_append]; tauto
theorem sub_s0 : defineLimbs s0 (smallSigmaBit W (-15) 7 18 3) ⊆ bitwise :=
  fun x hx => by simp only [bitwise, List.mem_append]; tauto
theorem sub_s1 : defineLimbs s1 (smallSigmaBit W (-2) 17 19 10) ⊆ bitwise :=
  fun x hx => by simp only [bitwise, List.mem_append]; tauto
end Subsets

section Columns

variable {logSize : ℕ} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize main)
include hsat

theorem bitwise_sat {c : Expr} (hc : c ∈ bitwise) {r : ℕ} (hr : r < 2 ^ logSize) :
    c.eval (2 ^ logSize) preCols main r = 0 :=
  sat hsat (by simp only [constraints, List.mem_append]; left; left; left; right; exact hc) hr

/-- A limb pair `defineLimbs D f` whose bit expressions encode word `y`: columns `D`, `D+1`
hold the low and high halves of `y`. -/
theorem limbcols {D : ℕ} {f : ℕ → Expr} (hsub : defineLimbs D f ⊆ bitwise) (y : Word) {r : ℕ}
    (hr : r < 2 ^ logSize)
    (h : ∀ i < 32, (f i).eval (2 ^ logSize) preCols main r = ((y.getLsbD i).toNat : F)) :
    (main D r).val = half16 y 0 ∧ (main (D + 1) r).val = half16 y 1 :=
  ⟨limbcol_val f y (by norm_num) hr (bitwise_sat hsat (hsub List.mem_cons_self) hr) h,
   limbcol_val f y (by norm_num) hr
     (bitwise_sat hsat (hsub (List.mem_cons_of_mem _ List.mem_cons_self)) hr) h⟩

section
variable {r : ℕ} (hr : r < 2 ^ logSize)
include hr

private theorem bits_back {k base : ℕ} (hk : k ≤ r) (hbase : base + 32 ≤ 96) :
    ∀ i < 32, (main (base + i) (r - k)).val ≤ 1 := word_bits hsat (by omega) hbase

omit hsat in
private theorem wrap_k {k : ℕ} (hk : k ≤ r) : wrap (2 ^ logSize) r (-(k : ℤ)) = r - k :=
  wrap_back hk hr

theorem S0_vals (h3 : 3 ≤ r) : (main S0 r).val = half16 (bsig0 (word main A (r - 1))) 0 ∧
    (main (S0 + 1) r).val = half16 (bsig0 (word main A (r - 1))) 1 :=
  limbcols hsat sub_S0 _ hr
    (fun i hi => eval_bigSigmaBit (wrap_k hr (k := 1) (by omega))
      (bits_back hsat hr (by omega) (by decide)) (by norm_num) (by norm_num) (by norm_num) hi)

theorem S1_vals (h3 : 3 ≤ r) : (main S1 r).val = half16 (bsig1 (word main E (r - 1))) 0 ∧
    (main (S1 + 1) r).val = half16 (bsig1 (word main E (r - 1))) 1 :=
  limbcols hsat sub_S1 _ hr
    (fun i hi => eval_bigSigmaBit (wrap_k hr (k := 1) (by omega))
      (bits_back hsat hr (by omega) (by decide)) (by norm_num) (by norm_num) (by norm_num) hi)

theorem CH_vals (h3 : 3 ≤ r) :
    (main CH r).val = half16 (ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3))) 0 ∧
    (main (CH + 1) r).val =
      half16 (ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3))) 1 :=
  limbcols hsat sub_CH _ hr
    (fun i hi => eval_chBit (wrap_k hr (k := 1) (by omega))
      (wrap_k hr (k := 2) (by omega)) (wrap_k hr (k := 3) (by omega))
      (bits_back hsat hr (by omega) (by decide)) (bits_back hsat hr (by omega) (by decide))
      (bits_back hsat hr (by omega) (by decide)) hi)

theorem MJ_vals (h3 : 3 ≤ r) :
    (main MJ r).val = half16 (maj (word main A (r - 1)) (word main A (r - 2)) (word main A (r - 3))) 0 ∧
    (main (MJ + 1) r).val =
      half16 (maj (word main A (r - 1)) (word main A (r - 2)) (word main A (r - 3))) 1 :=
  limbcols hsat sub_MJ _ hr
    (fun i hi => eval_majBit (wrap_k hr (k := 1) (by omega))
      (wrap_k hr (k := 2) (by omega)) (wrap_k hr (k := 3) (by omega))
      (bits_back hsat hr (by omega) (by decide)) (bits_back hsat hr (by omega) (by decide))
      (bits_back hsat hr (by omega) (by decide)) hi)

theorem s0_vals (h15 : 15 ≤ r) : (main s0 r).val = half16 (ssig0 (word main W (r - 15))) 0 ∧
    (main (s0 + 1) r).val = half16 (ssig0 (word main W (r - 15))) 1 :=
  limbcols hsat sub_s0 _ hr
    (fun i hi => eval_smallSigmaBit (wrap_k hr (k := 15) h15)
      (bits_back hsat hr h15 (by decide)) (by norm_num) (by norm_num) hi)

theorem s1_vals (h15 : 15 ≤ r) : (main s1 r).val = half16 (ssig1 (word main W (r - 2))) 0 ∧
    (main (s1 + 1) r).val = half16 (ssig1 (word main W (r - 2))) 1 :=
  limbcols hsat sub_s1 _ hr
    (fun i hi => eval_smallSigmaBit (wrap_k hr (k := 2) (by omega))
      (bits_back hsat hr (by omega) (by decide)) (by norm_num) (by norm_num) hi)
end

end Columns

/-! ## Layer 6: additions -/

section Adds

variable {n : ℕ} {main : ℕ → ℕ → F} {r : ℕ}

theorem eval_foldl_add (terms : List Expr) (init : Expr) :
    (terms.foldl .add init).eval n preCols main r =
      init.eval n preCols main r + (terms.map (·.eval n preCols main r)).sum := by
  induction terms generalizing init with
  | nil => simp
  | cons t ts ih => simp [List.foldl, ih, Expr.eval, add_assoc]

/-- A gated sum constraint, with the gate on and every term a small natural, is an
equation over ℕ. -/
theorem addC_nat {sel result carry : Expr} {terms : List Expr} {ts : List ℕ} {R C : ℕ}
    (h0 : (addC sel terms result carry).eval n preCols main r = 0)
    (hsel : sel.eval n preCols main r = 1)
    (hts : terms.map (·.eval n preCols main r) = ts.map (Nat.cast : ℕ → F))
    (hR : result.eval n preCols main r = (R : F)) (hC : carry.eval n preCols main r = (C : F))
    (hb1 : ts.sum < P) (hb2 : R + 65536 * C < P) : ts.sum = R + 65536 * C := by
  have hs : (ts.map (Nat.cast : ℕ → F)).sum = ((ts.sum : ℕ) : F) := (Nat.cast_list_sum ts).symm
  simp only [addC, Expr.eval, eval_foldl_add, eval_cst, hsel, hts, hR, hC, one_mul, hs,
    Nat.cast_zero, zero_add] at h0
  apply natCast_inj_of_lt hb1 hb2
  rw [Nat.cast_add, Nat.cast_mul]
  have : ((65536 : ℕ) : F) = 65536 := by norm_num
  rw [this]
  linear_combination h0

theorem eval_bitsOf {base k : ℕ} (hr : r < n) (hb : ∀ j < k, (main (base + j) r).val ≤ 1) :
    (bitsOf base k).eval n preCols main r = ((ofBits (fun j => bit main (base + j) r) k : ℕ) : F) :=
  eval_sumPow_bits _ _ k (fun j hj => by rw [eval_col, wrap_zero hr]; exact eq_bit (hb j hj))

theorem eval_col0_val {i : ℕ} (hr : r < n) :
    (col i).eval n preCols main r = (((main i r).val : ℕ) : F) := by
  rw [eval_col, wrap_zero hr, ZMod.natCast_zmod_val]

theorem half16_split (y : Word) : y.toNat = half16 y 0 + 65536 * half16 y 1 := by
  simp only [half16]; omega

end Adds

section Pre

variable {n : ℕ} {main : ℕ → ℕ → F} {r : ℕ}

private theorem periodic_at (f : ℕ → ℕ) (hr : r < n) {i : ℕ}
    (hi : preCols.getD i (.periodic [0]) = .periodic ((List.range PERIOD).map f)) :
    (pre i).eval n preCols main r = ((f (r % 72) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 72 < 72 := Nat.mod_lt _ (by norm_num)
  simp [PreCol.eval, PERIOD, List.getD_eq_getElem?_getD, this]

theorem pre_round (hr : r < n) :
    (pre IS_ROUND).eval n preCols main r =
      (((if 4 ≤ r % 72 ∧ r % 72 < 68 then 1 else 0 : ℕ)) : F) := by
  rw [periodic_at (fun p => if 4 ≤ p ∧ p < 68 then 1 else 0) hr (by simp [preCols, IS_ROUND])]

theorem pre_sched (hr : r < n) :
    (pre IS_SCHED).eval n preCols main r =
      (((if 20 ≤ r % 72 ∧ r % 72 < 68 then 1 else 0 : ℕ)) : F) := by
  rw [periodic_at (fun p => if 20 ≤ p ∧ p < 68 then 1 else 0) hr (by simp [preCols, IS_SCHED])]

theorem pre_final (hr : r < n) :
    (pre IS_FINAL).eval n preCols main r = (((if 68 ≤ r % 72 then 1 else 0 : ℕ)) : F) := by
  rw [periodic_at (fun p => if 68 ≤ p then 1 else 0) hr (by simp [preCols, IS_FINAL])]

theorem pre_klo (hr : r < n) (h4 : 4 ≤ r % 72) (h68 : r % 72 < 68) :
    (pre K_LO).eval n preCols main r = ((half16 (Spec.Sha256.K (r % 72 - 4)) 0 : ℕ) : F) := by
  rw [periodic_at (fun p => if 4 ≤ p ∧ p < 68 then Kn.getD (p - 4) 0 % 2 ^ 16 else 0) hr
    (by simp [preCols, K_LO, K])]
  simp [h4, h68, half16, K_toNat]

theorem pre_khi (hr : r < n) (h4 : 4 ≤ r % 72) (h68 : r % 72 < 68) :
    (pre (K_LO + 1)).eval n preCols main r = ((half16 (Spec.Sha256.K (r % 72 - 4)) 1 : ℕ) : F) := by
  rw [periodic_at (fun p => if 4 ≤ p ∧ p < 68 then Kn.getD (p - 4) 0 / 2 ^ 16 else 0) hr
    (by simp [preCols, K_LO, K])]
  simp [h4, h68, half16, K_toNat]

end Pre

/-! ## Layer 7: one round -/

section Round

variable {logSize : ℕ} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize main)
include hsat

theorem roundAdds_sat {r : ℕ} (hr : r < 2 ^ logSize) : ∀ c ∈ roundAdds, c.eval (2 ^ logSize) preCols main r = 0 :=
  fun _ hc => sat hsat (by simp only [constraints, List.mem_append]; left; left; right; exact hc) hr

theorem limbs_back {r k base : ℕ} (hr : r < 2 ^ logSize) (hk : k ≤ r) (hbase : base + 32 ≤ 96)
    {h : ℕ} (hh : h ≤ 1) :
    (limb base h (-(k : ℤ))).eval (2 ^ logSize) preCols main r = ((half16 (word main base (r - k)) h : ℕ) : F) :=
  eval_limb (wrap_back hk hr) (word_bits hsat (by omega) hbase) hh

theorem carry_val {r base k : ℕ} (hr : r < 2 ^ logSize) (hbase : 108 ≤ base) (hk : base + k ≤ 124) :
    (bitsOf base k).eval (2 ^ logSize) preCols main r = ((ofBits (fun j => bit main (base + j) r) k : ℕ) : F) :=
  eval_bitsOf hr (fun j hj => bool_val hsat hr (Or.inr ⟨by omega, by omega⟩))

/-- **Round step.** At a round row, `a` and `e` are FIPS round `t = r mod 72 − 4` applied to
the previous rows. -/
theorem round_step {r : ℕ} (hr : r < 2 ^ logSize) (h4 : 4 ≤ r % 72) (h68 : r % 72 < 68) :
    word main A r =
        (word main E (r - 4) + bsig1 (word main E (r - 1)) +
          ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3)) +
          Spec.Sha256.K (r % 72 - 4) + word main W r) +
        (bsig0 (word main A (r - 1)) +
          maj (word main A (r - 1)) (word main A (r - 2)) (word main A (r - 3))) ∧
    word main E r =
      word main A (r - 4) +
        (word main E (r - 4) + bsig1 (word main E (r - 1)) +
          ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3)) +
          Spec.Sha256.K (r % 72 - 4) + word main W r) := by
  have hr4 : 4 ≤ r := le_trans h4 (Nat.mod_le _ _)
  have h3 : 3 ≤ r := by omega
  -- Column facts.
  obtain ⟨S0l, S0h⟩ := S0_vals hsat hr h3
  obtain ⟨S1l, S1h⟩ := S1_vals hsat hr h3
  obtain ⟨CHl, CHh⟩ := CH_vals hsat hr h3
  obtain ⟨MJl, MJh⟩ := MJ_vals hsat hr h3
  have hsel : (pre IS_ROUND).eval (2 ^ logSize) preCols main r = 1 := by
    rw [pre_round hr]; simp [h4, h68]
  have E4 := fun h (hh : h ≤ 1) => limbs_back hsat hr (k := 4) hr4 (base := E) (by decide) hh
  have A4 := fun h (hh : h ≤ 1) => limbs_back hsat hr (k := 4) hr4 (base := A) (by decide) hh
  have W0 := fun h (hh : h ≤ 1) => limbs_back hsat hr (k := 0) (Nat.zero_le _) (base := W) (by decide) hh
  have A0 := fun h (hh : h ≤ 1) => limbs_back hsat hr (k := 0) (Nat.zero_le _) (base := A) (by decide) hh
  have E0 := fun h (hh : h ≤ 1) => limbs_back hsat hr (k := 0) (Nat.zero_le _) (base := E) (by decide) hh
  simp only [Nat.cast_ofNat, Nat.cast_zero, neg_zero, Nat.sub_zero] at E4 A4 W0 A0 E0
  have cAl := carry_val hsat hr (base := CA_LO) (k := 3) (by decide) (by decide)
  have cAh := carry_val hsat hr (base := CA_HI) (k := 3) (by decide) (by decide)
  have cEl := carry_val hsat hr (base := CE_LO) (k := 3) (by decide) (by decide)
  have cEh := carry_val hsat hr (base := CE_HI) (k := 3) (by decide) (by decide)
  have kl := pre_klo (main := main) hr h4 h68
  have kh := pre_khi (main := main) hr h4 h68
  have c0 := fun i => eval_col0_val (n := 2 ^ logSize) (main := main) (i := i) hr
  -- The four addition constraints.
  have hall := roundAdds_sat hsat hr
  simp only [roundAdds, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true] at hall
  obtain ⟨ea0, ea1, ee0, ee1⟩ := hall
  have hP : (2 : ℕ) ^ 20 < P := by norm_num [P]
  have bc := fun base k => ofBits_lt (fun j => bit main (base + j) r) k
  have hb := fun y h => half16_lt y h
  set Yr := word main E (r - 4)
  have na0 := addC_nat ea0 hsel
    (ts := [half16 Yr 0, half16 (bsig1 (word main E (r - 1))) 0,
      half16 (ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3))) 0,
      half16 (Spec.Sha256.K (r % 72 - 4)) 0, half16 (word main W r) 0,
      half16 (bsig0 (word main A (r - 1))) 0,
      half16 (maj (word main A (r - 1)) (word main A (r - 2)) (word main A (r - 3))) 0])
    (by simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, Nat.add_zero,
          E4 0 (by norm_num), W0 0 (by norm_num), kl, c0, S1l, CHl, S0l, MJl])
    (A0 0 (by norm_num)) cAl
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb Yr 0, hb (bsig1 (word main E (r - 1))) 0,
      hb (ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3))) 0,
      hb (Spec.Sha256.K (r % 72 - 4)) 0, hb (word main W r) 0, hb (bsig0 (word main A (r - 1))) 0,
      hb (maj (word main A (r - 1)) (word main A (r - 2)) (word main A (r - 3))) 0])
    (by linarith [hb (word main A r) 0, bc CA_LO 3])
  set Ch := ch (word main E (r - 1)) (word main E (r - 2)) (word main E (r - 3))
  set Mj := maj (word main A (r - 1)) (word main A (r - 2)) (word main A (r - 3))
  set B1 := bsig1 (word main E (r - 1))
  set B0 := bsig0 (word main A (r - 1))
  set Kt := Spec.Sha256.K (r % 72 - 4)
  set Wr := word main W r
  set Xr := word main A (r - 4)
  set cAL := ofBits (fun j => bit main (CA_LO + j) r) 3
  set cEL := ofBits (fun j => bit main (CE_LO + j) r) 3
  have na1 := addC_nat ea1 hsel
    (ts := [half16 Yr 1, half16 B1 1, half16 Ch 1, half16 Kt 1, half16 Wr 1, half16 B0 1,
      half16 Mj 1, cAL])
    (by simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          E4 1 (by norm_num), W0 1 (by norm_num), kh, c0, S1h, CHh, S0h, MJh, cAl])
    (A0 1 (by norm_num)) cAh
    (by simp only [List.sum_cons, List.sum_nil]
        linarith [hb Yr 1, hb B1 1, hb Ch 1, hb Kt 1, hb Wr 1, hb B0 1, hb Mj 1, bc CA_LO 3])
    (by linarith [hb (word main A r) 1, bc CA_HI 3])
  have ne0 := addC_nat ee0 hsel
    (ts := [half16 Xr 0, half16 Yr 0, half16 B1 0, half16 Ch 0, half16 Kt 0, half16 Wr 0])
    (by simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, Nat.add_zero,
          A4 0 (by norm_num), E4 0 (by norm_num), W0 0 (by norm_num), kl, c0, S1l, CHl])
    (E0 0 (by norm_num)) cEl
    (by simp only [List.sum_cons, List.sum_nil]
        linarith [hb Xr 0, hb Yr 0, hb B1 0, hb Ch 0, hb Kt 0, hb Wr 0])
    (by linarith [hb (word main E r) 0, bc CE_LO 3])
  have ne1 := addC_nat ee1 hsel
    (ts := [half16 Xr 1, half16 Yr 1, half16 B1 1, half16 Ch 1, half16 Kt 1, half16 Wr 1, cEL])
    (by simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil,
          A4 1 (by norm_num), E4 1 (by norm_num), W0 1 (by norm_num), kh, c0, S1h, CHh, cEl])
    (E0 1 (by norm_num)) cEh
    (by simp only [List.sum_cons, List.sum_nil]
        linarith [hb Xr 1, hb Yr 1, hb B1 1, hb Ch 1, hb Kt 1, hb Wr 1, bc CE_LO 3])
    (by linarith [hb (word main E r) 1, bc CE_HI 3])
  simp only [List.sum_cons, List.sum_nil] at na0 na1 ne0 ne1
  have sp := fun y => half16_split y
  have lt := fun y h => half16_lt y h
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add]
    rw [sp (word main A r), sp Yr, sp B1, sp Ch, sp Kt, sp Wr, sp B0, sp Mj]
    have := lt (word main A r) 0; have := lt (word main A r) 1
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add]
    rw [sp (word main E r), sp Xr, sp Yr, sp B1, sp Ch, sp Kt, sp Wr]
    have := lt (word main E r) 0; have := lt (word main E r) 1
    omega

end Round

end StarkedAir.Sha256
