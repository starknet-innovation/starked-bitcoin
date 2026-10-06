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

end StarkedAir.Sha256
