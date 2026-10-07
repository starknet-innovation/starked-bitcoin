/-
Soundness of the header chain's proof-of-work constraints (`HeaderChain.powCs`):
in any satisfying trace, every header meets Bitcoin Core's `CheckProofOfWork` for its own
`nBits` on mainnet (`Spec.Bitcoin.powOk`).
-/
import StarkedAir.Gadgets.HeaderChainSound
import StarkedAir.Gadgets.Retarget

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-! ## Generic lemmas -/

section Generic
variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ}

theorem eval_foldl_list (l : List ℕ) (f : ℕ → Expr) (init : Expr) :
    (l.foldl (fun acc i => .add acc (f i)) init).eval n pc pub main r =
      init.eval n pc pub main r + (l.map (fun i => (f i).eval n pc pub main r)).sum := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih => simp [List.foldl, ih, Expr.eval, add_assoc]

theorem list_range_sum (f : ℕ → F) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, ih, Finset.sum_range_succ]

theorem list_range_sum_nat (f : ℕ → ℕ) (k : ℕ) :
    ((List.range k).map f).sum = ∑ i ∈ Finset.range k, f i := by
  induction k with
  | zero => simp
  | succ k ih => simp [List.range_succ, ih, Finset.sum_range_succ]

end Generic

/-- Bits summing to one: there is exactly one set bit. -/
theorem onehot_of_sum {g : ℕ → Bool} {k : ℕ} (h : ∑ s ∈ Finset.range k, (g s).toNat = 1) :
    ∃ s0 < k, g s0 = true ∧ ∀ s < k, s ≠ s0 → g s = false := by
  induction k with
  | zero => simp at h
  | succ k ih =>
    rw [Finset.sum_range_succ] at h
    cases hk : g k
    · simp only [hk, Bool.toNat_false, add_zero] at h
      obtain ⟨s0, hs0, hg, hu⟩ := ih h
      exact ⟨s0, by omega, hg, fun s hs hne => by
        rcases (by omega : s < k ∨ s = k) with hl | rfl
        · exact hu s hl hne
        · exact hk⟩
    · simp only [hk, Bool.toNat_true] at h
      have h0 : ∑ s ∈ Finset.range k, (g s).toNat = 0 := by omega
      refine ⟨k, by omega, hk, fun s hs hne => ?_⟩
      have := (Finset.sum_eq_zero_iff.mp h0) s (Finset.mem_range.mpr (by omega))
      cases hgs : g s <;> simp_all

theorem sum_onehot {g : ℕ → Bool} {k s0 : ℕ} (hs0 : s0 < k) (hg : g s0 = true)
    (hu : ∀ s < k, s ≠ s0 → g s = false) (x : ℕ → F) :
    ∑ s ∈ Finset.range k, ((g s).toNat : F) * x s = x s0 := by
  rw [Finset.sum_eq_single s0 (fun s hs hne => by rw [hu s (Finset.mem_range.mp hs) hne]; simp)
    (fun h => absurd (Finset.mem_range.mpr hs0) h), hg]
  simp

/-- `L` bits starting at `m` are `y / 2^m mod 2^L`. -/
theorem ofBits_window (y : Word) (m L : ℕ) :
    ofBits (fun k => y.getLsbD (m + k)) L = y.toNat / 2 ^ m % 2 ^ L := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [testBit_ofBits, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : i < L
  · simp [hi, BitVec.getLsbD, Nat.add_comm]
  · simp [hi]

/-- Eight bits starting at `m` are the byte `y / 2^m mod 256`. -/
theorem ofBits_byte (y : Word) (m : ℕ) :
    ofBits (fun k => y.getLsbD (m + k)) 8 = y.toNat / 2 ^ m % 256 := ofBits_window y m 8

/-- `ofBits` splits at any point. -/
theorem ofBits_add (g : ℕ → Bool) (a b : ℕ) :
    ofBits g (a + b) = ofBits g a + 2 ^ a * ofBits (fun i => g (a + i)) b := by
  induction b with
  | zero => simp [ofBits]
  | succ b ih =>
    rw [show a + (b + 1) = (a + b) + 1 by omega]
    show ofBits g (a + b) + 2 ^ (a + b) * (g (a + b)).toNat =
      ofBits g a + 2 ^ a * (ofBits (fun i => g (a + i)) b + 2 ^ b * (g (a + b)).toNat)
    rw [ih, pow_add]; ring

/-- A little-endian byte string with nothing above position `s+2`, compared with
`mant · 256^s`. -/
theorem le_target (b : ℕ → ℕ) (hb : ∀ i, b i < 256) {s mant : ℕ} (hs : s + 3 ≤ 32)
    (hhigh : ∀ i, s + 3 ≤ i → i < 32 → b i = 0)
    (hcmp : (b s + 256 * b (s + 1) + 65536 * b (s + 2) < mant) ∨
      (b s + 256 * b (s + 1) + 65536 * b (s + 2) = mant ∧ ∀ i < s, b i = 0)) :
    ∑ i ∈ Finset.range 32, b i * 256 ^ i ≤ mant * 256 ^ s := by
  have split : ∑ i ∈ Finset.range 32, b i * 256 ^ i =
      ∑ i ∈ Finset.range s, b i * 256 ^ i + 256 ^ s * (b s + 256 * b (s + 1) + 65536 * b (s + 2)) := by
    rw [show (32 : ℕ) = s + (3 + (29 - s)) by omega, Finset.sum_range_add, Finset.sum_range_add]
    have hz : ∑ i ∈ Finset.range (29 - s), b (s + (3 + i)) * 256 ^ (s + (3 + i)) = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hhigh _ (by omega) (by simp at hi; omega)]; simp)
    rw [hz]
    simp [Finset.sum_range_succ, pow_add, pow_succ]
    ring
  have low_lt : ∀ k, ∑ i ∈ Finset.range k, b i * 256 ^ i < 256 ^ k := by
    intro k; induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, pow_succ]
      have := hb k
      nlinarith [pow_pos (show (0 : ℕ) < 256 by norm_num) k]
  rw [split]
  rcases hcmp with hlt | ⟨heq, hlow⟩
  · have := low_lt s
    calc _ ≤ 256 ^ s + 256 ^ s * (b s + 256 * b (s + 1) + 65536 * b (s + 2)) := by omega
      _ = 256 ^ s * (b s + 256 * b (s + 1) + 65536 * b (s + 2) + 1) := by ring
      _ ≤ 256 ^ s * mant := Nat.mul_le_mul_left _ hlt
      _ = mant * 256 ^ s := by ring
  · have : ∑ i ∈ Finset.range s, b i * 256 ^ i = 0 :=
      Finset.sum_eq_zero (fun i hi => by rw [hlow i (Finset.mem_range.mp hi)]; simp)
    rw [this, heq]; ring_nf; omega

/-- The 23 mantissa bits, as laid out by `mantBit`, are `nWord`. -/
theorem mant_ofBits (y : Word) :
    ofBits (fun t => if t < 8 then y.getLsbD (24 + t) else if t < 16 then y.getLsbD (8 + t)
      else y.getLsbD (t - 8)) 23 =
      y.toNat / 2 ^ 24 % 256 + 256 * (y.toNat / 2 ^ 16 % 256) + 65536 * (y.toNat / 2 ^ 8 % 128) := by
  rw [show (23 : ℕ) = 8 + 15 from rfl, ofBits_add, show (15 : ℕ) = 8 + 7 from rfl, ofBits_add]
  have e0 : ofBits (fun t => if t < 8 then y.getLsbD (24 + t) else if t < 16 then y.getLsbD (8 + t)
      else y.getLsbD (t - 8)) 8 = ofBits (fun k => y.getLsbD (24 + k)) 8 :=
    ofBits_congr (fun i hi => by simp [hi])
  have e1 : ofBits (fun i => (fun t => if t < 8 then y.getLsbD (24 + t) else if t < 16 then
      y.getLsbD (8 + t) else y.getLsbD (t - 8)) (8 + i)) 8 = ofBits (fun k => y.getLsbD (16 + k)) 8 :=
    ofBits_congr (fun i hi => by
      simp only [show ¬ (8 + i < 8) by omega, show 8 + i < 16 by omega, if_false, if_true]
      congr 1; omega)
  have e2 : ofBits (fun i => (fun i => (fun t => if t < 8 then y.getLsbD (24 + t) else if t < 16 then
      y.getLsbD (8 + t) else y.getLsbD (t - 8)) (8 + i)) (8 + i)) 7 = ofBits (fun k => y.getLsbD (8 + k)) 7 :=
    ofBits_congr (fun i hi => by
      simp only [show ¬ (8 + (8 + i) < 8) by omega, show ¬ (8 + (8 + i) < 16) by omega, if_false]
      congr 1; omega)
  rw [e0, e1, e2, ofBits_byte, ofBits_byte, ofBits_window]
  norm_num; ring

/-! ## Trace facts at a header's proof-of-work row -/

section Trace

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
include hsat

theorem chainSat_of : ChainSat (2 ^ logSize) pub main :=
  fun r hr c hc => hsat r hr c (by show c ∈ constraints; simp only [constraints, List.mem_append]; tauto)

theorem pow_sat {r : ℕ} (hr : r < 2 ^ logSize) :
    ∀ c ∈ powCs, c.eval (2 ^ logSize) preCols pub main r = 0 :=
  fun c hc => hsat r hr c (by show c ∈ constraints; simp only [constraints, List.mem_append]; tauto)

variable {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hj

omit hsat in
theorem hr216 : 256 * j + 216 < 2 ^ logSize := by omega

theorem eval_hashBit {i k : ℕ} (hi : i < 32) (hk : k < 8) :
    (hashBit i k).eval (2 ^ logSize) preCols pub main (256 * j + 216) =
      (((stateWord (hashAt main j) (i / 4)).getLsbD (8 * (3 - i % 4) + k)).toNat : F) := by
  have hr := hr216 hj
  have hcs := chainSat_of hsat
  have hb : 8 * (3 - i % 4) + k < 32 := by omega
  rw [hashAt, outputAt, stAt_word main _ (by omega : i / 4 < 8)]
  unfold hashBit
  by_cases hw : i / 4 < 4
  · simp only [hw, if_true]
    have := eval_bitcol (pc := preCols) (pub := pub) (base := A)
      (wrap_back (k := 1 + i / 4) (by omega) hr) (bits hcs (by omega) (by decide)) hb
    rwa [show 256 * j + 216 - (1 + i / 4) = 256 * j + 144 + 71 - i / 4 by omega] at this
  · simp only [hw, if_false]
    have := eval_bitcol (pc := preCols) (pub := pub) (base := E)
      (wrap_back (k := 1 + (i / 4 - 4)) (by omega) hr) (bits hcs (by omega) (by decide)) hb
    rwa [show 256 * j + 216 - (1 + (i / 4 - 4)) = 256 * j + 144 + 71 - (i / 4 - 4) by omega] at this

theorem eval_hashByte {i : ℕ} (hi : i < 32) :
    (hashByteE i).eval (2 ^ logSize) preCols pub main (256 * j + 216) =
      ((hashByte (hashAt main j) i : ℕ) : F) := by
  unfold hashByteE
  rw [eval_sumPow_bits _ (fun k => (stateWord (hashAt main j) (i / 4)).getLsbD (8 * (3 - i % 4) + k)) 8
    (fun k hk => eval_hashBit hsat hj hi hk), ofBits_byte]
  rfl

theorem eval_nbBit {k : ℕ} (hk : k < 32) :
    (nbBit k).eval (2 ^ logSize) preCols pub main (256 * j + 216) =
      ((((headerWord main j 18).getLsbD k).toNat : F)) := by
  have hr := hr216 hj
  have hw : wrap (2 ^ logSize) (256 * j + 216) (-138) = 256 * j + 76 + (18 - 16) := by
    have := wrap_back (n' := 2 ^ logSize) (k := 138) (by omega) hr
    simp only [Nat.cast_ofNat] at this
    rw [this]; omega
  unfold nbBit
  rw [eval_bitcol hw (bits (chainSat_of hsat) (by omega) (by decide)) hk]
  simp only [headerWord, show ¬ (18 < 16) by norm_num, if_false]

omit hsat hj in
theorem eval_mul' {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ} (a b : Expr) :
    (Expr.mul a b).eval n pc pub main r = a.eval n pc pub main r * b.eval n pc pub main r := rfl
omit hsat hj in
theorem eval_sub' {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ} (a b : Expr) :
    (Expr.sub a b).eval n pc pub main r = a.eval n pc pub main r - b.eval n pc pub main r := rfl
omit hsat hj in
theorem eval_add' {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ} (a b : Expr) :
    (Expr.add a b).eval n pc pub main r = a.eval n pc pub main r + b.eval n pc pub main r := rfl

/-- `nWord` as a natural number. -/
def mantNat (y : Word) : ℕ :=
  y.toNat / 2 ^ 24 % 256 + 256 * (y.toNat / 2 ^ 16 % 256) + 65536 * (y.toNat / 2 ^ 8 % 128)

theorem eval_expE : expE.eval (2 ^ logSize) preCols pub main (256 * j + 216) =
    (((headerWord main j 18).toNat % 256 : ℕ) : F) := by
  unfold expE
  rw [eval_sumPow_bits _ (fun k => (headerWord main j 18).getLsbD k) 8
    (fun k hk => eval_nbBit hsat hj (by omega))]
  have := ofBits_window (headerWord main j 18) 0 8
  simp only [Nat.zero_add, pow_zero, Nat.div_one] at this
  rw [this]; rfl

theorem eval_mantE : mantE.eval (2 ^ logSize) preCols pub main (256 * j + 216) =
    ((mantNat (headerWord main j 18) : ℕ) : F) := by
  unfold mantE
  rw [eval_sumPow_bits _ (fun t => if t < 8 then (headerWord main j 18).getLsbD (24 + t) else if t < 16 then
      (headerWord main j 18).getLsbD (8 + t) else (headerWord main j 18).getLsbD (t - 8)) 23
    (fun t ht => by
      unfold mantBit
      split_ifs <;> exact eval_nbBit hsat hj (by omega)), mant_ofBits]
  rfl

theorem eval_midE {s : ℕ} (hs : s ≤ 29) : (midE s).eval (2 ^ logSize) preCols pub main (256 * j + 216) =
    ((hashByte (hashAt main j) s + 256 * hashByte (hashAt main j) (s + 1) +
      65536 * hashByte (hashAt main j) (s + 2) : ℕ) : F) := by
  unfold midE
  rw [eval_add', eval_add', eval_mul', eval_mul', eval_cst, eval_cst, eval_hashByte hsat hj (by omega),
    eval_hashByte hsat hj (by omega), eval_hashByte hsat hj (by omega)]
  push_cast; ring

theorem eval_byteList (l : List ℕ) (hl : ∀ i ∈ l, i < 32) :
    (l.map (fun i => (hashByteE i).eval (2 ^ logSize) preCols pub main (256 * j + 216))).sum =
      (((l.map (hashByte (hashAt main j))).sum : ℕ) : F) := by
  rw [Nat.cast_list_sum, List.map_map]
  congr 1
  exact List.map_congr_left (fun i hi => eval_hashByte hsat hj (hl i hi))

theorem eval_suffixE (s : ℕ) : (suffixE s).eval (2 ^ logSize) preCols pub main (256 * j + 216) =
    (((((List.range 32).filter (s ≤ ·)).map (hashByte (hashAt main j))).sum : ℕ) : F) := by
  unfold suffixE
  rw [eval_foldl_list, eval_cst, Nat.cast_zero, zero_add,
    eval_byteList hsat hj _ (fun i hi => by simp at hi; omega)]

theorem eval_prefixE {s : ℕ} (hs : s ≤ 32) : (prefixE s).eval (2 ^ logSize) preCols pub main (256 * j + 216) =
    ((((List.range s).map (hashByte (hashAt main j))).sum : ℕ) : F) := by
  unfold prefixE
  rw [eval_foldl_list, eval_cst, Nat.cast_zero, zero_add,
    eval_byteList hsat hj _ (fun i hi => by simp at hi; omega)]

end Trace

/-- Spec bridge: the facts the PoW constraints establish imply `CheckProofOfWork`. -/
theorem powOk_intro (H : State) (hw : ℕ → Word) {s0 mant : ℕ}
    (hexp : (hw 18).toNat % 256 = s0 + 3)
    (hmant : mant = (hw 18).toNat / 2 ^ 24 % 256 + 256 * ((hw 18).toNat / 2 ^ 16 % 256) +
      65536 * ((hw 18).toNat / 2 ^ 8 % 128))
    (hsign : (hw 18).toNat / 2 ^ 8 % 256 / 128 = 0) (hm1 : 1 ≤ mant) (hs26 : s0 ≤ 26)
    (hlim : s0 = 26 → mant < 65536) (hle : hashNat H ≤ mant * 256 ^ s0) :
    powOk H (nBitsOf hw) := by
  set w := (hw 18).toNat
  set b0 := w / 2 ^ 24 % 256
  set b1 := w / 2 ^ 16 % 256
  set b2 := w / 2 ^ 8 % 256
  set b3 := w % 256
  have hb0 : b0 < 256 := Nat.mod_lt _ (by norm_num)
  have hb1 : b1 < 256 := Nat.mod_lt _ (by norm_num)
  have hb2 : b2 < 128 := by have := Nat.mod_lt (w / 2 ^ 8) (show 0 < 256 by norm_num); omega
  have hb2' : w / 2 ^ 8 % 128 = b2 := by
    have : w / 2 ^ 8 % 128 = w / 2 ^ 8 % 256 % 128 := by omega
    rw [this, Nat.mod_eq_of_lt hb2]
  rw [hb2'] at hmant
  have hn : nBitsOf hw = mant + 2 ^ 24 * (s0 + 3) := by
    have : nBitsOf hw = b0 + 256 * b1 + 65536 * b2 + 2 ^ 24 * b3 := rfl
    rw [this, hmant, ← hexp]
  have hmlt : mant < 2 ^ 23 := by omega
  have hsize : nBitsOf hw / 2 ^ 24 = s0 + 3 := by rw [hn]; omega
  have hword : nBitsOf hw % 2 ^ 23 = mant := by rw [hn]; omega
  have hneg : nBitsOf hw / 2 ^ 23 % 2 = 0 := by rw [hn]; omega
  have htarget : (if s0 + 3 ≤ 3 then mant / 256 ^ (3 - (s0 + 3)) else mant * 256 ^ (s0 + 3 - 3)) =
      mant * 256 ^ s0 := by
    by_cases h3 : s0 + 3 ≤ 3
    · rw [if_pos h3, show s0 = 0 by omega]; simp
    · rw [if_neg h3, show s0 + 3 - 3 = s0 by omega]
  have hpos : mant * 256 ^ s0 ≠ 0 := Nat.mul_ne_zero (by omega) (by positivity)
  refine ⟨mant * 256 ^ s0, ?_, ?_, hle⟩
  · unfold compactTarget
    simp only [hsize, hword, hneg]
    rw [htarget, if_neg]
    intro hc
    rcases hc with ⟨_, h⟩ | ⟨_, h⟩ | h
    · omega
    · omega
    · exact hpos h
  · unfold powLimit
    rcases (by omega : s0 ≤ 25 ∨ s0 = 26) with h | h
    · calc mant * 256 ^ s0 ≤ (2 ^ 23 - 1) * 256 ^ 25 :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by norm_num) h)
        _ ≤ 2 ^ 224 - 1 := by norm_num
    · subst h
      have := hlim rfl
      calc mant * 256 ^ 26 ≤ 65535 * 256 ^ 26 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ 2 ^ 224 - 1 := by norm_num

/-! ## Main theorem -/

section Main

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
include hsat

omit hsat in
theorem lt_P_of {a : ℕ} (h : a < 2 ^ 30) : a < P := lt_trans h (by norm_num [P])

/-- Proof of work, plus the row-216 exponent one-hot and the `powLimit` bounds (used by the
retarget soundness proof). -/
theorem header_pow_ex {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) :
    powOk (hashAt main j) (nBitsOf (headerWord main j)) ∧
    ∃ s0 < 27, bit main (A + s0) (256 * j + 216) = true ∧
      (∀ s < 27, s ≠ s0 → bit main (A + s) (256 * j + 216) = false) ∧
      (headerWord main j 18).toNat % 256 = s0 + 3 ∧ (s0 = 26 → mantNat (headerWord main j 18) < 65536) ∧
      1 ≤ mantNat (headerWord main j 18) ∧ (headerWord main j 18).toNat / 2 ^ 8 % 256 < 128 := by
  set n := 2 ^ logSize
  set r := 256 * j + 216
  have hr : r < n := hr216 hj
  have hr1 : r + 1 < n := by omega
  have hcs := chainSat_of hsat
  set y := headerWord main j 18
  set H := hashAt main j
  have bA := bits hcs hr (base := A) (by decide)
  have bE := bits hcs hr (base := E) (by decide)
  have bW := bits hcs hr (base := W) (by decide)
  have bA1 := bits hcs hr1 (base := A) (by decide)
  -- Column values as casts of bits.
  have colv : ∀ base, base + 32 ≤ 96 → ∀ i < 32, (col (base + i)).eval n preCols pub main r =
      ((bit main (base + i) r).toNat : F) := fun base hb i hi => by
    rw [eval_col, wrap_zero hr]; exact eq_bit (bits hcs hr hb i hi)
  have hsel : (pre POW).eval n preCols pub main r = 1 := by
    rw [eval_oneRow (show preCols.getD POW (.periodic [0]) = oneRow 216 from rfl) hr,
      show r % 256 = 216 by omega]; simp
  -- The ten constraints.
  have hall := pow_sat hsat hr
  simp only [powCs, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true,
    and_true] at hall
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10⟩ := hall
  -- Selections over the one-hot exponent.
  have sel_eval : ∀ f : ℕ → Expr, (selectE f).eval n preCols pub main r =
      ∑ s ∈ Finset.range 27, ((bit main (A + s) r).toNat : F) * (f s).eval n preCols pub main r := by
    intro f
    unfold selectE
    rw [eval_foldl_list _ (fun s => .mul (ohE s) (f s)), eval_cst, Nat.cast_zero, zero_add,
      list_range_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    rw [eval_mul']
    unfold ohE
    rw [colv A (by decide) s (by simp at hs; omega)]
  -- (1) exactly one exponent bit.
  rw [eval_mul', hsel, one_mul, eval_sub', sel_eval, eval_cst] at c1
  simp only [eval_cst, Nat.cast_one, mul_one] at c1
  have hone : ∑ s ∈ Finset.range 27, (bit main (A + s) r).toNat = 1 := by
    have hle : ∑ s ∈ Finset.range 27, (bit main (A + s) r).toNat ≤ 27 := by
      calc _ ≤ ∑ s ∈ Finset.range 27, 1 := Finset.sum_le_sum (fun s _ => Bool.toNat_le _)
        _ = 27 := by simp
    apply natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P])
    push_cast; exact sub_eq_zero.mp c1
  obtain ⟨s0, hs0, hg, hu⟩ := onehot_of_sum hone
  have pick : ∀ f : ℕ → Expr, (selectE f).eval n preCols pub main r = (f s0).eval n preCols pub main r :=
    fun f => by rw [sel_eval]; exact sum_onehot hs0 hg hu _
  have hbyte : ∀ i, hashByte H i < 256 := fun i => Nat.mod_lt _ (by norm_num)
  -- Scratch values.
  set ltn := (bit main W r).toNat
  have hltb : ltn ≤ 1 := Bool.toNat_le _
  have hlt : ltE.eval n preCols pub main r = (ltn : F) := by
    unfold ltE; rw [eval_col, wrap_zero hr]; exact eq_bit (by simpa using bW 0 (by norm_num))
  set Dn := ofBits (fun k => bit main (E + k) r) 24
  have hD : dE.eval n preCols pub main r = (Dn : F) :=
    eval_sumPow_bits _ _ 24 (fun k hk => colv E (by decide) k (by omega))
  set Ln := ofBits (fun k => bit main (A + k) (r + 1)) 13
  have hL : lE.eval n preCols pub main r = (Ln : F) :=
    eval_sumPow_bits _ _ 13 (fun k hk => by
      rw [eval_col, wrap_one hr1]; exact eq_bit (bA1 k (by omega)))
  set M1 := ofBits (fun k => bit main (W + 1 + k) r) 23
  have hM1 : m1E.eval n preCols pub main r = (M1 : F) :=
    eval_sumPow_bits _ _ 23 (fun k hk => by
      rw [eval_col, wrap_zero hr]
      exact eq_bit (by rw [Nat.add_assoc]; exact bW (1 + k) (by omega)))
  have Dlt := ofBits_lt (fun k => bit main (E + k) r) 24
  have Llt := ofBits_lt (fun k => bit main (A + k) (r + 1)) 13
  have M1lt := ofBits_lt (fun k => bit main (W + 1 + k) r) 23
  have hmlt : mantNat y < 2 ^ 23 := by unfold mantNat; omega
  have hmid : hashByte H s0 + 256 * hashByte H (s0 + 1) + 65536 * hashByte H (s0 + 2) < 2 ^ 24 := by
    have := hbyte s0; have := hbyte (s0 + 1); have := hbyte (s0 + 2); omega
  -- (2) nSize = s0 + 3.
  rw [eval_mul', hsel, one_mul, eval_sub', eval_sub', pick, eval_expE hsat hj, eval_cst, eval_cst] at c2
  have hexp : y.toNat % 256 = s0 + 3 := by
    have : y.toNat % 256 < 256 := Nat.mod_lt _ (by norm_num)
    apply natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega))
    push_cast at c2 ⊢; linear_combination c2
  -- (3) not negative.
  rw [eval_mul', hsel, one_mul, eval_nbBit hsat hj (by norm_num)] at c3
  have h15 : y.getLsbD 15 = false := by
    cases h : y.getLsbD 15
    · rfl
    · rw [h] at c3; simp at c3
  have hsign : y.toNat / 2 ^ 8 % 256 / 128 = 0 := by
    have := h15
    rw [← BitVec.testBit_toNat, Nat.testBit_eq_decide_div_mod_eq] at this
    simp at this; omega
  -- (4) bytes above the mantissa are zero.
  rw [eval_mul', hsel, one_mul, pick, eval_suffixE hsat hj] at c4
  have hhigh : ∀ i, s0 + 3 ≤ i → i < 32 → hashByte H i = 0 := by
    set l := (List.range 32).filter (s0 + 3 ≤ ·)
    have hbound : (l.map (hashByte H)).sum ≤ 32 * 255 := by
      calc (l.map (hashByte H)).sum ≤ (l.map (hashByte H)).length * 255 :=
            List.sum_le_card_nsmul _ _ (fun x hx => by
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; have := hbyte i; omega)
        _ ≤ 32 * 255 := by
            rw [List.length_map]
            exact Nat.mul_le_mul_right _ (le_trans (List.length_filter_le _ _) (by simp))
    have h0 : (l.map (hashByte H)).sum = 0 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by rw [c4]; simp)
    intro i hi1 hi2
    exact List.sum_eq_zero_iff.mp h0 _ (List.mem_map.mpr ⟨i, List.mem_filter.mpr
      ⟨List.mem_range.mpr hi2, by simpa using hi1⟩, rfl⟩)
  -- (5) mant = mid + lt + D.
  rw [eval_mul', hsel, one_mul, eval_sub', eval_sub', eval_sub', eval_mantE hsat hj, pick,
    eval_midE hsat hj (by omega), hlt, hD] at c5
  have hmant_eq : mantNat y = (hashByte H s0 + 256 * hashByte H (s0 + 1) + 65536 * hashByte H (s0 + 2)) +
      ltn + Dn := by
    apply natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega))
    push_cast at c5 ⊢; linear_combination c5
  -- (6) ¬lt → D = 0.
  rw [eval_mul', hsel, one_mul, eval_mul', eval_sub', eval_cst, hlt, hD] at c6
  -- (7) L = Σ_{i<s0} byte_i.
  rw [eval_mul', hsel, one_mul, eval_sub', hL, pick, eval_prefixE hsat hj (by omega)] at c7
  have hLeq : Ln = ((List.range s0).map (hashByte H)).sum := by
    have hb : ((List.range s0).map (hashByte H)).sum ≤ 26 * 255 := by
      calc ((List.range s0).map (hashByte H)).sum ≤ ((List.range s0).map (hashByte H)).length * 255 :=
            List.sum_le_card_nsmul _ _ (fun x hx => by
              obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; have := hbyte i; omega)
        _ ≤ 26 * 255 := by rw [List.length_map, List.length_range]; omega
    exact natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (sub_eq_zero.mp c7)
  -- (8) ¬lt → L = 0.
  rw [eval_mul', hsel, one_mul, eval_mul', eval_sub', eval_cst, hlt, hL] at c8
  -- (9) mant ≥ 1.
  rw [eval_mul', hsel, one_mul, eval_sub', eval_sub', eval_mantE hsat hj, eval_cst, hM1] at c9
  have hm1 : mantNat y = M1 + 1 := by
    apply natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega))
    push_cast at c9 ⊢; linear_combination c9
  -- (10) s0 = 26 → mant < 2^16.
  rw [eval_mul', hsel, one_mul, eval_mul'] at c10
  have hlim : s0 = 26 → mantNat y < 65536 := by
    intro h26
    have hb26 : bit main (A + 26) r = true := h26 ▸ hg
    have hoh : (ohE 26).eval n preCols pub main r = 1 := by
      unfold ohE; rw [colv A (by decide) 26 (by norm_num), hb26]; simp
    have hm2 : (sumPow (fun t => nbBit (8 + t)) 7).eval n preCols pub main r =
        ((y.toNat / 2 ^ 8 % 2 ^ 7 : ℕ) : F) := by
      rw [eval_sumPow_bits _ (fun t => y.getLsbD (8 + t)) 7
        (fun t ht => eval_nbBit hsat hj (by omega)), ofBits_window]
    rw [hoh, one_mul, hm2] at c10
    have : y.toNat / 2 ^ 8 % 2 ^ 7 = 0 :=
      natCast_inj_of_lt (lt_P_of (by have := Nat.mod_lt (y.toNat / 2 ^ 8) (show 0 < 2 ^ 7 by norm_num); omega))
        (by norm_num [P]) (by rw [c10]; simp)
    unfold mantNat; omega
  -- Comparison.
  have hcmp : (hashByte H s0 + 256 * hashByte H (s0 + 1) + 65536 * hashByte H (s0 + 2) < mantNat y) ∨
      (hashByte H s0 + 256 * hashByte H (s0 + 1) + 65536 * hashByte H (s0 + 2) = mantNat y ∧
        ∀ i < s0, hashByte H i = 0) := by
    rcases (by omega : ltn = 1 ∨ ltn = 0) with h1 | h0
    · left; omega
    · right
      rw [h0] at c6 c8
      simp only [Nat.cast_zero, Nat.cast_one, sub_zero, one_mul] at c6 c8
      have hD0 : Dn = 0 := natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by rw [c6]; simp)
      have hL0 : Ln = 0 := natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by rw [c8]; simp)
      refine ⟨by omega, fun i hi => ?_⟩
      rw [hL0] at hLeq
      exact List.sum_eq_zero_iff.mp hLeq.symm _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have hle := le_target (hashByte H) hbyte (s := s0) (by omega) hhigh hcmp
  exact ⟨powOk_intro H (headerWord main j) (mant := mantNat y) hexp rfl hsign (by rw [hm1]; omega) (by omega)
    hlim hle, s0, hs0, hg, hu, hexp, hlim, by omega, by omega⟩

/-- **Proof of work.** Every header of a satisfying trace meets Bitcoin Core's
`CheckProofOfWork` (mainnet) for its own `nBits`. -/
theorem header_pow {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) :
    powOk (hashAt main j) (nBitsOf (headerWord main j)) :=
  (header_pow_ex hsat hj).1

end Main

/-- **Header-chain soundness (v2).** For a trace satisfying the header-chain AIR with
`2^logSize` rows (`logSize ≥ 8`) and public inputs `pub`, with `H = 2^logSize / 256` headers:
every header's hash is SHA256d of its words and meets mainnet `CheckProofOfWork` for its own
`nBits`; consecutive headers are linked; and the chain runs from prev-hash `pubState pub 0`
to tip hash `pubState pub 16`. -/
theorem chain_sound_v2 {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
    (hsat : air.Satisfied logSize pub main) (hlog : 8 ≤ logSize) :
    let H := 2 ^ logSize / 256
    (∀ j < H, sha256d (headerWord main j) = hashAt main j ∧
      powOk (hashAt main j) (nBitsOf (headerWord main j))) ∧
    (∀ j < H, 1 ≤ j → prevHash (headerWord main j) = hashAt main (j - 1)) ∧
    prevHash (headerWord main 0) = pubState pub 0 ∧
    hashAt main (H - 1) = pubState pub 16 := by
  intro H
  obtain ⟨h1, h2, h3, h4⟩ := chain_sound (chainSat_of hsat) hlog
  have hN : 2 ^ logSize = 256 * H := by
    have : 2 ^ logSize = 2 ^ 8 * 2 ^ (logSize - 8) := by rw [← pow_add]; congr 1; omega
    simp only [H, this]; norm_num
  exact ⟨fun j hj => ⟨h1 j hj, header_pow hsat (by omega)⟩, h2, h3, h4⟩

end StarkedAir.HeaderChain
