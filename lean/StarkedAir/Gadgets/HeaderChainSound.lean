/-
Soundness of the header-chain AIR v1.

Main theorem (`chain_sound`): in any trace satisfying `HeaderChain.air` with `2^logSize`
rows (logSize ≥ 8), for every header `j < 2^logSize / 256`:
* the hash read from its rows is `sha256d` of the header words read from its rows;
* for `j > 0`, its prev-hash field equals header `j−1`'s hash;
* header 0's prev-hash field equals public inputs 0..15;
* the last header's hash equals public inputs 16..31.
-/
import StarkedAir.Gadgets.HeaderChain
import StarkedAir.Gadgets.Sha256Sound
import StarkedAir.Spec.Bitcoin

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-! ## Spec-level congruence -/

theorem schedule_congr {M M' : ℕ → Word} (h : ∀ t < 16, M t = M' t) (t : ℕ) :
    schedule M t = schedule M' t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rw [schedule.eq_1 M t, schedule.eq_1 M' t]
    by_cases h16 : t < 16
    · simp only [h16, dif_pos]; exact h t h16
    · simp only [h16, dif_neg, not_false_eq_true]
      rw [ih (t - 2) (by omega), ih (t - 7) (by omega), ih (t - 15) (by omega), ih (t - 16) (by omega)]

theorem compress_congr (H : State) {M M' : ℕ → Word} (h : ∀ t < 16, M t = M' t) :
    compress H M = compress H M' := by
  have : ∀ k, rounds H M k = rounds H M' k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => simp only [rounds, ih, schedule_congr h]
  simp only [compress, this]

/-! ## Trace accessors -/

/-- Header word `t` (< 20) of header `j`: compression 0 message rows, then compression 1's. -/
def headerWord (main : ℕ → ℕ → F) (j t : ℕ) : Word :=
  if t < 16 then word main W (256 * j + 4 + t) else word main W (256 * j + 76 + (t - 16))

/-- The hash of header `j`: the output of its third compression. -/
def hashAt (main : ℕ → ℕ → F) (j : ℕ) : State := outputAt main (256 * j + 144)

/-- A word given as two 16-bit public-input limbs. -/
def pubWord (pub : ℕ → F) (i : ℕ) : Word := BitVec.ofNat 32 ((pub i).val + 65536 * (pub (i + 1)).val)

def pubState (pub : ℕ → F) (b : ℕ) : State :=
  ⟨pubWord pub b, pubWord pub (b + 2), pubWord pub (b + 4), pubWord pub (b + 6),
   pubWord pub (b + 8), pubWord pub (b + 10), pubWord pub (b + 12), pubWord pub (b + 14)⟩

theorem stAt_word (main : ℕ → ℕ → F) (R : ℕ) {k : ℕ} (hk : k < 8) :
    stateWord (stAt main R) k = if k < 4 then word main A (R - k) else word main E (R - (k - 4)) := by
  interval_cases k <;> simp [stateWord, stAt]

/-! ## Preprocessed columns -/

section Pre
variable {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ}

theorem eval_p256 {i : ℕ} {f : ℕ → ℕ} (hi : preCols.getD i (.periodic [0]) = periodic256 f) (hr : r < n) :
    (pre i).eval n preCols pub main r = ((f (r % 256) : ℕ) : F) := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [hi]
  have : r % 256 < 256 := Nat.mod_lt _ (by norm_num)
  simp [periodic256, PreCol.eval, PERIOD, List.getD_eq_getElem?_getD, this]

theorem eval_first (hr : r < n) :
    (pre FIRST).eval n preCols pub main r = if r < 256 then 1 else 0 := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [show preCols.getD FIRST (.periodic [0]) = .rowLt 256 from rfl]
  simp [PreCol.eval]

theorem eval_last (hr : r < n) :
    (pre LAST).eval n preCols pub main r = if n ≤ r + 256 then 1 else 0 := by
  simp only [pre, Expr.eval, wrap_zero hr]
  rw [show preCols.getD LAST (.periodic [0]) = .rowGeEnd 256 from rfl]
  simp [PreCol.eval]

theorem eval_oneRow {i row : ℕ} (hi : preCols.getD i (.periodic [0]) = oneRow row) (hr : r < n) :
    (pre i).eval n preCols pub main r = if r % 256 = row then 1 else 0 := by
  rw [eval_p256 hi hr]; split <;> simp

end Pre

/-! ## Limb equalities -/

section Limbs
variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ}

theorem half16_inj {x y : Word} (h0 : half16 x 0 = half16 y 0) (h1 : half16 x 1 = half16 y 1) :
    x = y := by
  apply BitVec.eq_of_toNat_eq
  rw [half16_split x, half16_split y, h0, h1]

/-- A switched-on `eqLimbs` pins the word at `X`, `r'` to `Y`. -/
theorem eqLimbs_word {sel : Expr} {X : ℕ} {off : ℤ} {rhs : ℕ → Expr} {r' : ℕ} (Y : Word)
    (hc : ∀ c ∈ eqLimbs sel X off rhs, c.eval n pc pub main r = 0)
    (hsel : sel.eval n pc pub main r = 1) (hw : wrap n r off = r')
    (hb : ∀ i < 32, (main (X + i) r').val ≤ 1)
    (hrhs : ∀ h ≤ 1, (rhs h).eval n pc pub main r = ((half16 Y h : ℕ) : F)) :
    word main X r' = Y := by
  have key : ∀ h ≤ 1, half16 (word main X r') h = half16 Y h := by
    intro h hh
    have e := hc _ (by
      simp only [eqLimbs, List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil]
      exact ⟨h, by omega, rfl⟩)
    simp only [Expr.eval, hsel, one_mul, eval_limb hw hb hh, hrhs h hh, sub_eq_zero] at e
    exact natCast_inj_of_lt (lt_trans (half16_lt _ _) (by norm_num [P]))
      (lt_trans (half16_lt _ _) (by norm_num [P])) e
  exact half16_inj (key 0 (by norm_num)) (key 1 (by norm_num))

/-- A switched-on `eqLimbs` against public inputs `b`, `b+1` pins the word to `pubWord pub b`. -/
theorem eqLimbs_pub {sel : Expr} {X : ℕ} {r' b : ℕ}
    (hc : ∀ c ∈ eqLimbs sel X 0 (fun h => .pub (b + h)), c.eval n pc pub main r = 0)
    (hsel : sel.eval n pc pub main r = 1) (hr : r < n) (hr' : r' = r)
    (hb : ∀ i < 32, (main (X + i) r').val ≤ 1) :
    word main X r' = pubWord pub b := by
  subst hr'
  have key : ∀ h ≤ 1, half16 (word main X r') h = (pub (b + h)).val := by
    intro h hh
    have e := hc _ (by
      simp only [eqLimbs, List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil]
      exact ⟨h, by omega, rfl⟩)
    simp only [Expr.eval, hsel, one_mul, eval_limb (wrap_zero hr) hb hh, sub_eq_zero] at e
    rw [← e, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans (half16_lt _ _) (by norm_num [P]))]
  have k0 := key 0 (by norm_num)
  have k1 := key 1 (by norm_num)
  simp only [Nat.add_zero] at k0
  have l0 := half16_lt (word main X r') 0
  have l1 := half16_lt (word main X r') 1
  apply BitVec.eq_of_toNat_eq
  rw [half16_split, pubWord, BitVec.toNat_ofNat, ← k0, ← k1, Nat.mod_eq_of_lt (by omega)]

end Limbs

/-! ## Facts about one header -/

theorem ivWords_lt (k : ℕ) : ivWords.getD k 0 < 2 ^ 32 := by
  have hall : ivWords.all (· < 2 ^ 32) = true := by decide
  rw [List.all_eq_true] at hall
  rw [List.getD_eq_getElem?_getD]
  cases h : ivWords[k]? with
  | none => simp
  | some v => simpa using hall v (List.mem_of_getElem? h)

theorem half16_ofNat {v : ℕ} (hv : v < 2 ^ 32) (h : ℕ) (hh : h ≤ 1) :
    half16 (BitVec.ofNat 32 v) h = if h = 0 then v % 2 ^ 16 else v / 2 ^ 16 := by
  rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;>
    simp only [half16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hv] <;> simp

section Header

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
include hsat

theorem sat' {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < 2 ^ logSize) :
    c.eval (2 ^ logSize) preCols pub main r = 0 := hsat r hr c hc

theorem sha_sat : ShaSat (2 ^ logSize) preCols pub main :=
  fun r hr c hc => sat' hsat (by simp only [constraints, List.mem_append]; left; left; left; exact hc) hr

theorem plumbing_sat {c : Expr} (hc : c ∈ plumbing) {r : ℕ} (hr : r < 2 ^ logSize) :
    c.eval (2 ^ logSize) preCols pub main r = 0 :=
  sat' hsat (by simp only [constraints, List.mem_append]; left; left; right; exact hc) hr

theorem linkage_sat {c : Expr} (hc : c ∈ linkage) {r : ℕ} (hr : r < 2 ^ logSize) :
    c.eval (2 ^ logSize) preCols pub main r = 0 :=
  sat' hsat (by simp only [constraints, List.mem_append]; left; right; exact hc) hr

theorem outputs_sat {c : Expr} (hc : c ∈ outputs) {r : ℕ} (hr : r < 2 ^ logSize) :
    c.eval (2 ^ logSize) preCols pub main r = 0 :=
  sat' hsat (by simp only [constraints, List.mem_append]; right; exact hc) hr

theorem bits {base r : ℕ} (hr : r < 2 ^ logSize) (hbase : base + 32 ≤ 96) :
    ∀ i < 32, (main (base + i) r).val ≤ 1 := word_bits (sha_sat hsat) hr hbase

omit hsat in
/-- SHA's selectors take their block values on each of a header's three compressions. -/
theorem sha_pre {j k : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hk : k < 3) :
    ∀ p < 72, ∀ i < 5, (pre i).eval (2 ^ logSize) preCols pub main (256 * j + 72 * k + p) =
      shaPre i p := by
  intro p hp i hi
  have hcol : preCols.getD i (.periodic [0]) = periodic256 (shaSel i) := by interval_cases i <;> rfl
  rw [eval_p256 hcol (by omega), show (256 * j + 72 * k + p) % 256 = 72 * k + p by omega, shaSel,
    if_pos (by omega), show (72 * k + p) % 72 = p by omega, ZMod.natCast_zmod_val]
  rfl

theorem compress_block {j k : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hk : k < 3) :
    compress (inputAt main (256 * j + 72 * k)) (messageAt main (256 * j + 72 * k)) =
      outputAt main (256 * j + 72 * k) :=
  compress_sound (sha_sat hsat) (by omega) (sha_pre hj hk)

/-- The init rows of compressions 0 and 2 hold the IV. -/
theorem input_iv {j s0 : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hs0 : s0 = 256 * j ∨ s0 = 256 * j + 144) :
    inputAt main s0 = IV := by
  have row : ∀ q < 4, word main A (s0 + q) = BitVec.ofNat 32 (ivWords.getD (3 - q) 0) ∧
      word main E (s0 + q) = BitVec.ofNat 32 (ivWords.getD (7 - q) 0) := by
    intro q hq
    have hr : s0 + q < 2 ^ logSize := by omega
    have hm : (s0 + q) % 256 = (if s0 = 256 * j then q else 144 + q) := by
      rcases hs0 with rfl | rfl <;> simp <;> omega
    have hsel : (pre IS_IV).eval (2 ^ logSize) preCols pub main (s0 + q) = 1 := by
      rw [eval_p256 (f := fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then 1 else 0) rfl hr, hm]
      split <;> simp <;> omega
    have hq4 : (s0 + q) % 256 % 4 = q := by rw [hm]; split <;> omega
    have hiv : (s0 + q) % 256 < 4 ∨ (144 ≤ (s0 + q) % 256 ∧ (s0 + q) % 256 < 148) := by
      rw [hm]; split <;> omega
    constructor
    · refine eqLimbs_word _ (fun c hc => plumbing_sat hsat (by
        simp only [plumbing, List.mem_append]; tauto) hr) hsel (wrap_zero hr) (bits hsat hr (by decide)) ?_
      intro h hh
      interval_cases h
      · rw [eval_p256 (f := fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (3 - q % 4) 0 % 2 ^ 16 else 0) rfl hr,
          if_pos hiv, hq4, half16_ofNat (ivWords_lt _) 0 (by norm_num)]; rfl
      · rw [eval_p256 (f := fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (3 - q % 4) 0 / 2 ^ 16 else 0) rfl hr,
          if_pos hiv, hq4, half16_ofNat (ivWords_lt _) 1 (by norm_num)]; rfl
    · refine eqLimbs_word _ (fun c hc => plumbing_sat hsat (by
        simp only [plumbing, List.mem_append]; tauto) hr) hsel (wrap_zero hr) (bits hsat hr (by decide)) ?_
      intro h hh
      interval_cases h
      · rw [eval_p256 (f := fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (7 - q % 4) 0 % 2 ^ 16 else 0) rfl hr,
          if_pos hiv, hq4, half16_ofNat (ivWords_lt _) 0 (by norm_num)]; rfl
      · rw [eval_p256 (f := fun q => if q < 4 ∨ (144 ≤ q ∧ q < 148) then ivWords.getD (7 - q % 4) 0 / 2 ^ 16 else 0) rfl hr,
          if_pos hiv, hq4, half16_ofNat (ivWords_lt _) 1 (by norm_num)]; rfl
  obtain ⟨a0, e0⟩ := row 0 (by norm_num)
  obtain ⟨a1, e1⟩ := row 1 (by norm_num)
  obtain ⟨a2, e2⟩ := row 2 (by norm_num)
  obtain ⟨a3, e3⟩ := row 3 (by norm_num)
  simp only [Nat.add_zero] at a0 e0
  simp only [inputAt, stAt, show s0 + 3 - 1 = s0 + 2 by omega, show s0 + 3 - 2 = s0 + 1 by omega,
    show s0 + 3 - 3 = s0 by omega, a0, e0, a1, e1, a2, e2, a3, e3]
  rfl

/-- Compression 1 starts from compression 0's output. -/
theorem input_chain {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) :
    inputAt main (256 * j + 72) = outputAt main (256 * j) := by
  have row : ∀ q < 4, word main A (256 * j + 72 + q) = word main A (256 * j + 68 + q) ∧
      word main E (256 * j + 72 + q) = word main E (256 * j + 68 + q) := by
    intro q hq
    have hr : 256 * j + 72 + q < 2 ^ logSize := by omega
    have hsel : (pre IS_CHAIN).eval (2 ^ logSize) preCols pub main (256 * j + 72 + q) = 1 := by
      rw [eval_p256 (f := fun q => if 72 ≤ q ∧ q < 76 then 1 else 0) rfl hr,
        show (256 * j + 72 + q) % 256 = 72 + q by omega]
      simp; omega
    have hw : wrap (2 ^ logSize) (256 * j + 72 + q) (-((4 : ℕ) : ℤ)) = 256 * j + 68 + q := by
      rw [wrap_back (by omega) hr]; omega
    constructor
    · refine (eqLimbs_word (r := 256 * j + 72 + q) _ (fun c hc => plumbing_sat hsat (by
        simp only [plumbing, List.mem_append]; tauto) hr) hsel (wrap_zero hr)
        (bits hsat hr (by decide)) (fun h hh => ?_))
      exact eval_limb hw (bits hsat (by omega) (by decide)) hh
    · refine (eqLimbs_word (r := 256 * j + 72 + q) _ (fun c hc => plumbing_sat hsat (by
        simp only [plumbing, List.mem_append]; tauto) hr) hsel (wrap_zero hr)
        (bits hsat hr (by decide)) (fun h hh => ?_))
      exact eval_limb hw (bits hsat (by omega) (by decide)) hh
  obtain ⟨a0, e0⟩ := row 0 (by norm_num)
  obtain ⟨a1, e1⟩ := row 1 (by norm_num)
  obtain ⟨a2, e2⟩ := row 2 (by norm_num)
  obtain ⟨a3, e3⟩ := row 3 (by norm_num)
  simp only [inputAt, outputAt, stAt]
  simp only [show 256 * j + 72 + 3 = 256 * j + 75 by omega, show 256 * j + 75 - 1 = 256 * j + 74 by omega,
    show 256 * j + 75 - 2 = 256 * j + 73 by omega, show 256 * j + 75 - 3 = 256 * j + 72 by omega,
    show 256 * j + 71 - 1 = 256 * j + 70 by omega, show 256 * j + 71 - 2 = 256 * j + 69 by omega,
    show 256 * j + 71 - 3 = 256 * j + 68 by omega] at *
  simp only [Nat.add_zero, show 256 * j + 72 + 1 = 256 * j + 73 by omega,
    show 256 * j + 72 + 2 = 256 * j + 74 by omega, show 256 * j + 68 + 1 = 256 * j + 69 by omega,
    show 256 * j + 68 + 2 = 256 * j + 70 by omega, show 256 * j + 68 + 3 = 256 * j + 71 by omega]
    at a0 e0 a1 e1 a2 e2 a3 e3
  rw [a0, e0, a1, e1, a2, e2, a3, e3]

/-- A padding row holds its constant word. -/
theorem pad_word {j q : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hq : isPadRow q = true) (hq256 : q < 256) :
    word main W (256 * j + q) = BitVec.ofNat 32 (padWord q) := by
  have hr : 256 * j + q < 2 ^ logSize := by omega
  have hm : (256 * j + q) % 256 = q := by omega
  have hpw : padWord q < 2 ^ 32 := by unfold padWord; split_ifs <;> norm_num
  refine eqLimbs_word _ (fun c hc => plumbing_sat hsat (by
    simp only [plumbing, List.mem_append]; tauto) hr) ?_ (wrap_zero hr) (bits hsat hr (by decide)) ?_
  · rw [eval_p256 (f := fun q => if isPadRow q then 1 else 0) rfl hr, hm, if_pos hq]; simp
  · intro h hh
    interval_cases h
    · rw [eval_p256 (f := fun q => padWord q % 2 ^ 16) rfl hr, hm, half16_ofNat hpw 0 (by norm_num)]; rfl
    · rw [eval_p256 (f := fun q => padWord q / 2 ^ 16) rfl hr, hm, half16_ofNat hpw 1 (by norm_num)]; rfl

/-- Compression 1's message is header words 16..19 followed by the 80-byte padding. -/
theorem msg1 {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) :
    ∀ t < 16, messageAt main (256 * j + 72) t = block1 (headerWord main j) t := by
  intro t ht
  simp only [messageAt, block1, headerWord]
  by_cases h4 : t < 4
  · simp only [h4, if_true, show ¬ (16 + t < 16) by omega, if_false]
    congr 1; omega
  · simp only [h4, if_false]
    rw [show 256 * j + 72 + 4 + t = 256 * j + (76 + t) by omega,
      pad_word hsat hj (by simp [isPadRow]; omega) (by omega)]
    interval_cases t <;> rfl

/-- Compression 2's message is compression 1's digest followed by the 32-byte padding. -/
theorem msg2 {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) :
    ∀ t < 16, messageAt main (256 * j + 144) t = digestBlock (outputAt main (256 * j + 72)) t := by
  intro t ht
  simp only [messageAt, digestBlock]
  by_cases h8 : t < 8
  · simp only [h8, if_true, outputAt, stAt_word main _ h8]
    have hr : 256 * j + 144 + 4 + t < 2 ^ logSize := by omega
    have hsel : (pre (MSG0 + t)).eval (2 ^ logSize) preCols pub main (256 * j + 144 + 4 + t) = 1 := by
      have hcol : preCols.getD (MSG0 + t) (.periodic [0]) = oneRow (148 + t) := by
        interval_cases t <;> rfl
      rw [eval_oneRow hcol hr]; simp; omega
    have hmem : ∀ c ∈ eqLimbs (pre (MSG0 + t)) W 0 (fun h => limb (msgSrc t).1 h (msgSrc t).2),
        c ∈ plumbing := fun c hc => by
      simp only [plumbing, List.mem_append, List.mem_flatMap, List.mem_range]
      right; exact ⟨t, h8, hc⟩
    by_cases h4 : t < 4
    · simp only [h4, if_true]
      have hsrc : msgSrc t = (A, -((5 + 2 * t : ℕ) : ℤ)) := by simp [msgSrc, h4]
      simp only [hsrc] at hmem
      have hw : wrap (2 ^ logSize) (256 * j + 144 + 4 + t) (-((5 + 2 * t : ℕ) : ℤ)) =
          256 * j + 72 + 71 - t := by rw [wrap_back (by omega) hr]; omega
      exact eqLimbs_word (r := 256 * j + 144 + 4 + t) _
        (fun c hc => plumbing_sat hsat (hmem c hc) hr) hsel (wrap_zero hr) (bits hsat hr (by decide))
        (fun h hh => eval_limb hw (bits hsat (base := A) (by omega) (by decide)) hh)
    · simp only [h4, if_false]
      have hsrc : msgSrc t = (E, -((9 + 2 * (t - 4) : ℕ) : ℤ)) := by simp [msgSrc, h4]
      simp only [hsrc] at hmem
      have hw : wrap (2 ^ logSize) (256 * j + 144 + 4 + t) (-((9 + 2 * (t - 4) : ℕ) : ℤ)) =
          256 * j + 72 + 71 - (t - 4) := by rw [wrap_back (by omega) hr]; omega
      exact eqLimbs_word (r := 256 * j + 144 + 4 + t) _
        (fun c hc => plumbing_sat hsat (hmem c hc) hr) hsel (wrap_zero hr) (bits hsat hr (by decide))
        (fun h hh => eval_limb hw (bits hsat (base := E) (by omega) (by decide)) hh)
  · simp only [h8, if_false]
    rw [show 256 * j + 144 + 4 + t = 256 * j + (148 + t) by omega,
      pad_word hsat hj (by simp [isPadRow]; omega) (by omega)]
    interval_cases t <;> rfl

/-- Each header's hash is SHA256d of its words. -/
theorem header_hash {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) :
    sha256d (headerWord main j) = hashAt main j := by
  have c0 := compress_block hsat hj (k := 0) (by norm_num)
  have c1 := compress_block hsat hj (k := 1) (by norm_num)
  have c2 := compress_block hsat hj (k := 2) (by norm_num)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, show 72 * 2 = 144 by norm_num] at c0 c1 c2
  have m0 : compress IV (block0 (headerWord main j)) = outputAt main (256 * j) := by
    rw [← input_iv hsat hj (s0 := 256 * j) (Or.inl rfl), ← c0]
    apply compress_congr
    intro t ht
    simp only [block0, headerWord, messageAt, ht, if_true]
  have m1 : compress (outputAt main (256 * j)) (block1 (headerWord main j)) =
      outputAt main (256 * j + 72) := by
    rw [← input_chain hsat hj, ← c1]
    exact compress_congr _ (fun t ht => (msg1 hsat hj t ht).symm)
  rw [sha256d, m0, m1, hashAt, ← c2, input_iv hsat hj (s0 := 256 * j + 144) (Or.inr rfl)]
  exact compress_congr _ (fun t ht => (msg2 hsat hj t ht).symm)

/-- The selector of the linkage family is on at rows `5..12` of every header but the first. -/
theorem link_sel {j k : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hj1 : 1 ≤ j) (hk : k < 8) :
    (Expr.mul (pre (LINK0 + k)) (.sub (cst 1) (pre FIRST))).eval (2 ^ logSize) preCols pub main
      (256 * j + 5 + k) = 1 := by
  have hr : 256 * j + 5 + k < 2 ^ logSize := by omega
  have hcol : preCols.getD (LINK0 + k) (.periodic [0]) = oneRow (5 + k) := by interval_cases k <;> rfl
  simp only [Expr.eval, eval_oneRow hcol hr, eval_first hr, eval_cst,
    show (256 * j + 5 + k) % 256 = 5 + k by omega, if_true, show ¬ (256 * j + 5 + k < 256) by omega,
    if_false]
  simp

theorem link_word {j k : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hj1 : 1 ≤ j) (hk : k < 8) :
    word main W (256 * j + 5 + k) = stateWord (hashAt main (j - 1)) k := by
  have hr : 256 * j + 5 + k < 2 ^ logSize := by omega
  have hmem : ∀ c ∈ eqLimbs (.mul (pre (LINK0 + k)) (.sub (cst 1) (pre FIRST))) W 0
      (fun h => limb (linkSrc k).1 h (linkSrc k).2), c ∈ linkage := fun c hc => by
    simp only [linkage, List.mem_flatMap, List.mem_range, List.mem_append]
    exact ⟨k, hk, Or.inl hc⟩
  rw [hashAt, outputAt, stAt_word main _ hk]
  by_cases h4 : k < 4
  · simp only [h4, if_true]
    have hsrc : linkSrc k = (A, -((46 + 2 * k : ℕ) : ℤ)) := by simp [linkSrc, h4]
    simp only [hsrc] at hmem
    have hw : wrap (2 ^ logSize) (256 * j + 5 + k) (-((46 + 2 * k : ℕ) : ℤ)) =
        256 * (j - 1) + 144 + 71 - k := by rw [wrap_back (by omega) hr]; omega
    exact eqLimbs_word (r := 256 * j + 5 + k) _ (fun c hc => linkage_sat hsat (hmem c hc) hr)
      (link_sel hsat hj hj1 hk) (wrap_zero hr) (bits hsat hr (by decide))
      (fun h hh => eval_limb hw (bits hsat (base := A) (by omega) (by decide)) hh)
  · simp only [h4, if_false]
    have hsrc : linkSrc k = (E, -((50 + 2 * (k - 4) : ℕ) : ℤ)) := by simp [linkSrc, h4]
    simp only [hsrc] at hmem
    have hw : wrap (2 ^ logSize) (256 * j + 5 + k) (-((50 + 2 * (k - 4) : ℕ) : ℤ)) =
        256 * (j - 1) + 144 + 71 - (k - 4) := by rw [wrap_back (by omega) hr]; omega
    exact eqLimbs_word (r := 256 * j + 5 + k) _ (fun c hc => linkage_sat hsat (hmem c hc) hr)
      (link_sel hsat hj hj1 hk) (wrap_zero hr) (bits hsat hr (by decide))
      (fun h hh => eval_limb hw (bits hsat (base := E) (by omega) (by decide)) hh)

omit hsat in
theorem prevHash_eq {j : ℕ} {S : State} (hw : ∀ k < 8, headerWord main j (k + 1) = stateWord S k) :
    prevHash (headerWord main j) = S := by
  have := fun k hk => hw k hk
  obtain ⟨a, b, c, d, e, f, g, h⟩ := S
  simp only [prevHash, State.mk.injEq]
  exact ⟨hw 0 (by norm_num), hw 1 (by norm_num), hw 2 (by norm_num), hw 3 (by norm_num),
    hw 4 (by norm_num), hw 5 (by norm_num), hw 6 (by norm_num), hw 7 (by norm_num)⟩

/-- Every header after the first commits to its predecessor's hash. -/
theorem header_link {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize) (hj1 : 1 ≤ j) :
    prevHash (headerWord main j) = hashAt main (j - 1) :=
  prevHash_eq (fun k hk => by
    simp only [headerWord, show k + 1 < 16 by omega, if_true,
      show 256 * j + 4 + (k + 1) = 256 * j + 5 + k by omega]
    exact link_word hsat hj hj1 hk)

/-- The first header's prev-hash field is public inputs 0..15. -/
theorem first_link (hn : 256 ≤ 2 ^ logSize) : prevHash (headerWord main 0) = pubState pub 0 := by
  have w : ∀ k < 8, word main W (5 + k) = pubWord pub (2 * k) := by
    intro k hk
    have hr : 5 + k < 2 ^ logSize := by omega
    have hcol : preCols.getD (LINK0 + k) (.periodic [0]) = oneRow (5 + k) := by interval_cases k <;> rfl
    have hmem : ∀ c ∈ eqLimbs (.mul (pre (LINK0 + k)) (pre FIRST)) W 0 (fun h => .pub (2 * k + h)),
        c ∈ linkage := fun c hc => by
      simp only [linkage, List.mem_flatMap, List.mem_range, List.mem_append]
      exact ⟨k, hk, Or.inr hc⟩
    exact eqLimbs_pub (fun c hc => linkage_sat hsat (hmem c hc) hr)
      (by simp only [Expr.eval, eval_oneRow hcol hr, eval_first hr,
            show (5 + k) % 256 = 5 + k by omega, show 5 + k < 256 by omega, if_true]; simp)
      hr rfl (bits hsat hr (by decide))
  simp only [prevHash, pubState, State.mk.injEq, headerWord, Nat.mul_zero, Nat.zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  first
  | (rw [if_pos (by norm_num)]; exact w 0 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 1 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 2 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 3 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 4 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 5 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 6 (by norm_num))
  | (rw [if_pos (by norm_num)]; exact w 7 (by norm_num))

/-- The last header's hash is public inputs 16..31. -/
theorem last_hash {J : ℕ} (hJ : 256 * (J + 1) = 2 ^ logSize) : hashAt main J = pubState pub 16 := by
  have w : ∀ jj < 4, word main A (256 * J + 212 + jj) = pubWord pub (16 + 2 * (3 - jj)) ∧
      word main E (256 * J + 212 + jj) = pubWord pub (16 + 2 * (7 - jj)) := by
    intro jj hjj
    have hr : 256 * J + 212 + jj < 2 ^ logSize := by omega
    have hcol : preCols.getD (OUT0 + jj) (.periodic [0]) = oneRow (212 + jj) := by interval_cases jj <;> rfl
    have hsel : (Expr.mul (pre (OUT0 + jj)) (pre LAST)).eval (2 ^ logSize) preCols pub main
        (256 * J + 212 + jj) = 1 := by
      simp only [Expr.eval, eval_oneRow hcol hr, eval_last hr,
        show (256 * J + 212 + jj) % 256 = 212 + jj by omega, if_true,
        show 2 ^ logSize ≤ 256 * J + 212 + jj + 256 by omega]
      simp
    have hmemA : ∀ c ∈ eqLimbs (.mul (pre (OUT0 + jj)) (pre LAST)) A 0
        (fun h => .pub (16 + 2 * (3 - jj) + h)), c ∈ outputs := fun c hc => by
      simp only [outputs, List.mem_flatMap, List.mem_range, List.mem_append]
      exact ⟨jj, hjj, Or.inl hc⟩
    have hmemE : ∀ c ∈ eqLimbs (.mul (pre (OUT0 + jj)) (pre LAST)) E 0
        (fun h => .pub (16 + 2 * (7 - jj) + h)), c ∈ outputs := fun c hc => by
      simp only [outputs, List.mem_flatMap, List.mem_range, List.mem_append]
      exact ⟨jj, hjj, Or.inr hc⟩
    exact ⟨eqLimbs_pub (fun c hc => outputs_sat hsat (hmemA c hc) hr) hsel hr rfl (bits hsat hr (by decide)),
      eqLimbs_pub (fun c hc => outputs_sat hsat (hmemE c hc) hr) hsel hr rfl (bits hsat hr (by decide))⟩
  obtain ⟨a0, e0⟩ := w 0 (by norm_num)
  obtain ⟨a1, e1⟩ := w 1 (by norm_num)
  obtain ⟨a2, e2⟩ := w 2 (by norm_num)
  obtain ⟨a3, e3⟩ := w 3 (by norm_num)
  simp only [hashAt, outputAt, stAt, pubState, State.mk.injEq]
  simp only [Nat.add_zero, show 256 * J + 212 + 1 = 256 * J + 144 + 71 - 2 by omega,
    show 256 * J + 212 + 2 = 256 * J + 144 + 71 - 1 by omega, show 256 * J + 212 + 3 = 256 * J + 144 + 71 by omega,
    show 256 * J + 212 = 256 * J + 144 + 71 - 3 by omega] at a0 e0 a1 e1 a2 e2 a3 e3
  norm_num at a0 e0 a1 e1 a2 e2 a3 e3
  exact ⟨a3, a2, a1, a0, e3, e2, e1, e0⟩

end Header

/-- **Header-chain soundness (v1).** For a trace satisfying the header-chain AIR with
`2^logSize` rows (`logSize ≥ 8`) and public inputs `pub`, let `H = 2^logSize / 256`:
1. every header's hash (read from its rows) is SHA256d of its 20 words;
2. every header after the first has its predecessor's hash as prev-hash;
3. the first header's prev-hash is `pubState pub 0`;
4. the last header's hash is `pubState pub 16`. -/
theorem chain_sound {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
    (hsat : air.Satisfied logSize pub main) (hlog : 8 ≤ logSize) :
    let H := 2 ^ logSize / 256
    (∀ j < H, sha256d (headerWord main j) = hashAt main j) ∧
    (∀ j < H, 1 ≤ j → prevHash (headerWord main j) = hashAt main (j - 1)) ∧
    prevHash (headerWord main 0) = pubState pub 0 ∧
    hashAt main (H - 1) = pubState pub 16 := by
  intro H
  have hN : 2 ^ logSize = 256 * H := by
    have : 2 ^ logSize = 2 ^ 8 * 2 ^ (logSize - 8) := by rw [← pow_add]; congr 1; omega
    simp only [H, this]; norm_num
  have hH : 1 ≤ H := by
    have : 1 ≤ 2 ^ (logSize - 8) := Nat.one_le_two_pow
    have h2 : 2 ^ logSize = 2 ^ 8 * 2 ^ (logSize - 8) := by rw [← pow_add]; congr 1; omega
    omega
  refine ⟨fun j hj => header_hash hsat (by omega), fun j hj hj1 => header_link hsat (by omega) hj1,
    first_link hsat (by omega), last_hash hsat (by omega)⟩

end StarkedAir.HeaderChain
