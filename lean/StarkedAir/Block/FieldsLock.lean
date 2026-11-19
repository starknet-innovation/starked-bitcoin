/-
**Relative lock times in the fields component (BIP68, CONNECT-RULES step 2).** Given that byte slots
and the version bytes read the block and range slots hold bytes:
- `v2_head`, `v2_const`: `V2` on a transaction's rows says its version is at least 2;
- `seq_bits`: on an input row, `T22` and `D31` are bits 22 and 31 of the sequence, and the tuple's lock
  is the sequence's low 16 bits;
- `lkh_of`: an input whose height lock Core enforces (CSV active, version at least 2, bits 31 and 22
  clear) has `LKH = 1`;
- `row_in_tx`: an input row with a transaction's lock count lies between that transaction's head and
  its lock time.
-/
import StarkedAir.Block.TxChecks

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC sumPow)

theorem mem_lock {c : Expr} (h : c ∈ lockC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inr h

/-- The version's bytes: `b1 + b2 + b3 + b0² = b0` exactly when the version is 0 or 1. -/
theorem ver_arith {b0 b1 b2 b3 : ℕ} :
    b1 + b2 + b3 + b0 * b0 = b0 ↔ b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 < 2 := by
  constructor
  · intro h
    have h01 : b0 ≤ 1 := by
      by_contra hc
      have : 2 * b0 ≤ b0 * b0 := Nat.mul_le_mul_right b0 (by omega)
      omega
    have hsq : b0 * b0 = b0 := by interval_cases b0 <;> rfl
    omega
  · intro h
    have h1 : b1 = 0 := by omega
    have h2 : b2 = 0 := by omega
    have h3 : b3 = 0 := by omega
    have h01 : b0 ≤ 1 := by omega
    subst h1 h2 h3
    interval_cases b0 <;> rfl

section Lock

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (hby : ∀ r < n, ∀ j < 8, (chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = -1 →
    (M BASEC r).val + j < R.length ∧ (M (BY j) r).val = (R.getD ((M BASEC r).val + j) 0).toNat)
  (hrg : ∀ r < n, ∀ j < 13, (M (RG j) r).val < 256)
  (hvb : ∀ r < n, M K_TXH r = 1 → ∀ j < 4, (M START r).val + j < R.length ∧
    (M (VBY j) r).val = (R.getD ((M START r).val + j) 0).toNat)
  (hn : n ≤ 2 ^ 25)
include hsat hcs hmn hpad hfit hby hrg hvb hn

omit hcs hmn hpad hfit hby hrg hvb hn in
theorem lock_bool {X : ℕ} (hX : X ∈ [V2, T22, U23, D31]) {r : ℕ} (hr : r < n) : M X r = 0 ∨ M X r = 1 :=
  bool_of hsat (mem_lock (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hX
    rcases hX with rfl | rfl | rfl | rfl <;> simp [lockC])) hr

omit hcs hmn hpad hfit hby hrg hvb hn in
/-- `V2` is constant from a transaction's head through its lock time. -/
theorem v2_const {rh ρ : ℕ} (hρn : ρ < n) (hnt : ∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) :
    ∀ j, rh ≤ j → j ≤ ρ → M V2 j = M V2 rh := by
  intro j h1 h2
  induction j, h1 using Nat.le_induction with
  | base => rfl
  | succ j hj ih =>
    have hjn : j + 1 < n := by omega
    have := sat hsat (mem_lock (c := .mul (oneMinus (k K_TXH)) (same V2)) (by simp [lockC])) hjn
    simp only [Expr.eval, same, oneMinus, one, eval_cst, Nat.cast_one, ev_k hjn, ev_kp hjn, ev_notFirst hjn,
      hnt (j + 1) (by omega) h2, sub_zero, one_mul, sub_eq_zero] at this
    rw [this, ih (by omega)]

omit hcs hmn hpad hfit hby hrg hn in
/-- **On a transaction head, `V2` says the version is at least 2.** -/
theorem v2_head {rh : ℕ} (hr : rh < n) (ht : M K_TXH rh = 1) :
    M V2 rh = 1 ↔ 2 ≤ Spec.Block.le (slice R (M START rh).val 4) := by
  have vb := hvb rh hr ht
  set S := (M START rh).val
  have hfr : S + 4 ≤ R.length := by have := (vb 3 (by norm_num)).1; omega
  have b256 : ∀ j < 4, (M (VBY j) rh).val < 256 := fun j hj => by rw [(vb j hj).2]; exact UInt8.toNat_lt _
  have x0 := b256 0 (by norm_num); have x1 := b256 1 (by norm_num)
  have x2 := b256 2 (by norm_num); have x3 := b256 3 (by norm_num)
  have hver : Spec.Block.le (slice R S 4) = (M (VBY 0) rh).val + 256 * (M (VBY 1) rh).val +
      65536 * (M (VBY 2) rh).val + 16777216 * (M (VBY 3) rh).val := by
    have b0' : (M (VBY 0) rh).val = (R.getD S 0).toNat := by simpa using (vb 0 (by norm_num)).2
    rw [le_slice4 hfr, ← b0', ← (vb 1 (by norm_num)).2, ← (vb 2 (by norm_num)).2, ← (vb 3 (by norm_num)).2]
  have q := fun (cc : Expr) (h : cc ∈ lockC) => sat hsat (mem_lock h) hr
  have c1 := q (.mul (k K_TXH) (.sub (k VE) (.add (.add (.add (k (VBY 1)) (k (VBY 2))) (k (VBY 3)))
    (.mul (k (VBY 0)) (.sub (k (VBY 0)) one))))) (by simp [lockC])
  have c2 := q (.mul (k K_TXH) (.sub (k V2) (.mul (k VE) (k VINV)))) (by simp [lockC])
  have c3 := q (.mul (k K_TXH) (.mul (oneMinus (k V2)) (k VE))) (by simp [lockC])
  simp only [Expr.eval, ev_k hr, ht, one_mul, one, oneMinus, eval_cst, Nat.cast_one, sub_eq_zero] at c1 c2 c3
  have hE : M VE rh = (((M (VBY 1) rh).val + (M (VBY 2) rh).val + (M (VBY 3) rh).val +
      (M (VBY 0) rh).val * (M (VBY 0) rh).val : ℕ) : F) - (((M (VBY 0) rh).val : ℕ) : F) := by
    rw [c1]; push_cast; simp only [ZMod.natCast_zmod_val]; ring
  have hsq : (M (VBY 0) rh).val * (M (VBY 0) rh).val ≤ 255 * 255 := Nat.mul_le_mul (by omega) (by omega)
  have hz : M VE rh = 0 ↔ (M (VBY 1) rh).val + (M (VBY 2) rh).val + (M (VBY 3) rh).val +
      (M (VBY 0) rh).val * (M (VBY 0) rh).val = (M (VBY 0) rh).val := by
    rw [hE, sub_eq_zero]
    constructor
    · intro h; exact natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega)) h
    · intro h; rw [h]
  rw [hver, ← not_lt, ← ver_arith, ← hz]
  rcases lock_bool hsat (X := V2) (by simp) hr with v0 | v1
  · rw [v0] at c3 ⊢
    simp only [sub_zero, one_mul] at c3
    simp [c3]
  · rw [v1] at c2 ⊢
    simp only [true_iff]
    intro hz0; rw [hz0, zero_mul] at c2; exact one_ne_zero c2

omit hvb in
/-- **An input row's sequence bits.** With `s` the sequence (the row's last four bytes): `T22` and `D31`
are its bits 22 and 31, and the lock the input tuple carries is its low 16 bits. -/
theorem seq_bits {r : ℕ} (hr : r < m) (hi : M K_IN r = 1) {s : ℕ}
    (hs : s = Spec.Block.le (slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4)) :
    (M T22 r = 1 ↔ s / 2 ^ 22 % 2 = 1) ∧ (M D31 r = 1 ↔ s / 2 ^ 31 % 2 = 1) ∧
      lo16.eval n preCols pub M r = ((s % 65536 : ℕ) : F) := by
  have hrn : r < n := by omega
  have sb := fun j (hj : j < 4) => seq_bytes hsat R hcs hmn hpad hfit hby hrg hn hr hi hj
  set B := (M START r).val + 36 + prefOf M r + (M VAL r).val with hB
  have hfr : B + 4 ≤ R.length := by have := (sb 3 (by norm_num)).1; omega
  have b256 : ∀ j < 4, (M (BY j) r).val < 256 := fun j hj => by rw [(sb j hj).2]; exact UInt8.toNat_lt _
  have hs' : s = (M (BY 0) r).val + 256 * (M (BY 1) r).val + 65536 * (M (BY 2) r).val +
      16777216 * (M (BY 3) r).val := by
    have b0' : (M (BY 0) r).val = (R.getD B 0).toNat := by simpa using (sb 0 (by norm_num)).2
    rw [hs, le_slice4 hfr, ← b0', ← (sb 1 (by norm_num)).2, ← (sb 2 (by norm_num)).2, ← (sb 3 (by norm_num)).2]
  have q := fun (cc : Expr) (h : cc ∈ lockC) => sat hsat (mem_lock h) hrn
  have c1 := q (.mul (k K_IN) (.sub (by4 2) (.add (rg 0) (.add (.mul (c 64) (k T22)) (.mul (c 128) (k U23))))))
    (by simp [lockC])
  have c2 := q (.mul (k K_IN) (.sub (rg 1) (.mul (c 4) (rg 0)))) (by simp [lockC])
  have c3 := q (.mul (k K_IN) (.sub (by4 3) (.add (rg 2) (.mul (c 128) (k D31))))) (by simp [lockC])
  have c4 := q (.mul (k K_IN) (.sub (rg 3) (.mul (c 2) (rg 2)))) (by simp [lockC])
  simp only [Expr.eval, ev_k hrn, hi, one_mul, by4, rg, c, eval_cst, sub_eq_zero, Nat.cast_ofNat] at c1 c2 c3 c4
  obtain ⟨vt, lt⟩ := bool_val (lock_bool hsat (X := T22) (by simp) hrn)
  obtain ⟨vu, lu⟩ := bool_val (lock_bool hsat (X := U23) (by simp) hrn)
  obtain ⟨vd, ld⟩ := bool_val (lock_bool hsat (X := D31) (by simp) hrn)
  have g0 := hrg r hrn 0 (by norm_num); have g1 := hrg r hrn 1 (by norm_num)
  have g2 := hrg r hrn 2 (by norm_num); have g3 := hrg r hrn 3 (by norm_num)
  have x0 := b256 0 (by norm_num); have x1 := b256 1 (by norm_num)
  have x2 := b256 2 (by norm_num); have x3 := b256 3 (by norm_num)
  have e2 : (M (RG 1) r).val = 4 * (M (RG 0) r).val := by
    apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
    push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c2
  have e4 : (M (RG 3) r).val = 2 * (M (RG 2) r).val := by
    apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
    push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c4
  have e1 : (M (BY 2) r).val = (M (RG 0) r).val + 64 * (M T22 r).val + 128 * (M U23 r).val := by
    apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
    push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c1
  have e3 : (M (BY 3) r).val = (M (RG 2) r).val + 128 * (M D31 r).val := by
    apply natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega))
    push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination c3
  have t1 : M T22 r = 1 ↔ (M T22 r).val = 1 := by
    constructor
    · intro h; rw [h]; exact ZMod.val_one P
    · intro h; rw [vt, h]; simp
  have d1 : M D31 r = 1 ↔ (M D31 r).val = 1 := by
    constructor
    · intro h; rw [h]; exact ZMod.val_one P
    · intro h; rw [vd, h]; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [t1, hs']; omega
  · rw [d1, hs']; omega
  · simp only [lo16, le2, by4, c, Expr.eval, ev_k hrn, eval_cst, Nat.cast_ofNat]
    rw [hs', show ((M (BY 0) r).val + 256 * (M (BY 1) r).val + 65536 * (M (BY 2) r).val +
      16777216 * (M (BY 3) r).val) % 65536 = (M (BY 0) r).val + 256 * (M (BY 1) r).val by omega]
    push_cast; simp only [ZMod.natCast_zmod_val]

/-- **An enforced height lock sets `LKH`.** For an input row `r` of the transaction whose head is `rh`:
with CSV active (`pub 5 = 1`), the version at least 2, and bits 31 and 22 of the sequence clear,
`LKH = 1`. -/
theorem lkh_of {rh r : ℕ} (hrh : rh ≤ r) (hr : r < m) (ht : M K_TXH rh = 1)
    (hnt : ∀ j, rh < j → j ≤ r → M K_TXH j = 0) (hi : M K_IN r = 1) (hp5 : pub 5 = 1)
    (hv : 2 ≤ Spec.Block.le (slice R (M START rh).val 4)) {s : ℕ}
    (hs : s = Spec.Block.le (slice R ((M START r).val + 36 + prefOf M r + (M VAL r).val) 4))
    (h31 : s / 2 ^ 31 % 2 = 0) (h22 : s / 2 ^ 22 % 2 = 0) : M LKH r = 1 := by
  have hrn : r < n := by omega
  obtain ⟨b22, b31, -⟩ := seq_bits hsat R hcs hmn hpad hfit hby hrg hn hr hi hs
  have v2 : M V2 r = 1 := by
    rw [v2_const hsat hrn hnt r hrh le_rfl]
    exact (v2_head hsat R hvb (by omega) ht).mpr hv
  have t0 : M T22 r = 0 := by
    rcases lock_bool hsat (X := T22) (by simp) hrn with h | h
    · exact h
    · have := b22.mp h; omega
  have d0 : M D31 r = 0 := by
    rcases lock_bool hsat (X := D31) (by simp) hrn with h | h
    · exact h
    · have := b31.mp h; omega
  have a1 := defn hsat (a := A1) (e := .mul (k V2) (oneMinus (k D31))) (mem_lock (by simp [lockC])) hrn
  have lk := defn hsat (a := LKH) (e := .mul (.pub 5) (.mul (k A1) (oneMinus (k T22)))) (mem_lock (by simp [lockC])) hrn
  simp only [Expr.eval, ev_k hrn, oneMinus, one, eval_cst, Nat.cast_one, v2, d0, sub_zero, mul_one] at a1
  simp only [Expr.eval, ev_k hrn, oneMinus, one, eval_cst, Nat.cast_one, a1, t0, hp5, sub_zero, mul_one] at lk
  exact lk

omit hcs hmn hpad hfit hby hrg hvb in
/-- **An input row with a transaction's lock count is one of its rows.** If the rows from the head `rh`
to the lock time `ρ` have `ρ`'s lock count, an input row `r` with that count lies strictly between them. -/
theorem row_in_tx {rh ρ r : ℕ} (hrh : rh < ρ) (hρn : ρ < n) (ht : M K_TXH rh = 1) (hl : M K_LOCK ρ = 1)
    (hc : locks M rh = locks M ρ) (hrn : r < n) (hi : M K_IN r = 1) (hr : locks M r = locks M ρ) :
    rh < r ∧ r < ρ := by
  have hrρ : r ≠ ρ := by
    rintro rfl
    have := kind_unique hsat hrn (a := K_IN) (b := K_LOCK) (by simp [K_IN]) (by simp [K_LOCK]) (by simp [K_IN, K_LOCK]) hi
    rw [hl] at this; exact one_ne_zero this
  have hrh' : r ≠ rh := by
    rintro rfl
    have := kind_unique hsat hrn (a := K_IN) (b := K_TXH) (by simp [K_IN]) (by simp [K_TXH]) (by simp [K_IN, K_TXH]) hi
    rw [ht] at this; exact one_ne_zero this
  refine ⟨?_, ?_⟩
  · by_contra hlt
    have hlt' : r < rh := by omega
    obtain ⟨p, rfl⟩ : ∃ p, rh = p + 1 := ⟨rh - 1, by omega⟩
    have hpn : p + 1 < n := by omega
    have tr := trans_eq hsat (X := K_TXH) (fm := .add (kp K_BLK) (.mul (kp K_LOCK) (oneMinus (kp Z1))))
      (by simp [transC]) hpn
    simp only [Expr.eval, ev_kp hpn, oneMinus, one, eval_cst, Nat.cast_one, ht] at tr
    rcases kind_bool hsat (c := K_LOCK) (by simp [kinds]) (show p < n by omega) with l0 | l1
    · -- the row before the head is the block row: `p = 0`, so `r` would be before row 0
      rw [l0, zero_mul, add_zero] at tr
      rcases Nat.eq_zero_or_pos p with rfl | hp
      · obtain rfl : r = 0 := by omega
        have := kind_unique hsat hrn (a := K_BLK) (b := K_IN) (by simp [K_BLK]) (by simp [K_IN]) (by simp [K_BLK, K_IN])
          (first_blk hsat hrn)
        rw [hi] at this; exact one_ne_zero this
      · obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
        rw [not_blk hsat (show p' + 1 < n by omega)] at tr
        exact one_ne_zero tr
    · have hrp : r ≠ p := by
        rintro rfl
        have := kind_unique hsat hrn (a := K_IN) (b := K_LOCK) (by simp [K_IN]) (by simp [K_LOCK]) (by simp [K_IN, K_LOCK]) hi
        rw [l1] at this; exact one_ne_zero this
      have h2 := locks_succ (M := M) p
      rw [if_pos l1] at h2
      have h3 := locks_le_add (M := M) r (p - r)
      rw [show r + (p - r) = p by omega] at h3
      omega
  · by_contra hge
    have := locks_mono (M := M) (show ρ < r by omega) hl
    omega

end Lock

end StarkedAir.Block.Fields
