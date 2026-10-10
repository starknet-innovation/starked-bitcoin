/-
**The coin-event component's rows (M3b, D-040): what its constraints force, row by row.** This is the
component-local layer of the coin proof; the system links (the lookups to the fields, SHA digests,
undo records, fingerprints) and the step to `Spec.Coins.connect_of_run` build on it.

- `kinds`: each row is at most one of output (`KO`), non-coinbase input (`KI`), coinbase input
  (`CBI`); the rows in use are a prefix `[0, e)`; token starts strictly increase on them.
- `cbo_spec`: `CBO = 1` exactly when the row's transaction index is 0 (the coinbase); a coinbase input
  is in the coinbase, a non-coinbase input is not.
- `j_spec`: `J` counts the non-coinbase inputs before the row.
- `vout_spec`: an output's index is one more than the previous row's if that was an output, else 0.
- `out_spec`, `in_spec`: an output's code is `2·height + CBO`, its creation index its transaction's,
  its byte length the token's, its index limbs the output index; an input's code is `2·HC + CBC`, with
  `(HC, CTX)` before `(height, TXI)`, a coinbase coin at least 100 blocks old, and its txid and index
  limbs the prevout bytes.
- `unsp_spec`: `UNSP = 1` exactly for an `OP_RETURN` first byte of a nonempty script or a script over
  10,000 bytes, given the byte-sized columns the lookups range-check.
- `mm_spec`: the multiplicity is `+1` for a spendable, not BIP30-lost output, `−1` for an input, else 0.

Range facts (bytes, three-byte differences) come from the lookups and are hypotheses here.
-/
import StarkedAir.Block.Coin
import StarkedAir.Block.RunSum

namespace StarkedAir.Block.Coin

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst wrap_back boolC)

section Rows

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by simp [k, eval_col, wrap_zero hr]
omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl
omit hsat in
theorem ev_kn {c r : ℕ} (hr : r + 1 < n) : (kn c).eval n preCols pub M r = M c (r + 1) := by
  simp [kn, eval_col, wrap_one hr]
omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [first, StarkedAir.Sha256.pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval]
omit hsat in
theorem ev_notLast {r : ℕ} (hr : r < n) : notLast.eval n preCols pub M r = if r + 1 < n then 1 else 0 := by
  simp [notLast, StarkedAir.Sha256.pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval]

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 := hsat r hr c hc

omit hsat in
theorem mem_local {c : Expr} (h : c ∈ localC) : c ∈ constraints := by simp [constraints, h]

theorem bool_col {c r : ℕ} (hc : c ∈ [KO, KI, CBI, CBC, ORD, U6A, BIG, ZS]) (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (mem_local (c := boolC (k c)) (by simp only [localC, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩))) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- `on = KO + KI + CBI`. -/
def onV (M : ℕ → ℕ → F) (r : ℕ) : F := M KO r + M KI r + M CBI r

omit hsat in
theorem ev_on {r : ℕ} (hr : r < n) : on.eval n preCols pub M r = onV M r := by
  simp [on, Expr.eval, ev_k hr, onV]

theorem on_bool {r : ℕ} (hr : r < n) : onV M r = 0 ∨ onV M r = 1 := by
  have := sat hsat (mem_local (c := boolC on) (by simp [localC])) hr
  simp only [boolC, Expr.eval, ev_on hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- At most one kind: the three are Boolean and their sum is Boolean. -/
theorem kinds {r : ℕ} (hr : r < n) :
    (M KO r = 1 ∧ M KI r = 0 ∧ M CBI r = 0 ∧ onV M r = 1) ∨ (M KO r = 0 ∧ M KI r = 1 ∧ M CBI r = 0 ∧ onV M r = 1) ∨
      (M KO r = 0 ∧ M KI r = 0 ∧ M CBI r = 1 ∧ onV M r = 1) ∨ (M KO r = 0 ∧ M KI r = 0 ∧ M CBI r = 0 ∧ onV M r = 0) := by
  have ho := bool_col hsat (c := KO) (by simp) hr
  have hi := bool_col hsat (c := KI) (by simp) hr
  have hc := bool_col hsat (c := CBI) (by simp) hr
  have hs := on_bool hsat hr
  simp only [onV] at hs ⊢
  generalize M KO r = a at *
  generalize M KI r = b at *
  generalize M CBI r = c at *
  rcases ho with rfl | rfl <;> rcases hi with rfl | rfl <;> rcases hc with rfl | rfl <;> revert hs <;> decide

/-- **The rows in use are a prefix** `[0, e)`. -/
theorem on_prefix (hn : 0 < n) : ∃ e, e < n ∧ ∀ r < n, (onV M r = 1 ↔ r < e) := by
  have hl : onV M (n - 1) = 0 := by
    have := sat hsat (mem_local (c := .mul isLast on) (by simp [localC])) (show n - 1 < n by omega)
    simp only [isLast, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_notLast (show n - 1 < n by omega),
      show ¬ (n - 1 + 1 < n) by omega, if_false, sub_zero, one_mul, ev_on (show n - 1 < n by omega)] at this
    exact this
  have hstep : ∀ r, r + 1 < n → onV M (r + 1) = 1 → onV M r = 1 := by
    intro r hr h1
    have := sat hsat (mem_local (c := .mul notFirst (.mul on (om onp))) (by simp [localC])) hr
    have hp : onp.eval n preCols pub M (r + 1) = onV M r := by simp [onp, Expr.eval, ev_kp hr, onV]
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
      sub_zero, one_mul, ev_on hr, hp, h1] at this
    exact (sub_eq_zero.mp this).symm
  have ex : ∃ r, r < n ∧ onV M r = 0 := ⟨n - 1, by omega, hl⟩
  obtain ⟨heN, he0⟩ := Nat.find_spec ex
  have hmin : ∀ r < Nat.find ex, ¬ (r < n ∧ onV M r = 0) := fun r h => Nat.find_min ex h
  generalize Nat.find ex = e at heN he0 hmin
  refine ⟨e, heN, fun r hr => ⟨fun h1 => ?_, fun hlt => ?_⟩⟩
  · by_contra hc
    push Not at hc
    have : ∀ d, r - d < n → onV M (r - d) = 1 := by
      intro d
      induction d with
      | zero => intro _; simpa using h1
      | succ d ih =>
        intro h
        by_cases hd : d < r
        · exact hstep (r - (d + 1)) (by omega) (by rw [show r - (d + 1) + 1 = r - d by omega]; exact ih (by omega))
        · rw [show r - (d + 1) = r - d by omega]; exact ih (by omega)
    have := this (r - e) (by omega)
    rw [show r - (r - e) = e by omega, he0] at this; exact zero_ne_one this
  · rcases on_bool hsat hr with h | h
    · exact absurd ⟨hr, h⟩ (hmin r hlt)
    · exact h

/-- Three byte limbs. -/
def b3V (M : ℕ → ℕ → F) (f : ℕ → ℕ) (r : ℕ) : F := M (f 0) r + 256 * M (f 1) r + 65536 * M (f 2) r

omit hsat in
theorem ev_b3 {f : ℕ → ℕ} {r : ℕ} (hr : r < n) : (b3 f).eval n preCols pub M r = b3V M f r := by
  simp [b3, Expr.eval, ev_k hr, eval_cst, b3V]

/-- **Token starts increase** on consecutive rows in use: by one plus a three-byte difference. -/
theorem start_step {r : ℕ} (hr : r + 1 < n) (hon : onV M (r + 1) = 1) :
    M START (r + 1) = M START r + 1 + b3V M D (r + 1) := by
  have := sat hsat (mem_local (c := .mul notFirst (.mul on (.sub (.sub (.sub (k START) (kp START)) one) (b3 D))))
    (by simp [localC])) hr
  simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
    sub_zero, one_mul, ev_on hr, hon, ev_k hr, ev_kp hr, ev_b3 hr] at this
  linear_combination this

/-- **The coinbase flag:** `CBO = 1` iff the transaction index is 0; a coinbase input is in the
coinbase, a non-coinbase input is not. -/
theorem cbo_spec {r : ℕ} (hr : r < n) :
    (M CBO r = 1 ↔ M TXI r = 0) ∧ (M CBO r = 0 ∨ M CBO r = 1) ∧
      (M CBI r = 1 → M CBO r = 1) ∧ (M KI r = 1 → M CBO r = 0) := by
  have h1 := sat hsat (mem_local (c := .sub (k CBO) (om (.mul (k TXI) (k ZI)))) (by simp [localC])) hr
  have h2 := sat hsat (mem_local (c := .mul (k CBO) (k TXI)) (by simp [localC])) hr
  have h3 := sat hsat (mem_local (c := .mul (k CBI) (om (k CBO))) (by simp [localC])) hr
  have h4 := sat hsat (mem_local (c := .mul (k KI) (k CBO)) (by simp [localC])) hr
  simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_k hr] at h1 h2 h3 h4
  have hiff : M CBO r = 1 ↔ M TXI r = 0 := by
    constructor
    · intro h; rw [h, one_mul] at h2; exact h2
    · intro h; rw [h, zero_mul] at h1; linear_combination h1
  have hb : M CBO r = 0 ∨ M CBO r = 1 := by
    by_cases ht : M TXI r = 0
    · exact Or.inr (hiff.mpr ht)
    · exact Or.inl ((mul_eq_zero.mp h2).resolve_right ht)
  refine ⟨hiff, hb, fun h => ?_, fun h => ?_⟩
  · rw [h, one_mul] at h3; linear_combination -h3
  · rw [h, one_mul] at h4; exact h4

/-- **The record index:** `J` counts the non-coinbase inputs before the row. -/
theorem j_spec : ∀ r < n, M J r = ∑ q ∈ Finset.range r, M KI q := by
  intro r
  induction r with
  | zero =>
    intro hr
    have := sat hsat (mem_local (c := .mul first (k J)) (by simp [localC])) hr
    simp only [Expr.eval, ev_first hr, if_pos rfl, one_mul, ev_k hr] at this
    simpa using this
  | succ r ih =>
    intro hr
    have := sat hsat (mem_local (c := .mul notFirst (.sub (k J) (.add (kp J) (kp KI)))) (by simp [localC])) hr
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
      sub_zero, one_mul, ev_k hr, ev_kp hr] at this
    rw [Finset.sum_range_succ, ← ih (by omega)]
    linear_combination this

/-- **The output index:** one more than the previous row's if that was an output, else 0. -/
theorem vout_spec {r : ℕ} (hr : r + 1 < n) (hko : M KO (r + 1) = 1) :
    M VOUT (r + 1) = M KO r * (M VOUT r + 1) ∧ M VLO (r + 1) + 65536 * M VHI (r + 1) = M VOUT (r + 1) := by
  have h1 := sat hsat (mem_local (c := .mul (k KO) (.sub (k VOUT) (.mul (kp KO) (.add (kp VOUT) one)))) (by simp [localC])) hr
  have h2 := sat hsat (mem_local (c := .mul (k KO) (.sub (.add (k VLO) (.mul (cst 65536) (k VHI))) (k VOUT))) (by simp [localC])) hr
  simp only [one, Expr.eval, eval_cst, Nat.cast_one, ev_k hr, ev_kp hr, hko, one_mul] at h1 h2
  exact ⟨sub_eq_zero.mp h1, by linear_combination h2⟩

omit hsat in
theorem ev_kp0 {c : ℕ} (hn : 0 < n) : (kp c).eval n preCols pub M 0 = M c (n - 1) := by
  simp only [kp, eval_col]
  congr 1
  unfold wrap
  have : ((0 : ℕ) : ℤ) + -1 = ((n - 1 : ℕ) : ℤ) - (n : ℤ) := by push_cast [show 1 ≤ n by omega]; ring
  rw [this, Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _),
    Int.emod_eq_of_lt (by omega) (by omega)]
  simp

theorem vout_first (hn : 0 < n) (hko : M KO 0 = 1) : M VOUT 0 = 0 := by
  obtain ⟨e, hen, hon⟩ := on_prefix hsat hn
  have hoff : onV M (n - 1) = 0 := by
    rcases on_bool hsat (show n - 1 < n by omega) with h | h
    · exact h
    · exact absurd ((hon _ (by omega)).mp h) (by omega)
  have hko' : M KO (n - 1) = 0 := by
    rcases kinds hsat (show n - 1 < n by omega) with h | h | h | h <;> simp_all
  have h1 := sat hsat (mem_local (c := .mul (k KO) (.sub (k VOUT) (.mul (kp KO) (.add (kp VOUT) one)))) (by simp [localC])) hn
  simp only [one, Expr.eval, eval_cst, Nat.cast_one, ev_k hn, ev_kp0 hn, hko, hko', one_mul, zero_mul, sub_zero] at h1
  exact h1

/-- Two byte limbs. -/
def pairV (M : ℕ → ℕ → F) (a b r : ℕ) : F := M a r + 256 * M b r

omit hsat in
theorem ev_pair {a b r : ℕ} (hr : r < n) : (pair a b).eval n preCols pub M r = pairV M a b r := by
  simp [pair, Expr.eval, ev_k hr, eval_cst, pairV]

/-- **An output's tuple fields.** Code `2·height + CBO`, creation index the transaction's, byte length the
token's, the low index limb from two bytes, the code's low limb from two bytes. -/
theorem out_spec {r : ℕ} (hr : r < n) (hko : M KO r = 1) :
    M CLO r + 65536 * M CHI r = 2 * pub 2 + M CBO r ∧ M CTX r = M TXI r ∧ M SLEN r = M LEN r ∧
      M VLO r = pairV M (VB 0) (VB 1) r ∧ M CLO r = pairV M (CB 0) (CB 1) r := by
  have h1 := sat hsat (mem_local (c := .mul (k KO) (.sub (.add (k CLO) (.mul (cst 65536) (k CHI))) (.add (.mul (cst 2) height) (k CBO)))) (by simp [localC])) hr
  have h2 := sat hsat (mem_local (c := .mul (k KO) (.sub (k CTX) (k TXI))) (by simp [localC])) hr
  have h3 := sat hsat (mem_local (c := .mul (k KO) (.sub (k SLEN) (k LEN))) (by simp [localC])) hr
  have h4 := sat hsat (mem_local (c := .mul (k KO) (.sub (k VLO) (pair (VB 0) (VB 1)))) (by simp [localC])) hr
  have h5 := sat hsat (mem_local (c := .mul (k KO) (.sub (k CLO) (pair (CB 0) (CB 1)))) (by simp [localC])) hr
  simp only [height, Expr.eval, eval_cst, Nat.cast_ofNat, ev_k hr, ev_pair hr, hko, one_mul] at h1 h2 h3 h4 h5
  refine ⟨by linear_combination h1, sub_eq_zero.mp h2, sub_eq_zero.mp h3, sub_eq_zero.mp h4, sub_eq_zero.mp h5⟩

/-- **An input's tuple fields.** Code `2·HC + CBC` with `HC` three bytes; the claimed creation is before
the spending transaction (same height: an earlier transaction, by a three-byte difference; else an
earlier height); a coinbase coin is at least 100 blocks old; the index limbs and the txid limbs are the
prevout bytes. -/
theorem in_spec {r : ℕ} (hr : r < n) (hki : M KI r = 1) :
    M CLO r + 65536 * M CHI r = 2 * M HC r + M CBC r ∧ M HC r = b3V M HB r ∧
      (M ORD r = 0 → M HC r = pub 2 ∧ b3V M OB r = M TXI r - 1 - M CTX r) ∧
      (M ORD r = 1 → b3V M OB r = pub 2 - 1 - M HC r) ∧
      (M CBC r = 1 → b3V M MB r = pub 2 - M HC r - 100) ∧
      M VLO r = pairV M (PB 32) (PB 33) r ∧ M VHI r = pairV M (PB 34) (PB 35) r ∧
      ∀ i < 16, M (TLB i) r = (prevLimb i).eval n preCols pub M r := by
  have h1 := sat hsat (mem_local (c := .mul (k KI) (.sub (.add (k CLO) (.mul (cst 65536) (k CHI))) (.add (.mul (cst 2) (k HC)) (k CBC)))) (by simp [localC])) hr
  have h2 := sat hsat (mem_local (c := .mul (k KI) (.sub (k HC) (b3 HB))) (by simp [localC])) hr
  have h3 := sat hsat (mem_local (c := .mul (k KI) (.mul (om (k ORD)) (.sub (k HC) height))) (by simp [localC])) hr
  have h4 := sat hsat (mem_local (c := .mul (k KI) (.sub (b3 OB) (.add (.mul (k ORD) (.sub (.sub height one) (k HC)))
      (.mul (om (k ORD)) (.sub (.sub (k TXI) one) (k CTX)))))) (by simp [localC])) hr
  have h5 := sat hsat (mem_local (c := .mul (k KI) (.mul (k CBC) (.sub (.sub (.sub height (k HC)) (cst 100)) (b3 MB)))) (by simp [localC])) hr
  have h6 := sat hsat (mem_local (c := .mul (k KI) (.sub (k VLO) (pair (PB 32) (PB 33)))) (by simp [localC])) hr
  have h7 := sat hsat (mem_local (c := .mul (k KI) (.sub (k VHI) (pair (PB 34) (PB 35)))) (by simp [localC])) hr
  simp only [height, om, one, Expr.eval, eval_cst, Nat.cast_one, Nat.cast_ofNat, ev_k hr, ev_pair hr, ev_b3 hr, hki, one_mul] at h1 h2 h3 h4 h5 h6 h7
  refine ⟨by linear_combination h1, sub_eq_zero.mp h2, fun ho => ?_, fun ho => ?_, fun hc => ?_,
    sub_eq_zero.mp h6, sub_eq_zero.mp h7, fun i hi => ?_⟩
  · rw [ho, sub_zero, one_mul] at h3; rw [ho] at h4
    refine ⟨sub_eq_zero.mp h3, ?_⟩; linear_combination h4
  · rw [ho] at h4; linear_combination h4
  · rw [hc, one_mul] at h5; linear_combination -h5
  · have := sat hsat (mem_local (c := .mul (k KI) (.sub (k (TLB i)) (prevLimb i)))
      (by simp only [localC, List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨i, hi, rfl⟩)) hr
    simp only [Expr.eval, ev_k hr, hki, one_mul] at this
    exact sub_eq_zero.mp this

/-- **Unspendable.** With the script's first byte `SB` and length `SVAL`: `ZS = [SVAL = 0]`,
`U6A = [SB = 0x6a]`, `BIG = 1` for a length over 10,000 and 0 for at most 10,000 (the three-byte
`GB` range checks decide which), and `UNSP` is their combination. -/
theorem unsp_spec {r : ℕ} (hr : r < n) (hko : M KO r = 1) :
    (M ZS r = 1 ↔ M SVAL r = 0) ∧ (M U6A r = 1 ↔ M SB r = 0x6a) ∧
      (M BIG r = 1 → b3V M GB r = M SVAL r - 10001) ∧ (M BIG r = 0 → b3V M GB r = 10000 - M SVAL r) ∧
      M UNSP r = M U6A r * (1 - M ZS r) + M BIG r - M U6A r * (1 - M ZS r) * M BIG r := by
  have z1 := sat hsat (mem_local (c := .sub (k ZS) (om (.mul (k SVAL) (k SINV)))) (by simp [localC])) hr
  have z2 := sat hsat (mem_local (c := .mul (k ZS) (k SVAL)) (by simp [localC])) hr
  have u1 := sat hsat (mem_local (c := .sub (om (k U6A)) (.mul (.sub (k SB) (cst 0x6a)) (k INVB))) (by simp [localC])) hr
  have u2 := sat hsat (mem_local (c := .mul (k U6A) (.sub (k SB) (cst 0x6a))) (by simp [localC])) hr
  have u3 := sat hsat (mem_local (c := .sub (k U6Z) (.mul (k U6A) (om (k ZS)))) (by simp [localC])) hr
  have g := sat hsat (mem_local (c := .mul (k KO) (.sub (b3 GB) (.add (.mul (k BIG) (.sub (k SVAL) (cst 10001))) (.mul (om (k BIG)) (.sub (cst 10000) (k SVAL)))))) (by simp [localC])) hr
  have un := sat hsat (mem_local (c := .sub (k UNSP) (.sub (.add (k U6Z) (k BIG)) (.mul (k U6Z) (k BIG)))) (by simp [localC])) hr
  simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, Nat.cast_ofNat, ev_k hr, ev_b3 hr, hko, one_mul] at z1 z2 u1 u2 u3 g un
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩, fun h => ?_, fun h => ?_, ?_⟩
  · rw [h, one_mul] at z2; exact z2
  · rw [h, zero_mul] at z1; linear_combination z1
  · rw [h, one_mul] at u2; exact sub_eq_zero.mp u2
  · rw [h] at u1; linear_combination -u1
  · rw [h] at g; linear_combination g
  · rw [h] at g; linear_combination g
  · rw [sub_eq_zero.mp un, sub_eq_zero.mp u3]

/-- **The multiplicity:** `KO·(1 − UNSP)·(1 − CBO·lost) − KI`. -/
theorem mm_spec {r : ℕ} (hr : r < n) :
    M MM r = M KO r * ((1 - M UNSP r) * (1 - M CBO r * pub PUB_LOST)) - M KI r := by
  have := sat hsat (mem_local (c := .sub (k MM) (.sub (.mul (k KO) (.mul (om (k UNSP)) (om (.mul (k CBO) (.pub PUB_LOST))))) (k KI))) (by simp [localC])) hr
  simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_k hr] at this
  linear_combination this

/-- **The input count** (public) is the number of non-coinbase inputs. -/
theorem nin_spec (hn : 0 < n) : pub PUB_NIN = ∑ q ∈ Finset.range n, M KI q := by
  obtain ⟨e, hen, hon⟩ := on_prefix hsat hn
  have off : ∀ r < n, e ≤ r → M KI r = 0 := by
    intro r hr her
    rcases kinds hsat hr with h | h | h | h
    · exact absurd ((hon r hr).mp h.2.2.2) (by omega)
    · exact absurd ((hon r hr).mp h.2.2.2) (by omega)
    · exact absurd ((hon r hr).mp h.2.2.2) (by omega)
    · exact h.2.1
  have hsum : ∑ q ∈ Finset.range n, M KI q = ∑ q ∈ Finset.range e, M KI q := by
    rw [← Finset.sum_range_add_sum_Ico _ (show e ≤ n by omega)]
    rw [Finset.sum_eq_zero (fun q hq => off q (Finset.mem_Ico.mp hq).2 (Finset.mem_Ico.mp hq).1), add_zero]
  rw [hsum]
  by_cases he : e = 0
  · subst he
    have := sat hsat (mem_local (c := .mul first (.mul (om on) (.pub PUB_NIN))) (by simp [localC])) hn
    have h0 : onV M 0 = 0 := by
      rcases on_bool hsat hn with h | h
      · exact h
      · exact absurd ((hon 0 hn).mp h) (by omega)
    simp only [om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hn, if_pos rfl, one_mul, ev_on hn, h0, sub_zero] at this
    simpa using this
  · -- the last row in use: `J + KI = NIN`
    have hl : e - 1 < n := by omega
    have := sat hsat (mem_local (c := .mul lastOn (.sub (.add (k J) (k KI)) (.pub PUB_NIN))) (by simp [localC])) hl
    have hon1 : onV M (e - 1) = 1 := (hon _ hl).mpr (by omega)
    have hon2 : onn.eval n preCols pub M (e - 1) = 0 := by
      have hr1 : e - 1 + 1 < n := by omega
      have : onV M (e - 1 + 1) = 0 := by
        rcases on_bool hsat hr1 with h | h
        · exact h
        · exact absurd ((hon _ hr1).mp h) (by omega)
      simpa [onn, Expr.eval, ev_kn hr1, onV] using this
    simp only [lastOn, Expr.eval, ev_notLast hl, show e - 1 + 1 < n by omega, if_true, ev_on hl, hon1, hon2, sub_zero,
      one_mul, ev_k hl] at this
    rw [j_spec hsat _ hl] at this
    rw [show e = e - 1 + 1 by omega, Finset.sum_range_succ]
    linear_combination -this

/-- The fingerprint segment's id: the start for an output, the record index for an input. -/
theorem sidc_spec {r : ℕ} (hr : r < n) : M SIDC r = M KO r * M START r + M KI r * M J r := by
  have := sat hsat (mem_local (c := .sub (k SIDC) (.add (.mul (k KO) (k START)) (.mul (k KI) (k J)))) (by simp [localC])) hr
  simp only [Expr.eval, ev_k hr] at this
  linear_combination this

/-! ### The running sum -/

open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub emb_zero)
open StarkedAir.Block.ExtSum (QE)
open StarkedAir.Block.ExtSum.QE

omit hsat in
theorem fracC_eq : fracC = RunSum.fracC FC PUB_Z phi mE := rfl
omit hsat in
theorem zeroC_eq : zeroC = RunSum.zeroC FC mE := rfl
omit hsat in
theorem accC_eq : accC = RunSum.accC FC ACC := rfl
omit hsat in
theorem lastC_eq : lastC = RunSum.lastC ACC PUB_S := rfl

theorem runsum_sat : ∀ r < n, ∀ c ∈ RunSum.fracC FC PUB_Z phi mE ++ RunSum.zeroC FC mE ++ RunSum.accC FC ACC ++
    RunSum.lastC ACC PUB_S, c.eval n RunSum.preCols pub M r = 0 := by
  intro r hr c hc
  have : c ∈ constraints := by
    rw [← fracC_eq, ← zeroC_eq, ← accC_eq, ← lastC_eq] at hc
    simp only [constraints, List.mem_append] at hc ⊢
    tauto
  exact hsat r hr c this

/-- The fingerprint `φ = Σⱼ αⱼ tⱼ` of a row. -/
noncomputable def phiQ (pub : ℕ → F) (M : ℕ → ℕ → F) (n r : ℕ) : QM :=
  ((List.range W).map fun j => RunSum.pQ pub (PUB_ALPHA j) * emb ((tuple.getD j (cst 0)).eval n RunSum.preCols pub M r)).sum

omit hsat in
theorem ev_phi (r : ℕ) : toQ (phi.ev n RunSum.preCols pub M r) = phiQ pub M n r := by
  have gen : ∀ (l : List ℕ) (a : QE), toQ ((l.foldl (fun acc j => acc.add ((pubQ (PUB_ALPHA j)).mul (base (tuple.getD j (cst 0))))) a).ev
      n RunSum.preCols pub M r) = toQ (a.ev n RunSum.preCols pub M r) +
        (l.map fun j => RunSum.pQ pub (PUB_ALPHA j) * emb ((tuple.getD j (cst 0)).eval n RunSum.preCols pub M r)).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons j l ih =>
      intro a
      rw [List.foldl_cons, ih, ev_add, toQ_add, ev_mul, toQ_mul, toQ_ev_base, RunSum.ev_pubQ, List.map_cons, List.sum_cons,
        add_assoc]
  show toQ (((List.range W).foldl _ (base (cst 0))).ev n RunSum.preCols pub M r) = _
  rw [gen, toQ_ev_base]
  simp only [eval_cst, Nat.cast_zero, emb_zero, zero_add, phiQ]

/-- **The coin events' running sum.** The public partial sum is the rows' fractions summed; each row's
fraction `f` has `(z − φ)·f = MM`, and is zero when `MM = 0`. -/
theorem coin_runsum (hn : 0 < n) :
    RunSum.pQ pub PUB_S = ∑ r ∈ Finset.range n, RunSum.cQ M FC r ∧
    ∀ r < n, (RunSum.pQ pub PUB_Z - phiQ pub M n r) * RunSum.cQ M FC r = emb (M MM r) ∧
      (M MM r = 0 → RunSum.cQ M FC r = 0) := by
  obtain ⟨hs, hrow⟩ := RunSum.runsum_sound (runsum_sat hsat) hn
  refine ⟨hs, fun r hr => ?_⟩
  have hm : mE.eval n RunSum.preCols pub M r = M MM r := by simp [mE, k, eval_col, wrap_zero hr]
  obtain ⟨h1, h2⟩ := hrow r hr
  rw [ev_phi, hm] at h1
  rw [hm] at h2
  exact ⟨h1, h2⟩

end Rows

end StarkedAir.Block.Coin
