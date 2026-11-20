/-
**Per-transaction checks, row facts (M3a.5b).** Facts about one row of the fields component's check
columns (from column 118): the multiplicities of its new lookups, and what each kind of row establishes.
-/
import StarkedAir.Block.TxIndex

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)

theorem mem_chk {c : Expr} (h : c ∈ chkC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

theorem mem_sig {c : Expr} (h : c ∈ sigC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inr h

section Chk

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem chk_bool {e : ℕ} (hc : boolC (k e) ∈ chkC) {r : ℕ} (hr : r < n) : M e r = 0 ∨ M e r = 1 :=
  bool_of hsat (mem_chk hc) hr

theorem chk_defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ chkC) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r :=
  defn hsat (mem_chk h) hr

theorem kind_zero_of {r : ℕ} (hr : r < n) {a b : ℕ} (ha : a < 9) (hb : b < 9) (hab : a ≠ b) (h : M a r ≠ 0) :
    M b r = 0 := by
  rcases kind_bool hsat (c := a) (by rw [kinds_range]; exact List.mem_range.mpr ha) hr with h0 | h1
  · exact absurd h0 h
  · exact kind_unique hsat hr ha hb hab h1

/-- At most one of three kinds. -/
theorem kinds3 {r : ℕ} (hr : r < n) {a b c : ℕ} (ha : a < 9) (hb : b < 9) (hc : c < 9) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : M a r + M b r + M c r = 0 ∨ M a r + M b r + M c r = 1 := by
  obtain ⟨d, hd, h1⟩ := kind_exists hsat hr
  have z : ∀ x < 9, x ≠ d → M x r = 0 := fun x hx hne => kind_unique hsat hr hd hx (Ne.symm hne) h1
  by_cases e1 : d = a
  · subst e1; rw [h1, z b hb (Ne.symm hab), z c hc (Ne.symm hac)]; simp
  by_cases e2 : d = b
  · subst e2; rw [h1, z a ha (fun h => e1 h.symm), z c hc (Ne.symm hbc)]; simp
  by_cases e3 : d = c
  · subst e3; rw [h1, z a ha (fun h => e1 h.symm), z b hb (fun h => e2 h.symm)]; simp
  rw [z a ha (fun h => e1 h.symm), z b hb (fun h => e2 h.symm), z c hc (fun h => e3 h.symm)]; simp

theorem one_add_one_ne' : (1 : F) + 1 ≠ 0 := one_add_one_ne

/-- The auxiliary read's multiplicity is `−(GIN + MMB)`, with `GIN + MMB ∈ {0, 1}`: `MMB` rows are
output rows, `GIN` rows input rows. -/
theorem gin_mmb {r : ℕ} (hr : r < n) : M GIN r + M MMB r = 0 ∨ M GIN r + M MMB r = 1 := by
  have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr
  simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hgin
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
  have kin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
  have mmb := chk_bool hsat (e := MMB) (by simp [chkC, commitC]) hr
  have mml := chk_bool hsat (e := MML) (by simp [chkC, commitC]) hr
  rcases mmb with h0 | h1
  · rw [h0, add_zero, hgin]
    rcases zt with a | a <;> rcases kin with b | b <;> simp [a, b]
  · -- an MMB row is an output row, so not an input row
    have hreq := sat hsat (mem_chk (c := .sub (.add (k MML) (k MMB)) (k REQ)) (by simp [chkC, commitC])) hr
    simp only [Expr.eval, ev_k hr, sub_eq_zero] at hreq
    have hreq' := chk_defn hsat (a := REQ) (e := .mul (k REQC) (.add (oneMinus (k HASC)) (k AFT)))
      (by simp [chkC, commitC]) hr
    have hreqc := chk_defn hsat (a := REQC) (e := .mul (k G0) (oneMinus (k ISC))) (by simp [chkC, commitC]) hr
    have hg0 := chk_defn hsat (a := G0) (e := .mul (k K_OUT) (.mul (k ZT) (.pub 6))) (by simp [chkC, commitC]) hr
    simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hreq' hreqc hg0
    have hne : M REQ r ≠ 0 := by
      rw [← hreq, h1]; rcases mml with a | a <;> simp [a, one_add_one_ne]
    have hout : M K_OUT r ≠ 0 := by
      intro h0; apply hne; rw [hreq', hreqc, hg0, h0]; ring
    have hin : M K_IN r = 0 := kind_zero_of hsat hr (a := K_OUT) (b := K_IN) (by simp [K_OUT]) (by simp [K_IN])
      (by simp [K_OUT, K_IN]) hout
    rw [h1, hgin, hin]; simp

omit hsat in
theorem chk_mult_byte {j : ℕ} (hj : j < 4) :
    (chkLookups.getD j ⟨0, .const 0, []⟩).mult = .neg (.add (k K_OUT) (.add (k K_LOCK) (k K_IN))) := by
  interval_cases j <;> rfl

omit hsat in
theorem chk_mult_byte2 {j : ℕ} (hj4 : 4 ≤ j) (hj : j < 8) : (chkLookups.getD j ⟨0, .const 0, []⟩).mult = .neg (k K_OUT) := by
  interval_cases j <;> rfl

omit hsat in
theorem chk_mult_rg {j : ℕ} (hj9 : 9 ≤ j) (hj : j < 22) : (chkLookups.getD j ⟨0, .const 0, []⟩).mult = .neg one := by
  interval_cases j <;> rfl

/-- The redeem script's read flag `RDF = NZI · CP · SPO · ZLN` is 0 or 1 (step 3). -/
theorem rdf_bool {r : ℕ} (hr : r < n) : M RDF r = 0 ∨ M RDF r = 1 := by
  have hb : ∀ {x y : F}, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → (x * y = 0 ∨ x * y = 1) := by
    intro x y hx hy; rcases hx with h | h <;> rcases hy with h' | h' <;> simp [h, h']
  have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr
  have hnzi := defn hsat (mem_sig (c := .sub (k NZI) (.mul (k GIN) (oneMinus (k ZV)))) (by simp [sigC])) hr
  have har0 := defn hsat (mem_sig (c := .sub (k AR0) (.mul (k NZI) (.mul (k CP) (k SPO)))) (by simp [sigC])) hr
  have hrdf := defn hsat (mem_sig (c := .sub (k RDF) (.mul (k AR0) (k ZLN))) (by simp [sigC])) hr
  simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hgin hnzi har0 hrdf
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
  have zv := chk_bool hsat (e := ZV) (by simp [chkC, totalsC]) hr
  have kin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
  have cp := bool_of hsat (mem_sig (c := boolC (k CP)) (by simp [sigC])) hr
  have spo := bool_of hsat (mem_sig (c := boolC (k SPO)) (by simp [sigC])) hr
  have zln := bool_of hsat (mem_sig (c := boolC (k ZLN)) (by simp [sigC, isZero])) hr
  have om : ∀ {x : F}, (x = 0 ∨ x = 1) → (1 - x = 0 ∨ 1 - x = 1) := by
    intro x hx; rcases hx with h | h <;> simp [h]
  rw [hrdf, har0, hnzi, hgin]
  exact hb (hb (hb (hb kin (om zt)) (om zv)) (hb cp spo)) zln

/-- **A redeem script to walk** (step 3: `ARQ ≠ 0`) is 1 to `2^24 − 1` bytes long, given that the range
slots hold bytes. -/
theorem arq_val {r : ℕ} (hr : r < n) (hrg : ∀ j < 13, (M (RG j) r).val < 256) (h : M ARQ r ≠ 0) :
    1 ≤ (M SRL r).val ∧ (M SRL r).val < 2 ^ 24 := by
  have c1 := sat hsat (mem_sig (c := .mul (k ARQ) (.sub (k SRL) (le3 (rg 4) (rg 5) (rg 6)))) (by simp [sigC])) hr
  simp only [Expr.eval, ev_k hr, le3, le2, rg, c, eval_cst] at c1
  have e : M SRL r = (((M (RG 4) r).val + 256 * (M (RG 5) r).val + 65536 * (M (RG 6) r).val : ℕ) : F) := by
    push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rcases mul_eq_zero.mp c1 with h0 | h1
    · exact absurd h0 h
    · linear_combination h1
  have h4 := hrg 4 (by norm_num); have h5 := hrg 5 (by norm_num); have h6 := hrg 6 (by norm_num)
  have hv := val_lt_of_eq_cast e (lt_P (by omega))
  refine ⟨?_, by omega⟩
  by_contra hc
  have h0 : M SRL r = 0 := (ZMod.val_eq_zero _).mp (by omega)
  have z2 := sat hsat (mem_sig (c := .mul (oneMinus (k ZRL)) (.sub (.mul (k SRL) (k INVRL)) one)) (by simp [sigC, isZero])) hr
  have ha := defn hsat (mem_sig (c := .sub (k ARQ) (.mul (k AR0) (oneMinus (k ZRL)))) (by simp [sigC])) hr
  simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one, h0, zero_mul, zero_sub, mul_neg, mul_one,
    neg_eq_zero] at z2 ha
  apply h; rw [ha, z2, mul_zero]

/-- **The P2WPKH count is a bounded natural** (step 3): each row adds `GIN · CW20 + RW20`, two bits. -/
theorem w20_nat : ∀ r < n, ∃ w : ℕ, w ≤ 2 * (r + 1) ∧ M W20S r = (w : F) := by
  have term : ∀ r < n, ∃ t : ℕ, t ≤ 2 ∧ M GIN r * M CW20 r + M RW20 r = (t : F) := by
    intro r hr
    have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr
    simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hgin
    have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
    have kin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
    have cw := bool_of hsat (mem_sig (c := boolC (k CW20)) (by simp [sigC])) hr
    have rw := bool_of hsat (mem_sig (c := boolC (k RW20)) (by simp [sigC])) hr
    have x01 : M GIN r * M CW20 r = 0 ∨ M GIN r * M CW20 r = 1 := by
      rw [hgin]
      rcases zt with a | a <;> rcases kin with b | b <;> rcases cw with d | d <;> simp [a, b, d]
    rcases x01 with x | x <;> rcases rw with e | e <;> rw [x, e]
    · exact ⟨0, by norm_num, by norm_num⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨1, by norm_num, by norm_num⟩
    · exact ⟨2, by norm_num, by norm_num⟩
  intro r
  induction r with
  | zero =>
    intro h0
    have c1 := sat hsat (mem_sig (c := .mul first (k W20S)) (by simp [sigC])) h0
    simp only [Expr.eval, ev_first h0, if_true, one_mul, ev_k h0] at c1
    exact ⟨0, by norm_num, by rw [c1]; simp⟩
  | succ r ih =>
    intro hr
    obtain ⟨w, hw, e⟩ := ih (by omega)
    obtain ⟨t, ht, et⟩ := term (r + 1) hr
    have c1 := sat hsat (mem_sig (c := .mul notFirst (.sub (.sub (.sub (k W20S) (kp W20S)) (.mul (k GIN) (k CW20)))
      (k RW20))) (by simp [sigC])) hr
    simp only [Expr.eval, ev_notFirst hr, one_mul, ev_k hr, ev_kp hr] at c1
    refine ⟨w + t, by omega, ?_⟩
    push_cast; rw [← e, ← et]; linear_combination c1

/-- **The check lookups' use multiplicities** are `−1` or `0`: byte slots, the auxiliary read, range
slots, the context use, the version bytes, the redeem script's two bytes and the witness request's use
(`chkLookups` entries other than the yields 22, 23, 25, 26, 27, 34, 35, 36). -/
theorem chk_use_mult {r : ℕ} (hr : r < n) {j : ℕ} (hj : j < 38)
    (hy : j ≠ 22 ∧ j ≠ 23 ∧ j ≠ 25 ∧ j ≠ 26 ∧ j ≠ 27 ∧ j ≠ 34 ∧ j ≠ 35 ∧ j ≠ 36) :
    (chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = -1 ∨
    (chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval n preCols pub M r = 0 := by
  have neg01 : ∀ {x : F}, x = 0 ∨ x = 1 → -x = -1 ∨ -x = 0 := fun h => by rcases h with h | h <;> simp [h]
  by_cases h4 : j < 4
  · rw [chk_mult_byte h4]
    simp only [Expr.eval, ev_k hr]
    have k3 := kinds3 hsat hr (a := K_OUT) (b := K_LOCK) (c := K_IN) (by simp [K_OUT]) (by simp [K_LOCK]) (by simp [K_IN])
      (by simp [K_OUT, K_LOCK]) (by simp [K_OUT, K_IN]) (by simp [K_LOCK, K_IN])
    exact neg01 (by simpa [add_assoc] using k3)
  by_cases h8 : j < 8
  · rw [chk_mult_byte2 (by omega) h8]
    simp only [Expr.eval, ev_k hr]
    exact neg01 (kind_bool hsat (c := K_OUT) (by simp [kinds, K_OUT]) hr)
  by_cases h9 : j = 8
  · subst h9
    rw [show (chkLookups.getD 8 ⟨0, .const 0, []⟩).mult = .neg (.add (k GIN) (k MMB)) from rfl]
    simp only [Expr.eval, ev_k hr]
    exact neg01 (gin_mmb hsat hr)
  by_cases h22 : j < 22
  · rw [chk_mult_rg (by omega) h22]; left; simp [Expr.eval, one, eval_cst]
  by_cases h37 : j = 37
  · subst h37
    rw [show (chkLookups.getD 37 ⟨0, .const 0, []⟩).mult = .neg (.mul (k K_WCNT) (k WS)) from rfl]
    simp only [Expr.eval, ev_k hr]
    have kw := kind_bool hsat (c := K_WCNT) (by simp [kinds, K_WCNT]) hr
    have ws := bool_of hsat (mem_sig (c := boolC (k WS)) (by simp [sigC])) hr
    rcases kw with a | a <;> rcases ws with b | b <;> simp [a, b]
  by_cases h32 : 32 ≤ j
  · have e : (chkLookups.getD j ⟨0, .const 0, []⟩).mult = .neg (k RDF) := by
      have : j = 32 ∨ j = 33 := by omega
      rcases this with rfl | rfl <;> rfl
    rw [e]
    simp only [Expr.eval, ev_k hr]
    exact neg01 (rdf_bool hsat hr)
  by_cases h26 : 28 ≤ j
  · have e : (chkLookups.getD j ⟨0, .const 0, []⟩).mult = .neg (k K_TXH) := by
      have h32 : j < 32 := by omega
      interval_cases j <;> rfl
    rw [e]
    simp only [Expr.eval, ev_k hr]
    exact neg01 (kind_bool hsat (c := K_TXH) (by simp [kinds, K_TXH]) hr)
  have h24 : j = 24 := by omega
  subst h24
  rw [show (chkLookups.getD 24 ⟨0, .const 0, []⟩).mult = .neg first from rfl]
  simp only [Expr.eval, ev_first hr]
  split_ifs <;> simp

end Chk

end StarkedAir.Block.Fields
