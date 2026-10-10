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

/-- **The check lookups' use multiplicities** are `−1` or `0`: byte slots, the auxiliary read, range
slots and the context use (`chkLookups` entries other than the three yields 22, 23, 25). -/
theorem chk_use_mult {r : ℕ} (hr : r < n) {j : ℕ} (hj : j < 26) (hy : j ≠ 22 ∧ j ≠ 23 ∧ j ≠ 25) :
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
  have h24 : j = 24 := by omega
  subst h24
  rw [show (chkLookups.getD 24 ⟨0, .const 0, []⟩).mult = .neg first from rfl]
  simp only [Expr.eval, ev_first hr]
  split_ifs <;> simp

end Chk

end StarkedAir.Block.Fields
