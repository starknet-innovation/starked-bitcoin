/-
**Script yields (M3a.5d).** The fields component yields `script(SSC, VAL)` for every non-empty input or
output script: the script's start and length. Row by row, the legacy sigops of the yielded scripts are
the tokens' (`tokSig`), and a yielded script is 1 to `MAXS` bytes long.
-/
import StarkedAir.Block.FieldsTotals

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)

/-- The script yield's multiplicity. -/
def smult (M : ℕ → ℕ → F) (r : ℕ) : F := (M K_IN r + M K_OUT r) * (1 - M ZV r)

section Scripts

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem zv_spec {r : ℕ} (hr : r < n) : (M ZV r = 0 ∨ M ZV r = 1) ∧ (M ZV r = 1 → M VAL r = 0) ∧
    (M ZV r = 0 → M VAL r ≠ 0) := by
  have hb := chk_bool hsat (e := ZV) (by simp [chkC, totalsC]) hr
  have h1 := sat hsat (mem_chk (c := .mul (k ZV) (k VAL)) (by simp [chkC, totalsC])) hr
  have h2 := sat hsat (mem_chk (c := .mul (oneMinus (k ZV)) (.sub (.mul (k VAL) (k INVV)) one)) (by simp [chkC, totalsC])) hr
  simp only [Expr.eval, ev_k hr, oneMinus, one, eval_cst, Nat.cast_one] at h1 h2
  refine ⟨hb, fun h => by rw [h, one_mul] at h1; exact h1, fun h hv => ?_⟩
  rw [h, hv, sub_zero, one_mul, zero_mul, zero_sub, neg_eq_zero] at h2; exact one_ne_zero h2

theorem smult01 {r : ℕ} (hr : r < n) : smult M r = 0 ∨ smult M r = 1 := by
  unfold smult
  have hin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
  have hout := kind_bool hsat (c := K_OUT) (by simp [kinds, K_OUT]) hr
  have hz := (zv_spec hsat hr).1
  rcases hin with a | a
  · rcases hout with b | b <;> rcases hz with c | c <;> simp [a, b, c]
  · rw [kind_unique hsat hr (a := K_IN) (b := K_OUT) (by simp [K_IN]) (by simp [K_OUT]) (by simp [K_IN, K_OUT]) a]
    rcases hz with c | c <;> simp [a, c]

end Scripts

section ScriptsTok

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

/-- A script row's start: `SSC = START + OFF + pref`. -/
theorem ssc_val {r : ℕ} (hr : r < m) {a : ℕ} (ha : a = K_IN ∨ a = K_OUT) (h1 : M a r = 1) :
    (M SSC r).val = (M START r).val + (if a = K_IN then 36 else 8) + prefOf M r := by
  have hrn : r < n := by omega
  have ha9 : a < 9 := by rcases ha with rfl | rfl <;> simp [K_IN, K_OUT]
  have e := chk_defn hsat (a := SSC) (e := .add (.add (k START) (k OFF)) pref) (by simp [chkC, totalsC]) hrn
  obtain ⟨hoff, -⟩ := kind_vals hsat hrn ha9 h1
  have ka := kinds_at hsat hrn ha9 h1
  have hlp : M K_LOCK r + M K_PAD r = 0 := by
    rw [ka K_LOCK (by simp [K_LOCK]), ka K_PAD (by simp [K_PAD])]
    rcases ha with rfl | rfl <;> simp [K_IN, K_OUT, K_LOCK, K_PAD]
  have pc := pref_cast hsat hrn
  rw [if_pos hlp] at pc
  have hpre : 1 ≤ prefOf M r ∧ prefOf M r ≤ 5 := by unfold prefOf; split_ifs <;> omega
  have hst := start_lt hsat hrn
  have hoffv : offN a (M SEG r).val = if a = K_IN then 36 else 8 := by
    rcases ha with rfl | rfl <;> simp [offN, K_IN, K_OUT, K_BLK, K_TXH]
  have hv : M SSC r = (((M START r).val + (if a = K_IN then 36 else 8) + prefOf M r : ℕ) : F) := by
    rw [e]
    simp only [Expr.eval, ev_k hrn, pref, eval_cst, hoff, hoffv]
    push_cast
    rw [pc, ZMod.natCast_zmod_val]
  rw [hv, ZMod.val_natCast_of_lt (lt_P (by split_ifs <;> omega))]

/-- **A row's yielded script's sigops are its token's.** -/
theorem script_term (hnp : ∀ r < m, M K_PAD r = 0) {r : ℕ} (hr : r < m) :
    (if smult M r = 1 then Spec.Block.sigOps (slice R (M SSC r).val (M VAL r).val) else 0) =
      Spec.Block.tokSig (tokOf M R r) := by
  have hrn : r < n := by omega
  obtain ⟨a, ha, h1⟩ := kind_exists hsat hrn
  have ka := kinds_at hsat hrn ha h1
  obtain ⟨hzb, hz1, -⟩ := zv_spec hsat hrn
  have hzero : ∀ (x : Spec.Block.Bytes) (hx : M ZV r = 1),
      Spec.Block.sigOps (slice R (M SSC r).val (M VAL r).val) = 0 := by
    intro _ hx; rw [hz1 hx]; simp [slice, Spec.Block.sigOps, Spec.Block.ops]
  by_cases hio : a = K_IN ∨ a = K_OUT
  · have hs := ssc_val hsat R hcs hmn hpad hfit hr hio h1
    have hm : smult M r = 1 - M ZV r := by
      unfold smult; rw [ka K_IN (by simp [K_IN]), ka K_OUT (by simp [K_OUT])]
      rcases hio with rfl | rfl <;> simp [K_IN, K_OUT]
    rcases hio with rfl | rfl
    · rw [tok_in hsat R hcs hmn hpad hfit hrn h1]
      simp only [Spec.Block.tokSig]
      rw [hm, hs]
      rcases hzb with z | z
      · simp [z]
      · rw [hz1 z]; simp [z, slice, Spec.Block.sigOps, Spec.Block.ops]
    · rw [tok_out hsat R hcs hmn hpad hfit hrn h1]
      simp only [Spec.Block.tokSig]
      rw [hm, hs]
      rcases hzb with z | z
      · simp [z, K_OUT, K_IN]
      · rw [hz1 z]; simp [z, slice, Spec.Block.sigOps, Spec.Block.ops]
  · have hm : smult M r = 0 := by
      unfold smult; rw [ka K_IN (by simp [K_IN]), ka K_OUT (by simp [K_OUT])]
      push Not at hio; simp [Ne.symm hio.1, Ne.symm hio.2]
    rw [hm, if_neg zero_ne_one]
    push Not at hio
    interval_cases a
    · rw [tok_blk hsat R hcs hmn hpad hfit hrn h1]; rfl
    · rw [tok_txh hsat R hcs hmn hpad hfit hrn h1]; rfl
    · exact absurd rfl hio.1
    · rw [tok_nout hsat R hcs hmn hpad hfit hrn h1]; rfl
    · exact absurd rfl hio.2
    · rw [tok_wcnt hsat R hcs hmn hpad hfit hrn h1]; rfl
    · rw [tok_witem hsat R hcs hmn hpad hfit hrn h1]; rfl
    · rw [tok_lock hsat R hcs hmn hpad hfit hrn h1]; rfl
    · exfalso; have := hnp r hr; simp only [K_PAD] at this; rw [this] at h1; exact zero_ne_one h1

/-- No script yield on padding rows. -/
theorem script_pad {r : ℕ} (hr : r < n) (hm : m ≤ r) : smult M r = 0 := by
  have hp := hpad r hr hm
  have ka := kinds_at hsat hr (a := K_PAD) (by simp [K_PAD]) hp
  unfold smult; rw [ka K_IN (by simp [K_IN]), ka K_OUT (by simp [K_OUT])]; simp [K_IN, K_OUT, K_PAD]

/-- **A yielded script** is 1 to `MAXS` bytes long. -/
theorem script_val {r : ℕ} (hr : r < n) (h : smult M r ≠ 0) : 1 ≤ (M VAL r).val ∧ (M VAL r).val ≤ MAXS := by
  have hrm : r < m := by
    by_contra hc; exact h (script_pad hsat R hcs hmn hpad hfit hr (by omega))
  obtain ⟨hzb, -, hz0⟩ := zv_spec hsat hr
  have hz : M ZV r = 0 := by
    rcases hzb with z | z
    · exact z
    · exfalso; apply h; unfold smult; rw [z, sub_self, mul_zero]
  have hio : M K_IN r = 1 ∨ M K_OUT r = 1 := by
    rcases kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr with a | a
    · rcases kind_bool hsat (c := K_OUT) (by simp [kinds, K_OUT]) hr with b | b
      · exfalso; apply h; unfold smult; rw [a, b]; ring
      · exact Or.inr b
    · exact Or.inl a
  have hv0 : M VAL r ≠ 0 := hz0 hz
  have hle : (M VAL r).val ≤ MAXS := by
    rcases hio with g | g
    · exact (row_info hsat R hcs hmn hpad hfit hrm (a := K_IN) (by simp [K_IN]) g (by simp [K_IN, K_LOCK])
        (by simp [K_IN, K_PAD])).1
    · exact (row_info hsat R hcs hmn hpad hfit hrm (a := K_OUT) (by simp [K_OUT]) g (by simp [K_OUT, K_LOCK])
        (by simp [K_OUT, K_PAD])).1
  refine ⟨?_, hle⟩
  by_contra hc
  exact hv0 ((ZMod.val_eq_zero _).mp (by omega))

end ScriptsTok

end StarkedAir.Block.Fields
