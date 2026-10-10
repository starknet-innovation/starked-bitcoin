/-
**Block context (M3a.5c), row facts.** In a satisfied `block_ctx` trace with at least 256 rows: the block
constants are constant; each role row's constraints, with the role's preprocessed values.
-/
import StarkedAir.Block.Ctx
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.Ctx

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

section Rows

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by
  simp [k, eval_col, wrap_zero hr]

omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

omit hsat in
theorem ev_p {i r : ℕ} (hr : r < n) : (p i).eval n preCols pub M r = (preCols.getD i (.periodic [0])).eval n r := by
  simp [p, pre, Expr.eval, wrap_zero hr]

omit hsat in
theorem ev_tab {i : ℕ} {g : Role → ℕ} (hi : preCols.getD i (.periodic [0]) = tabR g) {r : ℕ} (hr : r < n) :
    (p i).eval n preCols pub M r = ((g (role (r % 256)) : ℕ) : F) := by
  rw [ev_p hr, hi]
  simp [tabR, PreCol.eval, List.getElem?_range (Nat.mod_lt r (by norm_num : 0 < 256))]

omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : (p P_FIRST).eval n preCols pub M r = if r = 0 then 1 else 0 := by
  rw [ev_p hr]; simp [preCols, P_FIRST, PreCol.eval]

omit hsat in
theorem ev_notFirst {r : ℕ} (hr : r + 1 < n) : notFirst.eval n preCols pub M (r + 1) = 1 := by
  simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one]
  rw [ev_first (by omega)]; simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

/-- **Block constants** are constant. -/
theorem const_eq {X : ℕ} (hX : X ∈ consts) : ∀ r < n, M X r = M X 0 := by
  intro r hr
  induction r with
  | zero => rfl
  | succ r ih =>
    have hm : Expr.mul notFirst (.sub (k X) (kp X)) ∈ consts.map (fun x => .mul notFirst (.sub (k x) (kp x))) :=
      List.mem_map.mpr ⟨X, hX, rfl⟩
    have := sat hsat (c := .mul notFirst (.sub (k X) (kp X))) (by simp only [constraints, List.mem_append]; tauto) hr
    simp only [Expr.eval, ev_notFirst hr, ev_k hr, ev_kp hr, one_mul, sub_eq_zero] at this
    rw [this, ih (by omega)]

theorem bool_of {c : ℕ} (hc : boolC (k c) ∈ constraints) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat hc hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- The role of row `r` as field values. -/
def rv (g : Role → ℕ) (r : ℕ) : F := ((g (role (r % 256)) : ℕ) : F)

omit hsat in
theorem ev_role {i : ℕ} {g : Role → ℕ} (hi : preCols.getD i (.periodic [0]) = tabR g) {r : ℕ} (hr : r < n) :
    (p i).eval n preCols pub M r = rv g r := ev_tab hi hr

/-- **The row equations**, with the row's role. -/
theorem row_eqs {r : ℕ} (hr : r < n) :
    M ADDR r = (rv (fun x => bn (decide (x.base = 2))) r + rv (fun x => bn (decide (x.base = 3))) r) *
        (M A0 r + 2 * M SEG0 r) + rv (fun x => bn (decide (x.base = 4))) r * M W0 r +
        rv (fun x => bn (decide (x.base = 5))) r * M CPOS r + rv (·.off) r ∧
    M ACTR r = rv (fun x => bn (decide (x.base = 2))) r + rv (fun x => bn (decide (x.base = 1))) r +
        rv (fun x => bn (decide (x.base = 3))) r * pub 4 +
        (rv (fun x => bn (decide (x.base = 4))) r + rv (fun x => bn (decide (x.base = 5))) r) * M HC r ∧
    rv (fun x => bn x.exp.isSome) r * (M ACTR r * (M B r - rv (fun x => x.exp.getD 0) r)) = 0 ∧
    rv (fun x => bn x.sc1) r * (M RA r - (M B r - 2 - 2 * pub 4)) = 0 ∧
    rv (fun x => bn x.hi) r * (M PACC r - 256 * M B r) = 0 ∧
    rv (fun x => bn x.capT0) r * (M TL16 r - M ACC r) = 0 ∧ rv (fun x => bn x.capT1) r * (M TH16 r - M ACC r) = 0 ∧
    rv (fun x => bn x.capM0) r * (M MLO r - M ACC r) = 0 ∧ rv (fun x => bn x.capM1) r * (M MHI r - M ACC r) = 0 ∧
    rv (fun x => bn x.chkH) r * (pub 4 * (M ACC r - pub 2)) = 0 ∧
    rv (fun x => bn x.chkL) r * (M HC r * (M ACC r - (M CLEN r - 38))) = 0 ∧
    rv (fun x => bn x.chkW) r * (M ACC r - (4000000 - 4 * pub 0 + 3 * M WT r)) = 0 ∧
    rv (fun x => bn x.chkS) r * (M ACC r - (20000 - M SIGS r)) = 0 := by
  have q := fun (cc : Expr) (h : cc ∈ constraints) => sat hsat h hr
  have e : ∀ i (g : Role → ℕ), preCols.getD i (.periodic [0]) = tabR g →
      (p i).eval n preCols pub M r = rv g r := fun i g hi => ev_role hi hr
  have c1 := q (.sub (k ADDR) (.add (.add (.mul (.add (p P_SCB) (p P_SB34)) (.add (k A0) (.mul (cst 2) (k SEG0))))
      (.add (.mul (p P_SW) (k W0)) (.mul (p P_SC) (k CPOS)))) (p P_OFF))) (by simp [constraints])
  have c2 := q (.sub (k ACTR) (.add (.add (p P_SCB) (p P_SHDR)) (.add (.mul (p P_SB34) (.pub 4))
      (.mul (.add (p P_SW) (p P_SC)) (k HC))))) (by simp [constraints])
  have c3 := q (.mul (p P_HEXP) (.mul (k ACTR) (.sub (k B) (p P_EXP)))) (by simp [constraints])
  have c4 := q (.mul (p P_SC1) (.sub (k RA) (.sub (.sub (k B) (cst 2)) (.mul (cst 2) (.pub 4))))) (by simp [constraints])
  have c5 := q (.mul (p P_HI) (.sub (k PACC) (.mul (cst 256) (k B)))) (by simp [constraints])
  have c6 := q (.mul (p P_CAPT0) (.sub (k TL16) (k ACC))) (by simp [constraints])
  have c7 := q (.mul (p P_CAPT1) (.sub (k TH16) (k ACC))) (by simp [constraints])
  have c8 := q (.mul (p P_CAPM0) (.sub (k MLO) (k ACC))) (by simp [constraints])
  have c9 := q (.mul (p P_CAPM1) (.sub (k MHI) (k ACC))) (by simp [constraints])
  have c10 := q (.mul (p P_CHKH) (.mul (.pub 4) (.sub (k ACC) (.pub 2)))) (by simp [constraints])
  have c11 := q (.mul (p P_CHKL) (.mul (k HC) (.sub (k ACC) (.sub (k CLEN) (cst 38))))) (by simp [constraints])
  have c12 := q (.mul (p P_CHKW) (.sub (k ACC) (.add (.sub (cst 4000000) (.mul (cst 4) (.pub 0))) (.mul (cst 3) (k WT)))))
    (by simp [constraints])
  have c13 := q (.mul (p P_CHKS) (.sub (k ACC) (.sub (cst 20000) (k SIGS)))) (by simp [constraints])
  simp only [Expr.eval, ev_k hr, eval_cst, Nat.cast_ofNat, e P_SCB (fun x => bn (decide (x.base = 2))) rfl, e P_SB34 (fun x => bn (decide (x.base = 3))) rfl, e P_SW (fun x => bn (decide (x.base = 4))) rfl, e P_SC (fun x => bn (decide (x.base = 5))) rfl,
    e P_OFF (·.off) rfl, e P_SHDR (fun x => bn (decide (x.base = 1))) rfl, e P_EXP (fun x => x.exp.getD 0) rfl, e P_HEXP (fun x => bn x.exp.isSome) rfl, e P_SC1 (fun x => bn x.sc1) rfl, e P_HI (fun x => bn x.hi) rfl, e P_CAPT0 (fun x => bn x.capT0) rfl,
    e P_CAPT1 (fun x => bn x.capT1) rfl, e P_CAPM0 (fun x => bn x.capM0) rfl, e P_CAPM1 (fun x => bn x.capM1) rfl, e P_CHKH (fun x => bn x.chkH) rfl, e P_CHKL (fun x => bn x.chkL) rfl, e P_CHKW (fun x => bn x.chkW) rfl,
    e P_CHKS (fun x => bn x.chkS) rfl] at c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  refine ⟨by linear_combination c1, by linear_combination c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13⟩

/-- **The step equations** between rows `r` and `r + 1`. -/
theorem step_eqs {r : ℕ} (hr : r + 1 < n) :
    M ACC (r + 1) = (1 - rv (fun x => bn x.rst) (r + 1)) * M ACC r +
        rv (·.wgt) (r + 1) * (rv (fun x => bn x.srcB) (r + 1) * M B (r + 1) + rv (fun x => bn x.srcR) (r + 1) * M RA (r + 1)) ∧
    rv (fun x => bn x.sc2) (r + 1) * (M RA (r + 1) - (100 - M B r)) = 0 ∧
    rv (fun x => bn x.flip) (r + 1) * (M RA (r + 1) - (1 - M RA r)) = 0 ∧
    rv (fun x => bn x.lo) (r + 1) * (M PACC (r + 1) - M PACC r - M B (r + 1)) = 0 ∧
    (∀ j < 15, rv (fun x => bn x.lo) (r + 1) * (M (LG j) (r + 1) - M (LG (j + 1)) r) = 0) ∧
    rv (fun x => bn x.lo) (r + 1) * (M (LG 15) (r + 1) - M PACC (r + 1)) = 0 ∧
    (∀ j < 16, (1 - rv (fun x => bn x.lo) (r + 1)) * (M (LG j) (r + 1) - M (LG j) r) = 0) := by
  have q := fun (cc : Expr) (h : cc ∈ constraints) => sat hsat h hr
  have e : ∀ i (g : Role → ℕ), preCols.getD i (.periodic [0]) = tabR g →
      (p i).eval n preCols pub M (r + 1) = rv g (r + 1) := fun i g hi => ev_role hi hr
  have c1 := q (.sub (k ACC) (.add (.mul (om (p P_RST)) (kp ACC))
      (.mul (p P_WGT) (.add (.mul (p P_SRCB) (k B)) (.mul (p P_SRCR) (k RA)))))) (by simp [constraints])
  have c2 := q (.mul (p P_SC2) (.sub (k RA) (.sub (cst 100) (kp B)))) (by simp [constraints])
  have c3 := q (.mul (p P_FLIP) (.sub (k RA) (om (kp RA)))) (by simp [constraints])
  have c4 := q (.mul (p P_LO) (.sub (.sub (k PACC) (kp PACC)) (k B))) (by simp [constraints])
  have c6 := q (.mul (p P_LO) (.sub (k (LG 15)) (k PACC))) (by simp [constraints])
  have ev := fun (c : Expr) => (rfl : c = c)
  simp only [Expr.eval, ev_k (show r + 1 < n from hr), ev_kp hr, eval_cst, Nat.cast_ofNat, om, one, Nat.cast_one,
    e P_RST (fun x => bn x.rst) rfl, e P_WGT (·.wgt) rfl, e P_SRCB (fun x => bn x.srcB) rfl,
    e P_SRCR (fun x => bn x.srcR) rfl, e P_SC2 (fun x => bn x.sc2) rfl, e P_FLIP (fun x => bn x.flip) rfl,
    e P_LO (fun x => bn x.lo) rfl, sub_eq_zero] at c1 c2 c3 c4 c6
  refine ⟨c1, by linear_combination c2, by linear_combination c3, by linear_combination c4, fun j hj => ?_,
    by linear_combination c6, fun j hj => ?_⟩
  · have hm : Expr.mul (p P_LO) (.sub (k (LG j)) (kp (LG (j + 1)))) ∈
        (List.range 15).map (fun j => .mul (p P_LO) (.sub (k (LG j)) (kp (LG (j + 1))))) :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have := q _ (by simp only [constraints, List.mem_append]; tauto)
    simp only [Expr.eval, ev_k (show r + 1 < n from hr), ev_kp hr, e P_LO (fun x => bn x.lo) rfl] at this
    exact this
  · have hm : Expr.mul notFirst (.mul (om (p P_LO)) (.sub (k (LG j)) (kp (LG j)))) ∈
        (List.range 16).map (fun j => .mul notFirst (.mul (om (p P_LO)) (.sub (k (LG j)) (kp (LG j))))) :=
      List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩
    have := q _ (by simp only [constraints, List.mem_append]; tauto)
    simp only [Expr.eval, ev_k (show r + 1 < n from hr), ev_kp hr, ev_notFirst hr, om, one, eval_cst, Nat.cast_one,
      one_mul, e P_LO (fun x => bn x.lo) rfl] at this
    exact this

/-- **The block-level equations.** -/
theorem glob_eqs (hn : 0 < n) :
    M HC 0 = pub 6 * M HASC 0 ∧ M HC 0 * (M L0 0 - (M W0 0 + 34)) = 0 ∧ (1 - M HC 0) * M NSEG 0 = 0 ∧
    M MLO 0 + 65536 * M MHI 0 = pub 3 ∧ M CLO 0 = pub 5 * M MLO 0 + (1 - pub 5) * M TL16 0 ∧
    M CHI 0 = pub 5 * M MHI 0 + (1 - pub 5) * M TH16 0 := by
  have q := fun (cc : Expr) (h : cc ∈ constraints) => sat hsat h hn
  have c1 := q (.sub (k HC) (.mul (.pub 6) (k HASC))) (by simp [constraints])
  have c2 := q (.mul (k HC) (.sub (k L0) (.add (k W0) (cst 34)))) (by simp [constraints])
  have c3 := q (.mul (om (k HC)) (k NSEG)) (by simp [constraints])
  have c4 := q (.sub (.add (k MLO) (.mul (cst 65536) (k MHI))) (.pub 3)) (by simp [constraints])
  have c5 := q (.sub (k CLO) (.add (.mul (.pub 5) (k MLO)) (.mul (om (.pub 5)) (k TL16)))) (by simp [constraints])
  have c6 := q (.sub (k CHI) (.add (.mul (.pub 5) (k MHI)) (.mul (om (.pub 5)) (k TH16)))) (by simp [constraints])
  simp only [Expr.eval, ev_k hn, eval_cst, Nat.cast_ofNat, om, one, Nat.cast_one, sub_eq_zero] at c1 c2 c3 c4 c5 c6
  exact ⟨c1, by linear_combination c2, by linear_combination c3, c4, c5, c6⟩

end Rows

end StarkedAir.Block.Ctx

namespace StarkedAir.Block.Ctx

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

theorem role_cb {r : ℕ} (hr : r ≤ 36) : (role r).base = 2 ∧ (role r).off = 4 + r ∧
    (role r).exp = some (if r = 0 then 1 else if r ≤ 32 then 0 else 0xff) := by
  interval_cases r <;> exact ⟨rfl, rfl, rfl⟩

theorem val255 : (255 : F).val = 255 := by
  rw [show (255 : F) = ((255 : ℕ) : F) by norm_num]; exact ZMod.val_natCast_of_lt (by unfold P; norm_num)

theorem rv_mod {g : Role → ℕ} {r : ℕ} (hr : r < 256) : rv g r = ((g (role r) : ℕ) : F) := by
  simp [rv, Nat.mod_eq_of_lt hr]

section Facts

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (hn : 256 ≤ n) (hnP : n ≤ 2 ^ 25)
  (R : Spec.Block.Bytes)
  (hread : ∀ r < n, M ACTR r = 1 → (M ADDR r).val < R.length ∧ (M B r).val = (R.getD (M ADDR r).val 0).toNat)
  (hra : ∀ r < n, (M RA r).val < 256)
  (hseg : M SEG0 0 = 0 ∨ M SEG0 0 = 1) (ha0 : (M A0 0).val < 2 ^ 25)
include hsat hn hnP hread hra hseg ha0

/-- The coinbase base position: after its version, marker and flag. -/
def cbase (M : ℕ → ℕ → F) : ℕ := (M A0 0).val + 2 * (M SEG0 0).val

/-- **The coinbase reads** (rows 0–36): one input, the null prevout. -/
theorem cb_read {r : ℕ} (hr : r ≤ 36) :
    cbase M + 4 + r < R.length ∧
    (R.getD (cbase M + 4 + r) 0).toNat = (if r = 0 then 1 else if r ≤ 32 then 0 else 0xff) := by
  have hrn : r < n := by omega
  obtain ⟨b2, o, ex⟩ := role_cb hr
  obtain ⟨ea, eact, eexp, -⟩ := row_eqs hsat hrn
  have rr : r < 256 := by omega
  simp only [rv_mod rr, b2, o, ex, bn] at ea eact eexp
  simp at ea eact eexp
  have hb : M B r = if r = 0 then 1 else if r ≤ 32 then 0 else 255 := by
    rcases eexp with h | h
    · exact absurd h (by rw [eact]; exact one_ne_zero)
    · exact sub_eq_zero.mp h
  rw [const_eq hsat (X := A0) (by simp [consts]) r hrn, const_eq hsat (X := SEG0) (by simp [consts]) r hrn] at ea
  have hav : (M ADDR r).val = cbase M + 4 + r := by
    have e : M A0 0 + 2 * M SEG0 0 + (4 + (r : F)) = ((cbase M + 4 + r : ℕ) : F) := by
      unfold cbase; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
    rw [ea, e]
    obtain ⟨-, ls⟩ := Fields.bool_val hseg
    exact ZMod.val_natCast_of_lt (Fields.lt_P (by unfold cbase; omega))
  obtain ⟨hlt, hv⟩ := hread r hrn eact
  rw [hav] at hlt hv
  refine ⟨hlt, ?_⟩
  rw [← hv, hb]
  split_ifs
  · exact ZMod.val_one _
  · exact ZMod.val_zero
  · exact val255

/-- The row-`r` read (`ACTR = 1`) is the block byte at `ADDR`, below 256. -/
theorem read_val {r : ℕ} (hr : r < n) (h : M ACTR r = 1) : (M B r).val < 256 := by
  rw [(hread r hr h).2]; exact UInt8.toNat_lt _

omit hseg ha0 in
theorem pub4_bool : pub 4 = 0 ∨ pub 4 = 1 := by
  have hr : 38 < n := by omega
  obtain ⟨-, eact, -⟩ := row_eqs hsat hr
  simp [rv_mod (show 38 < 256 by norm_num), role, bn] at eact
  rw [← eact]; exact bool_of hsat (by simp [constraints]) hr

omit hread hra hseg ha0 in
/-- The accumulator at row `r + 1`, with that row's role. -/
theorem acc_step {r : ℕ} (hr : r + 1 < n) (h256 : r + 1 < 256) :
    M ACC (r + 1) = (1 - ((bn (role (r + 1)).rst : ℕ) : F)) * M ACC r + (((role (r + 1)).wgt : ℕ) : F) *
      (((bn (role (r + 1)).srcB : ℕ) : F) * M B (r + 1) + ((bn (role (r + 1)).srcR : ℕ) : F) * M RA (r + 1)) := by
  have := (step_eqs hsat hr).1
  simpa [rv_mod h256] using this

/-- Row `r`'s role values. -/
theorem rv_at {g : Role → ℕ} {r : ℕ} (hr : r < 256) : rv g r = ((g (role r) : ℕ) : F) := rv_mod hr

omit hread hra hseg ha0 in
/-- Range-slot accumulation over rows `a, …, a + d`: the accumulator is `Σ 256^j · RA (a + j)`. -/
theorem acc_ra {a d : ℕ} (had : a + d < n) (h256 : a + d < 256)
    (hrst : (role a).rst = true) (hw : ∀ j ≤ d, (role (a + j)).wgt = 256 ^ j) (hsr : ∀ j ≤ d, (role (a + j)).srcR = true)
    (hsb : ∀ j ≤ d, (role (a + j)).srcB = false) (hnr : ∀ j ≤ d, 0 < j → (role (a + j)).rst = false) (ha1 : 1 ≤ a) :
    M ACC (a + d) = ∑ j ∈ Finset.range (d + 1), (256 : F) ^ j * M RA (a + j) := by
  induction d with
  | zero =>
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have := acc_step hsat hn hnP (r := b) (by omega) (by omega)
    rw [hrst, show (role (b + 1)).wgt = 1 by simpa using hw 0 le_rfl, show (role (b + 1)).srcR = true by simpa using hsr 0 le_rfl,
      show (role (b + 1)).srcB = false by simpa using hsb 0 le_rfl] at this
    simp only [bn, if_true, Bool.false_eq_true, if_false, Nat.cast_one, Nat.cast_zero, sub_self, zero_mul, zero_add,
      one_mul] at this
    simpa using this
  | succ d ih =>
    have := acc_step hsat hn hnP (r := a + d) (by omega) (by omega)
    rw [show a + d + 1 = a + (d + 1) by ring, hnr (d + 1) le_rfl (by omega), hw (d + 1) le_rfl, hsr (d + 1) le_rfl,
      hsb (d + 1) le_rfl] at this
    simp only [bn, if_true, Bool.false_eq_true, if_false, Nat.cast_one, Nat.cast_zero, sub_zero, zero_mul, zero_add,
      one_mul, Nat.cast_pow, Nat.cast_ofNat] at this
    rw [this, ih (by omega) (by omega) (fun j hj => hw j (by omega)) (fun j hj => hsr j (by omega))
      (fun j hj => hsb j (by omega)) (fun j hj h => hnr j (by omega) h), Finset.sum_range_succ _ (d + 1)]

omit hread hseg ha0 in
theorem ra_sum_lt {a d : ℕ} (had : a + d < n) :
    ∃ D : ℕ, D < 256 ^ (d + 1) ∧ ((D : ℕ) : F) = ∑ j ∈ Finset.range (d + 1), (256 : F) ^ j * M RA (a + j) := by
  induction d with
  | zero => exact ⟨(M RA a).val, by simpa using hra a (by omega), by simp⟩
  | succ d ih =>
    obtain ⟨D, hD, e⟩ := ih (by omega)
    refine ⟨D + 256 ^ (d + 1) * (M RA (a + (d + 1))).val, ?_, ?_⟩
    · have := hra (a + (d + 1)) (by omega)
      calc D + 256 ^ (d + 1) * (M RA (a + (d + 1))).val < 256 ^ (d + 1) + 256 ^ (d + 1) * 255 := by
            have := Nat.mul_le_mul_left (256 ^ (d + 1)) (show (M RA (a + (d + 1))).val ≤ 255 by omega); omega
        _ = 256 ^ (d + 1 + 1) := by ring
    · rw [Finset.sum_range_succ, ← e]; push_cast; rw [ZMod.natCast_zmod_val]

omit hread hseg ha0 in
/-- **The weight check**: `4,000,000 − 4·len + 3·W` is a 3-byte natural. -/
theorem weight_fact : ∃ D : ℕ, D < 2 ^ 24 ∧ ((D : ℕ) : F) = 4000000 - 4 * pub 0 + 3 * M WT 0 := by
  have h125 : 125 < n := by omega
  have acc := acc_ra hsat hn hnP (a := 123) (d := 2) (by omega) (by norm_num) rfl
    (fun j hj => by interval_cases j <;> rfl) (fun j hj => by interval_cases j <;> rfl)
    (fun j hj => by interval_cases j <;> rfl) (fun j hj h => by interval_cases j <;> first | omega | rfl) (by norm_num)
  obtain ⟨D, hD, e⟩ := ra_sum_lt hsat hn hnP hra (a := 123) (d := 2) (by omega)
  have chk := (row_eqs hsat h125).2.2.2.2.2.2.2.2.2.2.2.1
  simp [rv_mod (show 125 < 256 by norm_num), role, bn] at chk
  rw [const_eq hsat (X := WT) (by simp [consts]) 125 h125] at chk
  refine ⟨D, by simpa using hD, ?_⟩
  rw [e, ← show M ACC 125 = _ from acc]; linear_combination chk

omit hread hseg ha0 in
/-- **The sigop check**: `20,000 − SIGS` is a 2-byte natural. -/
theorem sigops_fact : ∃ D : ℕ, D < 2 ^ 16 ∧ ((D : ℕ) : F) = 20000 - M SIGS 0 := by
  have h127 : 127 < n := by omega
  have acc := acc_ra hsat hn hnP (a := 126) (d := 1) (by omega) (by norm_num) rfl
    (fun j hj => by interval_cases j <;> rfl) (fun j hj => by interval_cases j <;> rfl)
    (fun j hj => by interval_cases j <;> rfl) (fun j hj h => by interval_cases j <;> first | omega | rfl) (by norm_num)
  obtain ⟨D, hD, e⟩ := ra_sum_lt hsat hn hnP hra (a := 126) (d := 1) (by omega)
  have chk := (row_eqs hsat h127).2.2.2.2.2.2.2.2.2.2.2.2
  simp [rv_mod (show 127 < 256 by norm_num), role, bn] at chk
  rw [const_eq hsat (X := SIGS) (by simp [consts]) 127 h127] at chk
  refine ⟨D, by simpa using hD, ?_⟩
  rw [e, ← show M ACC 127 = _ from acc]; linear_combination chk

omit hread hseg ha0 in
/-- **The previous MTP's limbs** are 16-bit. -/
theorem mtp_fact : (M MLO 0).val < 2 ^ 16 ∧ (M MHI 0).val < 2 ^ 16 := by
  have h131 : 131 < n := by omega
  have accL := acc_ra hsat hn hnP (a := 128) (d := 1) (by omega) (by norm_num) rfl
    (fun j hj => by interval_cases j <;> rfl) (fun j hj => by interval_cases j <;> rfl)
    (fun j hj => by interval_cases j <;> rfl) (fun j hj h => by interval_cases j <;> first | omega | rfl) (by norm_num)
  have accH := acc_ra hsat hn hnP (a := 130) (d := 1) (by omega) (by norm_num) rfl
    (fun j hj => by interval_cases j <;> rfl) (fun j hj => by interval_cases j <;> rfl)
    (fun j hj => by interval_cases j <;> rfl) (fun j hj h => by interval_cases j <;> first | omega | rfl) (by norm_num)
  obtain ⟨DL, hDL, eL⟩ := ra_sum_lt hsat hn hnP hra (a := 128) (d := 1) (by omega)
  obtain ⟨DH, hDH, eH⟩ := ra_sum_lt hsat hn hnP hra (a := 130) (d := 1) (by omega)
  have c0 := (row_eqs hsat (show 129 < n by omega)).2.2.2.2.2.2.2.1
  have c1 := (row_eqs hsat h131).2.2.2.2.2.2.2.2.1
  simp [rv_mod (show 129 < 256 by norm_num), role, bn] at c0
  simp [rv_mod (show 131 < 256 by norm_num), role, bn] at c1
  rw [const_eq hsat (X := MLO) (by simp [consts]) 129 (by omega)] at c0
  rw [const_eq hsat (X := MHI) (by simp [consts]) 131 h131] at c1
  have e0 : M MLO 0 = ((DL : ℕ) : F) := by rw [eL, ← show M ACC 129 = _ from accL]; linear_combination c0
  have e1 : M MHI 0 = ((DH : ℕ) : F) := by rw [eH, ← show M ACC 131 = _ from accH]; linear_combination c1
  rw [e0, e1, ZMod.val_natCast_of_lt (Fields.lt_P (by simp at hDL; omega)),
    ZMod.val_natCast_of_lt (Fields.lt_P (by simp at hDH; omega))]
  simp at hDL hDH; exact ⟨hDL, hDH⟩

end Facts

end StarkedAir.Block.Ctx
