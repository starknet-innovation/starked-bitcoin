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

/-- **A read row's byte**, for the header (base 1) and coinbase (bases 2, 3) regions. -/
theorem read_at {r : ℕ} (hr : r < n) (h256 : r < 256) (hact : M ACTR r = 1)
    (hb : (role r).base = 1 ∨ (role r).base = 2 ∨ (role r).base = 3) (hoff : (role r).off ≤ 100) :
    (if (role r).base = 1 then 0 else cbase M) + (role r).off < R.length ∧
    (M B r).val = (R.getD ((if (role r).base = 1 then 0 else cbase M) + (role r).off) 0).toNat := by
  obtain ⟨ea, -⟩ := row_eqs hsat hr
  simp only [rv_mod h256] at ea
  rw [const_eq hsat (X := A0) (by simp [consts]) r hr, const_eq hsat (X := SEG0) (by simp [consts]) r hr] at ea
  obtain ⟨vs, ls⟩ := Fields.bool_val hseg
  have hav : (M ADDR r).val = (if (role r).base = 1 then 0 else cbase M) + (role r).off := by
    rcases hb with h | h | h
    · rw [h] at ea; simp [bn] at ea
      rw [ea, h, if_pos rfl, zero_add]
      exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
    all_goals
      rw [h] at ea; simp [bn] at ea
      rw [ea, h, if_neg (by decide)]
      rw [show M A0 0 + 2 * M SEG0 0 + ((role r).off : F) = ((cbase M + (role r).off : ℕ) : F) by
        unfold cbase; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]]
      exact ZMod.val_natCast_of_lt (Fields.lt_P (by unfold cbase; omega))
  obtain ⟨hlt, hv⟩ := hread r hr hact
  rw [hav] at hlt hv
  exact ⟨hlt, hv⟩

/-- **The header time** (rows 42–45): `TL16`, `TH16` are bytes 68–69 and 70–71. -/
theorem time_fact : 72 ≤ R.length ∧
    M TL16 0 = (((R.getD 68 0).toNat + 256 * (R.getD 69 0).toNat : ℕ) : F) ∧
    M TH16 0 = (((R.getD 70 0).toNat + 256 * (R.getD 71 0).toNat : ℕ) : F) := by
  have act : ∀ r, 42 ≤ r → r ≤ 45 → M ACTR r = 1 := fun r h1 h2 => by
    have := (row_eqs hsat (show r < n by omega)).2.1
    rw [this]; interval_cases r <;> simp [rv_mod, role, bn]
  have rd : ∀ r, 42 ≤ r → r ≤ 45 → r + 26 < R.length ∧ (M B r).val = (R.getD (r + 26) 0).toNat := fun r h1 h2 => by
    have := read_at hsat hn hnP R hread hra hseg ha0 (r := r) (by omega) (by omega) (act r h1 h2)
      (by interval_cases r <;> simp [role]) (by interval_cases r <;> simp [role])
    interval_cases r <;> simpa [role] using this
  have bc : ∀ r, M B r = (((M B r).val : ℕ) : F) := fun r => (ZMod.natCast_zmod_val _).symm
  have a42 := acc_step hsat hn hnP (r := 41) (by omega) (by norm_num)
  have a43 := acc_step hsat hn hnP (r := 42) (by omega) (by norm_num)
  have a44 := acc_step hsat hn hnP (r := 43) (by omega) (by norm_num)
  have a45 := acc_step hsat hn hnP (r := 44) (by omega) (by norm_num)
  simp [role, bn] at a42 a43 a44 a45
  have c43 := (row_eqs hsat (show 43 < n by omega)).2.2.2.2.2.1
  have c45 := (row_eqs hsat (show 45 < n by omega)).2.2.2.2.2.2.1
  simp [rv_mod, role, bn] at c43 c45
  rw [const_eq hsat (X := TL16) (by simp [consts]) 43 (by omega)] at c43
  rw [const_eq hsat (X := TH16) (by simp [consts]) 45 (by omega)] at c45
  refine ⟨by have := (rd 45 (by norm_num) le_rfl).1; omega, ?_, ?_⟩
  · rw [sub_eq_zero.mp c43, a43, a42, bc 42, bc 43, (rd 42 le_rfl (by norm_num)).2, (rd 43 (by norm_num) (by norm_num)).2]
    push_cast; ring
  · rw [sub_eq_zero.mp c45, a45, a44, bc 44, bc 45, (rd 44 (by norm_num) (by norm_num)).2, (rd 45 (by norm_num) le_rfl).2]
    push_cast; ring

/-- **The coinbase scriptSig length** (rows 37–38): one byte `s` with `2 + 2·bip34 ≤ s ≤ 100`. -/
theorem slen_fact : cbase M + 41 < R.length ∧
    2 + 2 * (pub 4).val ≤ (R.getD (cbase M + 41) 0).toNat ∧ (R.getD (cbase M + 41) 0).toNat ≤ 100 := by
  have h37 : 37 < n := by omega
  have act : M ACTR 37 = 1 := by
    have := (row_eqs hsat h37).2.1; rw [this]; simp [rv_mod, role, bn]
  have rd := read_at hsat hn hnP R hread hra hseg ha0 (r := 37) h37 (by norm_num) act (by simp [role]) (by simp [role])
  have hb37 : (role 37).base = 2 := rfl
  have ho37 : (role 37).off = 41 := rfl
  rw [hb37, ho37, if_neg (by decide)] at rd
  obtain ⟨hlt, hv⟩ := rd
  have c4 := (row_eqs hsat h37).2.2.2.1
  simp [rv_mod, role, bn] at c4
  have c38 := (step_eqs hsat (r := 37) (by omega)).2.1
  simp [rv_mod, role, bn] at c38
  have r37 := hra 37 h37
  have r38 := hra 38 (by omega)
  have bc : M B 37 = (((M B 37).val : ℕ) : F) := (ZMod.natCast_zmod_val _).symm
  obtain ⟨vp, lp⟩ := Fields.bool_val (pub4_bool hsat hn hnP R hread hra)
  have b256 : (M B 37).val < 256 := by rw [hv]; exact UInt8.toNat_lt _
  -- `RA37 + 2 + 2·bip34 = s` and `RA38 + s = 100`, as naturals
  have e1 : (((M RA 37).val + 2 + 2 * (pub 4).val : ℕ) : F) = (((M B 37).val : ℕ) : F) := by
    push_cast; rw [ZMod.natCast_zmod_val, ← vp, ← bc]; linear_combination c4
  have e2 : (((M RA 38).val + (M B 37).val : ℕ) : F) = ((100 : ℕ) : F) := by
    push_cast; rw [ZMod.natCast_zmod_val, ← bc]; linear_combination c38
  have n1 := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e1
  have n2 := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) e2
  rw [← hv]
  exact ⟨hlt, by omega, by omega⟩

/-- **BIP34** (rows 38–41, when `pub 4 = 1`): `03 h0 h1 h2` with `h0 + 256·h1 + 65536·h2 = pub 2`. -/
theorem bip34_fact (h4 : pub 4 = 1) : cbase M + 45 < R.length ∧ (R.getD (cbase M + 42) 0).toNat = 3 ∧
    (((R.getD (cbase M + 43) 0).toNat + 256 * (R.getD (cbase M + 44) 0).toNat +
      65536 * (R.getD (cbase M + 45) 0).toNat : ℕ) : F) = pub 2 := by
  have act : ∀ r, 38 ≤ r → r ≤ 41 → M ACTR r = 1 := fun r h1 h2 => by
    have := (row_eqs hsat (show r < n by omega)).2.1
    rw [this, h4]; interval_cases r <;> simp [rv_mod, role, bn]
  have rd : ∀ r, 38 ≤ r → r ≤ 41 → cbase M + (r + 4) < R.length ∧ (M B r).val = (R.getD (cbase M + (r + 4)) 0).toNat :=
    fun r h1 h2 => by
      have := read_at hsat hn hnP R hread hra hseg ha0 (r := r) (by omega) (by omega) (act r h1 h2)
        (by interval_cases r <;> simp [role]) (by interval_cases r <;> simp [role])
      interval_cases r <;> simpa [role] using this
  have bc : ∀ r, M B r = (((M B r).val : ℕ) : F) := fun r => (ZMod.natCast_zmod_val _).symm
  -- row 38: the push opcode
  have c38 := (row_eqs hsat (show 38 < n by omega)).2.2.1
  simp [rv_mod, role, bn] at c38
  rw [act 38 le_rfl (by norm_num)] at c38
  have b38 : M B 38 = 3 := by
    rcases c38 with h | h
    · exact absurd h one_ne_zero
    · exact sub_eq_zero.mp h
  -- rows 39–41: the height bytes, accumulated and checked
  have a39 := acc_step hsat hn hnP (r := 38) (by omega) (by norm_num)
  have a40 := acc_step hsat hn hnP (r := 39) (by omega) (by norm_num)
  have a41 := acc_step hsat hn hnP (r := 40) (by omega) (by norm_num)
  simp [role, bn] at a39 a40 a41
  have c41 := (row_eqs hsat (show 41 < n by omega)).2.2.2.2.2.2.2.2.2.1
  simp [rv_mod, role, bn, h4] at c41
  refine ⟨(rd 41 (by norm_num) le_rfl).1, ?_, ?_⟩
  · rw [← (rd 38 le_rfl (by norm_num)).2, b38]; rfl
  · rw [← (rd 39 (by norm_num) (by norm_num)).2, ← (rd 40 (by norm_num) (by norm_num)).2,
      ← (rd 41 (by norm_num) le_rfl).2]
    push_cast; rw [← bc, ← bc, ← bc, ← sub_eq_zero.mp c41, a41, a40, a39]

omit hread hra hseg ha0 in
/-- **The digest register.** Over the 16 byte pairs starting at row `s0` (48: the nonce, 86: the
commitment), after row `s0 + 31` register `LG i` holds pair `i`: `256 · B (s0 + 2i) + B (s0 + 2i + 1)`. -/
theorem register {s0 : ℕ} (hs : s0 = 48 ∨ s0 = 86) :
    ∀ t ≤ 15, ∀ i ≤ t, M (LG (15 - t + i)) (s0 + 1 + 2 * t) = 256 * M B (s0 + 2 * i) + M B (s0 + 2 * i + 1) := by
  have rhi : ∀ t ≤ 15, (role (s0 + 2 * t)).hi = true ∧ (role (s0 + 2 * t)).lo = false := fun t ht => by
    rcases hs with rfl | rfl <;> interval_cases t <;> exact ⟨rfl, rfl⟩
  have rlo : ∀ t ≤ 15, (role (s0 + 2 * t + 1)).lo = true ∧ (role (s0 + 2 * t + 1)).hi = false := fun t ht => by
    rcases hs with rfl | rfl <;> interval_cases t <;> exact ⟨rfl, rfl⟩
  have hs1 : 48 ≤ s0 ∧ s0 + 31 < 256 := by rcases hs with rfl | rfl <;> norm_num
  -- the pair accumulator at a pair's low row
  have pacc : ∀ t ≤ 15, M PACC (s0 + 2 * t + 1) = 256 * M B (s0 + 2 * t) + M B (s0 + 2 * t + 1) := by
    intro t ht
    have hi := (row_eqs hsat (show s0 + 2 * t < n by omega)).2.2.2.2.1
    rw [rv_mod (by omega), (rhi t ht).1] at hi
    simp [bn] at hi
    have lo := (step_eqs hsat (r := s0 + 2 * t) (by omega)).2.2.2.1
    rw [rv_mod (by omega), (rlo t ht).1] at lo
    simp [bn] at lo
    linear_combination lo + hi
  -- shifting at a low row; keeping at a high row
  have shift : ∀ t ≤ 15, (∀ j < 15, M (LG j) (s0 + 2 * t + 1) = M (LG (j + 1)) (s0 + 2 * t)) ∧
      M (LG 15) (s0 + 2 * t + 1) = M PACC (s0 + 2 * t + 1) := by
    intro t ht
    obtain ⟨-, -, -, -, sh, s15, -⟩ := step_eqs hsat (r := s0 + 2 * t) (show s0 + 2 * t + 1 < n by omega)
    rw [rv_mod (by omega), (rlo t ht).1] at sh s15
    simp [bn] at sh s15
    exact ⟨fun j hj => sub_eq_zero.mp (sh j hj), sub_eq_zero.mp s15⟩
  have keep : ∀ t, 1 ≤ t → t ≤ 15 → ∀ j < 16, M (LG j) (s0 + 2 * t) = M (LG j) (s0 + 2 * t - 1) := by
    intro t h1 ht j hj
    obtain ⟨-, -, -, -, -, -, kp⟩ := step_eqs hsat (r := s0 + 2 * t - 1) (show s0 + 2 * t - 1 + 1 < n by omega)
    rw [show s0 + 2 * t - 1 + 1 = s0 + 2 * t by omega, rv_mod (by omega), (rhi t ht).2] at kp
    simp [bn] at kp
    exact sub_eq_zero.mp (kp j hj)
  intro t ht
  induction t with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [show 15 - 0 + 0 = 15 by rfl, (shift 0 (by norm_num)).2, pacc 0 (by norm_num)]
  | succ t ih =>
    intro i hi
    rcases Nat.lt_or_ge i (t + 1) with h | h
    · -- an old pair: shifted down one register
      have e1 := (shift (t + 1) ht).1 (15 - (t + 1) + i) (by omega)
      rw [show s0 + 2 * (t + 1) + 1 = s0 + 1 + 2 * (t + 1) by ring] at e1
      rw [e1, keep (t + 1) (by omega) ht _ (by omega), show s0 + 2 * (t + 1) - 1 = s0 + 1 + 2 * t by omega,
        show 15 - (t + 1) + i + 1 = 15 - t + i by omega]
      exact ih (by omega) i (by omega)
    · -- the new pair
      obtain rfl : i = t + 1 := by omega
      rw [show 15 - (t + 1) + (t + 1) = 15 by omega, show s0 + 1 + 2 * (t + 1) = s0 + 2 * (t + 1) + 1 by ring,
        (shift (t + 1) ht).2, pacc (t + 1) ht]

/-- **A commitment-region read** (bases 4, 5), when the commitment is checked. -/
theorem read45 {r : ℕ} (hr : r < n) (h256 : r < 256) (hc : M HC 0 = 1)
    (hb : (role r).base = 4 ∨ (role r).base = 5) (hoff : (role r).off ≤ 100)
    (hw0 : (M W0 0).val < 2 ^ 25) (hcp : (M CPOS 0).val < 2 ^ 25) :
    M ACTR r = 1 ∧ (if (role r).base = 4 then (M W0 0).val else (M CPOS 0).val) + (role r).off < R.length ∧
    (M B r).val = (R.getD ((if (role r).base = 4 then (M W0 0).val else (M CPOS 0).val) + (role r).off) 0).toNat := by
  obtain ⟨ea, eact, -⟩ := row_eqs hsat hr
  simp only [rv_mod h256] at ea eact
  rw [const_eq hsat (X := W0) (by simp [consts]) r hr, const_eq hsat (X := CPOS) (by simp [consts]) r hr] at ea
  rw [const_eq hsat (X := HC) (by simp [consts]) r hr, hc] at eact
  have hact : M ACTR r = 1 := by rcases hb with h | h <;> rw [eact, h] <;> simp [bn]
  have hav : (M ADDR r).val = (if (role r).base = 4 then (M W0 0).val else (M CPOS 0).val) + (role r).off := by
    rcases hb with h | h
    · rw [h] at ea; simp [bn] at ea
      rw [ea, h, if_pos rfl, show M W0 0 + ((role r).off : F) = (((M W0 0).val + (role r).off : ℕ) : F) by
        push_cast; rw [ZMod.natCast_zmod_val]]
      exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
    · rw [h] at ea; simp [bn] at ea
      rw [ea, h, if_neg (by decide), show M CPOS 0 + ((role r).off : F) = (((M CPOS 0).val + (role r).off : ℕ) : F) by
        push_cast; rw [ZMod.natCast_zmod_val]]
      exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
  obtain ⟨hlt, hv⟩ := hread r hr hact
  rw [hav] at hlt hv
  exact ⟨hact, hlt, hv⟩

/-- **The commitment reads**, when the commitment is checked: the coinbase witness starts `01 20`; the
nonce's 16 limbs (register at row 79) are its 32 bytes; the commitment script starts with the pattern;
the 16 limbs at row 117 are the 32 bytes after it; and the script is at least 38 bytes long. -/
theorem commit_fact (hc : M HC 0 = 1) (hw0 : (M W0 0).val < 2 ^ 25) (hcp : (M CPOS 0).val < 2 ^ 25) :
    (M W0 0).val + 33 < R.length ∧ (R.getD (M W0 0).val 0).toNat = 1 ∧ (R.getD ((M W0 0).val + 1) 0).toNat = 0x20 ∧
    (∀ i < 16, M (LG i) 79 = ((256 * (R.getD ((M W0 0).val + 2 + 2 * i) 0).toNat +
      (R.getD ((M W0 0).val + 3 + 2 * i) 0).toNat : ℕ) : F)) ∧
    (M CPOS 0).val + 37 < R.length ∧ (∀ j < 6, (R.getD ((M CPOS 0).val + j) 0).toNat = Fields.pat.getD j 0) ∧
    (∀ i < 16, M (LG i) 117 = ((256 * (R.getD ((M CPOS 0).val + 6 + 2 * i) 0).toNat +
      (R.getD ((M CPOS 0).val + 7 + 2 * i) 0).toNat : ℕ) : F)) ∧
    ∃ D : ℕ, D < 2 ^ 25 ∧ ((D : ℕ) : F) = M CLEN 0 - 38 := by
  have rd := fun r (h1 : 46 ≤ r) (h2 : r ≤ 117) =>
    read45 hsat hn hnP R hread hra hseg ha0 (r := r) (by omega) (by omega) hc
      (by interval_cases r <;> simp [role]) (by interval_cases r <;> simp [role]) hw0 hcp
  have bc : ∀ r, M B r = (((M B r).val : ℕ) : F) := fun r => (ZMod.natCast_zmod_val _).symm
  -- expected bytes
  have exp : ∀ r, 46 ≤ r → r ≤ 85 → (role r).exp.isSome = true → M B r = (((role r).exp.getD 0 : ℕ) : F) := by
    intro r h1 h2 hs
    have c := (row_eqs hsat (show r < n by omega)).2.2.1
    rw [rv_mod (by omega), rv_mod (by omega), hs, (rd r h1 (by omega)).1] at c
    simp [bn] at c; exact sub_eq_zero.mp c
  have wb : ∀ r, 46 ≤ r → r ≤ 79 → (M W0 0).val + (r - 46) < R.length ∧
      (M B r).val = (R.getD ((M W0 0).val + (r - 46)) 0).toNat := by
    intro r h1 h2
    have := rd r h1 (by omega)
    have hb : (role r).base = 4 ∧ (role r).off = r - 46 := by interval_cases r <;> exact ⟨rfl, rfl⟩
    rw [hb.1, hb.2, if_pos rfl] at this
    exact ⟨this.2.1, this.2.2⟩
  have cb : ∀ r, 80 ≤ r → r ≤ 117 → (M CPOS 0).val + (r - 80) < R.length ∧
      (M B r).val = (R.getD ((M CPOS 0).val + (r - 80)) 0).toNat := by
    intro r h1 h2
    have := rd r (by omega) h2
    have hb : (role r).base = 5 ∧ (role r).off = r - 80 := by interval_cases r <;> exact ⟨rfl, rfl⟩
    rw [hb.1, hb.2, if_neg (by decide)] at this
    exact ⟨this.2.1, this.2.2⟩
  have regN := register hsat hn hnP (s0 := 48) (Or.inl rfl) 15 le_rfl
  have regC := register hsat hn hnP (s0 := 86) (Or.inr rfl) 15 le_rfl
  refine ⟨by have := (wb 79 (by norm_num) le_rfl).1; omega, ?_, ?_, fun i hi => ?_, by have := (cb 117 (by norm_num) le_rfl).1; omega,
    fun j hj => ?_, fun i hi => ?_, ?_⟩
  · rw [← show (M W0 0).val + (46 - 46) = (M W0 0).val by simp, ← (wb 46 le_rfl (by norm_num)).2,
      exp 46 le_rfl (by norm_num) rfl]; rfl
  · rw [← show (M W0 0).val + (47 - 46) = (M W0 0).val + 1 by simp, ← (wb 47 (by norm_num) (by norm_num)).2,
      exp 47 (by norm_num) (by norm_num) rfl]; rfl
  · have := regN i (by omega)
    rw [show 15 - 15 + i = i by omega] at this
    rw [show 48 + 1 + 2 * 15 = 79 by rfl] at this
    rw [this, bc (48 + 2 * i), bc (48 + 2 * i + 1), (wb (48 + 2 * i) (by omega) (by omega)).2,
      (wb (48 + 2 * i + 1) (by omega) (by omega)).2, show (M W0 0).val + (48 + 2 * i - 46) = (M W0 0).val + 2 + 2 * i by omega,
      show (M W0 0).val + (48 + 2 * i + 1 - 46) = (M W0 0).val + 3 + 2 * i by omega]
    push_cast; ring
  · have e := exp (80 + j) (by omega) (by omega) (by interval_cases j <;> rfl)
    rw [show (M CPOS 0).val + j = (M CPOS 0).val + (80 + j - 80) by omega, ← (cb (80 + j) (by omega) (by omega)).2, e]
    interval_cases j <;> rfl
  · have := regC i (by omega)
    rw [show 15 - 15 + i = i by omega, show 86 + 1 + 2 * 15 = 117 by rfl] at this
    rw [this, bc (86 + 2 * i), bc (86 + 2 * i + 1), (cb (86 + 2 * i) (by omega) (by omega)).2,
      (cb (86 + 2 * i + 1) (by omega) (by omega)).2, show (M CPOS 0).val + (86 + 2 * i - 80) = (M CPOS 0).val + 6 + 2 * i by omega,
      show (M CPOS 0).val + (86 + 2 * i + 1 - 80) = (M CPOS 0).val + 7 + 2 * i by omega]
    push_cast; ring
  · -- the length: four range bytes, the top one at most 1
    have acc := acc_ra hsat hn hnP (a := 118) (d := 3) (by omega) (by norm_num) rfl
      (fun j hj => by interval_cases j <;> rfl) (fun j hj => by interval_cases j <;> rfl)
      (fun j hj => by interval_cases j <;> rfl) (fun j hj h => by interval_cases j <;> first | omega | rfl) (by norm_num)
    have chk := (row_eqs hsat (show 121 < n by omega)).2.2.2.2.2.2.2.2.2.2.1
    simp [rv_mod (show 121 < 256 by norm_num), role, bn] at chk
    rw [const_eq hsat (X := HC) (by simp [consts]) 121 (by omega), hc, const_eq hsat (X := CLEN) (by simp [consts]) 121 (by omega)]
      at chk
    have fl := (step_eqs hsat (r := 121) (by omega)).2.2.1
    simp [rv_mod (show 122 < 256 by norm_num), role, bn] at fl
    have r121 := hra 121 (by omega); have r122 := hra 122 (by omega)
    have top : (M RA 121).val ≤ 1 := by
      have e : (((M RA 122).val + (M RA 121).val : ℕ) : F) = ((1 : ℕ) : F) := by
        push_cast; simp only [ZMod.natCast_zmod_val]; linear_combination fl
      have := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) e; omega
    have r118 := hra 118 (by omega); have r119 := hra 119 (by omega); have r120 := hra 120 (by omega)
    refine ⟨(M RA 118).val + 256 * (M RA 119).val + 65536 * (M RA 120).val + 16777216 * (M RA 121).val, by omega, ?_⟩
    have : M ACC 121 = M RA 118 + 256 * M RA 119 + 65536 * M RA 120 + 16777216 * M RA 121 := by
      rw [show (121 : ℕ) = 118 + 3 by rfl, acc]; simp [Finset.sum_range_succ]; ring
    push_cast; simp only [ZMod.natCast_zmod_val]
    rw [← this]
    rcases chk with h | h
    · exact absurd h one_ne_zero
    · linear_combination h

end Facts

end StarkedAir.Block.Ctx
