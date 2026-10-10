/-
**Sigop walker (M3a.5d), soundness.** In a satisfied `block_walk` trace whose reads are the block's bytes,
whose opcode lookups are table rows and whose range lookups are bytes: each script segment (from a first
row `FS` through `REM` rows) runs the automaton `wstep` of `Spec/BlockFlat.lean` over the script's bytes,
so the segment's `Σ OP · SG` is `walk .op script = sigOps script`.
-/
import StarkedAir.Block.Walk
import StarkedAir.Block.FieldsSound
import StarkedAir.Spec.BlockFlat

namespace StarkedAir.Block.Walk

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)
open StarkedAir.Spec.Block (WS wstep walk sigW)

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
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [first, pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval]

omit hsat in
theorem ev_notFirst {r : ℕ} (hr : r + 1 < n) : notFirst.eval n preCols pub M (r + 1) = 1 := by
  have := ev_first (pub := pub) (M := M) (show r + 1 < n from hr)
  simp only [first] at this
  simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, this]; simp

omit hsat in
theorem ev_last {r : ℕ} (hr : r < n) : isLast.eval n preCols pub M r = if r + 1 < n then 0 else 1 := by
  simp [isLast, om, one, pre, Expr.eval, eval_cst, wrap_zero hr, preCols, PreCol.eval]; split_ifs <;> simp

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 := hsat r hr c hc

omit hsat in
theorem mem_local {c : Expr} (h : c ∈ localC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

theorem bool {c : ℕ} (hc : c ∈ bools) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (mem_local (c := boolC (k c)) (by
    simp only [localC, List.mem_append, List.mem_map]; left; left; left; left; left; exact ⟨c, hc, rfl⟩)) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ localC) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := sat hsat (mem_local h) hr
  simp only [Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

theorem zspec {z inv : ℕ} {e : Expr} (h : ∀ c ∈ isZero z inv e, c ∈ localC) {r : ℕ} (hr : r < n) :
    (M z r = 0 ∨ M z r = 1) ∧ (M z r = 1 ↔ e.eval n preCols pub M r = 0) := by
  have h1 := sat hsat (mem_local (h (boolC (k z)) (by simp [isZero]))) hr
  have h2 := sat hsat (mem_local (h (.mul (k z) e) (by simp [isZero]))) hr
  have h3 := sat hsat (mem_local (h (.mul (om (k z)) (.sub (.mul e (k inv)) one)) (by simp [isZero]))) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, om, one, Nat.cast_one] at h1 h2 h3
  have hb : M z r = 0 ∨ M z r = 1 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  refine ⟨hb, ⟨fun h1' => by rw [h1', one_mul] at h2; exact h2, fun h0 => ?_⟩⟩
  rcases hb with hz | hz
  · rw [hz, h0] at h3; simp at h3
  · exact hz

/-- The defining equations of a row's derived columns. -/
theorem defs {r : ℕ} (hr : r < n) :
    M ACC2 r = M LACC r + M B r * (M (LI 0) r + 256 * M (LI 1) r + 65536 * M (LI 2) r + 16777216 * M (LI 3) r) ∧
    M ENDC r = M (LI 0) r * M LK1 r + M (LI 1) r * M LK2 r + M (LI 3) r * M LK4 r ∧
    M LE r = M LN r * M ENDC r ∧ M LEF r = M LE r * (1 - M TOPF r) ∧ M L4 r = M LEF r * M LK4 r ∧
    M NOP r = M OP r * (1 - (M NZP r + M K1 r + M K2 r + M K4 r)) + M LEF r * M ZA r + M DT r * M ZD r ∧
    M NDT r = M OP r * M NZP r + M LEF r * (1 - M ZA r) + M DT r * (1 - M ZD r) ∧
    M NLN r = M OP r * (M K1 r + M K2 r + M K4 r) + (M LN r - M LE r) ∧
    M NINF r = M LE r * M TOPF r + M INF r ∧
    M NDR r = M OP r * M PN r + M LEF r * M ACC2 r + M DT r * (M DR r - 1) ∧
    M NLACC r = (M LN r - M LE r) * M ACC2 r ∧
    M (NLI 0) r = M OP r * (M K1 r + M K2 r + M K4 r) ∧ M (NLI 1) r = (M LN r - M LE r) * M (LI 0) r ∧
    M (NLI 2) r = (M LN r - M LE r) * M (LI 1) r ∧ M (NLI 3) r = (M LN r - M LE r) * M (LI 2) r ∧
    M NLK1 r = M OP r * M K1 r + (M LN r - M LE r) * M LK1 r ∧ M NLK2 r = M OP r * M K2 r + (M LN r - M LE r) * M LK2 r ∧
    M NLK4 r = M OP r * M K4 r + (M LN r - M LE r) * M LK4 r ∧ M GC r = M ACT r * (1 - M FS r) := by
  have d := fun (a : ℕ) (e : Expr) (h : Expr.sub (k a) e ∈ localC) => defn hsat h hr
  have e1 := d ACC2 (.add (k LACC) (.mul (k B) (.add (k (LI 0)) (.add (.mul (cst 256) (k (LI 1)))
      (.add (.mul (cst 65536) (k (LI 2))) (.mul (cst 16777216) (k (LI 3)))))))) (by simp [localC])
  have e2 := d ENDC (.add (.mul (k (LI 0)) (k LK1)) (.add (.mul (k (LI 1)) (k LK2)) (.mul (k (LI 3)) (k LK4))))
    (by simp [localC])
  have e3 := d LE (.mul (k LN) (k ENDC)) (by simp [localC])
  have e4 := d LEF (.mul (k LE) (om (k TOPF))) (by simp [localC])
  have e5 := d L4 (.mul (k LEF) (k LK4)) (by simp [localC])
  have e6 := d NOP (.add (.mul (k OP) (om (.add (k NZP) (.add (k K1) (.add (k K2) (k K4))))))
      (.add (.mul (k LEF) (k ZA)) (.mul (k DT) (k ZD)))) (by simp [localC])
  have e7 := d NDT (.add (.mul (k OP) (k NZP)) (.add (.mul (k LEF) (om (k ZA))) (.mul (k DT) (om (k ZD)))))
    (by simp [localC])
  have e8 := d NLN (.add (.mul (k OP) (.add (k K1) (.add (k K2) (k K4)))) (.sub (k LN) (k LE))) (by simp [localC])
  have e9 := d NINF (.add (.mul (k LE) (k TOPF)) (k INF)) (by simp [localC])
  have e10 := d NDR (.add (.mul (k OP) (k PN)) (.add (.mul (k LEF) (k ACC2)) (.mul (k DT) (.sub (k DR) one))))
    (by simp [localC])
  have e11 := d NLACC (.mul (.sub (k LN) (k LE)) (k ACC2)) (by simp [localC])
  have e12 := d (NLI 0) (.mul (k OP) (.add (k K1) (.add (k K2) (k K4)))) (by simp [localC])
  have e13 := d (NLI 1) (.mul (.sub (k LN) (k LE)) (k (LI 0))) (by simp [localC])
  have e14 := d (NLI 2) (.mul (.sub (k LN) (k LE)) (k (LI 1))) (by simp [localC])
  have e15 := d (NLI 3) (.mul (.sub (k LN) (k LE)) (k (LI 2))) (by simp [localC])
  have e16 := d NLK1 (.add (.mul (k OP) (k K1)) (.mul (.sub (k LN) (k LE)) (k LK1))) (by simp [localC])
  have e17 := d NLK2 (.add (.mul (k OP) (k K2)) (.mul (.sub (k LN) (k LE)) (k LK2))) (by simp [localC])
  have e18 := d NLK4 (.add (.mul (k OP) (k K4)) (.mul (.sub (k LN) (k LE)) (k LK4))) (by simp [localC])
  have e19 := d GC (.mul (k ACT) (om (k FS))) (by simp [localC])
  simp only [Expr.eval, ev_k hr, eval_cst, om, one, Nat.cast_one, Nat.cast_ofNat] at e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 e13 e14 e15 e16 e17 e18 e19
  refine ⟨by rw [e1]; ring, by rw [e2]; ring, e3, e4, e5, by rw [e6]; ring, by rw [e7]; ring, by rw [e8]; ring, e9,
    by rw [e10]; ring, e11, by rw [e12]; ring, e13, e14, e15, e16, e17, e18, e19⟩

omit hsat in
theorem mem_step {c : Expr} (h : c ∈ stepC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

omit hsat in
theorem mem_script {c : Expr} (h : c ∈ scriptC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

/-- **Continuing a script**: row `r + 1` takes row `r`'s next state, one byte on. -/
theorem step {r : ℕ} (hr : r + 1 < n) (hg : M GC (r + 1) = 1) :
    M OP (r + 1) = M NOP r ∧ M LN (r + 1) = M NLN r ∧ M DT (r + 1) = M NDT r ∧ M INF (r + 1) = M NINF r ∧
    M DR (r + 1) = M NDR r ∧ M LACC (r + 1) = M NLACC r ∧ (∀ j < 4, M (LI j) (r + 1) = M (NLI j) r) ∧
    M LK1 (r + 1) = M NLK1 r ∧ M LK2 (r + 1) = M NLK2 r ∧ M LK4 (r + 1) = M NLK4 r ∧
    M POS (r + 1) = M POS r + 1 ∧ M REM (r + 1) = M REM r - 1 ∧ M ZR r = 0 := by
  have q : ∀ a b, Expr.mul (k GC) (.sub (k a) (kp b)) ∈ stepC → M a (r + 1) = M b r := fun a b h => by
    have := sat hsat (mem_step h) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hg, one_mul, sub_eq_zero] at this
    exact this
  have p1 := sat hsat (mem_step (c := .mul (k GC) (.sub (.sub (k POS) (kp POS)) one)) (by simp [stepC])) hr
  have p2 := sat hsat (mem_step (c := .mul (k GC) (.add (.sub (k REM) (kp REM)) one)) (by simp [stepC])) hr
  have p3 := sat hsat (mem_step (c := .mul (k GC) (kp ZR)) (by simp [stepC])) hr
  simp only [Expr.eval, ev_k hr, ev_kp hr, hg, one_mul, one, eval_cst, Nat.cast_one] at p1 p2 p3
  refine ⟨q OP NOP (by simp [stepC]), q LN NLN (by simp [stepC]), q DT NDT (by simp [stepC]),
    q INF NINF (by simp [stepC]), q DR NDR (by simp [stepC]), q LACC NLACC (by simp [stepC]),
    fun j hj => by interval_cases j <;> exact q _ _ (by simp [stepC]),
    q LK1 NLK1 (by simp [stepC]), q LK2 NLK2 (by simp [stepC]), q LK4 NLK4 (by simp [stepC]),
    by linear_combination p1, by linear_combination p2, p3⟩

/-- Kinds: one-hot on active rows; a first row is an active opcode. -/
theorem kinds {r : ℕ} (hr : r < n) : M OP r + M LN r + M DT r + M INF r = M ACT r ∧
    M FS r * (1 - M ACT r) = 0 ∧ M FS r * (1 - M OP r) = 0 := by
  have c1 := sat hsat (mem_local (c := .sub (.add (k OP) (.add (k LN) (.add (k DT) (k INF)))) (k ACT)) (by simp [localC])) hr
  have c2 := sat hsat (mem_local (c := .mul (k FS) (om (k ACT))) (by simp [localC])) hr
  have c3 := sat hsat (mem_local (c := .mul (k FS) (om (k OP))) (by simp [localC])) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, sub_eq_zero] at c1 c2 c3
  exact ⟨by rw [← c1]; ring, c2, c3⟩

/-- **Script boundaries.** An active row whose remaining count is not 1 is followed by a continuing row. -/
theorem cont {r : ℕ} (hr : r + 1 < n) (ha : M ACT r = 1) (hz : M ZR r = 0) : M GC (r + 1) = 1 := by
  have c3 := sat hsat (mem_script (c := .mul notFirst (.mul (k FS) (om (kp ZR)))) (by simp [scriptC])) hr
  have c4 := sat hsat (mem_script (c := .mul notFirst (.mul (.sub (kp ACT) (k ACT)) (om (kp ZR)))) (by simp [scriptC])) hr
  simp only [Expr.eval, ev_notFirst hr, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one, one_mul, hz, ha,
    sub_zero, mul_one] at c3 c4
  have hact : M ACT (r + 1) = 1 := by linear_combination -c4
  rw [(defs hsat hr).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hact, c3]; ring

end Rows

/-! ### The automaton -/

theorem sigW_eq (x : UInt8) : sigW x = Tables.sigN x.toNat := by
  unfold sigW Tables.sigN
  simp only [← UInt8.toNat_inj]
  rfl

/-- `wstep` at an opcode, by the byte's value. -/
theorem wstep_op (x : UInt8) : wstep .op x =
    if x.toNat < 0x4c then (if x.toNat = 0 then .op else .data x.toNat, 0)
    else if x.toNat = 0x4c then (.len 1 0 0, 0) else if x.toNat = 0x4d then (.len 2 0 0, 0)
    else if x.toNat = 0x4e then (.len 4 0 0, 0) else (.op, Tables.sigN x.toNat) := by
  simp only [wstep, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, sigW_eq]
  rfl

/-- One-hot length-byte count `k ∈ {1, 2, 4}`. -/
def LKof (M : ℕ → ℕ → F) (r k : ℕ) : Prop :=
  (k = 1 ∧ M LK1 r = 1 ∧ M LK2 r = 0 ∧ M LK4 r = 0) ∨ (k = 2 ∧ M LK1 r = 0 ∧ M LK2 r = 1 ∧ M LK4 r = 0) ∨
    (k = 4 ∧ M LK1 r = 0 ∧ M LK2 r = 0 ∧ M LK4 r = 1)

/-- **Row `r` represents automaton state `s`.** -/
def Rep (M : ℕ → ℕ → F) (r : ℕ) : WS → Prop
  | .op => M OP r = 1
  | .len k i acc => M LN r = 1 ∧ LKof M r k ∧ i < k ∧ (∀ j < 4, M (LI j) r = if j = i then 1 else 0) ∧
      M LACC r = (acc : F) ∧ acc < 256 ^ i
  | .data d => M DT r = 1 ∧ M DR r = (d : F) ∧ 1 ≤ d ∧ d < 2 ^ 25

section Walker

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
  (hopc : ∀ r < n, M OP r = 1 → M PN r = (Tables.pushN (M B r).val : F) ∧ M K1 r = (Tables.isK 0x4c (M B r).val : F) ∧
    M K2 r = (Tables.isK 0x4d (M B r).val : F) ∧ M K4 r = (Tables.isK 0x4e (M B r).val : F) ∧
    M SG r = (Tables.sigN (M B r).val : F) ∧ M NZP r = (Tables.nzp (M B r).val : F))
  (hr8 : ∀ r < n, M TOPF r = 1 → (M B r - 2).val < 256)
include hsat hopc hr8

omit hopc hr8 in
/-- On a row of one kind, the other kinds are 0 and the row is active. -/
theorem only {r : ℕ} (hr : r < n) {c : ℕ} (hc : c ∈ [OP, LN, DT, INF]) (h : M c r = 1) :
    M ACT r = 1 ∧ ∀ d ∈ [OP, LN, DT, INF], d ≠ c → M d r = 0 := by
  obtain ⟨hk, -, -⟩ := kinds hsat hr
  have bv := fun d (hd : d ∈ bools) => Fields.bool_val (bool hsat hd hr)
  obtain ⟨vo, lo⟩ := bv OP (by simp [bools]); obtain ⟨vl, ll⟩ := bv LN (by simp [bools])
  obtain ⟨vd, ld⟩ := bv DT (by simp [bools]); obtain ⟨vi, li⟩ := bv INF (by simp [bools])
  obtain ⟨va, la⟩ := bv ACT (by simp [bools])
  have e : (((M OP r).val + (M LN r).val + (M DT r).val + (M INF r).val : ℕ) : F) = (((M ACT r).val : ℕ) : F) := by
    push_cast; rw [← vo, ← vl, ← vd, ← vi, ← va]; exact hk
  have en := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
  have hc1 : (M c r).val = 1 := by rw [h]; exact ZMod.val_one _
  have z : ∀ d ∈ [OP, LN, DT, INF], d ≠ c → (M d r).val = 0 := by
    intro d hd hne
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc hd
    rcases hc with rfl | rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | omega
  have hact : (M ACT r).val = 1 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl <;> omega
  refine ⟨by rw [va, hact]; simp, fun d hd hne => ?_⟩
  have := z d hd hne
  have hdb : d ∈ bools := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl | rfl <;> simp [bools]
  have hv := (bv d hdb).1
  rw [hv, this]; simp

/-- **An opcode row steps as `wstep .op`.** -/
theorem trans_op {r : ℕ} (hr : r + 1 < n) (hop : M OP r = 1) (x : UInt8) (hx : (M B r).val = x.toNat) :
    M OP r * M SG r = (((wstep .op x).2 : ℕ) : F) ∧ (M GC (r + 1) = 1 → Rep M (r + 1) (wstep .op x).1) := by
  have hrn : r < n := by omega
  obtain ⟨-, hz⟩ := only hsat hrn (c := OP) (by simp) hop
  have hl : M LN r = 0 := hz LN (by simp) (by simp [LN, OP])
  have hd : M DT r = 0 := hz DT (by simp) (by simp [DT, OP])
  have hi : M INF r = 0 := hz INF (by simp) (by simp [INF, OP])
  obtain ⟨-, -, hLE, hLEF, -, hNOP, hNDT, hNLN, hNINF, hNDR, hNLACC, hNLI0, hNLI1, hNLI2, hNLI3, hNLK1, hNLK2, hNLK4,
    -⟩ := defs hsat hrn
  obtain ⟨hpn, hk1, hk2, hk4, hsg, hnzp⟩ := hopc r hrn hop
  rw [hx] at hpn hk1 hk2 hk4 hsg hnzp
  have hle0 : M LE r = 0 := by rw [hLE, hl, zero_mul]
  have hlef0 : M LEF r = 0 := by rw [hLEF, hle0, zero_mul]
  have xb : x.toNat < 256 := x.toNat_lt
  set b := x.toNat
  rw [wstep_op x]
  -- the next row's columns are this row's next state
  have nxt : M GC (r + 1) = 1 → M OP (r + 1) = 1 - ((Tables.nzp b : F) + Tables.isK 0x4c b + Tables.isK 0x4d b + Tables.isK 0x4e b) ∧
      M LN (r + 1) = (Tables.isK 0x4c b : F) + Tables.isK 0x4d b + Tables.isK 0x4e b ∧ M DT (r + 1) = (Tables.nzp b : F) ∧
      M DR (r + 1) = (Tables.pushN b : F) ∧ M LACC (r + 1) = 0 ∧
      M (LI 0) (r + 1) = (Tables.isK 0x4c b : F) + Tables.isK 0x4d b + Tables.isK 0x4e b ∧
      M (LI 1) (r + 1) = 0 ∧ M (LI 2) (r + 1) = 0 ∧ M (LI 3) (r + 1) = 0 ∧
      M LK1 (r + 1) = (Tables.isK 0x4c b : F) ∧ M LK2 (r + 1) = (Tables.isK 0x4d b : F) ∧
      M LK4 (r + 1) = (Tables.isK 0x4e b : F) := by
    intro hg
    obtain ⟨sOP, sLN, sDT, -, sDR, sLACC, sLI, sLK1, sLK2, sLK4, -⟩ := step hsat hr hg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [sOP, hNOP, hop, hlef0, hd, hnzp, hk1, hk2, hk4]; ring
    · rw [sLN, hNLN, hop, hl, hle0, hk1, hk2, hk4]; ring
    · rw [sDT, hNDT, hop, hlef0, hd, hnzp]; ring
    · rw [sDR, hNDR, hop, hlef0, hd, hpn]; ring
    · rw [sLACC, hNLACC, hl, hle0]; ring
    · rw [sLI 0 (by norm_num), hNLI0, hop, hk1, hk2, hk4]; ring
    · rw [sLI 1 (by norm_num), hNLI1, hl, hle0]; ring
    · rw [sLI 2 (by norm_num), hNLI2, hl, hle0]; ring
    · rw [sLI 3 (by norm_num), hNLI3, hl, hle0]; ring
    · rw [sLK1, hNLK1, hop, hk1, hl, hle0]; ring
    · rw [sLK2, hNLK2, hop, hk2, hl, hle0]; ring
    · rw [sLK4, hNLK4, hop, hk4, hl, hle0]; ring
  rw [hop, one_mul, hsg]
  by_cases h1 : b < 0x4c
  · rw [if_pos h1]
    have sg0 : Tables.sigN b = 0 := by unfold Tables.sigN; split_ifs <;> omega
    have k0 : Tables.isK 0x4c b = 0 ∧ Tables.isK 0x4d b = 0 ∧ Tables.isK 0x4e b = 0 := by
      unfold Tables.isK; refine ⟨?_, ?_, ?_⟩ <;> split_ifs <;> omega
    by_cases h0 : b = 0
    · rw [if_pos h0]
      refine ⟨by simp [sg0], fun hg => ?_⟩
      obtain ⟨o, -⟩ := nxt hg
      show M OP (r + 1) = 1
      rw [o, k0.1, k0.2.1, k0.2.2, show Tables.nzp b = 0 by unfold Tables.nzp; split_ifs <;> omega]; simp
    · rw [if_neg h0]
      refine ⟨by simp [sg0], fun hg => ?_⟩
      obtain ⟨-, -, dt, dr, -⟩ := nxt hg
      refine ⟨?_, ?_, by omega, by omega⟩
      · rw [dt, show Tables.nzp b = 1 by unfold Tables.nzp; split_ifs <;> omega]; simp
      · rw [dr, show Tables.pushN b = b by unfold Tables.pushN; split_ifs <;> omega]
  · rw [if_neg h1]
    have nz : Tables.nzp b = 0 := by unfold Tables.nzp; split_ifs <;> omega
    by_cases h2 : b = 0x4c
    · rw [if_pos h2]
      refine ⟨by simp [Tables.sigN, h2], fun hg => ?_⟩
      obtain ⟨-, ln, -, -, lacc, li0, li1, li2, li3, lk1, lk2, lk4⟩ := nxt hg
      simp only [Tables.isK, h2] at ln li0 lk1 lk2 lk4
      norm_num at ln li0 lk1 lk2 lk4
      refine ⟨ln, Or.inl ⟨rfl, lk1, lk2, lk4⟩, by norm_num, fun j hj => ?_, by simpa using lacc, by norm_num⟩
      interval_cases j <;> simp [li0, li1, li2, li3]
    by_cases h3 : b = 0x4d
    · rw [if_neg h2, if_pos h3]
      refine ⟨by simp [Tables.sigN, h3], fun hg => ?_⟩
      obtain ⟨-, ln, -, -, lacc, li0, li1, li2, li3, lk1, lk2, lk4⟩ := nxt hg
      simp only [Tables.isK, h3] at ln li0 lk1 lk2 lk4
      norm_num at ln li0 lk1 lk2 lk4
      refine ⟨ln, Or.inr (Or.inl ⟨rfl, lk1, lk2, lk4⟩), by norm_num, fun j hj => ?_, by simpa using lacc, by norm_num⟩
      interval_cases j <;> simp [li0, li1, li2, li3]
    by_cases h4 : b = 0x4e
    · rw [if_neg h2, if_neg h3, if_pos h4]
      refine ⟨by simp [Tables.sigN, h4], fun hg => ?_⟩
      obtain ⟨-, ln, -, -, lacc, li0, li1, li2, li3, lk1, lk2, lk4⟩ := nxt hg
      simp only [Tables.isK, h4] at ln li0 lk1 lk2 lk4
      norm_num at ln li0 lk1 lk2 lk4
      refine ⟨ln, Or.inr (Or.inr ⟨rfl, lk1, lk2, lk4⟩), by norm_num, fun j hj => ?_, by simpa using lacc, by norm_num⟩
      interval_cases j <;> simp [li0, li1, li2, li3]
    · rw [if_neg h2, if_neg h3, if_neg h4]
      refine ⟨rfl, fun hg => ?_⟩
      obtain ⟨o, -⟩ := nxt hg
      show M OP (r + 1) = 1
      rw [o, nz, show Tables.isK 0x4c b = 0 by unfold Tables.isK; split_ifs <;> omega,
        show Tables.isK 0x4d b = 0 by unfold Tables.isK; split_ifs <;> omega,
        show Tables.isK 0x4e b = 0 by unfold Tables.isK; split_ifs <;> omega]; simp

/-- **A data row steps as `wstep (.data d)`.** -/
theorem trans_data {r d : ℕ} (hr : r + 1 < n) (hrep : Rep M r (.data d)) (x : UInt8) :
    M OP r * M SG r = (((wstep (.data d) x).2 : ℕ) : F) ∧ (M GC (r + 1) = 1 → Rep M (r + 1) (wstep (.data d) x).1) := by
  have hrn : r < n := by omega
  obtain ⟨hdt, hdr, hd1, hd25⟩ := hrep
  obtain ⟨-, hz⟩ := only hsat hrn (c := DT) (by simp) hdt
  have ho : M OP r = 0 := hz OP (by simp) (by simp [DT, OP])
  have hl : M LN r = 0 := hz LN (by simp) (by simp [LN, DT])
  have hi : M INF r = 0 := hz INF (by simp) (by simp [INF, DT])
  obtain ⟨-, -, hLE, hLEF, -, hNOP, hNDT, -, -, hNDR, -⟩ := defs hsat hrn
  have hle0 : M LE r = 0 := by rw [hLE, hl, zero_mul]
  have hlef0 : M LEF r = 0 := by rw [hLEF, hle0, zero_mul]
  have zd := zspec hsat (z := ZD) (inv := INVD) (e := .sub (k DR) one) (fun c hc => by simp only [localC, List.mem_append]; tauto) hrn
  simp only [Expr.eval, ev_k hrn, one, eval_cst, Nat.cast_one] at zd
  refine ⟨by simp [wstep, ho], fun hg => ?_⟩
  obtain ⟨sOP, -, sDT, -, sDR, -⟩ := step hsat hr hg
  simp only [wstep]
  by_cases h1 : d = 1
  · rw [if_pos h1]
    show M OP (r + 1) = 1
    have : M ZD r = 1 := zd.2.2 (by rw [hdr, h1]; simp)
    rw [sOP, hNOP, ho, hlef0, hdt, this]; ring
  · rw [if_neg h1]
    have hz0 : M ZD r = 0 := by
      rcases zd.1 with h | h
      · exact h
      · exfalso
        have := zd.2.1 h
        rw [hdr, sub_eq_zero] at this
        have := natCast_inj_of_lt (a := d) (b := 1) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) (by simpa using this)
        exact h1 this
    refine ⟨by rw [sDT, hNDT, ho, hlef0, hdt, hz0]; ring, ?_, by omega, by omega⟩
    rw [sDR, hNDR, ho, hlef0, hdt, hdr]; push_cast [Nat.cast_sub (show 1 ≤ d by omega)]; ring

/-- **A run-to-the-end data row** counts nothing, and so does the next. -/
theorem trans_inf {r : ℕ} (hr : r + 1 < n) (hinf : M INF r = 1) :
    M OP r * M SG r = 0 ∧ (M GC (r + 1) = 1 → M INF (r + 1) = 1) := by
  have hrn : r < n := by omega
  obtain ⟨-, hz⟩ := only hsat hrn (c := INF) (by simp) hinf
  have ho : M OP r = 0 := hz OP (by simp) (by simp [INF, OP])
  have hl : M LN r = 0 := hz LN (by simp) (by simp [INF, LN])
  obtain ⟨-, -, hLE, -, -, -, -, -, hNINF, -⟩ := defs hsat hrn
  refine ⟨by rw [ho, zero_mul], fun hg => ?_⟩
  obtain ⟨-, -, -, sINF, -⟩ := step hsat hr hg
  rw [sINF, hNINF, hLE, hl, hinf]; ring

/-- **A length-byte row steps as `wstep (.len k i acc)`**; a 4-byte length whose top byte is at least 2 goes to
the run-to-the-end state (data of at least `2^25` bytes). -/
theorem trans_len {r k i acc : ℕ} (hr : r + 1 < n) (hrep : Rep M r (.len k i acc)) (x : UInt8)
    (hx : (M B r).val = x.toNat) :
    M OP r * M SG r = (((wstep (.len k i acc) x).2 : ℕ) : F) ∧
    (M GC (r + 1) = 1 → Rep M (r + 1) (wstep (.len k i acc) x).1 ∨
      (M INF (r + 1) = 1 ∧ ∃ d, 2 ^ 25 ≤ d ∧ (wstep (.len k i acc) x).1 = .data d)) := by
  have hrn : r < n := by omega
  obtain ⟨hln, hlk, hik, hli, hlacc, hacc⟩ := hrep
  obtain ⟨-, hz⟩ := only hsat hrn (c := LN) (by simp) hln
  have ho : M OP r = 0 := hz OP (by simp) (by simp [LN, OP])
  have hd : M DT r = 0 := hz DT (by simp) (by simp [LN, DT])
  have hi : M INF r = 0 := hz INF (by simp) (by simp [INF, LN])
  obtain ⟨hACC2, hENDC, hLE, hLEF, hL4, hNOP, hNDT, hNLN, hNINF, hNDR, hNLACC, hNLI0, hNLI1, hNLI2, hNLI3, hNLK1,
    hNLK2, hNLK4, -⟩ := defs hsat hrn
  have xb : x.toNat < 256 := x.toNat_lt
  have hk : k = 1 ∨ k = 2 ∨ k = 4 := by rcases hlk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hi4 : i < 4 := by omega
  -- the length so far, with this byte
  have w : M (LI 0) r + 256 * M (LI 1) r + 65536 * M (LI 2) r + 16777216 * M (LI 3) r = ((256 ^ i : ℕ) : F) := by
    rw [hli 0 (by norm_num), hli 1 (by norm_num), hli 2 (by norm_num), hli 3 (by norm_num)]
    interval_cases i <;> norm_num
  have acc2 : M ACC2 r = ((acc + x.toNat * 256 ^ i : ℕ) : F) := by
    rw [hACC2, hlacc, w, ← ZMod.natCast_zmod_val (M B r), hx]; push_cast; ring
  -- the end flag: this is the last length byte
  have endc : M ENDC r = if i + 1 = k then 1 else 0 := by
    rw [hENDC, hli 0 (by norm_num), hli 1 (by norm_num), hli 3 (by norm_num)]
    rcases hlk with ⟨rfl, a, b, c⟩ | ⟨rfl, a, b, c⟩ | ⟨rfl, a, b, c⟩ <;> rw [a, b, c] <;> interval_cases i <;> norm_num
  have hle : M LE r = if i + 1 = k then 1 else 0 := by rw [hLE, hln, one_mul, endc]
  refine ⟨by rw [ho, zero_mul]; simp only [wstep]; split_ifs <;> simp, fun hg => ?_⟩
  obtain ⟨sOP, sLN, sDT, sINF, sDR, sLACC, sLI, sLK1, sLK2, sLK4, -⟩ := step hsat hr hg
  simp only [wstep]
  by_cases hend : i + 1 = k
  · rw [if_pos hend]
    rw [if_pos hend] at hle
    have topf := bool hsat (c := TOPF) (by simp [bools]) hrn
    rcases topf with t0 | t1
    · -- not a huge push: the length is exact
      have hlef : M LEF r = 1 := by rw [hLEF, hle, t0]; ring
      have small : acc + x.toNat * 256 ^ i < 2 ^ 25 := by
        rcases hk with rfl | rfl | rfl
        · have : i = 0 := by omega
          subst this; simp at hacc ⊢; omega
        · have : i = 1 := by omega
          subst this; simp at hacc ⊢; omega
        · -- `PUSHDATA4`: the top byte is 0 or 1
          have : i = 3 := by omega
          subst this
          have lk4 : M LK4 r = 1 := by
            rcases hlk with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, -, -, h⟩ <;> first | omega | exact h
          have l4 : M L4 r = 1 := by rw [hL4, hlef, lk4]; ring
          have c := sat hsat (mem_local (c := .mul (Walk.k L4) (.mul (Walk.k B) (.sub (Walk.k B) one))) (by simp [localC])) hrn
          simp only [Expr.eval, ev_k hrn, l4, one_mul, one, eval_cst, Nat.cast_one] at c
          have hx1 : x.toNat ≤ 1 := by
            rcases mul_eq_zero.mp c with h | h
            · rw [h] at hx; simp at hx; omega
            · rw [sub_eq_zero.mp h, ZMod.val_one] at hx; omega
          simp at hacc ⊢; omega
      have za := zspec hsat (z := ZA) (inv := INVA) (e := Walk.k ACC2) (fun c hc => by simp only [localC, List.mem_append]; tauto) hrn
      simp only [ev_k hrn] at za
      left
      by_cases h0 : acc + x.toNat * 256 ^ i = 0
      · rw [if_pos h0]
        show M OP (r + 1) = 1
        have : M ZA r = 1 := za.2.2 (by rw [acc2, h0]; simp)
        rw [sOP, hNOP, ho, hlef, hd, this]; ring
      · rw [if_neg h0]
        have hz0 : M ZA r = 0 := by
          rcases za.1 with h | h
          · exact h
          · exfalso; have := za.2.1 h; rw [acc2] at this
            exact h0 (natCast_inj_of_lt (b := 0) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) (by simpa using this))
        exact ⟨by rw [sDT, hNDT, ho, hlef, hd, hz0]; ring, by rw [sDR, hNDR, ho, hlef, hd, acc2]; ring, by omega, small⟩
    · -- a push of at least `2^25` bytes: the rest of the script is data
      right
      have lk4 : M LK4 r = 1 := by
        have c := sat hsat (mem_local (c := .mul (Walk.k TOPF) (om (Walk.k LK4))) (by simp [localC])) hrn
        simp only [Expr.eval, ev_k hrn, t1, one_mul, om, one, eval_cst, Nat.cast_one, sub_eq_zero] at c
        exact c.symm
      have hk4 : k = 4 := by
        rcases hlk with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨h, -⟩
        · rw [lk4] at h; exact absurd h one_ne_zero
        · rw [lk4] at h; exact absurd h one_ne_zero
        · exact h
      have hi3 : i = 3 := by omega
      have x2 : 2 ≤ x.toNat := by
        have := hr8 r hrn t1
        rw [← ZMod.natCast_zmod_val (M B r), hx] at this
        by_contra hc
        have e : ((x.toNat : ℕ) : F) - 2 = ((P - (2 - x.toNat) : ℕ) : F) := by
          rw [Nat.cast_sub (by unfold P; omega)]; simp; push_cast [Nat.cast_sub (show x.toNat ≤ 2 by omega)]; ring
        rw [e, ZMod.val_natCast_of_lt (by unfold P; omega)] at this
        unfold P at this; omega
      refine ⟨by rw [sINF, hNINF, hle, t1, hi]; ring, acc + x.toNat * 256 ^ i, ?_, ?_⟩
      · subst hi3; nlinarith
      · rw [if_neg (by subst hi3; nlinarith)]
  · rw [if_neg hend]
    rw [if_neg hend] at hle
    have hlef : M LEF r = 0 := by rw [hLEF, hle, zero_mul]
    left
    refine ⟨by rw [sLN, hNLN, ho, hln, hle]; ring, ?_, by omega, fun j hj => ?_, by rw [sLACC, hNLACC, hln, hle, acc2]; ring, ?_⟩
    · rcases hlk with ⟨rfl, a, b, c⟩ | ⟨rfl, a, b, c⟩ | ⟨rfl, a, b, c⟩
      · exact Or.inl ⟨rfl, by rw [sLK1, hNLK1, ho, hln, hle, a]; ring, by rw [sLK2, hNLK2, ho, hln, hle, b]; ring,
          by rw [sLK4, hNLK4, ho, hln, hle, c]; ring⟩
      · exact Or.inr (Or.inl ⟨rfl, by rw [sLK1, hNLK1, ho, hln, hle, a]; ring, by rw [sLK2, hNLK2, ho, hln, hle, b]; ring,
          by rw [sLK4, hNLK4, ho, hln, hle, c]; ring⟩)
      · exact Or.inr (Or.inr ⟨rfl, by rw [sLK1, hNLK1, ho, hln, hle, a]; ring, by rw [sLK2, hNLK2, ho, hln, hle, b]; ring,
          by rw [sLK4, hNLK4, ho, hln, hle, c]; ring⟩)
    · rw [sLI j hj]
      interval_cases j
      · rw [hNLI0, ho]; simp
      · rw [hNLI1, hln, hle, hli 0 (by norm_num)]; by_cases h : i = 0 <;> simp [h]; omega
      · rw [hNLI2, hln, hle, hli 1 (by norm_num)]; by_cases h : i = 1 <;> simp [h]; omega
      · rw [hNLI3, hln, hle, hli 2 (by norm_num)]; by_cases h : i = 2 <;> simp [h]; omega
    · have := x.toNat_lt
      calc acc + x.toNat * 256 ^ i < 256 ^ i + 255 * 256 ^ i := by nlinarith
        _ = 256 ^ (i + 1) := by ring

end Walker

theorem slice_cons {R : Spec.Block.Bytes} {a L : ℕ} (h : a < R.length) :
    Fields.slice R a (L + 1) = R.getD a 0 :: Fields.slice R (a + 1) L := by
  simp only [Fields.slice]
  rw [List.drop_eq_getElem_cons h, List.take_succ_cons, List.getD_eq_getElem _ _ h]

section Segments

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
  (hopc : ∀ r < n, M OP r = 1 → M PN r = (Tables.pushN (M B r).val : F) ∧ M K1 r = (Tables.isK 0x4c (M B r).val : F) ∧
    M K2 r = (Tables.isK 0x4d (M B r).val : F) ∧ M K4 r = (Tables.isK 0x4e (M B r).val : F) ∧
    M SG r = (Tables.sigN (M B r).val : F) ∧ M NZP r = (Tables.nzp (M B r).val : F))
  (hr8 : ∀ r < n, M TOPF r = 1 → (M B r - 2).val < 256)
  (R : Spec.Block.Bytes)
  (hread : ∀ r < n, M ACT r = 1 → (M POS r).val < R.length ∧ (M B r).val = (R.getD (M POS r).val 0).toNat)
  (hR : R.length ≤ 2 ^ 25)
include hsat hopc hr8 hread hR

omit hopc hr8 hread hR in
/-- An active row is not the last row. -/
theorem act_lt {r : ℕ} (hr : r < n) (ha : M ACT r = 1) : r + 1 < n := by
  have c := sat hsat (mem_script (c := .mul isLast (k ACT)) (by simp [scriptC])) hr
  simp only [Expr.eval, ev_last hr, ev_k hr, ha, mul_one] at c
  by_contra h
  rw [if_neg h] at c; exact one_ne_zero c

/-- **A script segment walks its bytes.** From an active row `r` with `L` bytes left: if the row represents
state `s`, the segment's sigop sum is `walk s` of those bytes; a run-to-the-end row counts nothing. -/
theorem segment : ∀ L r, r < n → M ACT r = 1 → (M REM r).val = L → 1 ≤ L → L ≤ 2 ^ 25 →
    (∀ s, Rep M r s → ∑ j ∈ Finset.range L, M OP (r + j) * M SG (r + j) =
      ((Spec.Block.walk s (Fields.slice R (M POS r).val L) : ℕ) : F)) ∧
    (M INF r = 1 → ∑ j ∈ Finset.range L, M OP (r + j) * M SG (r + j) = 0) := by
  intro L
  induction L with
  | zero => intro r _ _ _ h; omega
  | succ L ih =>
    intro r hr ha hrem _ hL
    have hr1 := act_lt hsat hr ha
    obtain ⟨hpos, hx⟩ := hread r hr ha
    set x := R.getD (M POS r).val 0
    have hsl := slice_cons (L := L) hpos
    -- the row's own count and next state
    have tr : ∀ s, Rep M r s → M OP r * M SG r = (((wstep s x).2 : ℕ) : F) ∧
        (M GC (r + 1) = 1 → Rep M (r + 1) (wstep s x).1 ∨
          (M INF (r + 1) = 1 ∧ ∃ d, 2 ^ 25 ≤ d ∧ (wstep s x).1 = .data d)) := by
      intro s hs
      match s, hs with
      | .op, hs => obtain ⟨a, b⟩ := trans_op hsat hopc hr8 hr1 hs x hx; exact ⟨a, fun hg => Or.inl (b hg)⟩
      | .len k i acc, hs => exact trans_len hsat hopc hr8 hr1 hs x hx
      | .data d, hs => obtain ⟨a, b⟩ := trans_data hsat hopc hr8 hr1 hs x; exact ⟨a, fun hg => Or.inl (b hg)⟩
    rcases Nat.eq_zero_or_pos L with h0 | hpos'
    · -- the last byte
      subst h0
      refine ⟨fun s hs => ?_, fun hi => ?_⟩
      · rw [show (0 : ℕ) + 1 = 1 from rfl] at hsl ⊢
        rw [Finset.sum_range_one, Nat.add_zero, (tr s hs).1, hsl]
        simp [Fields.slice, Spec.Block.walk, x, List.getD_eq_getElem?_getD]
      · simp [(trans_inf hsat hopc hr8 hr1 hi).1]
    · -- more bytes: the next row continues the segment
      have zr := zspec hsat (z := ZR) (inv := INVR) (e := .sub (k REM) one)
        (fun c hc => by simp only [localC, List.mem_append]; tauto) hr
      simp only [Expr.eval, ev_k hr, one, eval_cst, Nat.cast_one] at zr
      have hz : M ZR r = 0 := by
        rcases zr.1 with h | h
        · exact h
        · exfalso; have := zr.2.1 h
          rw [← ZMod.natCast_zmod_val (M REM r), hrem, sub_eq_zero] at this
          have := natCast_inj_of_lt (a := L + 1) (b := 1) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num))
            (by simpa using this)
          omega
      have hg := cont hsat hr1 ha hz
      obtain ⟨-, -, -, -, -, -, -, -, -, -, sPOS, sREM, -⟩ := step hsat hr1 hg
      have ha1 : M ACT (r + 1) = 1 := by
        have := (defs hsat hr1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        have fsb := bool hsat (c := FS) (by simp [bools]) hr1
        have acb := bool hsat (c := ACT) (by simp [bools]) hr1
        rw [hg] at this
        rcases acb with h | h
        · rw [h, zero_mul] at this; exact absurd this one_ne_zero
        · exact h
      have hrem1 : (M REM (r + 1)).val = L := by
        rw [sREM, ← ZMod.natCast_zmod_val (M REM r), hrem]
        rw [show ((L + 1 : ℕ) : F) - 1 = ((L : ℕ) : F) by push_cast; ring]
        exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
      have hpos1 : (M POS (r + 1)).val = (M POS r).val + 1 := by
        have e : M POS (r + 1) = (((M POS r).val + 1 : ℕ) : F) := by
          rw [sPOS]; push_cast; rw [ZMod.natCast_zmod_val]
        rw [e]
        exact ZMod.val_natCast_of_lt (Fields.lt_P (m := (M POS r).val + 1) (by omega))
      obtain ⟨ihr, ihi⟩ := ih (r + 1) hr1 ha1 hrem1 hpos' (by omega)
      have split : ∑ j ∈ Finset.range (L + 1), M OP (r + j) * M SG (r + j) =
          M OP r * M SG r + ∑ j ∈ Finset.range L, M OP (r + 1 + j) * M SG (r + 1 + j) := by
        rw [Finset.sum_range_succ', add_comm]; simp only [Nat.add_zero]; congr 1
        apply Finset.sum_congr rfl; intro j _; rw [show r + (j + 1) = r + 1 + j by ring]
      refine ⟨fun s hs => ?_, fun hi => ?_⟩
      · obtain ⟨o, nx⟩ := tr s hs
        rw [split, o, hsl, Spec.Block.walk]
        rcases nx hg with h | ⟨hi1, d, hd, he⟩
        · rw [ihr _ h, hpos1]; push_cast; simp [x, List.getD_eq_getElem?_getD]
        · have hlen : (Fields.slice R ((M POS r).val + 1) L).length ≤ L := List.length_take_le _ _
          rw [ihi hi1, he, Spec.Block.walk_data _ _ (by omega), if_neg (by omega)]
          simp [x, List.getD_eq_getElem?_getD]
      · obtain ⟨o, nx⟩ := trans_inf hsat hopc hr8 hr1 hi
        rw [split, o, ihi (nx hg)]; simp

omit hopc hr8 hread hR in
/-- A segment's rows: from an active row with `L` bytes left, the next `L − 1` rows continue it and its last
row ends it. -/
theorem seg_rows : ∀ L r, r < n → M ACT r = 1 → (M REM r).val = L → 1 ≤ L → L ≤ 2 ^ 25 →
    (∀ j, 1 ≤ j → j < L → M GC (r + j) = 1) ∧ M ZR (r + L - 1) = 1 ∧ M ACT (r + L - 1) = 1 ∧ r + L < n := by
  intro L
  induction L with
  | zero => intro r _ _ _ h; omega
  | succ L ih =>
    intro r hr ha hrem _ hL
    have hr1 := act_lt hsat hr ha
    have zr := zspec hsat (z := ZR) (inv := INVR) (e := .sub (k REM) one)
      (fun c hc => by simp only [localC, List.mem_append]; tauto) hr
    simp only [Expr.eval, ev_k hr, one, eval_cst, Nat.cast_one] at zr
    rcases Nat.eq_zero_or_pos L with h0 | hpos
    · subst h0
      have : M ZR r = 1 := zr.2.2 (by rw [← ZMod.natCast_zmod_val (M REM r), hrem]; simp)
      exact ⟨fun j h1 h2 => by omega, by simpa using this, by simpa using ha, hr1⟩
    · have hz : M ZR r = 0 := by
        rcases zr.1 with h | h
        · exact h
        · exfalso; have := zr.2.1 h
          rw [← ZMod.natCast_zmod_val (M REM r), hrem, sub_eq_zero] at this
          have := natCast_inj_of_lt (a := L + 1) (b := 1) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num))
            (by simpa using this)
          omega
      have hg := cont hsat hr1 ha hz
      obtain ⟨-, -, -, -, -, -, -, -, -, -, -, sREM, -⟩ := step hsat hr1 hg
      have ha1 : M ACT (r + 1) = 1 := by
        have := (defs hsat hr1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
        rw [hg] at this
        rcases bool hsat (c := ACT) (by simp [bools]) hr1 with h | h
        · rw [h, zero_mul] at this; exact absurd this one_ne_zero
        · exact h
      have hrem1 : (M REM (r + 1)).val = L := by
        have e : M REM (r + 1) = ((L : ℕ) : F) := by
          rw [sREM, ← ZMod.natCast_zmod_val (M REM r), hrem]; push_cast; ring
        rw [e]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
      obtain ⟨c1, c2, c3, c4⟩ := ih (r + 1) hr1 ha1 hrem1 hpos (by omega)
      refine ⟨fun j h1 h2 => ?_, by rw [show r + (L + 1) - 1 = r + 1 + L - 1 by omega]; exact c2,
        by rw [show r + (L + 1) - 1 = r + 1 + L - 1 by omega]; exact c3, by omega⟩
      rcases Nat.eq_or_lt_of_le h1 with e | e
      · subst e; exact hg
      · rw [show r + j = r + 1 + (j - 1) by omega]; exact c1 (j - 1) (by omega) (by omega)

omit hopc hr8 hread hR in
theorem sums_eq : ∀ r < n, M SUMS r = ∑ j ∈ Finset.range (r + 1), M OP j * M SG j := by
  intro r
  induction r with
  | zero =>
    intro h0
    have c := sat hsat (mem_script (c := .mul first (.sub (k SUMS) (.mul (k OP) (k SG)))) (by simp [scriptC])) h0
    simp only [Expr.eval, ev_first h0, if_true, one_mul, ev_k h0, sub_eq_zero] at c
    simp [c]
  | succ r ih =>
    intro hr
    have c := sat hsat (mem_script (c := .mul notFirst (.sub (.sub (k SUMS) (kp SUMS)) (.mul (k OP) (k SG))))
      (by simp [scriptC])) hr
    simp only [Expr.eval, ev_notFirst hr, one_mul, ev_k hr, ev_kp hr] at c
    rw [Finset.sum_range_succ, ← ih (by omega)]; linear_combination c

omit hopc hr8 hread hR in
/-- Inactive rows are a suffix and count nothing. -/
theorem inactive {f : ℕ} (hf : f < n) (h0 : M ACT f = 0) :
    ∀ j, f ≤ j → j < n → M ACT j = 0 ∧ M OP j * M SG j = 0 ∧ M FS j = 0 := by
  intro j h1 h2
  have hact : M ACT j = 0 := by
    induction j, h1 using Nat.le_induction with
    | base => exact h0
    | succ j hj ih =>
      have c := sat hsat (mem_script (c := .mul notFirst (.mul (k ACT) (om (kp ACT)))) (by simp [scriptC])) h2
      simp only [Expr.eval, ev_notFirst h2, one_mul, ev_k h2, ev_kp h2, om, one, eval_cst, Nat.cast_one,
        ih (by omega), sub_zero, mul_one] at c
      exact c
  obtain ⟨hk, hfa, -⟩ := kinds hsat h2
  have bv := fun d (hd : d ∈ bools) => Fields.bool_val (bool hsat hd h2)
  obtain ⟨vo, lo⟩ := bv OP (by simp [bools]); obtain ⟨vl, ll⟩ := bv LN (by simp [bools])
  obtain ⟨vd, ld⟩ := bv DT (by simp [bools]); obtain ⟨vi, li⟩ := bv INF (by simp [bools])
  have e : (((M OP j).val + (M LN j).val + (M DT j).val + (M INF j).val : ℕ) : F) = ((0 : ℕ) : F) := by
    push_cast; rw [← vo, ← vl, ← vd, ← vi, hk, hact]
  have := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num)) e
  refine ⟨hact, by rw [vo, show (M OP j).val = 0 by omega]; simp, by rw [hact, sub_zero, mul_one] at hfa; exact hfa⟩

/-- **The walker's total.** If every script starts with at most `2^25` bytes left, the sigop sum is the sum,
over first rows, of the legacy sigops of their scripts. -/
theorem total (hrem : ∀ r < n, M FS r = 1 → 1 ≤ (M REM r).val ∧ (M REM r).val ≤ 2 ^ 25) (hn : 0 < n) :
    M SUMS (n - 1) = ∑ f ∈ (Finset.range n).filter (fun f => M FS f = 1),
      ((Spec.Block.sigOps (Fields.slice R (M POS f).val (M REM f).val) : ℕ) : F) := by
  rw [sums_eq hsat (n - 1) (by omega), show n - 1 + 1 = n by omega]
  -- from any segment start (or the inactive suffix) to the end
  set g := fun j => M OP j * M SG j
  set h := fun j => ((Spec.Block.sigOps (Fields.slice R (M POS j).val (M REM j).val) : ℕ) : F)
  have claim : ∀ d f, n - f = d → f ≤ n → (M ACT f = 0 ∨ M FS f = 1) →
      ∑ j ∈ Finset.Ico f n, g j = ∑ j ∈ Finset.Ico f n, (if M FS j = 1 then h j else 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro f hd hfn hc
      rcases Nat.eq_or_lt_of_le hfn with rfl | hfn'
      · simp
      rcases hc with h0 | hfs
      · have z := inactive hsat hfn' h0
        rw [Finset.sum_eq_zero (fun j hj => (z j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2).2.1),
          Finset.sum_eq_zero (fun j hj => by rw [if_neg (by rw [(z j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2).2.2]; exact zero_ne_one)])]
      · obtain ⟨-, hfa, hfo⟩ := kinds hsat hfn'
        have ha : M ACT f = 1 := by rw [hfs] at hfa; linear_combination -hfa
        have hop : M OP f = 1 := by rw [hfs] at hfo; linear_combination -hfo
        obtain ⟨hL1, hL⟩ := hrem f hfn' hfs
        set L := (M REM f).val
        obtain ⟨cont', zrl, -, hfl⟩ := seg_rows hsat L f hfn' ha rfl hL1 hL
        have seg := (segment hsat hopc hr8 R hread hR L f hfn' ha rfl hL1 hL).1 .op hop
        rw [Spec.Block.walk_eq_sigOps] at seg
        -- the next row starts a segment or is inactive
        have nxt : M ACT (f + L) = 0 ∨ M FS (f + L) = 1 := by
          have hi : f + L - 1 + 1 < n := by omega
          have c := sat hsat (mem_step (c := .mul (k GC) (kp ZR)) (by simp [stepC])) hi
          simp only [Expr.eval, ev_k hi, ev_kp hi, zrl, mul_one] at c
          rw [show f + L - 1 + 1 = f + L by omega] at c
          have gc := (defs hsat (show f + L < n by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          rw [c] at gc
          rcases bool hsat (c := ACT) (by simp [bools]) (show f + L < n by omega) with a0 | a1
          · exact Or.inl a0
          · rw [a1, one_mul] at gc
            exact Or.inr (by linear_combination gc)
        have ih' := ih (n - (f + L)) (by omega) (f + L) rfl (by omega) nxt
        rw [← Finset.sum_Ico_consecutive _ (show f ≤ f + L by omega) (show f + L ≤ n by omega),
          ← Finset.sum_Ico_consecutive (fun j => if M FS j = 1 then h j else 0) (show f ≤ f + L by omega)
            (show f + L ≤ n by omega), ih']
        congr 1
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, show f + L - f = L by omega, seg]
        rw [Finset.sum_eq_single 0]
        · simp [hfs, h, L]
        · intro j hj hj0
          have hjL := Finset.mem_range.mp hj
          have gcj := cont' j (by omega) hjL
          have := (defs hsat (show f + j < n by omega)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          rw [gcj] at this
          rw [if_neg]
          intro hfs'
          rw [hfs', sub_self, mul_zero] at this; exact one_ne_zero this
        · intro h0; exact absurd (Finset.mem_range.mpr (by omega)) h0
  have hc := claim n 0 (by simp) (by omega) (by
    have c := sat hsat (mem_script (c := .mul first (.mul (k ACT) (om (k FS)))) (by simp [scriptC])) hn
    simp only [Expr.eval, ev_first hn, if_true, one_mul, ev_k hn, om, one, eval_cst, Nat.cast_one] at c
    rcases mul_eq_zero.mp c with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination -h))
  rw [Finset.range_eq_Ico, hc, Finset.sum_filter]

end Segments

end StarkedAir.Block.Walk
