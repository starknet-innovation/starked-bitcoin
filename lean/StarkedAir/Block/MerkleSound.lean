/-
**Merkle tree soundness (M3a.4), row facts.** In a satisfied `block_merkle` trace: `RIX` is the row
index, so node ids `NB + row` are distinct and at least `NB`.
-/
import StarkedAir.Block.Merkle
import StarkedAir.Block.FieldsSound

namespace StarkedAir.Block.Merkle

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
theorem ev_first {r : ℕ} (hr : r < n) : (pre FIRST).eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval, FIRST]

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 :=
  hsat r hr c hc

omit hsat in
theorem mem_levelC {c : Expr} (h : c ∈ levelC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

/-- `RIX` is the row index. -/
theorem rix_eq : ∀ r < n, M RIX r = (r : F) := by
  intro r hr
  induction r with
  | zero =>
    have := sat hsat (mem_levelC (c := .mul (pre FIRST) (k RIX)) (by simp [levelC])) hr
    simpa [Expr.eval, ev_first hr, ev_k hr] using this
  | succ r ih =>
    have := sat hsat (mem_levelC (c := .mul notFirst (.sub (.sub (k RIX) (kp RIX)) one)) (by simp [levelC])) hr
    simp only [Expr.eval, notFirst, om, one, eval_cst, ev_first hr, ev_k hr, ev_kp hr, Nat.cast_one,
      show r + 1 ≠ 0 by omega, if_false, sub_zero, one_mul] at this
    rw [ih (by omega)] at this; push_cast; linear_combination this

end Rows

end StarkedAir.Block.Merkle

namespace StarkedAir.Block.Merkle

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)

/-- Level sizes: `N` leaves, then halving (rounded up). -/
def cntL (N : ℕ) : ℕ → ℕ
  | 0 => N
  | l + 1 => (cntL N l + 1) / 2

/-- The first row of level `l ≥ 1`. -/
def baseL (N : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | l + 2 => baseL N (l + 1) + cntL N (l + 1)

theorem cntL_pos {N : ℕ} (h : 1 ≤ N) : ∀ l, 1 ≤ cntL N l
  | 0 => h
  | l + 1 => by have := cntL_pos h l; simp only [cntL]; omega

theorem cntL_le {N : ℕ} : ∀ l, cntL N (l + 1) ≤ cntL N l
  | l => by simp only [cntL]; omega

theorem cntL_bound {N : ℕ} (h : 1 ≤ N) : ∀ l, cntL N l ≤ max 1 (N - l)
  | 0 => by simp [cntL]
  | l + 1 => by
    have := cntL_bound h l; have := cntL_pos h l
    simp only [cntL]; omega

/-- The SHA message id of tree entry `(l, i)`: the txid message of transaction `i` on level 0, node row
`base l + i` above. -/
def idOf (N l i : ℕ) : ℕ := if l = 0 then 1 + 2 * i else NB + baseL N l + i

section Rows2

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem kbool {c : ℕ} (hc : c ∈ [ACTN, RT, FIRSTL, ODD, L1]) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (c := boolC (k c)) (by
    simp only [constraints, kindC, List.mem_append, List.mem_map]; left; left; left; left; exact ⟨c, hc, rfl⟩) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

omit hsat in
theorem mem_kindC {c : Expr} (h : c ∈ kindC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_flagC {c : Expr} (h : c ∈ flagC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
omit hsat in
theorem mem_childC {c : Expr} (h : c ∈ childC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

/-- The is-zero flags. -/
theorem last_iff {r : ℕ} (hr : r < n) : M LAST r = 1 ↔ M I r - M CNT r + 1 = 0 := by
  have h1 := sat hsat (mem_flagC (c := .mul (k LAST) (.add (.sub (k I) (k CNT)) one)) (by simp [flagC])) hr
  have h2 := sat hsat (mem_flagC (c := .mul (om (k LAST)) (.sub (.mul (.add (.sub (k I) (k CNT)) one) (k LINV)) one))
    (by simp [flagC])) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
  constructor
  · intro h; rw [h, one_mul] at h1; exact h1
  · intro h; rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact h2.symm

theorem c1_iff {r : ℕ} (hr : r < n) : M C1 r = 1 ↔ M CNT r - 1 = 0 := by
  have h1 := sat hsat (mem_flagC (c := .mul (k C1) (.sub (k CNT) one)) (by simp [flagC])) hr
  have h2 := sat hsat (mem_flagC (c := .mul (om (k C1)) (.sub (.mul (.sub (k CNT) one) (k C1INV)) one))
    (by simp [flagC])) hr
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
  constructor
  · intro h; rw [h, one_mul] at h1; exact h1
  · intro h; rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact h2.symm

theorem flag01 {c : ℕ} (hc : c = LAST ∨ c = C1) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  rcases hc with rfl | rfl
  · have h1 := sat hsat (mem_flagC (c := .mul (k LAST) (.add (.sub (k I) (k CNT)) one)) (by simp [flagC])) hr
    have h2 := sat hsat (mem_flagC (c := .mul (om (k LAST)) (.sub (.mul (.add (.sub (k I) (k CNT)) one) (k LINV)) one))
      (by simp [flagC])) hr
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact Or.inr h2.symm
  · have h1 := sat hsat (mem_flagC (c := .mul (k C1) (.sub (k CNT) one)) (by simp [flagC])) hr
    have h2 := sat hsat (mem_flagC (c := .mul (om (k C1)) (.sub (.mul (.sub (k CNT) one) (k C1INV)) one))
      (by simp [flagC])) hr
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one] at h1 h2
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · rw [h, zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at h2; exact Or.inr h2.symm

theorem defn {a : ℕ} {e : Expr} (h : Expr.sub (k a) e ∈ constraints) {r : ℕ} (hr : r < n) :
    M a r = e.eval n preCols pub M r := by
  have := sat hsat h hr
  simp only [Expr.eval, ev_k hr] at this
  exact sub_eq_zero.mp this

theorem rn_eq {r : ℕ} (hr : r < n) : M RN r = M LAST r * M C1 r := by
  rw [defn hsat (e := .mul (k LAST) (k C1)) (mem_flagC (by simp [flagC])) hr]; simp [Expr.eval, ev_k hr]

/-- Kind transitions at row `r + 1`. -/
theorem kind_next {r : ℕ} (hr : r + 1 < n) :
    M ACTN (r + 1) = M ACTN r * (1 - M RN r) ∧ M RT (r + 1) = M ACTN r * M RN r ∧
    (M ACTN (r + 1) = 1 → M FIRSTL (r + 1) = M LAST r) := by
  have c := fun (e : Expr) (h : e ∈ kindC) => sat hsat (mem_kindC h) hr
  have hnf : notFirst.eval n preCols pub M (r + 1) = 1 := by
    simp [notFirst, om, one, Expr.eval, ev_first hr, eval_cst]
  have h1 := c (.mul notFirst (.sub (k ACTN) (.mul (kp ACTN) (om (kp RN))))) (by simp [kindC])
  have h2 := c (.mul notFirst (.sub (k RT) (.mul (kp ACTN) (kp RN)))) (by simp [kindC])
  simp only [Expr.eval, hnf, one_mul, ev_k hr, ev_kp hr, om, one, eval_cst, Nat.cast_one, sub_eq_zero] at h1 h2
  refine ⟨h1, h2, fun ha => ?_⟩
  have h3 := sat hsat (mem_levelC (c := .mul notFirst (.mul (k ACTN) (.sub (k FIRSTL) (kp LAST)))) (by simp [levelC])) hr
  simp only [Expr.eval, hnf, one_mul, ev_k hr, ev_kp hr, ha] at h3
  exact sub_eq_zero.mp h3

theorem nf_eq {r : ℕ} (hr : r < n) : M NF r = M ACTN r * (1 - M FIRSTL r) := by
  rw [defn hsat (e := .mul (k ACTN) (om (k FIRSTL))) (mem_levelC (by simp [levelC])) hr]
  simp [Expr.eval, ev_k hr, om, one, eval_cst]

theorem fs_eq {r : ℕ} (hr : r < n) : M FS r = M ACTN r * M FIRSTL r := by
  rw [defn hsat (e := .mul (k ACTN) (k FIRSTL)) (mem_levelC (by simp [levelC])) hr]
  simp [Expr.eval, ev_k hr]

/-- A node row continuing its level. -/
theorem cont_row {r : ℕ} (hr : r + 1 < n) (ha : M ACTN (r + 1) = 1) (hf : M FIRSTL (r + 1) = 0) :
    M I (r + 1) = M I r + 1 ∧ ∀ c ∈ [CNT, PCNT, BASE, PBASE, L1], M c (r + 1) = M c r := by
  have hnf : M NF (r + 1) = 1 := by rw [nf_eq hsat hr, ha, hf]; ring
  constructor
  · have := sat hsat (mem_levelC (c := .mul (k NF) (.sub (.sub (k I) (kp I)) one)) (by simp [levelC])) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hnf, one_mul, one, eval_cst, Nat.cast_one] at this
    linear_combination this
  · intro c hc
    have := sat hsat (mem_levelC (c := .mul (k NF) (.sub (k c) (kp c)))
      (by simp only [levelC, List.mem_append, List.mem_map]; left; right; exact ⟨c, hc, rfl⟩)) hr
    simp only [Expr.eval, ev_k hr, ev_kp hr, hnf, one_mul] at this
    exact sub_eq_zero.mp this

/-- A node row starting a level (after the first row). -/
theorem start_row {r : ℕ} (hr : r + 1 < n) (ha : M ACTN (r + 1) = 1) (hf : M FIRSTL (r + 1) = 1) :
    M I (r + 1) = 0 ∧ M PCNT (r + 1) = M CNT r ∧ M BASE (r + 1) = ((r + 1 : ℕ) : F) ∧
      M PBASE (r + 1) = M BASE r ∧ M L1 (r + 1) = 0 := by
  have hfs : M FS (r + 1) = 1 := by rw [fs_eq hsat hr, ha, hf]; ring
  have hnf : notFirst.eval n preCols pub M (r + 1) = 1 := by
    simp [notFirst, om, one, Expr.eval, ev_first hr, eval_cst]
  have e := fun (c : Expr) (h : c ∈ levelC) => sat hsat (mem_levelC h) hr
  have h0 := e (.mul (k FIRSTL) (k I)) (by simp [levelC])
  have h1 := e (.mul notFirst (.mul (k FS) (.sub (k PCNT) (kp CNT)))) (by simp [levelC])
  have h2 := e (.mul notFirst (.mul (k FS) (.sub (k BASE) (k RIX)))) (by simp [levelC])
  have h3 := e (.mul notFirst (.mul (k FS) (.sub (k PBASE) (kp BASE)))) (by simp [levelC])
  have h4 := e (.mul notFirst (.mul (k FS) (k L1))) (by simp [levelC])
  simp only [Expr.eval, ev_k hr, ev_kp hr, hnf, hfs, hf, one_mul, sub_eq_zero] at h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2.trans (rix_eq hsat _ hr), h3, h4⟩

/-- Row 0 starts level 1 over the `pub 1` leaves (also when it is the root row). -/
theorem row0 (hn : 0 < n) : M FIRSTL 0 = 1 ∧ M L1 0 = 1 ∧ M BASE 0 = 0 ∧ M PCNT 0 = pub 1 ∧ M I 0 = 0 := by
  have e := fun (c : Expr) (h : c ∈ levelC) => sat hsat (mem_levelC h) hn
  have hf : (pre FIRST).eval n preCols pub M 0 = 1 := by simp [ev_first hn]
  have h1 := e (.mul (pre FIRST) (.sub (k FIRSTL) one)) (by simp [levelC])
  have h2 := e (.mul (pre FIRST) (.sub (k L1) one)) (by simp [levelC])
  have h3 := e (.mul (pre FIRST) (k BASE)) (by simp [levelC])
  have h4 := e (.mul (pre FIRST) (.sub (k PCNT) NTX)) (by simp [levelC])
  simp only [Expr.eval, ev_k hn, hf, one_mul, one, eval_cst, Nat.cast_one, NTX, sub_eq_zero] at h1 h2 h3 h4
  have h0 := e (.mul (k FIRSTL) (k I)) (by simp [levelC])
  simp only [Expr.eval, ev_k hn, h1, one_mul] at h0
  exact ⟨h1, h2, h3, h4, h0⟩

theorem size_eq {r : ℕ} (hr : r < n) (ha : M ACTN r = 1) :
    2 * M CNT r = M PCNT r + M ODD r ∧ M PCNT r ≠ 1 := by
  have h1 := sat hsat (mem_levelC (c := .mul (k ACTN) (.sub (.mul (cst 2) (k CNT)) (.add (k PCNT) (k ODD))))
    (by simp [levelC])) hr
  have h2 := sat hsat (mem_flagC (c := .mul (k ACTN) (.sub (.mul (.sub (k PCNT) one) (k PINV)) one))
    (by simp [flagC])) hr
  simp only [Expr.eval, ev_k hr, ha, one_mul, eval_cst, one, Nat.cast_one, Nat.cast_ofNat, sub_eq_zero] at h1 h2
  refine ⟨h1, fun h => ?_⟩
  rw [h, sub_self, zero_mul] at h2; exact zero_ne_one h2

theorem last_not_node (hn : 0 < n) : M ACTN (n - 1) = 0 := by
  have := sat hsat (mem_kindC (c := .mul (om (pre NOTLAST)) (k ACTN)) (by simp [kindC])) (show n - 1 < n by omega)
  have hnl : (pre NOTLAST).eval n preCols pub M (n - 1) = 0 := by
    simp [pre, Expr.eval, wrap_zero (show n - 1 < n by omega), preCols, PreCol.eval, NOTLAST]; omega
  simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, hnl, sub_zero, one_mul, ev_k (show n - 1 < n by omega)] at this
  exact this

/-- **One level.** A level starting at row `s` over `p` children has `c = (p + 1) / 2` rows: index `j`,
size `c`, the level's constants, `LAST` only on the last; then the next level starts, or (`c = 1`) the
root row follows. -/
theorem level_rows {s p : ℕ} (hs : s < n) (hn : n ≤ 2 ^ 25) (ha : M ACTN s = 1) (hf : M FIRSTL s = 1)
    (hp : M PCNT s = (p : F)) (hp25 : p < 2 ^ 25) :
    2 ≤ p ∧ s + (p + 1) / 2 < n ∧
      (∀ j < (p + 1) / 2, M ACTN (s + j) = 1 ∧ M I (s + j) = (j : F) ∧ M CNT (s + j) = (((p + 1) / 2 : ℕ) : F) ∧
        M PCNT (s + j) = (p : F) ∧ M BASE (s + j) = M BASE s ∧ M PBASE (s + j) = M PBASE s ∧
        M L1 (s + j) = M L1 s ∧ M ODD (s + j) = ((p % 2 : ℕ) : F) ∧
        M LAST (s + j) = (if j + 1 = (p + 1) / 2 then 1 else 0)) ∧
      ((p + 1) / 2 = 1 → M RT (s + 1) = 1) ∧
      ((p + 1) / 2 ≠ 1 → M ACTN (s + (p + 1) / 2) = 1 ∧ M FIRSTL (s + (p + 1) / 2) = 1) := by
  classical
  -- rows continue while no `LAST`
  have walkA : ∀ j, s + j < n → (∀ j' < j, M LAST (s + j') = 0) →
      M ACTN (s + j) = 1 ∧ (0 < j → M FIRSTL (s + j) = 0) ∧ M I (s + j) = (j : F) ∧
      ∀ c ∈ [CNT, PCNT, BASE, PBASE, L1], M c (s + j) = M c s := by
    intro j
    induction j with
    | zero =>
      intro _ _
      have := (row0 hsat (show 0 < n by omega))
      refine ⟨ha, fun h => absurd h (lt_irrefl 0), ?_, fun c _ => rfl⟩
      rcases Nat.eq_zero_or_pos s with e | e
      · subst e; simpa using this.2.2.2.2
      · have := start_row hsat (r := s - 1) (by omega) (by rw [show s - 1 + 1 = s by omega]; exact ha)
          (by rw [show s - 1 + 1 = s by omega]; exact hf)
        rw [show s - 1 + 1 = s by omega] at this; simpa using this.1
    | succ j ih =>
      intro hj hl
      obtain ⟨a, -, i, cs⟩ := ih (by omega) (fun j' h => hl j' (by omega))
      have hr : s + j + 1 < n := by omega
      obtain ⟨k1, -, k3⟩ := kind_next hsat hr
      have hrn : M RN (s + j) = 0 := by rw [rn_eq hsat (by omega), hl j (by omega), zero_mul]
      have a1 : M ACTN (s + j + 1) = 1 := by rw [k1, a, hrn]; ring
      have f1 : M FIRSTL (s + j + 1) = 0 := by rw [k3 a1, hl j (by omega)]
      obtain ⟨i1, c1⟩ := cont_row hsat hr a1 f1
      rw [show s + (j + 1) = s + j + 1 by ring]
      exact ⟨a1, fun _ => f1, by rw [i1, i]; push_cast; ring, fun c hc => (c1 c hc).trans (cs c hc)⟩
  -- some row of the level is `LAST`
  have ex : ∃ j, s + j < n ∧ M LAST (s + j) = 1 := by
    by_contra hne
    push Not at hne
    have hz : ∀ j, s + j < n → M LAST (s + j) = 0 := fun j hj =>
      ((flag01 hsat (c := LAST) (Or.inl rfl) hj).resolve_right (hne j hj))
    have := (walkA (n - 1 - s) (by omega) (fun j' h => hz j' (by omega))).1
    rw [show s + (n - 1 - s) = n - 1 by omega, last_not_node hsat (by omega)] at this
    exact zero_ne_one this
  have hspec := Nat.find_spec ex
  have hmin0 : ∀ {j}, j < Nat.find ex → ¬ (s + j < n ∧ M LAST (s + j) = 1) := fun h => Nat.find_min ex h
  generalize Nat.find ex = jl at hspec hmin0
  obtain ⟨hjn, hlast⟩ := hspec
  have hmin : ∀ j < jl, M LAST (s + j) = 0 := fun j h =>
    (flag01 hsat (c := LAST) (Or.inl rfl) (by omega)).resolve_right (fun h1 => hmin0 h ⟨by omega, h1⟩)
  obtain ⟨ajl, -, ijl, cjl⟩ := walkA jl hjn hmin
  -- the level's size
  have hcnt : M CNT (s + jl) = ((jl + 1 : ℕ) : F) := by
    have := (last_iff hsat hjn).mp hlast
    rw [ijl] at this; push_cast; linear_combination -this
  obtain ⟨hsz, hp1⟩ := size_eq hsat hjn ajl
  rw [hcnt, cjl PCNT (by simp), hp] at hsz
  rw [cjl PCNT (by simp), hp] at hp1
  have hodd := kbool hsat (c := ODD) (by simp) hjn
  have hn25 : jl < 2 ^ 25 := by omega
  have hnat : 2 * (jl + 1) = p + (M ODD (s + jl)).val ∧ (M ODD (s + jl)).val ≤ 1 := by
    have hov : (M ODD (s + jl)).val ≤ 1 := by rcases hodd with h | h <;> simp [h, ZMod.val_one]
    refine ⟨natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) ?_, hov⟩
    push_cast at hsz ⊢; rw [ZMod.natCast_zmod_val]; exact hsz
  have hc : jl + 1 = (p + 1) / 2 := by omega
  have hp2 : 2 ≤ p := by
    by_contra h
    have : p = 1 := by omega
    exact hp1 (by rw [this]; simp)
  have hoddv : M ODD (s + jl) = ((p % 2 : ℕ) : F) := by
    rw [← ZMod.natCast_zmod_val (M ODD (s + jl))]; congr 1; omega
  -- the next row
  have hlt : s + jl + 1 < n := by
    by_contra h
    have : s + jl = n - 1 := by omega
    rw [this, last_not_node hsat (by omega)] at ajl; exact zero_ne_one ajl
  obtain ⟨k1, k2, k3⟩ := kind_next hsat hlt
  have hc1 : M C1 (s + jl) = (if jl = 0 then 1 else 0) := by
    rcases flag01 hsat (c := C1) (Or.inr rfl) hjn with h | h
    · rw [h]; split_ifs with h0
      · exfalso; have := (c1_iff hsat hjn).mp; rw [hcnt, h0] at this
        rcases (flag01 hsat (c := C1) (Or.inr rfl) hjn) with g | g
        · have := (c1_iff hsat hjn).mpr (by rw [hcnt, h0]; simp); rw [h] at this; exact zero_ne_one this
        · rw [h] at g; exact zero_ne_one g
      · rfl
    · rw [h]; split_ifs with h0
      · rfl
      · have := (c1_iff hsat hjn).mp h; rw [hcnt] at this
        have e : ((jl : ℕ) : F) = ((0 : ℕ) : F) := by push_cast at this ⊢; linear_combination this
        exact absurd (natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e) h0
  have hrn : M RN (s + jl) = (if jl = 0 then 1 else 0) := by rw [rn_eq hsat hjn, hlast, hc1, one_mul]
  refine ⟨hp2, by omega, fun j hj => ?_, fun h1 => ?_, fun h1 => ?_⟩
  · have hjj : j ≤ jl := by omega
    obtain ⟨aj, -, ij, cj⟩ := walkA j (by omega) (fun j' h => hmin j' (by omega))
    refine ⟨aj, ij, ?_, (cj PCNT (by simp)).trans hp, cj BASE (by simp), cj PBASE (by simp), cj L1 (by simp), ?_, ?_⟩
    · rw [cj CNT (by simp), ← cjl CNT (by simp), hcnt, hc]
    · rcases Nat.lt_or_ge j jl with h | h
      · -- `ODD` is determined by the level's sizes, which are constant
        have e1 := (size_eq hsat (by omega) aj).1
        have e2 := (size_eq hsat hjn ajl).1
        rw [cj CNT (by simp), cj PCNT (by simp)] at e1
        rw [cjl CNT (by simp), cjl PCNT (by simp)] at e2
        rw [← hoddv]; linear_combination e2 - e1
      · rw [show j = jl by omega]; exact hoddv
    · split_ifs with h
      · rw [show j = jl by omega]; exact hlast
      · exact hmin j (by omega)
  · have hj0 : jl = 0 := by omega
    rw [hj0] at hrn k2 ajl
    simp only [Nat.add_zero, if_true] at hrn k2 ajl
    rw [k2, ajl, hrn, one_mul]
  · have hj0 : jl ≠ 0 := by omega
    rw [if_neg hj0] at hrn
    have a1 : M ACTN (s + jl + 1) = 1 := by rw [k1, ajl, hrn]; ring
    rw [show s + (p + 1) / 2 = s + jl + 1 by omega]
    exact ⟨a1, (k3 a1).trans hlast⟩

omit hsat in
theorem baseL_succ {N : ℕ} {l : ℕ} (hl : 1 ≤ l) : baseL N (l + 1) = baseL N l + cntL N l := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
  rfl

/-- **The tree's rows.** With `N ≥ 1` leaves (public input 1): level `l ≥ 1` (over `cnt (l − 1) ≥ 2`
children) occupies rows `base l + j`, `j < cnt l`, with the expected columns; after the top level
(`cnt l = 1`) comes the root row; with one leaf, row 0 is the root row. -/
theorem tree_rows (hn0 : 0 < n) (hn : n ≤ 2 ^ 25) {N : ℕ} (hN : pub 1 = (N : F)) (hN1 : 1 ≤ N) (hN25 : N < 2 ^ 25) :
    (∀ l, 1 ≤ l → 2 ≤ cntL N (l - 1) →
      baseL N l + cntL N l < n ∧
      ∀ j < cntL N l, M ACTN (baseL N l + j) = 1 ∧ M I (baseL N l + j) = (j : F) ∧
        M PCNT (baseL N l + j) = (cntL N (l - 1) : F) ∧ M L1 (baseL N l + j) = (if l = 1 then 1 else 0) ∧
        (l ≠ 1 → M PBASE (baseL N l + j) = (baseL N (l - 1) : F)) ∧
        M ODD (baseL N l + j) = ((cntL N (l - 1) % 2 : ℕ) : F) ∧
        M LAST (baseL N l + j) = (if j + 1 = cntL N l then 1 else 0) ∧
        (cntL N l = 1 → M RT (baseL N l + 1) = 1)) ∧
    (N = 1 → M RT 0 = 1) := by
  have r0 := row0 hsat hn0
  have hfirst : ∀ c ∈ kindC, c.eval n preCols pub M 0 = 0 := fun c h => sat hsat (mem_kindC h) hn0
  have c1 := hfirst (.mul (pre FIRST) (.sub (.add (k ACTN) (k RT)) one)) (by simp [kindC])
  have c2 := hfirst (.mul (pre FIRST) (.mul (k RT) (.sub NTX one))) (by simp [kindC])
  simp only [Expr.eval, ev_first hn0, if_true, one_mul, ev_k hn0, one, eval_cst, Nat.cast_one, NTX, hN] at c1 c2
  -- the start of each level
  have start : ∀ l, 1 ≤ l → 2 ≤ cntL N (l - 1) →
      baseL N l < n ∧ M ACTN (baseL N l) = 1 ∧ M FIRSTL (baseL N l) = 1 ∧
      M PCNT (baseL N l) = (cntL N (l - 1) : F) ∧ M L1 (baseL N l) = (if l = 1 then 1 else 0) ∧
      M BASE (baseL N l) = (baseL N l : F) ∧ (l ≠ 1 → M PBASE (baseL N l) = (baseL N (l - 1) : F)) := by
    intro l hl
    induction l with
    | zero => omega
    | succ l ih =>
      intro h2
      rcases Nat.eq_zero_or_pos l with e | e
      · subst e
        simp only [baseL, cntL, Nat.zero_add, Nat.sub_self, if_true] at h2 ⊢
        have ha : M ACTN 0 = 1 := by
          rcases kbool hsat (c := RT) (by simp) hn0 with t | t
          · rw [t, add_zero, sub_eq_zero] at c1; exact c1
          · rw [t, one_mul, sub_eq_zero] at c2
            have := natCast_inj_of_lt (a := N) (b := 1) (Fields.lt_P (by omega)) (Fields.lt_P (by norm_num))
              (by simpa using c2)
            omega
        exact ⟨hn0, ha, r0.1, by rw [r0.2.2.2.1, hN], r0.2.1, by rw [r0.2.2.1]; simp, fun h => absurd rfl h⟩
      · -- level `l + 1 ≥ 2` starts after level `l`
        have hcl : 2 ≤ cntL N l := by simpa using h2
        have hcl1 : 2 ≤ cntL N (l - 1) := by
          have := cntL_le (N := N) (l - 1); rw [show l - 1 + 1 = l by omega] at this; omega
        obtain ⟨sl, al, fl, pl, ll, bl, -⟩ := ih (by omega) hcl1
        have hp25 : cntL N (l - 1) < 2 ^ 25 := by
          have := cntL_bound hN1 (l - 1); omega
        obtain ⟨-, hlt, rows, -, nxt⟩ := level_rows hsat sl hn al fl pl hp25
        have hc : (cntL N (l - 1) + 1) / 2 = cntL N l := by
          rw [show cntL N l = cntL N (l - 1 + 1) by rw [show l - 1 + 1 = l by omega]]; rfl
        rw [hc] at hlt rows nxt
        obtain ⟨a1, f1⟩ := nxt (by omega)
        have hb : baseL N (l + 1) = baseL N l + cntL N l := baseL_succ (by omega)
        rw [hb]
        have hr : baseL N l + cntL N l - 1 + 1 < n := by omega
        have e1 : baseL N l + cntL N l - 1 + 1 = baseL N l + cntL N l := by omega
        have a1' : M ACTN (baseL N l + cntL N l - 1 + 1) = 1 := by rw [e1]; exact a1
        have f1' : M FIRSTL (baseL N l + cntL N l - 1 + 1) = 1 := by rw [e1]; exact f1
        obtain ⟨-, p1, b1, pb1, l1⟩ := start_row hsat hr a1' f1'
        rw [show baseL N l + cntL N l - 1 + 1 = baseL N l + cntL N l by omega] at p1 b1 pb1 l1
        obtain ⟨-, -, cn, -, bs, -, -, -, -⟩ := rows (cntL N l - 1) (by omega)
        rw [show baseL N l + (cntL N l - 1) = baseL N l + cntL N l - 1 by omega] at cn bs
        refine ⟨hlt, a1, f1, by rw [p1, cn]; simp, by rw [l1]; simp; omega, by rw [b1]; try push_cast,
          fun _ => by rw [pb1, bs, bl]; simp⟩
  refine ⟨fun l hl h2 => ?_, fun h1 => ?_⟩
  · obtain ⟨sl, al, fl, pl, ll, bl, pbl⟩ := start l hl h2
    have hp25 : cntL N (l - 1) < 2 ^ 25 := by have := cntL_bound hN1 (l - 1); omega
    obtain ⟨-, hlt, rows, rt, -⟩ := level_rows hsat sl hn al fl pl hp25
    have hc : (cntL N (l - 1) + 1) / 2 = cntL N l := by
      rw [show cntL N l = cntL N (l - 1 + 1) by rw [show l - 1 + 1 = l by omega]]; rfl
    rw [hc] at hlt rows rt
    refine ⟨hlt, fun j hj => ?_⟩
    obtain ⟨a, i, -, pc, -, pb, l1, od, la⟩ := rows j hj
    exact ⟨a, i, pc, l1.trans ll, fun h => pb.trans (pbl h), od, la, rt⟩
  · subst h1
    rcases kbool hsat (c := RT) (by simp) hn0 with t | t
    · exfalso
      rw [t, add_zero, sub_eq_zero] at c1
      obtain ⟨-, hp1⟩ := size_eq hsat hn0 c1
      exact hp1 (by rw [r0.2.2.2.1, hN]; simp)
    · exact t

/-- **The root row** reads tree entry `(H, 0)`, the top of the tree (`cnt H = 1`). -/
theorem root_row (hn0 : 0 < n) (hn : n ≤ 2 ^ 25) {N : ℕ} (hN : pub 1 = (N : F)) (hN1 : 1 ≤ N) (hN25 : N < 2 ^ 25)
    {H : ℕ} (hH : cntL N H = 1) (hHl : ∀ l < H, 2 ≤ cntL N l) :
    ∃ r < n, M RT r = 1 ∧ M RIDC r = (idOf N H 0 : F) := by
  have tr := tree_rows hsat hn0 hn hN hN1 hN25
  rcases Nat.eq_zero_or_pos H with h0 | hpos
  · subst h0
    have h1 : N = 1 := by simpa [cntL] using hH
    have hrt := tr.2 h1
    refine ⟨0, hn0, hrt, ?_⟩
    have := sat hsat (mem_childC (c := .mul (pre FIRST) (.mul (k RT) (.sub (k RIDC) one))) (by simp [childC])) hn0
    simp only [Expr.eval, ev_first hn0, if_true, one_mul, ev_k hn0, hrt, one, eval_cst, Nat.cast_one,
      sub_eq_zero] at this
    rw [this, idOf, if_pos rfl]; simp
  · obtain ⟨hlt, rows⟩ := tr.1 H hpos (hHl (H - 1) (by omega))
    obtain ⟨-, -, -, -, -, -, -, rt⟩ := rows 0 (by omega)
    have hrt := rt hH
    have hr : baseL N H + 1 < n := by rw [hH] at hlt; exact hlt
    refine ⟨baseL N H + 1, hr, hrt, ?_⟩
    have := sat hsat (mem_childC (c := .mul notFirst (.mul (k RT) (.sub (.add (k RIDC) one) (.add (cst NB) (k RIX)))))
      (by simp [childC])) hr
    simp only [Expr.eval, notFirst, om, one, eval_cst, Nat.cast_one, ev_first hr, show baseL N H + 1 ≠ 0 by omega,
      if_false, sub_zero, one_mul, ev_k hr, hrt, rix_eq hsat _ hr, sub_eq_zero] at this
    rw [idOf, if_neg (by omega)]
    push_cast at this ⊢; linear_combination this

/-- **A node row's children** in terms of tree entries: `left = (l − 1, 2i)`, `right = (l − 1, 2i + 1)`, or the
left again when `2i + 1` is the previous level's size (`dup`). -/
theorem kids {N l i r c : ℕ} (hr : r < n) (hl : 1 ≤ l) (hc : c = cntL N (l - 1)) (hi : i < (c + 1) / 2)
    (hL1 : M L1 r = (if l = 1 then 1 else 0)) (hpb : l ≠ 1 → M PBASE r = (baseL N (l - 1) : F))
    (hI : M I r = (i : F)) (hodd : M ODD r = ((c % 2 : ℕ) : F))
    (hlast : M LAST r = (if i + 1 = (c + 1) / 2 then 1 else 0)) :
    M DUP r = (if 2 * i + 1 = c then 1 else 0) ∧ M LEFT r = (idOf N (l - 1) (2 * i) : F) ∧
      M RIGHT r = (idOf N (l - 1) (min (2 * i + 1) (c - 1)) : F) := by
  have hdup : M DUP r = (if 2 * i + 1 = c then 1 else 0) := by
    rw [defn hsat (e := .mul (k ODD) (k LAST)) (mem_childC (by simp [childC])) hr]
    simp only [Expr.eval, ev_k hr, hodd, hlast]
    by_cases h : 2 * i + 1 = c
    · rw [if_pos (by omega), if_pos h, show c % 2 = 1 by omega]; simp
    · rw [if_neg h]
      by_cases h2 : i + 1 = (c + 1) / 2
      · rw [if_pos h2, show c % 2 = 0 by omega]; simp
      · rw [if_neg h2]; simp
  have hleft : M LEFT r = (idOf N (l - 1) (2 * i) : F) := by
    rw [defn hsat (e := .add (.mul (k L1) (.add (.mul (cst 4) (k I)) one))
      (.mul (om (k L1)) (.add (.add (cst NB) (k PBASE)) (.mul (cst 2) (k I))))) (mem_childC (by simp [childC])) hr]
    rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | h2
    · simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, hL1, hI, idOf]; simp; push_cast; ring
    · have hne : l ≠ 1 := by omega
      simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, hL1, hI, idOf, hpb hne, if_neg hne,
        if_neg (show ¬ (l - 1 = 0) by omega)]
      push_cast; ring
  refine ⟨hdup, hleft, ?_⟩
  rw [defn hsat (e := .add (k LEFT) (.mul (om (k DUP)) (.add (k L1) one))) (mem_childC (by simp [childC])) hr]
  rcases (show l = 1 ∨ 2 ≤ l by omega) with rfl | h2
  · simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, hleft, hdup, hL1, idOf]
    by_cases h : 2 * i + 1 = c
    · rw [if_pos h, show min (2 * i + 1) (c - 1) = 2 * i by omega]; simp
    · rw [if_neg h, show min (2 * i + 1) (c - 1) = 2 * i + 1 by omega]; simp; push_cast; ring
  · have hne : l ≠ 1 := by omega
    simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, hleft, hdup, hL1, idOf, if_neg hne,
      if_neg (show ¬ (l - 1 = 0) by omega)]
    by_cases h : 2 * i + 1 = c
    · rw [if_pos h, show min (2 * i + 1) (c - 1) = 2 * i by omega]; simp
    · rw [if_neg h, show min (2 * i + 1) (c - 1) = 2 * i + 1 by omega]; simp; push_cast; ring

end Rows2

end StarkedAir.Block.Merkle
