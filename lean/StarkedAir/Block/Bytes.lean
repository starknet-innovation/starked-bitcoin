/-
**Block bytes (M3a.1 `BLK-BYTES`).** The raw block as one byte per row: `(pos, byte)` with the
byte range-checked by its bits. The public input `LEN` (`pub 0`) is the block length: an `ACTIVE`
flag is `1` exactly on rows `r < LEN`. Each active row yields the lookup tuple
`byte(pos, byte)` with a free multiplicity, so other components read block bytes by position.

`bytes_rows`: in a satisfied trace with fewer than `P` rows, `pos = r`, every byte is below 256,
and `ACTIVE r = 1 ↔ r < LEN`. `yield_sound`: a row yielding with nonzero multiplicity yields
`(r, raw[r])` with `r < LEN`.
-/
import StarkedAir.Lookup
import StarkedAir.Gadgets.Sha256Sound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC bitsOf eval_col eval_cst bit eq_bit eval_bitsOf wrap_back)

def REL_BYTE : ℕ := 3

def POS : ℕ := 0
def BYTE : ℕ := 1
/-- Bits of the byte: columns `2 … 9`. -/
def BIT0 : ℕ := 2
def ACTIVE : ℕ := 10
def MULT : ℕ := 11

/-- Preprocessed columns: `isFirst`, `notLast`. -/
def preCols : List PreCol := [.isFirst, .notLast]

def LEN : Expr := .pub 0
def notFirst : Expr := .sub (cst 1) (pre 0)
def isLast : Expr := .sub (cst 1) (pre 1)

def constraints : List Expr :=
  [ .mul (pre 0) (col POS),
    .mul notFirst (.sub (.sub (col POS) (col POS (-1))) (cst 1)),
    .sub (col BYTE) (bitsOf BIT0 8),
    boolC (col ACTIVE),
    .mul (pre 0) (.sub (cst 1) (col ACTIVE)),
    .mul notFirst (.mul (col ACTIVE) (.sub (cst 1) (col ACTIVE (-1)))),
    .mul notFirst (.mul (.sub (col ACTIVE (-1)) (col ACTIVE)) (.sub (col POS) LEN)),
    .mul isLast (.mul (col ACTIVE) (.sub (.add (col POS) (cst 1)) LEN)) ] ++
  (List.range 8).map (fun i => boolC (col (BIT0 + i)))

def bytes : Comp where
  air := { name := "block_bytes", nMain := 12, pre := preCols, constraints := constraints }
  lookups := [⟨REL_BYTE, .mul (col ACTIVE) (col MULT), [col POS, col BYTE]⟩]

/-- The block's bytes, read from the trace. -/
def raw (main : ℕ → ℕ → F) (len : ℕ) : List ℕ := (List.range len).map fun r => (main BYTE r).val

section Rows

variable {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub main r = 0)
include hsat

theorem sat_at {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub main r = 0 :=
  hsat r hr c hc

theorem first_eval {r : ℕ} (hr : r < n) : (pre 0).eval n preCols pub main r = if r = 0 then 1 else 0 := by
  simp [pre, Expr.eval, preCols, PreCol.eval, wrap_zero hr]

theorem last_eval {r : ℕ} (hr : r < n) : (pre 1).eval n preCols pub main r = if r + 1 < n then 1 else 0 := by
  simp [pre, Expr.eval, preCols, PreCol.eval, wrap_zero hr]

theorem pos_eq : ∀ r < n, main POS r = r := by
  intro r
  induction r with
  | zero =>
    intro h0
    have := sat_at hsat (c := .mul (pre 0) (col POS)) (by simp [constraints]) h0
    simpa [Expr.eval, first_eval hsat h0, eval_col, wrap_zero h0] using this
  | succ r ih =>
    intro hr
    have := sat_at hsat (c := .mul notFirst (.sub (.sub (col POS) (col POS (-1))) (cst 1))) (by simp [constraints]) hr
    simp only [notFirst, Expr.eval, first_eval hsat hr, eval_col, eval_cst, wrap_zero hr,
      show wrap n (r + 1) (-1) = r from by
        rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl] at this
    rw [ih (by omega)] at this
    simp at this
    push_cast
    linear_combination this

theorem byte_lt {r : ℕ} (hr : r < n) : (main BYTE r).val < 256 := by
  have hb : ∀ j < 8, (main (BIT0 + j) r).val ≤ 1 := fun j hj => val_le_one_of_bool (by
    have := sat_at hsat (c := boolC (col (BIT0 + j))) (List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)) hr
    simpa [boolC, Expr.eval, eval_col, eval_cst, wrap_zero hr] using this)
  have e := sat_at hsat (c := .sub (col BYTE) (bitsOf BIT0 8)) (by simp [constraints]) hr
  simp only [Expr.eval, eval_col, wrap_zero hr, eval_bitsOf hr hb, sub_eq_zero] at e
  rw [e, ZMod.val_natCast]
  exact lt_of_le_of_lt (Nat.mod_le _ _) (ofBits_lt _ 8)

theorem active_bool {r : ℕ} (hr : r < n) : main ACTIVE r = 0 ∨ main ACTIVE r = 1 := by
  have := sat_at hsat (c := boolC (col ACTIVE)) (by simp [constraints]) hr
  simp [boolC, Expr.eval, eval_col, eval_cst, wrap_zero hr, sub_eq_zero] at this
  exact this

/-- Active rows are a prefix. -/
theorem active_prev {r : ℕ} (hr : r + 1 < n) (h : main ACTIVE (r + 1) = 1) : main ACTIVE r = 1 := by
  have := sat_at hsat (c := .mul notFirst (.mul (col ACTIVE) (.sub (cst 1) (col ACTIVE (-1))))) (by simp [constraints]) hr
  simp only [notFirst, Expr.eval, first_eval hsat hr, eval_col, eval_cst, wrap_zero hr, h,
    show wrap n (r + 1) (-1) = r from by
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl] at this
  simp at this
  linear_combination -this

theorem active_prefix {r : ℕ} (hr : r < n) (h : main ACTIVE r = 1) : ∀ s ≤ r, main ACTIVE s = 1 := by
  intro s hs
  induction r, hs using Nat.le_induction with
  | base => exact h
  | succ r hsr ih => exact ih (by omega) (active_prev hsat hr h)

theorem wrap_prev {r : ℕ} (hr : r + 1 < n) : wrap n (r + 1) (-1) = r := by
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl

/-- **The rows.** `pos = r`, bytes are below 256, and row `r` is active iff `r < LEN`. -/
theorem bytes_rows (hP : n < P) (hn : 0 < n) :
    (∀ r < n, main POS r = r ∧ (main BYTE r).val < 256) ∧ (pub 0).val ≤ n ∧
    ∀ r < n, (main ACTIVE r = 1 ↔ r < (pub 0).val) := by
  refine ⟨fun r hr => ⟨pos_eq hsat r hr, byte_lt hsat hr⟩, ?_⟩
  have a0 : main ACTIVE 0 = 1 := by
    have := sat_at hsat (c := .mul (pre 0) (.sub (cst 1) (col ACTIVE))) (by simp [constraints]) hn
    simp [Expr.eval, first_eval hsat hn, eval_col, eval_cst, wrap_zero hn, sub_eq_zero] at this
    exact this.symm
  have castv : ∀ d : ℕ, d ≤ n → pub 0 = (d : F) → (pub 0).val = d := fun d hd e => by
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  by_cases hz : ∃ r, r < n ∧ main ACTIVE r = 0
  · classical
    let d := Nat.find hz
    have hd : d < n ∧ main ACTIVE d = 0 := Nat.find_spec hz
    have hmin : ∀ r < d, main ACTIVE r = 1 := fun r hr => by
      have := Nat.find_min hz hr
      rcases active_bool hsat (show r < n by omega) with h | h
      · exact absurd ⟨by omega, h⟩ this
      · exact h
    have hd1 : 1 ≤ d := by
      by_contra h0
      have : d = 0 := by omega
      rw [this] at hd; rw [hd.2] at a0; exact zero_ne_one a0
    obtain ⟨e, he⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have hlen : (pub 0).val = d := by
      have := sat_at hsat (c := .mul notFirst (.mul (.sub (col ACTIVE (-1)) (col ACTIVE)) (.sub (col POS) LEN)))
        (by simp [constraints]) hd.1
      rw [he] at this hd
      simp only [notFirst, LEN, Expr.eval, first_eval hsat hd.1, eval_col, eval_cst, wrap_zero hd.1,
        wrap_prev hsat hd.1, hd.2, hmin e (by omega), pos_eq hsat _ hd.1] at this
      simp at this
      rw [he]; exact castv _ (by omega) (by rw [sub_eq_zero] at this; push_cast; exact this.symm)
    refine ⟨by omega, fun r hr => ⟨fun h => ?_, fun h => hmin r (by omega)⟩⟩
    by_contra hge
    have := active_prefix hsat hr h d (by omega)
    rw [hd.2] at this; exact zero_ne_one this
  · push Not at hz
    have hall : ∀ r < n, main ACTIVE r = 1 := fun r hr =>
      (active_bool hsat hr).resolve_left (hz r hr)
    have hlen : (pub 0).val = n := by
      have hl : n - 1 < n := by omega
      have := sat_at hsat (c := .mul isLast (.mul (col ACTIVE) (.sub (.add (col POS) (cst 1)) LEN)))
        (by simp [constraints]) hl
      simp only [isLast, LEN, Expr.eval, last_eval hsat hl, eval_col, eval_cst, wrap_zero hl, hall _ hl,
        pos_eq hsat _ hl, show ¬ (n - 1 + 1 < n) by omega, if_false] at this
      simp at this
      refine castv _ le_rfl ?_
      rw [sub_eq_zero] at this
      rw [← this]
      have e : ((n - 1 : ℕ) : F) + 1 = ((n - 1 + 1 : ℕ) : F) := by push_cast; ring
      rw [e, Nat.sub_add_cancel hn]
    exact ⟨by omega, fun r hr => ⟨fun _ => by omega, fun _ => hall r hr⟩⟩

end Rows

/-! ### Reading bytes through the lookup -/

/-- A yielding row (nonzero multiplicity) yields `(r, byte r)` with `r < LEN`. -/
theorem yield_sound {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
    (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub main r = 0) (hP : n < P) {r : ℕ} (hr : r < n)
    (hm : (Expr.mul (col ACTIVE) (col MULT)).eval n preCols pub main r ≠ 0) :
    r < (pub 0).val ∧ ([col POS, col BYTE].map (Expr.eval n preCols pub main r)) = [(r : F), main BYTE r] := by
  obtain ⟨hrows, -, hact⟩ := bytes_rows hsat hP (by omega)
  simp only [Expr.eval, eval_col, wrap_zero hr] at hm
  have ha : main ACTIVE r = 1 := (active_bool hsat hr).resolve_left (fun h => hm (by rw [h, zero_mul]))
  refine ⟨(hact r hr).mp ha, ?_⟩
  simp [eval_col, wrap_zero hr, (hrows r hr).1]

/-- **Reading the block.** In a system whose component 0 is `bytes` and whose other components
read bytes (relation `REL_BYTE`) with multiplicity `−1` or `0`, every read with multiplicity `−1`
of `(p, b)` reads a real byte: `p = r < LEN` and `b` is the block's byte `r`. -/
theorem read_byte {sys : System} {inst : ℕ → Inst} {pub : ℕ → F}
    (hb : BalancedExt sys inst pub []) (h0 : sys.comp 0 = bytes)
    (hsat0 : bytes.air.Satisfied (inst 0).logSize pub (inst 0).main) (hP : 2 ^ (inst 0).logSize < P)
    (huse : ∀ s ∈ sites sys inst, s.1 ≠ 0 → siteRel sys s = REL_BYTE →
      siteMult sys inst pub s = -1 ∨ siteMult sys inst pub s = 0)
    (hcount : ((sites sys inst).filter fun s => s.1 ≠ 0 ∧ siteRel sys s = REL_BYTE).length < P)
    {s0 : Site} (hs0 : s0 ∈ sites sys inst) (h0ne : s0.1 ≠ 0) (hrel : siteRel sys s0 = REL_BYTE)
    (hm : siteMult sys inst pub s0 = -1) {p b : F} (hv : siteVals sys inst pub s0 = [p, b]) :
    ∃ r, r < (pub 0).val ∧ p = (r : F) ∧ b = (inst 0).main BYTE r := by
  classical
  obtain ⟨s, hs, hnu, hsm, hsr, hsv⟩ := used_in_table_ext hb
    (use := fun i k => i ≠ 0 ∧ ((sys.comp i).lookups.getD k ⟨0, .const 0, []⟩).rel = REL_BYTE)
    (fun s hs hu => huse s hs hu.1 hu.2) (by simp) (by simpa [siteRel, siteLookup] using hcount)
    (Or.inl ⟨s0, hs0, ⟨h0ne, hrel⟩, hm, hrel, hv⟩)
  have hi : s.1 = 0 := by
    by_contra hne; exact hnu ⟨hne, hsr⟩
  obtain ⟨i, r, k⟩ := s
  simp only at hi; subst hi
  have hmem : r < 2 ^ (inst 0).logSize ∧ k < bytes.lookups.length := by
    have := (List.mem_flatMap.mp hs); simp [sites, h0] at hs; omega
  have hk : k = 0 := by simp [bytes] at hmem; omega
  subst hk
  have hsat' : ∀ r < 2 ^ (inst 0).logSize, ∀ c ∈ constraints, c.eval (2 ^ (inst 0).logSize) preCols pub (inst 0).main r = 0 :=
    hsat0
  have hm' : (Expr.mul (col ACTIVE) (col MULT)).eval (2 ^ (inst 0).logSize) preCols pub (inst 0).main r ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, h0, bytes] using hsm
  obtain ⟨hlt, hvals⟩ := yield_sound hsat' hP hmem.1 hm'
  have : siteVals sys inst pub (0, r, 0) = [(r : F), (inst 0).main BYTE r] := by
    simpa [siteVals, siteEval, siteLookup, h0, bytes] using hvals
  rw [this] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨r, hlt, hsv.1.symm, hsv.2.symm⟩

end StarkedAir.Block
