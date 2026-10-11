/-
**Undo records (M3b, D-038/D-040).** The undo stream is `0x01`, then per input after the coinbase a record:
a 4-byte code (`2·height + coinbase`), the creating transaction's index in its block (3 bytes), the
`serTxOut` length `TL` (2 bytes), then the spent output's `serTxOut` (amount and script). The index and
the length are claims like the code, so the block commitment (the stream's Blake2s) fixes them before
the epoch challenge, and with them the records' boundaries (D-041). One row per record:
- record `J` starts at `S`, with `S = 1` at row 0 (after the version byte, read as `(0, 1)`) and the next
  record starting at `S + 9 + TL`, `TL` the record's length bytes;
- the last record ends at the undo length (`pub 8`); with no records, the length is 1;
- the code bytes `S … S + 3`, the index bytes `S + 4 … S + 6`, the length bytes `S + 7`, `S + 8` and
  the amount bytes `S + 9 … S + 16` are read from the undo table;
- the `serTxOut` part is the fingerprint segment `(1, J, S + 9, TL)` (`block_fpwalk`);
- each row yields `urec(J, code lo, code hi, amount lo, amount hi, index)`: the amount as 24 low bits
  (bytes 0–2) and the next 32 (bytes 3–6), as the fields split an output's value.

The coin tuple fixes the bytes behind the fingerprint, so this component parses no CompactSize: an undo
record whose `serTxOut` part matches a created output is that output's serialization.

**`rows_sound`**: on rows are a prefix `[0, e)`, `J` is the row index, `S_0 = 1`,
`S_{j+1} = S_j + 9 + TL_j`, and `S + 9 + TL` at the last on row is the undo length (or `e = 0` and the
length is 1).
-/
import StarkedAir.Block.FpWalk

namespace StarkedAir.Block.URec

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)
open StarkedAir.Block.Fields (degE)

def REL_UREC : ℕ := 23

def ON : ℕ := 0
def J : ℕ := 1
def S : ℕ := 2
def TL : ℕ := 3
/-- Code bytes `C 0 … C 3`, amount bytes `V 0 … V 7`, index bytes `X 0 … X 2`, length bytes `T 0`, `T 1`. -/
def C (i : ℕ) : ℕ := 4 + i
def V (i : ℕ) : ℕ := 8 + i
def X (i : ℕ) : ℕ := 16 + i
def T (i : ℕ) : ℕ := 19 + i
/-- The record header: code, index and length. -/
def HDR : ℕ := 9
def N_MAIN : ℕ := 21
/-- Header and amount byte `c` (`c < 17`, at `S + c`): its column and its lookup. -/
def ucol (c : ℕ) : ℕ := if c < 4 then C c else if c < 7 then X (c - 4) else if c < 9 then T (c - 7) else V (c - 9)
def uidx (c : ℕ) : ℕ :=
  if c < 4 then 1 + c else if c < 7 then 13 + (c - 4) else if c < 9 then 16 + (c - 7) else 5 + (c - 9)

def preCols : List PreCol := [.isFirst, .notLast]
def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := pre 0
def notFirst : Expr := om first
def notLast : Expr := pre 1
def isLast : Expr := om notLast
/-- The record's end. -/
def endE : Expr := .add (.add (k S) (cst HDR)) (k TL)
/-- The last on row: on, and the next row off. -/
def lastOn : Expr := .mul notLast (.sub (k ON) (kn ON))

def constraints : List Expr :=
  [ boolC (k ON),
    .mul notFirst (.mul (k ON) (om (kp ON))),
    .mul isLast (k ON),
    .mul first (k J), .mul notFirst (.mul (k ON) (.sub (.sub (k J) (kp J)) one)),
    .mul first (.sub (k S) one),
    .mul notFirst (.mul (k ON) (.sub (k S) (.add (.add (kp S) (cst HDR)) (kp TL)))),
    .mul lastOn (.sub endE (.pub Undo.PUB_LEN)),
    .mul first (.mul (om (k ON)) (.sub (.pub Undo.PUB_LEN) one)),
    .mul (k ON) (.sub (k TL) (.add (k (T 0)) (.mul (cst 256) (k (T 1))))) ]

def limb (a b : ℕ) : Expr := .add (k a) (.mul (cst 256) (k b))

def lookups : List Lookup :=
  [ ⟨Undo.REL_UBYTE, .neg first, [cst 0, cst 1]⟩ ] ++
  (List.range 4).map (fun i => ⟨Undo.REL_UBYTE, .neg (k ON), [.add (k S) (cst i), k (C i)]⟩) ++
  (List.range 8).map (fun i => ⟨Undo.REL_UBYTE, .neg (k ON), [.add (k S) (cst (HDR + i)), k (V i)]⟩) ++
  (List.range 3).map (fun i => ⟨Undo.REL_UBYTE, .neg (k ON), [.add (k S) (cst (4 + i)), k (X i)]⟩) ++
  (List.range 2).map (fun i => ⟨Undo.REL_UBYTE, .neg (k ON), [.add (k S) (cst (7 + i)), k (T i)]⟩) ++
  [ ⟨FpWalk.REL_SEG, k ON, [cst 1, k J, .add (k S) (cst HDR), k TL]⟩,
    ⟨REL_UREC, k ON, [k J, limb (C 0) (C 1), limb (C 2) (C 3),
      .add (.add (k (V 0)) (.mul (cst 256) (k (V 1)))) (.mul (cst 65536) (k (V 2))),
      .add (.add (.add (k (V 3)) (.mul (cst 256) (k (V 4)))) (.mul (cst 65536) (k (V 5)))) (.mul (cst 16777216) (k (V 6))),
      .add (.add (k (X 0)) (.mul (cst 256) (k (X 1)))) (.mul (cst 65536) (k (X 2)))]⟩ ]

def urec : Comp where
  air := { name := "block_urec", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

/-! ### Soundness (rows) -/

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

theorem on_bool {r : ℕ} (hr : r < n) : M ON r = 0 ∨ M ON r = 1 := by
  have := sat hsat (c := boolC (k ON)) (by simp [constraints]) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-- **On rows are a prefix** `[0, e)` with `e < n`. -/
theorem on_prefix (hn : 0 < n) : ∃ e, e < n ∧ ∀ r < n, (M ON r = 1 ↔ r < e) := by
  have hl : M ON (n - 1) = 0 := by
    have := sat hsat (c := .mul isLast (k ON)) (by simp [constraints]) (show n - 1 < n by omega)
    simp only [isLast, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_notLast (show n - 1 < n by omega),
      show ¬ (n - 1 + 1 < n) by omega, if_false, sub_zero, one_mul, ev_k (show n - 1 < n by omega)] at this
    exact this
  have hstep : ∀ r, r + 1 < n → M ON (r + 1) = 1 → M ON r = 1 := by
    intro r hr h1
    have := sat hsat (c := .mul notFirst (.mul (k ON) (om (kp ON)))) (by simp [constraints]) hr
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr, show r + 1 ≠ 0 by omega, if_false,
      sub_zero, one_mul, ev_k hr, ev_kp hr, h1] at this
    exact (sub_eq_zero.mp this).symm
  have ex : ∃ r, r < n ∧ M ON r = 0 := ⟨n - 1, by omega, hl⟩
  obtain ⟨heN, he0⟩ := Nat.find_spec ex
  have hmin : ∀ r < Nat.find ex, ¬ (r < n ∧ M ON r = 0) := fun r h => Nat.find_min ex h
  generalize Nat.find ex = e at heN he0 hmin
  refine ⟨e, heN, fun r hr => ⟨fun h1 => ?_, fun hlt => ?_⟩⟩
  · by_contra hc
    push Not at hc
    have : ∀ d, r - d < n → M ON (r - d) = 1 := by
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

/-- **The records tile the stream.** -/
theorem rows_sound (hn : 0 < n) : ∃ e, e < n ∧ (∀ r < n, (M ON r = 1 ↔ r < e)) ∧
    (∀ r < e, M J r = (r : F)) ∧ M S 0 = 1 ∧
    (∀ r, r + 1 < e → M S (r + 1) = M S r + 9 + M TL r) ∧
    (e = 0 → pub Undo.PUB_LEN = 1) ∧ (0 < e → M S (e - 1) + 9 + M TL (e - 1) = pub Undo.PUB_LEN) := by
  obtain ⟨e, hen, hon⟩ := on_prefix hsat hn
  have onv : ∀ r < n, M ON r = if r < e then 1 else 0 := by
    intro r hr; split_ifs with h
    · exact (hon r hr).mpr h
    · rcases on_bool hsat hr with g | g
      · exact g
      · exact absurd ((hon r hr).mp g) h
  refine ⟨e, hen, hon, fun r hr => ?_, ?_, fun r hr => ?_, fun he => ?_, fun he => ?_⟩
  · induction r with
    | zero =>
      have := sat hsat (c := .mul first (k J)) (by simp [constraints]) hn
      simpa [Expr.eval, ev_first hn, ev_k hn] using this
    | succ r ih =>
      have hr1 : r + 1 < n := by omega
      have := sat hsat (c := .mul notFirst (.mul (k ON) (.sub (.sub (k J) (kp J)) one))) (by simp [constraints]) hr1
      simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr1, show r + 1 ≠ 0 by omega, if_false,
        sub_zero, one_mul, ev_k hr1, ev_kp hr1, onv (r + 1) hr1, if_pos hr] at this
      rw [ih (by omega)] at this; push_cast; linear_combination this
  · have := sat hsat (c := .mul first (.sub (k S) one)) (by simp [constraints]) hn
    simp only [Expr.eval, ev_first hn, ev_k hn, one, eval_cst, Nat.cast_one, if_true, one_mul] at this
    exact sub_eq_zero.mp this
  · have hr1 : r + 1 < n := by omega
    have := sat hsat (c := .mul notFirst (.mul (k ON) (.sub (k S) (.add (.add (kp S) (cst HDR)) (kp TL)))))
      (by simp [constraints]) hr1
    simp only [notFirst, om, one, Expr.eval, eval_cst, Nat.cast_one, ev_first hr1, show r + 1 ≠ 0 by omega, if_false,
      sub_zero, one_mul, ev_k hr1, ev_kp hr1, onv (r + 1) hr1, if_pos hr, HDR] at this
    push_cast at this; linear_combination this
  · subst he
    have := sat hsat (c := .mul first (.mul (om (k ON)) (.sub (.pub Undo.PUB_LEN) one))) (by simp [constraints]) hn
    simp only [Expr.eval, ev_first hn, om, one, eval_cst, Nat.cast_one, ev_k hn, onv 0 hn,
      show ¬ (0 < 0) by omega, if_false, sub_zero, if_true, one_mul] at this
    exact sub_eq_zero.mp this
  · have hr : e - 1 < n := by omega
    have := sat hsat (c := .mul lastOn (.sub endE (.pub Undo.PUB_LEN))) (by simp [constraints]) hr
    simp only [lastOn, endE, Expr.eval, ev_notLast hr, show e - 1 + 1 < n by omega, if_true, one_mul, ev_k hr,
      ev_kn (show e - 1 + 1 < n by omega), onv (e - 1) hr, onv (e - 1 + 1) (by omega), if_pos (show e - 1 < e by omega),
      show ¬ (e - 1 + 1 < e) by omega, if_false, sub_zero, eval_cst, HDR] at this
    push_cast at this; linear_combination this

/-- **A record's length is its length bytes.** -/
theorem tl_bytes {r : ℕ} (hr : r < n) (hon : M ON r = 1) : M TL r = M (T 0) r + 256 * M (T 1) r := by
  have := sat hsat (c := .mul (k ON) (.sub (k TL) (.add (k (T 0)) (.mul (cst 256) (k (T 1)))))) (by simp [constraints]) hr
  simp only [Expr.eval, ev_k hr, eval_cst, hon, one_mul] at this
  push_cast at this; linear_combination this

end Rows

end StarkedAir.Block.URec
