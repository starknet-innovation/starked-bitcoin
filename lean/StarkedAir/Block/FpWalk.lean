/-
**Segment fingerprints (M3b, D-040).** A coin's amount and script, `serTxOut`, is a contiguous byte
segment: an output's serialization in the raw block, and the same bytes in the undo record that spends
it. The coin tuple carries their length and a fingerprint `H = Σₖ bₖ γ^(len−1−k)` (Horner, over QM31,
with public `γ`), so the multiset argument forces an undo record's bytes to equal the spent output's
(with high probability over `γ`).

One row per segment byte:
- columns: stream `STR` (0 raw, 1 undo), segment id `SID`, position `POS`, byte `B`, flags `FST`/`LST`,
  remaining count `REM`, length `LEN`, and `H`;
- the first row takes the descriptor `(STR, SID, POS, LEN)` (`seg` use);
- each following row continues the previous one;
- the last row (`REM = 1`) yields `(STR, SID, LEN, H)` (`fp`).

**`seg_sound`**: a last row's `H` is the Horner fingerprint of the bytes of the rows back to its first
row, with consecutive positions, and the length is the row count.
-/
import StarkedAir.Block.ExtSum
import StarkedAir.Block.Undo

namespace StarkedAir.Block.FpWalk

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub emb_zero emb_one emb_add emb_mul emb_sub)
open StarkedAir.Block.Fields (degE)
open StarkedAir.Block.ExtSum (QE)
open StarkedAir.Block.ExtSum.QE

def REL_SEG : ℕ := 21
def REL_FP : ℕ := 22

def ON : ℕ := 0
def STR : ℕ := 1
def SID : ℕ := 2
def POS : ℕ := 3
def B : ℕ := 4
def FST : ℕ := 5
def LST : ℕ := 6
def REM : ℕ := 7
def LINV : ℕ := 8
def LEN : ℕ := 9
def H : ℕ := 10
def N_MAIN : ℕ := 14

/-- `γ` (four public inputs). -/
def PUB_G : ℕ := 41

def preCols : List PreCol := [.isFirst, .notLast]
def k (c : ℕ) : Expr := col c
def kp (c : ℕ) : Expr := col c (-1)
def kn (c : ℕ) : Expr := col c 1
def one : Expr := cst 1
def om (e : Expr) : Expr := .sub one e
def first : Expr := pre 0
def isLast : Expr := om (pre 1)
/-- A continuing row: on, not a segment's first. -/
def cont : Expr := .mul (k ON) (om (k FST))
/-- An on row that is not a segment's last (`LST` implies `ON`). -/
def nl : Expr := .sub (k ON) (k LST)

def hornerQE : QE := ((colQ H (-1)).mul (pubQ PUB_G)).add (base (k B))

def constraints : List Expr :=
  [ON, STR, FST, LST].map (fun c => boolC (k c)) ++
  [ .mul (k FST) (om (k ON)), .mul (k LST) (om (k ON)),
    .mul first (cont),
    .mul cont (om (kp ON)), .mul cont (kp LST),
    .mul cont (.sub (k STR) (kp STR)), .mul cont (.sub (k SID) (kp SID)),
    .mul cont (.sub (.sub (k POS) (kp POS)) one), .mul cont (.add (.sub (k REM) (kp REM)) one),
    .mul cont (.sub (k LEN) (kp LEN)),
    .mul (k FST) (.sub (k LEN) (k REM)),
    .mul (k LST) (.sub (k REM) one), .mul nl (.sub (.mul (.sub (k REM) one) (k LINV)) one),
    .mul isLast nl, .mul nl (om (kn ON)), .mul nl (kn FST) ] ++
  ((colQ H).sub (base (k B))).coords.map (fun e => .mul (k FST) e) ++
  ((colQ H).sub hornerQE).coords.map (fun e => .mul cont e)

def lookups : List Lookup :=
  [ ⟨REL_BYTE, .neg (.mul (k ON) (om (k STR))), [k POS, k B]⟩,
    ⟨Undo.REL_UBYTE, .neg (.mul (k ON) (k STR)), [k POS, k B]⟩,
    ⟨REL_SEG, .neg (k FST), [k STR, k SID, k POS, k REM]⟩,
    ⟨REL_FP, k LST, [k STR, k SID, k LEN, col H, col (H + 1), col (H + 2), col (H + 3)]⟩ ]

def fpwalk : Comp where
  air := { name := "block_fpwalk", nMain := N_MAIN, pre := preCols, constraints := constraints }
  lookups := lookups

#guard constraints.all (fun c => degE c ≤ 3)
#guard lookups.all (fun l => degE l.mult ≤ 2 && l.vals.all (fun v => degE v ≤ 1))

/-- The Horner fingerprint of a byte list. -/
noncomputable def horner (γ : QM) (l : List QM) : QM := l.foldl (fun h b => h * γ + b) 0

theorem horner_concat (γ : QM) (l : List QM) (b : QM) : horner γ (l ++ [b]) = horner γ l * γ + b := by
  simp [horner, List.foldl_append]

/-! ### Soundness -/

section Sound

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

theorem sat {c : Expr} (hc : c ∈ constraints) {r : ℕ} (hr : r < n) : c.eval n preCols pub M r = 0 := hsat r hr c hc

theorem bool {c : ℕ} (hc : c ∈ [ON, STR, FST, LST]) {r : ℕ} (hr : r < n) : M c r = 0 ∨ M c r = 1 := by
  have := sat hsat (c := boolC (k c)) (by simp only [constraints, List.mem_append, List.mem_map]; left; left; left; exact ⟨c, hc, rfl⟩) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

omit hsat in
theorem mem_main {c : Expr} (h : c ∈ [ .mul (k FST) (om (k ON)), .mul (k LST) (om (k ON)),
    .mul first (cont),
    .mul cont (om (kp ON)), .mul cont (kp LST),
    .mul cont (.sub (k STR) (kp STR)), .mul cont (.sub (k SID) (kp SID)),
    .mul cont (.sub (.sub (k POS) (kp POS)) one), .mul cont (.add (.sub (k REM) (kp REM)) one),
    .mul cont (.sub (k LEN) (kp LEN)),
    .mul (k FST) (.sub (k LEN) (k REM)),
    .mul (k LST) (.sub (k REM) one), .mul nl (.sub (.mul (.sub (k REM) one) (k LINV)) one),
    .mul isLast nl, .mul nl (om (kn ON)), .mul nl (kn FST) ]) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; left; left; right; exact h

/-- Row `r`'s fingerprint register in QM31. -/
noncomputable def hQ (M : ℕ → ℕ → F) (r : ℕ) : QM := toQ ⟨M H r, M (H + 1) r, M (H + 2) r, M (H + 3) r⟩
noncomputable def gQ (pub : ℕ → F) : QM := toQ ⟨pub PUB_G, pub (PUB_G + 1), pub (PUB_G + 2), pub (PUB_G + 3)⟩

theorem fst_on {r : ℕ} (hr : r < n) (h : M FST r = 1) : M ON r = 1 := by
  have := sat hsat (mem_main (c := .mul (k FST) (om (k ON))) (by simp)) hr
  simp only [Expr.eval, om, one, ev_k hr, h, eval_cst, Nat.cast_one, one_mul] at this
  exact (sub_eq_zero.mp this).symm

theorem lst_on {r : ℕ} (hr : r < n) (h : M LST r = 1) : M ON r = 1 := by
  have := sat hsat (mem_main (c := .mul (k LST) (om (k ON))) (by simp)) hr
  simp only [Expr.eval, om, one, ev_k hr, h, eval_cst, Nat.cast_one, one_mul] at this
  exact (sub_eq_zero.mp this).symm

/-- A first row's register is its byte. -/
theorem h_first {r : ℕ} (hr : r < n) (hf : M FST r = 1) : hQ M r = emb (M B r) := by
  have hc : ∀ e ∈ ((colQ H).sub (base (k B))).coords, Expr.eval n preCols pub M r e = 0 := by
    intro e he
    have := sat hsat (c := .mul (k FST) e) (by
      simp only [constraints, List.mem_append, List.mem_map]; left; right; exact ⟨e, he, rfl⟩) hr
    simpa [Expr.eval, ev_k hr, hf] using this
  have := toQ_zero_of hc
  rw [ev_sub, toQ_sub, toQ_ev_base] at this
  have hcol : toQ ((colQ H).ev n preCols pub M r) = hQ M r := by simp [hQ, ev, colQ, eval_col, wrap_zero hr]
  rw [hcol, ev_k hr] at this
  exact sub_eq_zero.mp this

/-- A continuing row's register extends the previous row's. -/
theorem h_cont {r : ℕ} (hr : r + 1 < n) (hc : M ON (r + 1) = 1) (hf : M FST (r + 1) = 0) :
    hQ M (r + 1) = hQ M r * gQ pub + emb (M B (r + 1)) := by
  have hce : cont.eval n preCols pub M (r + 1) = 1 := by simp [cont, Expr.eval, om, one, ev_k hr, hc, hf, eval_cst]
  have hz : ∀ e ∈ ((colQ H).sub hornerQE).coords, Expr.eval n preCols pub M (r + 1) e = 0 := by
    intro e he
    have := sat hsat (c := .mul cont e) (by
      simp only [constraints, List.mem_append, List.mem_map]; right; exact ⟨e, he, rfl⟩) hr
    simpa [Expr.eval, hce] using this
  have := toQ_zero_of hz
  rw [ev_sub, toQ_sub, hornerQE, ev_add, toQ_add, ev_mul, toQ_mul, toQ_ev_base] at this
  have h1 : toQ ((colQ H).ev n preCols pub M (r + 1)) = hQ M (r + 1) := by
    simp [hQ, ev, colQ, eval_col, wrap_zero hr]
  have h2 : toQ ((colQ H (-1)).ev n preCols pub M (r + 1)) = hQ M r := by
    have hw : wrap n (r + 1) (-1) = r := by
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl
    simp [hQ, ev, colQ, eval_col, hw]
  have h3 : toQ ((pubQ PUB_G).ev n preCols pub M (r + 1)) = gQ pub := by simp [gQ, ev, pubQ, Expr.eval]
  rw [h1, h2, h3, ev_k hr] at this
  exact sub_eq_zero.mp this

/-- **A segment, back from any on row.** -/
theorem seg_back : ∀ e < n, M ON e = 1 → ∃ s ≤ e, M FST s = 1 ∧
    (∀ r, s ≤ r → r ≤ e → M ON r = 1 ∧ M STR r = M STR e ∧ M SID r = M SID e ∧ M LEN r = M LEN e ∧
      M POS r = M POS s + ((r - s : ℕ) : F) ∧ (s < r → M FST r = 0 ∧ M LST (r - 1) = 0)) ∧
    M REM e = M REM s - ((e - s : ℕ) : F) ∧
    hQ M e = horner (gQ pub) ((List.range (e - s + 1)).map fun j => emb (M B (s + j))) := by
  intro e
  induction e with
  | zero =>
    intro hn hon
    have hf : M FST 0 = 1 := by
      have := sat hsat (mem_main (c := .mul first cont) (by simp)) hn
      rw [Expr.eval, ev_first hn, if_pos rfl, one_mul] at this
      simp only [cont, om, one, Expr.eval, ev_k hn, hon, eval_cst, Nat.cast_one, one_mul] at this
      exact (sub_eq_zero.mp this).symm
    refine ⟨0, le_rfl, hf, fun r h1 h2 => ?_, by simp, ?_⟩
    · obtain rfl : r = 0 := by omega
      simp [hon]
    · rw [h_first hsat hn hf]; simp [horner]
  | succ e ih =>
    intro hn hon
    rcases bool hsat (c := FST) (by simp) hn with f0 | f1
    · -- a continuing row
      have hce : cont.eval n preCols pub M (e + 1) = 1 := by simp [cont, Expr.eval, om, one, ev_k hn, hon, f0, eval_cst]
      have c := fun (x : Expr) (hx : Expr.mul cont x ∈ [ .mul (k FST) (om (k ON)), .mul (k LST) (om (k ON)),
          .mul first (cont), .mul cont (om (kp ON)), .mul cont (kp LST),
          .mul cont (.sub (k STR) (kp STR)), .mul cont (.sub (k SID) (kp SID)),
          .mul cont (.sub (.sub (k POS) (kp POS)) one), .mul cont (.add (.sub (k REM) (kp REM)) one),
          .mul cont (.sub (k LEN) (kp LEN)), .mul (k FST) (.sub (k LEN) (k REM)),
          .mul (k LST) (.sub (k REM) one), .mul nl (.sub (.mul (.sub (k REM) one) (k LINV)) one),
          .mul isLast nl, .mul nl (om (kn ON)), .mul nl (kn FST) ]) => by
        have := sat hsat (mem_main hx) hn
        simp only [Expr.eval, hce, one_mul] at this
        exact this
      have c1 := c (om (kp ON)) (by simp)
      have c2 := c (kp LST) (by simp)
      have c3 := c (.sub (k STR) (kp STR)) (by simp)
      have c4 := c (.sub (k SID) (kp SID)) (by simp)
      have c5 := c (.sub (.sub (k POS) (kp POS)) one) (by simp)
      have c6 := c (.add (.sub (k REM) (kp REM)) one) (by simp)
      have c7 := c (.sub (k LEN) (kp LEN)) (by simp)
      simp only [Expr.eval, om, one, eval_cst, Nat.cast_one, ev_k hn, ev_kp hn, sub_eq_zero] at c1 c2 c3 c4 c5 c6 c7
      obtain ⟨s, hse, hfs, hrow, hrem, hh⟩ := ih (by omega) c1.symm
      refine ⟨s, by omega, hfs, fun r h1 h2 => ?_, ?_, ?_⟩
      · rcases Nat.lt_or_ge r (e + 1) with hlt | hge
        · obtain ⟨o, st, si, le, po, nf⟩ := hrow r h1 (by omega)
          exact ⟨o, by rw [st, c3], by rw [si, c4], by rw [le, c7], po, nf⟩
        · obtain rfl : r = e + 1 := by omega
          have hpe := (hrow e hse le_rfl).2.2.2.2.1
          refine ⟨hon, rfl, rfl, rfl, ?_, fun _ => ⟨f0, by simpa using c2⟩⟩
          rw [show e + 1 - s = (e - s) + 1 by omega]; push_cast
          linear_combination c5 + hpe
      · rw [show e + 1 - s = (e - s) + 1 by omega]; push_cast; linear_combination c6 + hrem
      · rw [h_cont hsat hn hon f0, hh, show e + 1 - s + 1 = (e - s + 1) + 1 by omega, List.range_succ (n := e - s + 1),
          List.map_append, List.map_cons, List.map_nil, horner_concat, show s + (e - s + 1) = e + 1 by omega]
    · -- a first row
      refine ⟨e + 1, le_rfl, f1, fun r h1 h2 => ?_, by simp, ?_⟩
      · obtain rfl : r = e + 1 := by omega
        simp [hon]
      · rw [h_first hsat hn f1]; simp [horner]

/-- **Segment soundness.** A last row's fingerprint is the Horner fingerprint of the segment's bytes, at
consecutive positions from its first row, whose `REM` is the length. -/
theorem seg_sound {e : ℕ} (he : e < n) (hl : M LST e = 1) : ∃ s ≤ e, M FST s = 1 ∧
    (∀ r, s ≤ r → r ≤ e → M ON r = 1 ∧ M STR r = M STR e ∧ M SID r = M SID e ∧ M LEN r = M LEN e ∧
      M POS r = M POS s + ((r - s : ℕ) : F)) ∧
    M REM s = ((e - s + 1 : ℕ) : F) ∧ M LEN e = ((e - s + 1 : ℕ) : F) ∧
    hQ M e = horner (gQ pub) ((List.range (e - s + 1)).map fun j => emb (M B (s + j))) := by
  obtain ⟨s, hse, hfs, hrow, hrem, hh⟩ := seg_back hsat e he (lst_on hsat he hl)
  have hr1 : M REM e = 1 := by
    have := sat hsat (mem_main (c := .mul (k LST) (.sub (k REM) one)) (by simp)) he
    simp only [Expr.eval, ev_k he, hl, one_mul, one, eval_cst, Nat.cast_one] at this
    exact sub_eq_zero.mp this
  have hrs : M REM s = ((e - s + 1 : ℕ) : F) := by push_cast; linear_combination hr1 - hrem
  have hlen : M LEN e = ((e - s + 1 : ℕ) : F) := by
    have := sat hsat (mem_main (c := .mul (k FST) (.sub (k LEN) (k REM))) (by simp)) (show s < n by omega)
    simp only [Expr.eval, ev_k (show s < n by omega), hfs, one_mul] at this
    rw [← (hrow s le_rfl hse).2.2.2.1, sub_eq_zero.mp this, hrs]
  exact ⟨s, hse, hfs, fun r h1 h2 => by
    obtain ⟨o, st, si, le, po, -⟩ := hrow r h1 h2; exact ⟨o, st, si, le, po⟩, hrs, hlen, hh⟩

end Sound

end StarkedAir.Block.FpWalk
