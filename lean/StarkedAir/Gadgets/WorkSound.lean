/-
Soundness of the chainwork constraints (header chain v5, `Work.lean`).

For every header `j` of a satisfying trace (`workAt main j` = the chainwork in rows 248..249):
- `work_q`: the header's `q` digits encode `blockProof (nBitsOf header)` (Core `GetBlockProof`);
- `work_step`: `workAt j = (j = 0 ? pubWork pub 88 : workAt (j − 1)) + blockProof (nBitsOf header_j)`,
  given canonical (16-bit) input-work public limbs;
- `work_out`: the last header's `workAt` is public inputs 98..107.
-/
import StarkedAir.Gadgets.MtpSound

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-! ## Column arithmetic (pure) -/

/-- Carry into column `k`. -/
def cin (c : ℕ → ℕ) (k : ℕ) : ℕ := if k = 0 then 0 else c (k - 1)

theorem carry_inv (a d c : ℕ → ℕ) (B : ℕ) : ∀ n, (∀ k < n, a k + cin c k = d k + B * c k) →
    ∑ k ∈ Finset.range n, a k * B ^ k = ∑ k ∈ Finset.range n, d k * B ^ k + B ^ n * cin c n := by
  intro n
  induction n with
  | zero => intro _; simp [cin]
  | succ n ih =>
    intro h
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih (fun k hk => h k (by omega))]
    have e := h n (by omega)
    have hc : cin c (n + 1) = c n := by simp [cin]
    rw [hc]
    set D := ∑ k ∈ Finset.range n, d k * B ^ k
    calc D + B ^ n * cin c n + a n * B ^ n = D + B ^ n * (a n + cin c n) := by ring
      _ = D + B ^ n * (d n + B * c n) := by rw [e]
      _ = D + d n * B ^ n + B ^ (n + 1) * c n := by ring

/-- Column-wise addition with carries: if column `k < K` reads `a k + c (k−1) = d k + B · c k`
and nothing carries out of the last column, the weighted sums agree. -/
theorem carry_chain (a d c : ℕ → ℕ) (B K : ℕ) (h : ∀ k < K, a k + cin c k = d k + B * c k)
    (hlast : cin c K = 0) :
    ∑ k ∈ Finset.range K, a k * B ^ k = ∑ k ∈ Finset.range K, d k * B ^ k := by
  rw [carry_inv a d c B K h, hlast]; simp

/-- A digit string shifted by `s` places: `Σ_k [s ≤ k < s + n] f (k − s) B^k = B^s Σ_{i<n} f i B^i`. -/
theorem shift_sum (f : ℕ → ℕ) (B s n K : ℕ) (h : s + n ≤ K) :
    ∑ k ∈ Finset.range K, (if s ≤ k ∧ k - s < n then f (k - s) else 0) * B ^ k =
      B ^ s * ∑ i ∈ Finset.range n, f i * B ^ i := by
  rw [← Finset.sum_range_add_sum_Ico _ (show s ≤ K by omega)]
  rw [Finset.sum_eq_zero (fun k hk => by simp at hk; simp [show ¬ (s ≤ k) by omega])]
  rw [zero_add, Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
  rw [← Finset.sum_range_add_sum_Ico _ (show n ≤ K - s by omega)]
  rw [Finset.sum_eq_zero (s := Finset.Ico n (K - s)) (fun i hi => by simp at hi; simp [show ¬ (i < n) by omega])]
  rw [add_zero]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp at hi
  simp [show s + i - s = i by omega, hi, pow_add]; ring

/-- The schoolbook product: `Σ_k Σ_i [i ≤ k < i + n] x i y (k − i) B^k = (Σ x_i B^i)(Σ y_j B^j)`. -/
theorem cauchy (x y : ℕ → ℕ) (B m n K : ℕ) (h : m + n ≤ K + 1) (hn : 0 < n) :
    ∑ k ∈ Finset.range K, (∑ i ∈ Finset.range m, if i ≤ k ∧ k - i < n then x i * y (k - i) else 0) * B ^ k =
      (∑ i ∈ Finset.range m, x i * B ^ i) * ∑ j ∈ Finset.range n, y j * B ^ j := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  simp at hi
  have := shift_sum y B i n K (by omega)
  rw [show (∑ k ∈ Finset.range K, (if i ≤ k ∧ k - i < n then x i * y (k - i) else 0) * B ^ k) =
      x i * ∑ k ∈ Finset.range K, (if i ≤ k ∧ k - i < n then y (k - i) else 0) * B ^ k by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun k _ => ?_); split <;> ring]
  rw [this, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun _ _ => by ring)


/-! ## Digits held in the work rows -/

/-- Field `i` of a slot layout for header `j` (rows shifted by `sh`; −256 = previous header). -/
def fieldVal (main : ℕ → ℕ → F) (j : ℕ) (L : List (ℕ × ℕ)) (w per : ℕ) (sh : ℤ) (i : ℕ) : ℕ :=
  match L[i / per]? with
  | some (row, X) => (word main X ((((256 * j + 248 : ℕ) : ℤ) + workOff row sh).toNat)).toNat /
      2 ^ (w * (i % per)) % 2 ^ w
  | none => 0

theorem fieldVal_lt (main : ℕ → ℕ → F) (j : ℕ) (L : List (ℕ × ℕ)) (w per : ℕ) (sh : ℤ) (i : ℕ) :
    fieldVal main j L w per sh i < 2 ^ w := by
  unfold fieldVal
  split
  · exact Nat.mod_lt _ (by positivity)
  · positivity

/-- All slots read bit-column words at rows inside the trace. -/
def SlotsOk (logSize j : ℕ) (L : List (ℕ × ℕ)) (sh : ℤ) : Prop :=
  ∀ p ∈ L, p.2 + 32 ≤ 96 ∧ 0 ≤ ((256 * j + 248 : ℕ) : ℤ) + workOff p.1 sh ∧
    ((256 * j + 248 : ℕ) : ℤ) + workOff p.1 sh < 2 ^ logSize

theorem ev_sumE {n' : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ} (k : ℕ) (f : ℕ → Expr) :
    (sumE k f).eval n' pc pub main r = ∑ i ∈ Finset.range k, (f i).eval n' pc pub main r := by
  unfold sumE
  rw [eval_foldl_list _ f, eval_cst, Nat.cast_zero, zero_add, list_range_sum]

/-! ## Named digit strings -/

def qd (main : ℕ → ℕ → F) (j i : ℕ) : ℕ := fieldVal main j qSlots 8 4 0 i
def rd (main : ℕ → ℕ → F) (j i : ℕ) : ℕ := fieldVal main j rSlots 8 4 0 i
def rhod (main : ℕ → ℕ → F) (j i : ℕ) : ℕ := fieldVal main j rhoSlots 8 4 0 i
def sigd (main : ℕ → ℕ → F) (j i : ℕ) : ℕ := fieldVal main j sigSlots 8 4 0 i
def wd (main : ℕ → ℕ → F) (j : ℕ) (sh : ℤ) (i : ℕ) : ℕ := fieldVal main j wSlots 8 4 sh i
/-- Carries, zero past the last column that has one. -/
def pcc (main : ℕ → ℕ → F) (j k : ℕ) : ℕ := if k < 17 then fieldVal main j pcSlots 10 3 0 k else 0
def mcc (main : ℕ → ℕ → F) (j k : ℕ) : ℕ := if k < 41 then fieldVal main j mcSlots 2 16 0 k else 0
def ecc (main : ℕ → ℕ → F) (j k : ℕ) : ℕ := if k < 28 then fieldVal main j [(253, A)] 1 32 0 k else 0
def wcc (main : ℕ → ℕ → F) (j k : ℕ) : ℕ := if k < 9 then fieldVal main j [(253, E)] 1 32 0 k else 0
/-- Mantissa bytes of an nBits word. -/
def md (y : Word) (i : ℕ) : ℕ :=
  if i = 0 then y.toNat / 2 ^ 24 % 256 else if i = 1 then y.toNat / 2 ^ 16 % 256 else
    if i = 2 then y.toNat / 2 ^ 8 % 128 else 0
/-- Exponent one-hot bit `s` at the PoW row. -/
def ohv (main : ℕ → ℕ → F) (j s : ℕ) : ℕ := (bit main (A + s) (256 * j + 216)).toNat

/-- 16-bit limbs of `q` and of the chainwork (header `j`). -/
def ql (main : ℕ → ℕ → F) (j l : ℕ) : ℕ := qd main j (2 * l) + 256 * qd main j (2 * l + 1)
def wl (main : ℕ → ℕ → F) (j l : ℕ) : ℕ := wd main j 0 (2 * l) + 256 * wd main j 0 (2 * l + 1)

/-- The work `q`, chainwork `W`, and public chainwork values as numbers. -/
def workQ (main : ℕ → ℕ → F) (j : ℕ) : ℕ := ∑ i ∈ Finset.range 16, qd main j i * 256 ^ i
def workAt (main : ℕ → ℕ → F) (j : ℕ) : ℕ := ∑ i ∈ Finset.range 20, wd main j 0 i * 256 ^ i
def pubWork (pub : ℕ → F) (b : ℕ) : ℕ := ∑ l ∈ Finset.range 10, (pub (b + l)).val * 65536 ^ l

/-- Pairs of bytes as 16-bit limbs. -/
theorem limbs_bytes (x : ℕ → ℕ) : ∀ n, ∑ l ∈ Finset.range n, (x (2 * l) + 256 * x (2 * l + 1)) * 65536 ^ l =
    ∑ i ∈ Finset.range (2 * n), x i * 256 ^ i := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, show (65536 : ℕ) = 256 ^ 2 by norm_num, ← pow_mul, show 2 * n + 1 = 2 * n + 1 from rfl]
    ring

/-- Digits beyond `n` are zero, so the sum stops at `n`. -/
theorem sum_stop (f : ℕ → ℕ) (B n K : ℕ) (hnK : n ≤ K) (hz : ∀ i, n ≤ i → f i = 0) :
    ∑ i ∈ Finset.range K, f i * B ^ i = ∑ i ∈ Finset.range n, f i * B ^ i := by
  rw [← Finset.sum_range_add_sum_Ico _ hnK, Finset.sum_eq_zero (s := Finset.Ico n K)
    (fun i hi => by simp at hi; simp [hz i hi.1]), add_zero]

theorem fieldVal_none (main : ℕ → ℕ → F) (j : ℕ) (L : List (ℕ × ℕ)) (w per : ℕ) (sh : ℤ) (i : ℕ)
    (h : L.length ≤ i / per) : fieldVal main j L w per sh i = 0 := by
  unfold fieldVal; rw [List.getElem?_eq_none h]

section Work

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
  {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ logSize)
include hsat hj

theorem ev_field {L : List (ℕ × ℕ)} {w per : ℕ} {sh : ℤ} (hL : SlotsOk logSize j L sh)
    (hw : w * per ≤ 32) (hper : 0 < per) (i : ℕ) :
    (fieldOf L w per sh i).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      ((fieldVal main j L w per sh i : ℕ) : F) := by
  unfold fieldOf fieldVal
  rcases h : L[i / per]? with _ | ⟨row, X⟩
  · simp [eval_cst]
  · obtain ⟨hX, h0, h1⟩ := hL _ (List.mem_of_getElem? h)
    have hb : w * (i % per) + w ≤ 32 := by
      have := Nat.mod_lt i hper
      calc w * (i % per) + w = w * (i % per + 1) := by ring
        _ ≤ w * per := Nat.mul_le_mul_left _ (by omega)
        _ ≤ 32 := hw
    have hrr : (((256 * j + 248 : ℕ) : ℤ) + workOff row sh).toNat < 2 ^ logSize := by
      rw [← Int.ofNat_lt, Int.toNat_of_nonneg h0]; exact_mod_cast h1
    simp only
    exact ev_window hb (wrap_eq h0 (by exact_mod_cast h1)) (bA hsat hj hrr hX)


omit hsat in
theorem slotsOk0 {L : List (ℕ × ℕ)} (hL : ∀ p ∈ L, (p.2 = A ∨ p.2 = E ∨ p.2 = W) ∧ 241 ≤ p.1 ∧ p.1 ≤ 253) :
    SlotsOk logSize j L 0 := by
  intro p hp
  obtain ⟨hX, h1, h2⟩ := hL p hp
  have hj' : ((256 * (j + 1) : ℕ) : ℤ) ≤ ((2 ^ logSize : ℕ) : ℤ) := by exact_mod_cast hj
  push_cast at hj'
  refine ⟨by rcases hX with h | h | h <;> rw [h] <;> decide, ?_, ?_⟩ <;> unfold workOff <;> push_cast <;> omega

omit hsat in
theorem slotsOkPrev (hj1 : 1 ≤ j) {L : List (ℕ × ℕ)}
    (hL : ∀ p ∈ L, (p.2 = A ∨ p.2 = E ∨ p.2 = W) ∧ 241 ≤ p.1 ∧ p.1 ≤ 253) :
    SlotsOk logSize j L (-256) := by
  intro p hp
  obtain ⟨hX, h1, h2⟩ := hL p hp
  have hj' : ((256 * (j + 1) : ℕ) : ℤ) ≤ ((2 ^ logSize : ℕ) : ℤ) := by exact_mod_cast hj
  push_cast at hj'
  refine ⟨by rcases hX with h | h | h <;> rw [h] <;> decide, ?_, ?_⟩ <;> unfold workOff <;> push_cast <;> omega

theorem work_sat {c : Expr} (hc : c ∈ workCs) :
    c.eval (2 ^ logSize) preCols pub main (256 * j + 248) = 0 :=
  hsat _ (by omega) c (by show c ∈ constraints; simp only [constraints, List.mem_append]; right; exact hc)

omit hsat in
theorem ev_workSel : workSel.eval (2 ^ logSize) preCols pub main (256 * j + 248) = 1 := by
  unfold workSel
  rw [eval_oneRow (i := WORK) (row := 248) rfl (by omega), show (256 * j + 248) % 256 = 248 by omega]; simp

theorem ev_ohS {s : ℕ} (hs : s < 27) :
    (ohS s).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((ohv main j s : ℕ) : F) := by
  unfold ohS ohv
  have hw : wrap (2 ^ logSize) (256 * j + 248) (-32) = 256 * j + 216 := by
    have := wrapN (N := 2 ^ logSize) (k := 32) (show 32 ≤ 256 * j + 248 by omega) (by omega)
    simp only [Nat.cast_ofNat] at this; rw [this]; omega
  exact ev_bit hw (bA hsat hj (by omega) (by decide) s (by omega))

theorem ev_mB (i : ℕ) :
    (mB i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((md (headerWord main j 18) i : ℕ) : F) := by
  have hw : wrap (2 ^ logSize) (256 * j + 248) (-170) = 256 * j + 78 := by
    have := wrapN (N := 2 ^ logSize) (k := 170) (show 170 ≤ 256 * j + 248 by omega) (by omega)
    simp only [Nat.cast_ofNat] at this; rw [this]; omega
  have hy : headerWord main j 18 = word main W (256 * j + 78) := by simp [headerWord]
  have hb := bA hsat hj (rr := 256 * j + 78) (by omega) (base := W) (by decide)
  unfold mB md
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ 3 ≤ i) with rfl | rfl | rfl | h3
  · simp only [show (0 : ℕ) < 2 from by norm_num, if_true]; rw [ev_beByte (by norm_num) hw hb, hy]
  · simp only [show (1 : ℕ) < 2 from by norm_num, if_true, show (1 : ℕ) ≠ 0 from by norm_num, if_false]
    rw [ev_beByte (by norm_num) hw hb, hy]
  · simp only [show ¬ (2 : ℕ) < 2 from by norm_num, if_false, if_true, show (2 : ℕ) ≠ 0 from by norm_num,
      show (2 : ℕ) ≠ 1 from by norm_num]
    rw [ev_window (by norm_num) hw hb, hy]; norm_num
  · simp only [show ¬ i < 2 by omega, show i ≠ 2 by omega, show i ≠ 0 by omega, show i ≠ 1 by omega,
      if_false, eval_cst, Nat.cast_zero]

omit hsat hj in
theorem md_lt (y : Word) (i : ℕ) : md y i < 256 := by
  unfold md; split_ifs <;> omega

/-- Product columns as exact equations: `Σ_{i+j=k} q_i·m_j + carry_in = R_k + 256·carry_out`. -/
theorem prod_col {k : ℕ} (hk : k < 18) :
    (∑ i ∈ Finset.range 16, if i ≤ k ∧ k - i < 3 then qd main j i * md (headerWord main j 18) (k - i) else 0) +
      cin (pcc main j) k = rd main j k + 256 * pcc main j k := by
  have hq : SlotsOk logSize j qSlots 0 := slotsOk0 hj (by intro p hp; simp [qSlots] at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp)
  have hr : SlotsOk logSize j rSlots 0 := slotsOk0 hj (by intro p hp; simp [rSlots] at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp)
  have hp : SlotsOk logSize j pcSlots 0 := slotsOk0 hj (by
    intro p hp; simp [pcSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have c := work_sat hsat hj (c := prodCol k) (by
    unfold workCs
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))
  have eq : ∀ i, (qB i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((qd main j i : ℕ) : F) :=
    fun i => ev_field hsat hj hq (by norm_num) (by norm_num) i
  have er : (rB k).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((rd main j k : ℕ) : F) :=
    ev_field hsat hj hr (by norm_num) (by norm_num) k
  have ein : (if k = 0 then cst 0 else pcE (k - 1)).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      ((cin (pcc main j) k : ℕ) : F) := by
    unfold cin pcc
    split
    · simp [eval_cst]
    · rw [if_pos (by omega)]; exact ev_field hsat hj hp (by norm_num) (by norm_num) _
  have eout : (if k < 17 then Expr.mul (cst 256) (pcE k) else cst 0).eval (2 ^ logSize) preCols pub main
      (256 * j + 248) = ((256 * pcc main j k : ℕ) : F) := by
    unfold pcc
    split
    · rw [eval_mul', eval_cst, show pcE k = fieldOf pcSlots 10 3 0 k from rfl,
        ev_field hsat hj hp (by norm_num) (by norm_num)]; push_cast; ring
    · simp [eval_cst]
  have esum : (sumE 16 fun i => if i ≤ k ∧ k - i < 3 then Expr.mul (qB i) (mB (k - i)) else cst 0).eval
      (2 ^ logSize) preCols pub main (256 * j + 248) =
      (((∑ i ∈ Finset.range 16, if i ≤ k ∧ k - i < 3 then qd main j i * md (headerWord main j 18) (k - i) else 0 : ℕ)) : F) := by
    rw [ev_sumE, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split
    · rw [eval_mul', eq, ev_mB hsat hj]; push_cast; ring
    · simp [eval_cst]
  unfold prodCol at c
  rw [eval_mul', ev_workSel hj, one_mul, eval_sub', eval_add', eval_add', esum, ein, er, eout] at c
  have hbq : ∀ i, qd main j i < 256 := fun i => fieldVal_lt main j qSlots 8 4 0 i
  have hbs : (∑ i ∈ Finset.range 16, if i ≤ k ∧ k - i < 3 then qd main j i * md (headerWord main j 18) (k - i) else 0)
      ≤ 16 * (255 * 255) := by
    calc _ ≤ ∑ i ∈ Finset.range 16, 255 * 255 := Finset.sum_le_sum (fun i _ => by
            split
            · exact Nat.mul_le_mul (by have := hbq i; omega) (by have := md_lt (headerWord main j 18) (k - i); omega)
            · omega)
      _ = 16 * (255 * 255) := by simp
  have hpc : ∀ k, pcc main j k < 1024 := fun k => by
    unfold pcc; split
    · exact fieldVal_lt main j pcSlots 10 3 0 k
    · omega
  have hcin : cin (pcc main j) k < 1024 := by unfold cin; split <;> [omega; exact hpc _]
  have hrd : rd main j k < 256 := fieldVal_lt main j rSlots 8 4 0 k
  have := hpc k
  exact natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega))
    (by rw [Nat.cast_add, Nat.cast_add]; exact sub_eq_zero.mp c)


theorem ev_qB (i : ℕ) : (qB i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((qd main j i : ℕ) : F) :=
  ev_field hsat hj (slotsOk0 hj (by intro p hp; simp [qSlots] at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp))
    (by norm_num) (by norm_num) i
theorem ev_rB (i : ℕ) : (rB i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((rd main j i : ℕ) : F) :=
  ev_field hsat hj (slotsOk0 hj (by intro p hp; simp [rSlots] at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp))
    (by norm_num) (by norm_num) i
theorem ev_rhoB (i : ℕ) : (rhoB i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((rhod main j i : ℕ) : F) :=
  ev_field hsat hj (slotsOk0 hj (by
    intro p hp; simp [rhoSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    (by norm_num) (by norm_num) i
theorem ev_sigB (i : ℕ) : (sigB i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((sigd main j i : ℕ) : F) :=
  ev_field hsat hj (slotsOk0 hj (by
    intro p hp; simp [sigSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp))
    (by norm_num) (by norm_num) i

/-- Main columns: `Σ_s [oh_s] R_{k−s} + q_k + ρ_k + carry_in = [k = 32] + 256·carry_out`. -/
theorem main_col {k : ℕ} (hk : k < 42) :
    (∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < 16 then ohv main j s * rd main j (k - s) else 0) +
      qd main j k + rhod main j k + cin (mcc main j) k = (if k = 32 then 1 else 0) + 256 * mcc main j k := by
  have hq : SlotsOk logSize j qSlots 0 := slotsOk0 hj (by intro p hp; simp [qSlots] at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp)
  have hr : SlotsOk logSize j rSlots 0 := slotsOk0 hj (by intro p hp; simp [rSlots] at hp; rcases hp with rfl | rfl | rfl | rfl <;> simp)
  have hrho : SlotsOk logSize j rhoSlots 0 := slotsOk0 hj (by
    intro p hp; simp [rhoSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hm : SlotsOk logSize j mcSlots 0 := slotsOk0 hj (by intro p hp; simp [mcSlots] at hp; rcases hp with rfl | rfl | rfl <;> simp)
  have c := work_sat hsat hj (c := mainCol k) (by
    unfold workCs
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))))
  have ein : (if k = 0 then cst 0 else mcE' (k - 1)).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      ((cin (mcc main j) k : ℕ) : F) := by
    unfold cin mcc
    split
    · simp [eval_cst]
    · rw [if_pos (by omega)]; exact ev_field hsat hj hm (by norm_num) (by norm_num) _
  have eout : (if k < 41 then Expr.mul (cst 256) (mcE' k) else cst 0).eval (2 ^ logSize) preCols pub main
      (256 * j + 248) = ((256 * mcc main j k : ℕ) : F) := by
    unfold mcc
    split
    · rw [eval_mul', eval_cst, show mcE' k = fieldOf mcSlots 2 16 0 k from rfl,
        ev_field hsat hj hm (by norm_num) (by norm_num)]; push_cast; ring
    · simp [eval_cst]
  have e32 : (if k = 32 then cst 1 else cst 0).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      (((if k = 32 then 1 else 0 : ℕ)) : F) := by split <;> simp [eval_cst]
  have esum : (sumE 27 fun s => if 16 ≤ s ∧ s ≤ k ∧ k - s < 16 then Expr.mul (ohS s) (rB (k - s)) else cst 0).eval
      (2 ^ logSize) preCols pub main (256 * j + 248) =
      (((∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < 16 then ohv main j s * rd main j (k - s) else 0 : ℕ)) : F) := by
    rw [ev_sumE, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    split
    · rw [eval_mul', ev_ohS hsat hj (by simpa using hs), ev_rB hsat hj]
      push_cast; ring
    · simp [eval_cst]
  unfold mainCol at c
  rw [eval_mul', ev_workSel hj, one_mul, eval_sub', eval_add', eval_add', eval_add', eval_add', esum,
    ev_qB hsat hj, ev_rhoB hsat hj, ein, e32, eout] at c
  have hbs : (∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < 16 then ohv main j s * rd main j (k - s) else 0)
      ≤ 27 * 255 := by
    calc _ ≤ ∑ s ∈ Finset.range 27, 255 := Finset.sum_le_sum (fun s _ => by
            split
            · have h1 : ohv main j s ≤ 1 := Bool.toNat_le _
              have h2 := fieldVal_lt main j rSlots 8 4 0 (k - s)
              calc ohv main j s * rd main j (k - s) ≤ 1 * 255 := Nat.mul_le_mul h1 (by unfold rd; omega)
                _ = 255 := by norm_num
            · omega)
      _ = 27 * 255 := by simp
  have hmc : ∀ k, mcc main j k < 4 := fun k => by
    unfold mcc; split
    · exact fieldVal_lt main j mcSlots 2 16 0 k
    · omega
  have hcin : cin (mcc main j) k < 4 := by unfold cin; split <;> [omega; exact hmc _]
  have h1 := fieldVal_lt main j qSlots 8 4 0 k
  have h2 := fieldVal_lt main j rhoSlots 8 4 0 k
  have := hmc k
  have h32 : (if k = 32 then 1 else 0) ≤ 1 := by split <;> omega
  exact natCast_inj_of_lt (lt_P_of (by unfold qd rhod; omega)) (lt_P_of (by omega))
    (by rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, Nat.cast_add]; exact sub_eq_zero.mp c)

/-- Remainder columns: `ρ_k + σ_k + carry_in = Σ_s [oh_s] m_{k−s} + 256·carry_out`. -/
theorem rs_col {k : ℕ} (hk : k < 29) :
    rhod main j k + sigd main j k + cin (ecc main j) k =
      (∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < 3 then ohv main j s * md (headerWord main j 18) (k - s) else 0) +
        256 * ecc main j k := by
  have hrho : SlotsOk logSize j rhoSlots 0 := slotsOk0 hj (by
    intro p hp; simp [rhoSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have hsig : SlotsOk logSize j sigSlots 0 := slotsOk0 hj (by
    intro p hp; simp [sigSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
  have he : SlotsOk logSize j [(253, A)] 0 := slotsOk0 hj (by intro p hp; simp at hp; subst hp; simp)
  have c := work_sat hsat hj (c := rsCol k) (by
    unfold workCs
    exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))
  have ein : (if k = 0 then cst 0 else ecE (k - 1)).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      ((cin (ecc main j) k : ℕ) : F) := by
    unfold cin ecc
    split
    · simp [eval_cst]
    · rw [if_pos (by omega)]; exact ev_field hsat hj he (by norm_num) (by norm_num) _
  have eout : (if k < 28 then Expr.mul (cst 256) (ecE k) else cst 0).eval (2 ^ logSize) preCols pub main
      (256 * j + 248) = ((256 * ecc main j k : ℕ) : F) := by
    unfold ecc
    split
    · rw [eval_mul', eval_cst, show ecE k = fieldOf [(253, A)] 1 32 0 k from rfl,
        ev_field hsat hj he (by norm_num) (by norm_num)]; push_cast; ring
    · simp [eval_cst]
  have esum : (sumE 27 fun s => if 16 ≤ s ∧ s ≤ k ∧ k - s < 3 then Expr.mul (ohS s) (mB (k - s)) else cst 0).eval
      (2 ^ logSize) preCols pub main (256 * j + 248) =
      (((∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < 3 then ohv main j s * md (headerWord main j 18) (k - s) else 0 : ℕ)) : F) := by
    rw [ev_sumE, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    split
    · rw [eval_mul', ev_ohS hsat hj (by simpa using hs), ev_mB hsat hj]; push_cast; ring
    · simp [eval_cst]
  unfold rsCol at c
  rw [eval_mul', ev_workSel hj, one_mul, eval_sub', eval_add', eval_add', eval_add',
    ev_rhoB hsat hj, ev_sigB hsat hj, ein, esum, eout] at c
  have hbs : (∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < 3 then ohv main j s * md (headerWord main j 18) (k - s) else 0)
      ≤ 27 * 255 := by
    calc _ ≤ ∑ s ∈ Finset.range 27, 255 := Finset.sum_le_sum (fun s _ => by
            split
            · have h1 : ohv main j s ≤ 1 := Bool.toNat_le _
              have h2 := md_lt (headerWord main j 18) (k - s)
              calc ohv main j s * md (headerWord main j 18) (k - s) ≤ 1 * 255 := Nat.mul_le_mul h1 (by omega)
                _ = 255 := by norm_num
            · omega)
      _ = 27 * 255 := by simp
  have hec : ∀ k, ecc main j k < 2 := fun k => by
    unfold ecc; split
    · exact fieldVal_lt main j [(253, A)] 1 32 0 k
    · omega
  have hcin : cin (ecc main j) k < 2 := by unfold cin; split <;> [omega; exact hec _]
  have h1 := fieldVal_lt main j rhoSlots 8 4 0 k
  have h2 := fieldVal_lt main j sigSlots 8 4 0 k
  have := hec k
  exact natCast_inj_of_lt (lt_P_of (by unfold rhod sigd; omega)) (lt_P_of (by omega))
    (by rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]; exact sub_eq_zero.mp c)


omit hsat hj in
theorem wd_prev (hj1 : 1 ≤ j) (i : ℕ) : wd main j (-256) i = wd main (j - 1) 0 i := by
  unfold wd fieldVal
  split
  · rename_i row X _
    rw [show ((((256 * j + 248 : ℕ) : ℤ) + workOff row (-256))).toNat =
        (((256 * (j - 1) + 248 : ℕ) : ℤ) + workOff row 0).toNat by unfold workOff; omega]
  · rfl

theorem ev_wB0 (i : ℕ) : (wB 0 i).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((wd main j 0 i : ℕ) : F) :=
  ev_field hsat hj (slotsOk0 hj (by
    intro p hp; simp [wSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp)) (by norm_num) (by norm_num) i

theorem ev_wL0 (l : ℕ) : (wL 0 l).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((wl main j l : ℕ) : F) := by
  unfold wL wl; rw [eval_add', eval_mul', eval_cst, ev_wB0 hsat hj, ev_wB0 hsat hj]; push_cast; ring

theorem ev_qL (l : ℕ) : (qL l).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((ql main j l : ℕ) : F) := by
  unfold qL ql; rw [eval_add', eval_mul', eval_cst, ev_qB hsat hj, ev_qB hsat hj]; push_cast; ring

theorem ev_wcin (l : ℕ) (hl : l < 10) :
    (if l = 0 then cst 0 else wcE (l - 1)).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      ((cin (wcc main j) l : ℕ) : F) := by
  have he : SlotsOk logSize j [(253, E)] 0 := slotsOk0 hj (by intro p hp; simp at hp; subst hp; simp)
  unfold cin wcc
  split
  · simp [eval_cst]
  · rw [if_pos (by omega)]; exact ev_field hsat hj he (by norm_num) (by norm_num) _

theorem ev_wcout (l : ℕ) :
    (if l < 9 then Expr.mul (cst 65536) (wcE l) else cst 0).eval (2 ^ logSize) preCols pub main (256 * j + 248) =
      ((65536 * wcc main j l : ℕ) : F) := by
  have he : SlotsOk logSize j [(253, E)] 0 := slotsOk0 hj (by intro p hp; simp at hp; subst hp; simp)
  unfold wcc
  split
  · rw [eval_mul', eval_cst, show wcE l = fieldOf [(253, E)] 1 32 0 l from rfl,
      ev_field hsat hj he (by norm_num) (by norm_num)]; push_cast; ring
  · simp [eval_cst]

omit hsat hj in
theorem wcc_lt (main : ℕ → ℕ → F) (j k : ℕ) : wcc main j k < 2 := by
  unfold wcc; split
  · exact fieldVal_lt main j [(253, E)] 1 32 0 k
  · omega

omit hsat hj in
theorem limb_lt {x : ℕ → ℕ} (hx : ∀ i, x i < 256) (l : ℕ) : x (2 * l) + 256 * x (2 * l + 1) < 65536 := by
  have := hx (2 * l); have := hx (2 * l + 1); omega

omit hsat hj in
theorem mem_workFam {c : Expr} {l : ℕ} (hl : l < 10) (hc : c ∈ workFam l) : c ∈ workCs := by
  unfold workCs
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨l, List.mem_range.mpr hl, hc⟩)

/-- Chainwork limb columns on a non-first header. -/
theorem w_col_nf (hj1 : 1 ≤ j) {l : ℕ} (hl : l < 10) :
    wl main (j - 1) l + ql main j l + cin (wcc main j) l = wl main j l + 65536 * wcc main j l := by
  have hprev : SlotsOk logSize j wSlots (-256) := slotsOkPrev hj hj1 (by
    intro p hp; simp [wSlots] at hp; rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp)
  have c := work_sat hsat hj (mem_workFam hl (List.mem_cons_self ..))
  have ep : (wL (-256) l).eval (2 ^ logSize) preCols pub main (256 * j + 248) = ((wl main (j - 1) l : ℕ) : F) := by
    unfold wL wl
    rw [eval_add', eval_mul', eval_cst, show wB (-256) (2 * l) = fieldOf wSlots 8 4 (-256) (2 * l) from rfl,
      show wB (-256) (2 * l + 1) = fieldOf wSlots 8 4 (-256) (2 * l + 1) from rfl,
      ev_field hsat hj hprev (by norm_num) (by norm_num), ev_field hsat hj hprev (by norm_num) (by norm_num)]
    rw [show fieldVal main j wSlots 8 4 (-256) (2 * l) = wd main j (-256) (2 * l) from rfl,
      show fieldVal main j wSlots 8 4 (-256) (2 * l + 1) = wd main j (-256) (2 * l + 1) from rfl,
      wd_prev hj1, wd_prev hj1]
    push_cast; ring
  have hf := ev_firstAt (pub := pub) (main := main) hj (q := 248) (by norm_num)
  simp only [workAdd, workSel, notFirst] at c
  rw [eval_mul', eval_mul', show (pre WORK) = workSel from rfl, ev_workSel hj, eval_sub', eval_cst, hf,
    if_neg (by omega), eval_sub', eval_add', eval_add', eval_add', ep, ev_qL hsat hj, ev_wcin hsat hj l hl,
    ev_wL0 hsat hj, ev_wcout hsat hj] at c
  simp only [sub_zero, Nat.cast_one, one_mul] at c
  have h1 := limb_lt (fun i => fieldVal_lt main (j - 1) wSlots 8 4 0 i) l
  have h2 := limb_lt (fun i => fieldVal_lt main j qSlots 8 4 0 i) l
  have h3 := limb_lt (fun i => fieldVal_lt main j wSlots 8 4 0 i) l
  have h4 : cin (wcc main j) l < 2 := by unfold cin; split <;> [omega; exact wcc_lt main j _]
  have h5 := wcc_lt main j l
  exact natCast_inj_of_lt (lt_P_of (by unfold wl ql wd qd at *; omega)) (lt_P_of (by unfold wl wd at *; omega))
    (by rw [Nat.cast_add, Nat.cast_add, Nat.cast_add]; exact sub_eq_zero.mp c)

/-- Chainwork limb columns on the first header (input work from public inputs 88..97). -/
theorem w_col_f (hj0 : j = 0) {l : ℕ} (hl : l < 10) (hpub : (pub (88 + l)).val < 65536) :
    (pub (88 + l)).val + ql main j l + cin (wcc main j) l = wl main j l + 65536 * wcc main j l := by
  have c := work_sat hsat hj (mem_workFam hl (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  have hf := ev_firstAt (pub := pub) (main := main) hj (q := 248) (by norm_num)
  simp only [workAdd, workSel] at c
  rw [eval_mul', eval_mul', show (pre WORK) = workSel from rfl, ev_workSel hj, hf, if_pos hj0, one_mul,
    eval_sub', eval_add', eval_add', eval_add', ev_qL hsat hj, ev_wcin hsat hj l hl,
    ev_wL0 hsat hj, ev_wcout hsat hj] at c
  simp only [Expr.eval, one_mul] at c
  have h2 := limb_lt (fun i => fieldVal_lt main j qSlots 8 4 0 i) l
  have h3 := limb_lt (fun i => fieldVal_lt main j wSlots 8 4 0 i) l
  have h4 : cin (wcc main j) l < 2 := by unfold cin; split <;> [omega; exact wcc_lt main j _]
  have h5 := wcc_lt main j l
  exact natCast_inj_of_lt (lt_P_of (by unfold ql qd at *; omega)) (lt_P_of (by unfold wl wd at *; omega))
    (by rw [Nat.cast_add, Nat.cast_add, Nat.cast_add, ZMod.natCast_zmod_val]; exact sub_eq_zero.mp c)

/-- The last header's chainwork limbs are public inputs 98..107. -/
theorem w_out (hlast : 2 ^ logSize = 256 * (j + 1)) {l : ℕ} (hl : l < 10) :
    (pub (98 + l)).val = wl main j l := by
  have c := work_sat hsat hj (mem_workFam hl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))))
  have hL : (pre LAST).eval (2 ^ logSize) preCols pub main (256 * j + 248) = 1 := by
    rw [eval_last (by omega)]; simp; omega
  rw [eval_mul', eval_mul', ev_workSel hj, hL, one_mul, one_mul, eval_sub', ev_wL0 hsat hj] at c
  simp only [Expr.eval] at c
  have h3 := limb_lt (fun i => fieldVal_lt main j wSlots 8 4 0 i) l
  have := sub_eq_zero.mp c
  rw [← this, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_P_of (by unfold wl wd at *; omega))]


/-- The one-hot exponent and the PoW facts at a header. -/
theorem work_exp : ∃ s0, 16 ≤ s0 ∧ s0 < 27 ∧ (∀ s < 27, ohv main j s = if s = s0 then 1 else 0) ∧
    compactTarget (nBitsOf (headerWord main j)) = some (mantNat (headerWord main j 18) * 256 ^ s0) := by
  obtain ⟨-, s0, hs0, hg, hu, hexp, -, hm1, hsign⟩ := header_pow_ex hsat hj
  have hoh : ∀ s < 27, ohv main j s = if s = s0 then 1 else 0 := fun s hs => by
    unfold ohv
    by_cases h : s = s0
    · subst h; simp [hg]
    · simp [h, hu s hs h]
  refine ⟨s0, ?_, hs0, hoh, compactTarget_of _ hexp rfl (by omega) hm1 (by omega)⟩
  -- s ≥ 16 from `sMin`.
  have c := work_sat hsat hj (c := sMin) (by unfold workCs; simp)
  unfold sMin at c
  rw [eval_mul', ev_workSel hj, one_mul, ev_sumE, Finset.sum_congr rfl (fun s hs => ev_ohS hsat hj
    (by simp at hs; omega)), ← Nat.cast_sum] at c
  have hle : ∑ s ∈ Finset.range 16, ohv main j s ≤ 16 := by
    calc _ ≤ ∑ s ∈ Finset.range 16, 1 := Finset.sum_le_sum (fun s _ => Bool.toNat_le _)
      _ = 16 := by simp
  have h0 : ∑ s ∈ Finset.range 16, ohv main j s = 0 :=
    natCast_inj_of_lt (lt_P_of (by omega)) (by norm_num [P]) (by rw [c]; simp)
  by_contra hlt
  have := (Finset.sum_eq_zero_iff.mp h0) s0 (Finset.mem_range.mpr (by omega))
  rw [hoh s0 hs0, if_pos rfl] at this
  exact absurd this one_ne_zero

/-- **Per-header work.** The header's `q` is Core's `GetBlockProof` of its nBits. -/
theorem work_q : workQ main j = blockProof (nBitsOf (headerWord main j)) := by
  obtain ⟨s0, h16, hs0, hoh, hct⟩ := work_exp hsat hj
  have hM : ∑ i ∈ Finset.range 3, md (headerWord main j 18) i * 256 ^ i = mantNat (headerWord main j 18) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, md, mantNat]; norm_num; ring
  -- Product: Q · M = R.
  have hprod : workQ main j * mantNat (headerWord main j 18) = ∑ i ∈ Finset.range 16, rd main j i * 256 ^ i := by
    have := carry_chain _ (rd main j) (pcc main j) 256 18 (fun k hk => prod_col hsat hj hk) (by simp [cin, pcc])
    rw [cauchy _ _ 256 16 3 18 (by norm_num) (by norm_num), hM] at this
    rw [workQ, this, sum_stop (rd main j) 256 16 18 (by norm_num) (fun i hi => fieldVal_none main j rSlots 8 4 0 i (by simp [rSlots]; omega))]
  -- One-hot selection inside the column sums.
  have sel : ∀ (g : ℕ → ℕ) (n k : ℕ),
      (∑ s ∈ Finset.range 27, if 16 ≤ s ∧ s ≤ k ∧ k - s < n then ohv main j s * g (k - s) else 0) =
        if s0 ≤ k ∧ k - s0 < n then g (k - s0) else 0 := by
    intro g n k
    rw [Finset.sum_eq_single s0]
    · rw [hoh s0 hs0, if_pos rfl, one_mul]
      by_cases h : s0 ≤ k ∧ k - s0 < n
      · rw [if_pos ⟨h16, h⟩, if_pos h]
      · rw [if_neg (by tauto), if_neg h]
    · intro s hs hne
      rw [hoh s (by simpa using hs), if_neg hne, zero_mul]; simp
    · intro h; simp at h; omega
  -- Main: R · 256^s + Q + ρ = 2^256.
  have hmain : 256 ^ s0 * (∑ i ∈ Finset.range 16, rd main j i * 256 ^ i) + workQ main j +
      (∑ i ∈ Finset.range 28, rhod main j i * 256 ^ i) = 2 ^ 256 := by
    have := carry_chain _ (fun k => if k = 32 then 1 else 0) (mcc main j) 256 42
      (fun k hk => main_col hsat hj hk) (by simp [cin, mcc])
    simp only [add_mul, Finset.sum_add_distrib, sel] at this
    rw [shift_sum _ 256 s0 16 42 (by omega),
      sum_stop (qd main j) 256 16 42 (by norm_num) (fun i hi => fieldVal_none main j qSlots 8 4 0 i (by simp [qSlots]; omega)),
      sum_stop (rhod main j) 256 28 42 (by norm_num) (fun i hi => fieldVal_none main j rhoSlots 8 4 0 i (by simp [rhoSlots]; omega))] at this
    rw [workQ, this]
    simp [Finset.sum_ite_eq']
  -- Remainder: ρ + σ = M · 256^s.
  have hrs : (∑ i ∈ Finset.range 28, rhod main j i * 256 ^ i) + (∑ i ∈ Finset.range 28, sigd main j i * 256 ^ i) =
      256 ^ s0 * mantNat (headerWord main j 18) := by
    have := carry_chain _ _ (ecc main j) 256 29 (fun k hk => rs_col hsat hj hk) (by simp [cin, ecc])
    simp only [add_mul, Finset.sum_add_distrib, sel] at this
    rw [shift_sum _ 256 s0 3 29 (by omega), hM,
      sum_stop (rhod main j) 256 28 29 (by norm_num) (fun i hi => fieldVal_none main j rhoSlots 8 4 0 i (by simp [rhoSlots]; omega)),
      sum_stop (sigd main j) 256 28 29 (by norm_num) (fun i hi => fieldVal_none main j sigSlots 8 4 0 i (by simp [sigSlots]; omega))] at this
    exact this
  -- Conclude: Q = ⌊2^256 / (T + 1)⌋ with T = M · 256^s.
  set M := mantNat (headerWord main j 18)
  set Rv := ∑ i ∈ Finset.range 16, rd main j i * 256 ^ i
  set ρ := ∑ i ∈ Finset.range 28, rhod main j i * 256 ^ i
  set σ := ∑ i ∈ Finset.range 28, sigd main j i * 256 ^ i
  set Q := workQ main j
  have hT : M * 256 ^ s0 < 2 ^ 256 := by
    have hm : M < 2 ^ 23 := by simp only [M]; unfold mantNat; omega
    calc M * 256 ^ s0 < 2 ^ 23 * 256 ^ 26 :=
          Nat.mul_lt_mul_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)) (by positivity)
      _ ≤ 2 ^ 256 := by norm_num
  rw [blockProof_eq hct hT]
  symm
  apply Nat.div_eq_of_lt_le
  · rw [← hmain, ← hprod]; nlinarith
  · rw [← hmain, ← hprod]; nlinarith

/-- **Chainwork step.** -/
theorem work_step (hpub : j = 0 → ∀ l < 10, (pub (88 + l)).val < 65536) :
    workAt main j = (if j = 0 then pubWork pub 88 else workAt main (j - 1)) +
      blockProof (nBitsOf (headerWord main j)) := by
  rw [← work_q hsat hj]
  have hW : ∀ jj, workAt main jj = ∑ l ∈ Finset.range 10, wl main jj l * 65536 ^ l := fun jj => by
    unfold workAt wl; rw [limbs_bytes (fun i => wd main jj 0 i) 10]
  have hQ : workQ main j = ∑ l ∈ Finset.range 10, ql main j l * 65536 ^ l := by
    unfold workQ ql; rw [limbs_bytes (fun i => qd main j i) 10]
    exact (sum_stop _ 256 16 20 (by norm_num) (fun i hi => fieldVal_none main j qSlots 8 4 0 i (by simp [qSlots]; omega))).symm
  by_cases h0 : j = 0
  · rw [if_pos h0, hW, hQ, pubWork, ← Finset.sum_add_distrib]
    have := carry_chain _ (wl main j) (wcc main j) 65536 10
      (fun l hl => w_col_f hsat hj h0 hl (hpub h0 l hl)) (by simp [cin, wcc])
    simp only [add_mul] at this
    rw [this]
  · rw [if_neg h0, hW, hW, hQ, ← Finset.sum_add_distrib]
    have := carry_chain _ (wl main j) (wcc main j) 65536 10
      (fun l hl => w_col_nf hsat hj (by omega) hl) (by simp [cin, wcc])
    simp only [add_mul] at this
    rw [this]

/-- The last header's chainwork is public (inputs 98..107). -/
theorem work_out (hlast : 2 ^ logSize = 256 * (j + 1)) : workAt main j = pubWork pub 98 := by
  unfold workAt pubWork
  rw [← limbs_bytes (fun i => wd main j 0 i) 10]
  refine Finset.sum_congr rfl (fun l hl => ?_)
  rw [w_out hsat hj hlast (by simpa using hl)]; rfl

end Work

end StarkedAir.HeaderChain
