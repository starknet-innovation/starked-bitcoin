/-
**The block leaf's height-derived context (BLOCK-REC, D-043 part 4), Lean-first.** A block proof's
public inputs carry context the block system takes as given: the BIP34, CSV and segwit flags (inputs
4–6, `BlockPubs`) and the subsidy (inputs 159–160, two limbs). They are functions of the height, so
the leaf pins them from the height:

- `flagOps`: a flag `f` is a bit and `f·(H − c) + (1 − f)·(c − 1 − H) < 2^30`; with `H, c < 2^30`
  the wrong branch would wrap mod P far above `2^30`, so `f = [c ≤ H]` (`flag_sound`);
- `subOps`: `H = 210000·q + r` with `r < 210000`, a one-hot `e` over 64 halvings with `Σ e = 1`,
  `Σ j·e_j = q`, and the subsidy's limbs `Σ e_j·low_j`, `Σ e_j·high_j` (`sub_sound`).

`ctx_sound`: the inputs `[H, f34, fcsv, fsw, subl, subh]` are the height's context.
-/
import StarkedAir.Circuit.BlockNode
import StarkedAir.Spec.Block

namespace StarkedAir.Circuit.BlockCtx

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockNode Q

/-- The subsidy at height `h` (Core's `GetBlockSubsidy`, mainnet). -/
def subsidy (h : ℕ) : ℕ := if 64 ≤ h / 210000 then 0 else 5000000000 >>> (h / 210000)

/-- Registers: 0 the height, 1–3 the flags, 4–5 the subsidy's limbs (low 24 bits, the rest); 6 one. -/
def ONE : ℕ := 6

/-- A flag at `fr` for threshold `c`, registers from `m` (`m … m + 17`). -/
def flagOps (m fr c : ℕ) : List Op :=
  [.const m c 0 0 0, .const (m + 1) (c - 1) 0 0 0, .sub (m + 2) 0 m, .sub (m + 3) (m + 1) 0,
   .mul (m + 4) fr (m + 2), .sub (m + 5) ONE fr, .mul (m + 6) (m + 5) (m + 3), .add (m + 7) (m + 4) (m + 6),
   .mul (m + 8) fr fr, .eq (m + 8) fr] ++ lt30 (m + 9) (m + 7)

variable {ρ : ℕ → Q}

theorem base_sub {x y : Q} (hx : IsBase x) (hy : IsBase y) : x - y = ⟨x.a - y.a, 0, 0, 0⟩ := by
  obtain ⟨b1, c1, d1⟩ := hx; obtain ⟨b2, c2, d2⟩ := hy; ext <;> simp [b1, c1, d1, b2, c2, d2]

theorem base_add {x y : Q} (hx : IsBase x) (hy : IsBase y) : x + y = ⟨x.a + y.a, 0, 0, 0⟩ := by
  obtain ⟨b1, c1, d1⟩ := hx; obtain ⟨b2, c2, d2⟩ := hy; ext <;> simp [b1, c1, d1, b2, c2, d2]

theorem lit_base (a : ℕ) : IsBase (lit a 0 0 0) := ⟨by simp [lit], by simp [lit], by simp [lit]⟩

theorem mk_base (a : F) : IsBase (⟨a, 0, 0, 0⟩ : Q) := ⟨rfl, rfl, rfl⟩

/-- `x − y` for naturals below `2^30` wraps above `2^30` when `x < y`. -/
theorem val_sub_big {x y : ℕ} (hx : x < 2 ^ 30) (hy : y < 2 ^ 30) (hxy : x < y) :
    2 ^ 30 ≤ ((x : F) - (y : F)).val := by
  have hP : P = 2147483647 := rfl
  have e : (x : F) - (y : F) = ((P - (y - x) : ℕ) : F) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega), ZMod.natCast_self]; ring
  rw [e, ZMod.val_natCast_of_lt (by omega)]; omega

/-- **Flags.** -/
theorem flag_sound {m fr c H : ℕ} (h : Holds ρ (flagOps m fr c)) (hc : c < 2 ^ 30) (hc1 : 1 ≤ c)
    (hH : H < 2 ^ 30) (h0 : ρ 0 = ⟨(H : F), 0, 0, 0⟩) (hf : IsBase (ρ fr)) (hone : ρ ONE = lit 1 0 0 0) :
    (ρ fr).a = if c ≤ H then 1 else 0 := by
  have g := fun (o : Op) (ho : o ∈ flagOps m fr c) => h o ho
  have c0 := g (.const m c 0 0 0) (by simp [flagOps])
  have c1 := g (.const (m + 1) (c - 1) 0 0 0) (by simp [flagOps])
  have s2 := g (.sub (m + 2) 0 m) (by simp [flagOps])
  have s3 := g (.sub (m + 3) (m + 1) 0) (by simp [flagOps])
  have m4 := g (.mul (m + 4) fr (m + 2)) (by simp [flagOps])
  have s5 := g (.sub (m + 5) ONE fr) (by simp [flagOps])
  have m6 := g (.mul (m + 6) (m + 5) (m + 3)) (by simp [flagOps])
  have a7 := g (.add (m + 7) (m + 4) (m + 6)) (by simp [flagOps])
  have m8 := g (.mul (m + 8) fr fr) (by simp [flagOps])
  have e8 := g (.eq (m + 8) fr) (by simp [flagOps])
  have lt := lt30_sound (fun o ho => g o (by simp only [flagOps]; exact List.mem_append_right _ ho))
  simp only [Op.holds] at c0 c1 s2 s3 m4 s5 m6 a7 m8 e8
  have b0 : IsBase (ρ 0) := by rw [h0]; exact mk_base _
  rw [c0, h0, base_sub (mk_base _) (lit_base _)] at s2
  rw [c1, h0, base_sub (lit_base _) (mk_base _)] at s3
  rw [s2, mul_base _ _ hf (mk_base _)] at m4
  rw [hone, base_sub (lit_base _) hf] at s5
  rw [s5, s3, mul_base _ _ (mk_base _) (mk_base _)] at m6
  rw [m4, m6, base_add (mk_base _) (mk_base _)] at a7
  rw [mul_base _ _ hf hf] at m8
  have hb : (ρ fr).a * ((ρ fr).a - 1) = 0 := by
    have := congrArg Q.a (m8.symm.trans e8); simp only at this; linear_combination this
  have tv := lt.2
  rw [a7] at tv
  simp only [lit, Nat.cast_one] at tv
  rcases mul_eq_zero.mp hb with hz | ho
  · rw [hz] at tv
    simp only [zero_mul, sub_zero, one_mul, zero_add] at tv
    rw [hz, if_neg]
    intro hle
    have := val_sub_big (x := c - 1) (y := H) (by omega) hH (by omega)
    omega
  · have hf1 : (ρ fr).a = 1 := sub_eq_zero.mp ho
    rw [hf1] at tv
    simp only [one_mul, sub_self, zero_mul, add_zero] at tv
    rw [hf1, if_pos]
    by_contra hlt
    have := val_sub_big (x := H) (y := c) hH hc (by omega)
    omega

/-! ### The subsidy -/

def lowOf (j : ℕ) : ℕ := (5000000000 >>> j) % 2 ^ 24
def highOf (j : ℕ) : ℕ := (5000000000 >>> j) / 2 ^ 24

/-- One halving's registers `b … b + 11`: the bit, its square, and the four running sums. -/
def hotOps (z b0 q : ℕ) (j : ℕ) : List Op :=
  let b := b0 + 12 * j
  let prev : ℕ → ℕ := fun k => if j = 0 then z else b0 + 12 * (j - 1) + k
  [.guessM31 b (.isEq (.reg q) j), .mul (b + 1) b b, .eq (b + 1) b, .add (b + 2) (prev 2) b,
   .const (b + 3) j 0 0 0, .mul (b + 4) b (b + 3), .add (b + 5) (prev 5) (b + 4),
   .const (b + 6) (lowOf j) 0 0 0, .mul (b + 7) b (b + 6), .add (b + 8) (prev 8) (b + 7),
   .const (b + 9) (highOf j) 0 0 0, .mul (b + 10) b (b + 9), .add (b + 11) (prev 11) (b + 10)]

/-- The subsidy from register `m`: the quotient `m`, the remainder `m + 1`, the one-hot from `m + 26`. -/
def subOps (m : ℕ) : List Op :=
  [.guessM31 m (.divC (.reg 0) 210000), .guessM31 (m + 1) (.modC (.reg 0) 210000), .const (m + 2) 210000 0 0 0,
   .mul (m + 3) m (m + 2), .add (m + 4) (m + 3) (m + 1), .eq (m + 4) 0] ++ lt30 (m + 5) (m + 1) ++
  [.const (m + 14) 209999 0 0 0, .sub (m + 15) (m + 14) (m + 1)] ++ lt30 (m + 16) (m + 15) ++
  [.zero (m + 25)] ++ (List.range 64).flatMap (hotOps (m + 25) (m + 26) m) ++
  [.eq (m + 26 + 12 * 63 + 2) ONE, .eq (m + 26 + 12 * 63 + 5) m, .eq (m + 26 + 12 * 63 + 8) 4,
   .eq (m + 26 + 12 * 63 + 11) 5]

theorem hot_mem {z b0 q j : ℕ} (hj : j < 64) {o : Op} (ho : o ∈ hotOps z b0 q j) :
    o ∈ (List.range 64).flatMap (hotOps z b0 q) := List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ho⟩

/-- The running sums of the one-hot, by induction over the halvings. -/
theorem hot_sums {z b0 q : ℕ} (h : Holds ρ ((List.range 64).flatMap (hotOps z b0 q))) (hz : ρ z = lit 0 0 0 0) :
    ∀ j < 64, (∀ i ≤ j, IsBase (ρ (b0 + 12 * i)) ∧ ((ρ (b0 + 12 * i)).a = 0 ∨ (ρ (b0 + 12 * i)).a = 1)) ∧
      ρ (b0 + 12 * j + 2) = ⟨∑ i ∈ Finset.range (j + 1), (ρ (b0 + 12 * i)).a, 0, 0, 0⟩ ∧
      ρ (b0 + 12 * j + 5) = ⟨∑ i ∈ Finset.range (j + 1), (i : F) * (ρ (b0 + 12 * i)).a, 0, 0, 0⟩ ∧
      ρ (b0 + 12 * j + 8) = ⟨∑ i ∈ Finset.range (j + 1), (lowOf i : F) * (ρ (b0 + 12 * i)).a, 0, 0, 0⟩ ∧
      ρ (b0 + 12 * j + 11) = ⟨∑ i ∈ Finset.range (j + 1), (highOf i : F) * (ρ (b0 + 12 * i)).a, 0, 0, 0⟩ := by
  intro j
  induction j with
  | zero =>
    intro hj
    have g := fun (o : Op) (ho : o ∈ hotOps z b0 q 0) => h o (hot_mem (by norm_num) ho)
    have gb := g (.guessM31 b0 (.isEq (.reg q) 0)) (by simp [hotOps])
    have m1 := g (.mul (b0 + 1) b0 b0) (by simp [hotOps])
    have e1 := g (.eq (b0 + 1) b0) (by simp [hotOps])
    have a2 := g (.add (b0 + 2) z b0) (by simp [hotOps])
    have c3 := g (.const (b0 + 3) 0 0 0 0) (by simp [hotOps])
    have m4 := g (.mul (b0 + 4) b0 (b0 + 3)) (by simp [hotOps])
    have a5 := g (.add (b0 + 5) z (b0 + 4)) (by simp [hotOps])
    have c6 := g (.const (b0 + 6) (lowOf 0) 0 0 0) (by simp [hotOps])
    have m7 := g (.mul (b0 + 7) b0 (b0 + 6)) (by simp [hotOps])
    have a8 := g (.add (b0 + 8) z (b0 + 7)) (by simp [hotOps])
    have c9 := g (.const (b0 + 9) (highOf 0) 0 0 0) (by simp [hotOps])
    have m10 := g (.mul (b0 + 10) b0 (b0 + 9)) (by simp [hotOps])
    have a11 := g (.add (b0 + 11) z (b0 + 10)) (by simp [hotOps])
    simp only [Op.holds] at gb m1 e1 a2 c3 m4 a5 c6 m7 a8 c9 m10 a11
    have hb : (ρ b0).a = 0 ∨ (ρ b0).a = 1 := by
      have := congrArg Q.a (m1.symm.trans e1)
      rw [mul_base _ _ gb gb] at this
      have h2 : (ρ b0).a * ((ρ b0).a - 1) = 0 := by simp only at this; linear_combination this
      rcases mul_eq_zero.mp h2 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    refine ⟨fun i hi => by rw [show i = 0 by omega]; exact ⟨by simpa using gb, by simpa using hb⟩, ?_, ?_, ?_, ?_⟩
    · rw [a2, hz, base_add (lit_base _) gb]; simp [lit]
    · rw [a5, hz, m4, c3, mul_base _ _ gb (lit_base _), base_add (lit_base _) (mk_base _)]; simp [lit]
    · rw [a8, hz, m7, c6, mul_base _ _ gb (lit_base _), base_add (lit_base _) (mk_base _)]; simp [lit]; ring
    · rw [a11, hz, m10, c9, mul_base _ _ gb (lit_base _), base_add (lit_base _) (mk_base _)]; simp [lit]; ring
  | succ j ih =>
    intro hj
    obtain ⟨hbits, s2, s5, s8, s11⟩ := ih (by omega)
    have g := fun (o : Op) (ho : o ∈ hotOps z b0 q (j + 1)) => h o (hot_mem hj ho)
    set b := b0 + 12 * (j + 1) with hbdef
    have pv : ∀ k, (if j + 1 = 0 then z else b0 + 12 * (j + 1 - 1) + k) = b0 + 12 * j + k := fun k => by simp
    have gb := g (.guessM31 b (.isEq (.reg q) (j + 1))) (by simp [hotOps, hbdef])
    have m1 := g (.mul (b + 1) b b) (by simp [hotOps, hbdef])
    have e1 := g (.eq (b + 1) b) (by simp [hotOps, hbdef])
    have a2 := g (.add (b + 2) (b0 + 12 * j + 2) b) (by simp [hotOps, hbdef])
    have c3 := g (.const (b + 3) (j + 1) 0 0 0) (by simp [hotOps, hbdef])
    have m4 := g (.mul (b + 4) b (b + 3)) (by simp [hotOps, hbdef])
    have a5 := g (.add (b + 5) (b0 + 12 * j + 5) (b + 4)) (by simp [hotOps, hbdef])
    have c6 := g (.const (b + 6) (lowOf (j + 1)) 0 0 0) (by simp [hotOps, hbdef])
    have m7 := g (.mul (b + 7) b (b + 6)) (by simp [hotOps, hbdef])
    have a8 := g (.add (b + 8) (b0 + 12 * j + 8) (b + 7)) (by simp [hotOps, hbdef])
    have c9 := g (.const (b + 9) (highOf (j + 1)) 0 0 0) (by simp [hotOps, hbdef])
    have m10 := g (.mul (b + 10) b (b + 9)) (by simp [hotOps, hbdef])
    have a11 := g (.add (b + 11) (b0 + 12 * j + 11) (b + 10)) (by simp [hotOps, hbdef])
    simp only [Op.holds] at gb m1 e1 a2 c3 m4 a5 c6 m7 a8 c9 m10 a11
    have hb : (ρ b).a = 0 ∨ (ρ b).a = 1 := by
      have := congrArg Q.a (m1.symm.trans e1)
      rw [mul_base _ _ gb gb] at this
      have h2 : (ρ b).a * ((ρ b).a - 1) = 0 := by simp only at this; linear_combination this
      rcases mul_eq_zero.mp h2 with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    refine ⟨fun i hi => ?_, ?_, ?_, ?_, ?_⟩
    · rcases Nat.lt_or_ge i (j + 1) with hi' | hi'
      · exact hbits i (by omega)
      · rw [show i = j + 1 by omega]; exact ⟨gb, hb⟩
    · rw [a2, s2, base_add (mk_base _) gb, Finset.sum_range_succ (fun i => (ρ (b0 + 12 * i)).a) (j + 1)]
    · rw [a5, s5, m4, c3, mul_base _ _ gb (lit_base _), base_add (mk_base _) (mk_base _),
        Finset.sum_range_succ (fun i => (i : F) * (ρ (b0 + 12 * i)).a) (j + 1)]
      congr 1; simp only [lit]; push_cast; ring
    · rw [a8, s8, m7, c6, mul_base _ _ gb (lit_base _), base_add (mk_base _) (mk_base _),
        Finset.sum_range_succ (fun i => (lowOf i : F) * (ρ (b0 + 12 * i)).a) (j + 1)]
      congr 1; simp only [lit]; ring
    · rw [a11, s11, m10, c9, mul_base _ _ gb (lit_base _), base_add (mk_base _) (mk_base _),
        Finset.sum_range_succ (fun i => (highOf i : F) * (ρ (b0 + 12 * i)).a) (j + 1)]
      congr 1; simp only [lit]; ring

/-- Bits summing to one: exactly one is set. -/
theorem one_hot {b : ℕ → ℕ} {n : ℕ} (hb : ∀ i < n, b i ≤ 1) (hs : ∑ i ∈ Finset.range n, b i = 1) :
    ∃ j0 < n, b j0 = 1 ∧ ∀ i < n, i ≠ j0 → b i = 0 := by
  obtain ⟨j0, hj0, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by rw [hs]; norm_num : ∑ i ∈ Finset.range n, b i ≠ 0)
  have hj0' := Finset.mem_range.mp hj0
  refine ⟨j0, hj0', by have := hb j0 hj0'; omega, fun i hi hij => ?_⟩
  have : b i + b j0 ≤ 1 := by
    rw [← hs, ← Finset.sum_pair hij]
    exact Finset.sum_le_sum_of_subset (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [hi, hj0'])
  omega

theorem natCast_sum_F (b : ℕ → ℕ) (n : ℕ) : (∑ i ∈ Finset.range n, (b i : F)) = ((∑ i ∈ Finset.range n, b i : ℕ) : F) := by
  push_cast; rfl

/-- **The subsidy.** If the subsidy ops hold on the height `H < 2^30` (register 0), the limbs at 4 and 5
are the subsidy's low 24 bits and the rest. -/
theorem sub_sound {m H : ℕ} (h : Holds ρ (subOps m)) (hH : H < 2 ^ 30) (h0 : ρ 0 = ⟨(H : F), 0, 0, 0⟩)
    (hone : ρ ONE = lit 1 0 0 0) :
    (ρ 4).a = ((subsidy H % 2 ^ 24 : ℕ) : F) ∧ (ρ 5).a = ((subsidy H / 2 ^ 24 : ℕ) : F) := by
  have hP : P = 2147483647 := rfl
  unfold subOps at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨hA, l1⟩, hB⟩, l2⟩, hz⟩, hhot⟩, hfin⟩ := h
  have gA := fun (o : Op) (ho : o ∈ _) => hA o ho
  have gq := gA (.guessM31 m (.divC (.reg 0) 210000)) (by simp)
  have gr := gA (.guessM31 (m + 1) (.modC (.reg 0) 210000)) (by simp)
  have c2 := gA (.const (m + 2) 210000 0 0 0) (by simp)
  have m3 := gA (.mul (m + 3) m (m + 2)) (by simp)
  have a4 := gA (.add (m + 4) (m + 3) (m + 1)) (by simp)
  have e4 := gA (.eq (m + 4) 0) (by simp)
  have c14 := hB (.const (m + 14) 209999 0 0 0) (by simp)
  have s15 := hB (.sub (m + 15) (m + 14) (m + 1)) (by simp)
  have z25 := hz (.zero (m + 25)) (by simp)
  simp only [Op.holds] at gq gr c2 m3 a4 e4 c14 s15 z25
  -- the remainder is below 210000
  have lr := (lt30_sound l1).2
  have lt := (lt30_sound l2).2
  set R := (ρ (m + 1)).a.val with hR
  have eR : (ρ (m + 1)).a = (R : F) := (ZMod.natCast_zmod_val _).symm
  rw [s15, c14, base_sub (lit_base _) gr] at lt
  simp only [lit] at lt
  rw [eR] at lt
  have hR209 : R ≤ 209999 := by
    by_contra hc
    have := val_sub_big (x := 209999) (y := R) (by norm_num) (by omega) (by omega)
    omega
  -- the one-hot
  obtain ⟨hbits, s2, s5, s8, s11⟩ := hot_sums hhot z25 63 (by norm_num)
  have gf := fun (o : Op) (ho : o ∈ _) => hfin o ho
  have f1 := gf (.eq (m + 26 + 12 * 63 + 2) ONE) (by simp)
  have f2 := gf (.eq (m + 26 + 12 * 63 + 5) m) (by simp)
  have f3 := gf (.eq (m + 26 + 12 * 63 + 8) 4) (by simp)
  have f4 := gf (.eq (m + 26 + 12 * 63 + 11) 5) (by simp)
  simp only [Op.holds] at f1 f2 f3 f4
  obtain ⟨bn, hbn⟩ : ∃ bn : ℕ → ℕ, ∀ i, bn i = (ρ (m + 26 + 12 * i)).a.val := ⟨_, fun _ => rfl⟩
  have ebn : ∀ i, (ρ (m + 26 + 12 * i)).a = (bn i : F) := fun i => by rw [hbn]; exact (ZMod.natCast_zmod_val _).symm
  have bn1 : ∀ i < 64, bn i ≤ 1 := by
    intro i hi
    rw [hbn]
    rcases (hbits i (by omega)).2 with h | h <;> rw [h] <;> decide
  have sum1 : ∑ i ∈ Finset.range 64, bn i = 1 := by
    have := congrArg Q.a (s2.symm.trans (f1.trans hone))
    simp only [lit, Nat.cast_one] at this
    rw [show (∑ i ∈ Finset.range (63 + 1), (ρ (m + 26 + 12 * i)).a) = ∑ i ∈ Finset.range 64, (bn i : F) from
      Finset.sum_congr rfl fun i _ => ebn i, natCast_sum_F] at this
    have hle : ∑ i ∈ Finset.range 64, bn i ≤ 64 := by
      calc _ ≤ ∑ _i ∈ Finset.range 64, 1 := Finset.sum_le_sum fun i hi => bn1 i (Finset.mem_range.mp hi)
        _ = 64 := by simp
    exact natCast_inj_of_lt (by omega) (by rw [hP]; norm_num) (by rw [this]; simp)
  obtain ⟨j0, hj0, hb1, hb0⟩ := one_hot bn1 sum1
  have ej : ∀ i < 64, (ρ (m + 26 + 12 * i)).a = if i = j0 then 1 else 0 := by
    intro i hi
    rw [ebn i]
    by_cases hij : i = j0
    · rw [if_pos hij, hij, hb1]; simp
    · rw [if_neg hij, hb0 i hi hij]; simp
  have pick : ∀ (w : ℕ → F), ∑ i ∈ Finset.range (63 + 1), w i * (ρ (m + 26 + 12 * i)).a = w j0 := by
    intro w
    rw [Finset.sum_eq_single j0]
    · rw [ej j0 hj0, if_pos rfl, mul_one]
    · intro i hi hij; rw [ej i (by simpa using hi), if_neg hij, mul_zero]
    · intro hn; exact absurd (Finset.mem_range.mpr (by omega)) hn
  -- the quotient is the one-hot's index
  have hq : (ρ m).a = (j0 : F) := by
    have := congrArg Q.a (s5.symm.trans f2)
    simp only at this; rw [← this]; exact pick (fun i => (i : F))
  -- the height is 210000·j0 + R
  have hHj : H = 210000 * j0 + R := by
    have := congrArg Q.a (a4.symm.trans (e4.trans h0))
    rw [m3, c2, mul_base _ _ gq (lit_base _), base_add (mk_base _) gr] at this
    simp only [lit] at this
    rw [hq, eR] at this
    have := this.symm
    apply natCast_inj_of_lt (by omega) (by omega)
    rw [this]; push_cast; ring
  have hdiv : H / 210000 = j0 := by omega
  have hsub : subsidy H = 5000000000 >>> j0 := by unfold subsidy; rw [hdiv, if_neg (by omega)]
  refine ⟨?_, ?_⟩
  · have := congrArg Q.a (s8.symm.trans f3)
    simp only at this; rw [← this, pick (fun i => (lowOf i : F)), hsub]; rfl
  · have := congrArg Q.a (s11.symm.trans f4)
    simp only at this; rw [← this, pick (fun i => (highOf i : F)), hsub]; rfl

/-! ### The context program -/

def ctxOps : List Op :=
  [.one ONE] ++ flagOps 7 1 Spec.Block.BIP34_HEIGHT ++ flagOps 25 2 Spec.Block.CSV_HEIGHT ++
    flagOps 43 3 Spec.Block.SEGWIT_HEIGHT ++ subOps 61

/-- **The leaf's context is the height's.** With inputs `[H, f34, fcsv, fsw, subl, subh]` (base, `H < 2^30`)
and the ops holding, the flags are the height's activations and the limbs its subsidy's. -/
theorem ctx_sound {H : ℕ} (h : Holds ρ ctxOps) (hH : H < 2 ^ 30) (h0 : ρ 0 = ⟨(H : F), 0, 0, 0⟩)
    (hb : ∀ j < 4, 1 ≤ j → IsBase (ρ j)) :
    (ρ 1).a = (if Spec.Block.BIP34_HEIGHT ≤ H then 1 else 0) ∧ (ρ 2).a = (if Spec.Block.CSV_HEIGHT ≤ H then 1 else 0) ∧
    (ρ 3).a = (if Spec.Block.SEGWIT_HEIGHT ≤ H then 1 else 0) ∧
    (ρ 4).a = ((subsidy H % 2 ^ 24 : ℕ) : F) ∧ (ρ 5).a = ((subsidy H / 2 ^ 24 : ℕ) : F) := by
  unfold ctxOps at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨ho, f1⟩, f2⟩, f3⟩, hs⟩ := h
  have hone : ρ ONE = lit 1 0 0 0 := by have := ho (.one ONE) (by simp); simpa [Op.holds] using this
  exact ⟨flag_sound f1 (by decide) (by decide) hH h0 (hb 1 (by norm_num) le_rfl) hone,
    flag_sound f2 (by decide) (by decide) hH h0 (hb 2 (by norm_num) (by norm_num)) hone,
    flag_sound f3 (by decide) (by decide) hH h0 (hb 3 (by norm_num) (by norm_num)) hone,
    sub_sound hs hH h0 hone⟩

def ctxJson : String :=
  let ops := [Op.hook 0 [] (List.range 6)] ++ ctxOps
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[]}"

end StarkedAir.Circuit.BlockCtx
