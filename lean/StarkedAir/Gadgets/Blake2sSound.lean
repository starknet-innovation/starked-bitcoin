/-
Soundness of the Blake2s compression AIR (`Gadgets/Blake2s.lean`) against RFC 7693
(`Spec/Blake2s.lean`). Layers: row facts (booleans, words, message limbs); one G row computes
`mix`; the period's init, half-round and final layouts; the compression.
-/
import StarkedAir.Gadgets.Blake2s
import StarkedAir.Gadgets.Sha256Sound

namespace StarkedAir.Blake2s

open StarkedAir
open StarkedAir.Sha256 (bit word eq_bit eval_col eval_cst eval_bitcol eval_limb half16 half16_lt half16_split
  addC_nat eval_bitsOf eval_col0_val eval_xor2 rotr_getLsbD wrap_back word_getLsbD)

abbrev Word := Spec.Blake2s.Word

/-- Every Blake2s compression constraint holds on every row. -/
def BlakeSat (n : ℕ) (pc : List PreCol) (pub : ℕ → F) (main : ℕ → ℕ → F) : Prop :=
  ∀ r < n, ∀ c ∈ constraints, c.eval n pc pub main r = 0

/-! ## Constraint families -/

theorem mem_booleans {c : Expr} (h : c ∈ booleans) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_gFirst {g : ℕ} (hg : g < 8) {c : Expr} (h : c ∈ gFirst g) : c ∈ constraints := by
  simp only [constraints, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨g, hg, h⟩))))
theorem mem_gSecond {c : Expr} (h : c ∈ gSecond) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_init {c : Expr} (h : c ∈ init) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_final {c : Expr} (h : c ∈ final) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto
theorem mem_copy {c : Expr} (h : c ∈ copy) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; tauto

/-! ## Row facts -/

section Row

variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : BlakeSat n pc pub main)
include hsat

theorem bool_val {c r : ℕ} (hr : r < n) (hc : c < 256 ∨ (288 ≤ c ∧ c < 300)) : (main c r).val ≤ 1 := by
  have hm : boolC (col c) ∈ booleans := by
    simp only [booleans, List.mem_map, List.mem_append, List.mem_range, Function.comp]
    rcases hc with hc | ⟨h1, h2⟩
    · exact ⟨c, Or.inl hc, rfl⟩
    · exact ⟨c, Or.inr ⟨c - 288, by omega, by simp only [CA1_LO]; omega⟩, rfl⟩
  have := hsat r hr _ (mem_booleans hm)
  simp only [boolC, Expr.eval, eval_col, eval_cst, wrap_zero hr, Nat.cast_one] at this
  exact val_le_one_of_bool this

theorem word_bits {w r : ℕ} (hr : r < n) (hw : w < 8) : ∀ i < 32, (main (32 * w + i) r).val ≤ 1 :=
  fun i hi => bool_val hsat hr (Or.inl (by omega))

end Row

/-! ## Message limbs -/

/-- The word of message slot `k` at row `r` (from its two 16-bit limbs). -/
def msgWord (main : ℕ → ℕ → F) (k r : ℕ) : Word :=
  BitVec.ofNat 32 ((main (ML k 0) r).val + 65536 * (main (ML k 1) r).val)

theorem eval_msgLimb {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r base κ : ℕ}
    (hr : r < n) (hκ : κ < 16)
    (hsel : ∀ k < 16, (pre (base + k)).eval n pc pub main r = if k = κ then 1 else 0) (h : ℕ) :
    (msgLimb base h).eval n pc pub main r = main (ML κ h) r := by
  have key : ∀ m ≤ 16, ((List.range m).foldl (fun acc k => Expr.add acc (.mul (pre (base + k)) (col (ML k h))))
      (cst 0)).eval n pc pub main r = if κ < m then main (ML κ h) r else 0 := by
    intro m hm
    induction m with
    | zero => simp [eval_cst]
    | succ m ih =>
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      simp only [Expr.eval]
      rw [ih (by omega), hsel m (by omega), eval_col, wrap_zero hr]
      by_cases hmk : m = κ
      · subst hmk; simp
      · by_cases hk : κ < m
        · simp [hmk, hk, show κ < m + 1 by omega]
        · simp [hmk, hk, show ¬ κ < m + 1 by omega]
  unfold msgLimb
  rw [key 16 le_rfl, if_pos hκ]

/-! ## Bitwise -/

section Bits

variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ}

theorem eval_rotXor {wx wy rx ry rr : ℕ} {ox oy : ℤ} (hwx : wrap n r ox = rx) (hwy : wrap n r oy = ry)
    (hbx : ∀ i < 32, (main (32 * wx + i) rx).val ≤ 1) (hby : ∀ i < 32, (main (32 * wy + i) ry).val ≤ 1)
    (hrr : rr < 32) {i : ℕ} (hi : i < 32) :
    (rotXor wx ox wy oy rr i).eval n pc pub main r =
      ((((word main (32 * wx) rx ^^^ word main (32 * wy) ry).rotateRight rr).getLsbD i).toNat : F) := by
  unfold rotXor
  rw [eval_xor2 (eval_bitcol hwx hbx (Nat.mod_lt _ (by norm_num))) (eval_bitcol hwy hby (Nat.mod_lt _ (by norm_num)))]
  simp [rotr_getLsbD _ hrr hi, BitVec.getLsbD_xor]

/-- `bitsEq sel w val` with the gate on and `val` the bits of `Y` pins word slot `w` to `Y`. -/
theorem bitsEq_word {sel : Expr} {w : ℕ} {val : ℕ → Expr} {Y : Word} (hr : r < n)
    (hall : ∀ c ∈ bitsEq sel w val, c.eval n pc pub main r = 0) (hsel : sel.eval n pc pub main r = 1)
    (hbits : ∀ i < 32, (main (32 * w + i) r).val ≤ 1)
    (hval : ∀ i < 32, (val i).eval n pc pub main r = ((Y.getLsbD i).toNat : F)) :
    word main (32 * w) r = Y := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hc := hall _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simp only [Expr.eval, hsel, one_mul, sub_eq_zero, hval i hi] at hc
  rw [eval_col, wrap_zero hr, eq_bit (hbits i hi)] at hc
  rw [word_getLsbD _ _ hi]
  have := congrArg ZMod.val hc
  cases hb : bit main (32 * w + i) r <;> cases hy : Y.getLsbD i <;> simp_all

end Bits

/-! ## Additions -/

section Adds

variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : BlakeSat n pc pub main)
include hsat

theorem limb_at {r w k : ℕ} (hr : r < n) (hk : k ≤ r) (hw : w < 8) {h : ℕ} (hh : h ≤ 1) :
    (limb w h (-(k : ℤ))).eval n pc pub main r = ((half16 (word main (32 * w) (r - k)) h : ℕ) : F) :=
  eval_limb (wrap_back hk hr) (word_bits hsat (by omega) hw) hh

theorem limb_here {r w : ℕ} (hr : r < n) (hw : w < 8) {h : ℕ} (hh : h ≤ 1) :
    (limb w h).eval n pc pub main r = ((half16 (word main (32 * w) r) h : ℕ) : F) := by
  have := limb_at hsat hr (k := 0) (Nat.zero_le _) hw hh
  simpa using this

theorem carry_at {r base k : ℕ} (hr : r < n) (hb : 288 ≤ base) (hk : base + k ≤ 300) :
    (bitsOf base k).eval n pc pub main r = ((ofBits (fun j => bit main (base + j) r) k : ℕ) : F) :=
  eval_bitsOf hr (fun j hj => bool_val hsat (c := base + j) hr (Or.inr ⟨by omega, by omega⟩))

end Adds

/-- Two limb equations with carries give a word addition mod 2³². -/
theorem add_words {R X Y Z : Word} {zl zh cl ch : ℕ}
    (hl : half16 X 0 + half16 Y 0 + zl = half16 R 0 + 65536 * cl)
    (hh : half16 X 1 + half16 Y 1 + zh + cl = half16 R 1 + 65536 * ch)
    (hz : Z.toNat = zl + 65536 * zh) (hzl : zl < 65536) : R = X + Y + Z := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add]
  rw [half16_split R, half16_split X, half16_split Y, hz]
  have := half16_lt R 0; have := half16_lt R 1; have := half16_lt X 0; have := half16_lt X 1
  have := half16_lt Y 0; have := half16_lt Y 1
  omega

theorem add2_words {R X Y : Word} {cl ch : ℕ}
    (hl : half16 X 0 + half16 Y 0 = half16 R 0 + 65536 * cl)
    (hh : half16 X 1 + half16 Y 1 + cl = half16 R 1 + 65536 * ch) : R = X + Y := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add]
  rw [half16_split R, half16_split X, half16_split Y]
  have := half16_lt R 0; have := half16_lt R 1; have := half16_lt X 0; have := half16_lt X 1
  have := half16_lt Y 0; have := half16_lt Y 1
  omega

theorem msgWord_toNat {main : ℕ → ℕ → F} {k r : ℕ} (h0 : (main (ML k 0) r).val < 65536)
    (h1 : (main (ML k 1) r).val < 65536) :
    (msgWord main k r).toNat = (main (ML k 0) r).val + 65536 * (main (ML k 1) r).val := by
  unfold msgWord; rw [BitVec.toNat_ofNat]; omega

/-! ## One G row -/

section GStep

variable {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : BlakeSat n pc pub main)
include hsat

/-- **G step.** At a row of G position `g` (whose message selectors pick words `κx`, `κy`), the
row's output words are `mix` of the inputs read at the distances `src g`. -/
theorem g_step {r g κx κy : ℕ} (hr : r < n) (hsr : ∀ role, src g role ≤ r) (hg : g < 8)
    (hG : (pre (P_G g)).eval n pc pub main r = 1) (hI : (pre P_ISG).eval n pc pub main r = 1)
    (hx : ∀ k < 16, (pre (P_XSEL 0 + k)).eval n pc pub main r = if k = κx then 1 else 0) (hκx : κx < 16)
    (hy : ∀ k < 16, (pre (P_YSEL 0 + k)).eval n pc pub main r = if k = κy then 1 else 0) (hκy : κy < 16)
    (hm : ∀ k < 16, ∀ h ≤ 1, (main (ML k h) r).val < 65536) :
    Spec.Blake2s.mix (word main (32 * 4) (r - src g 0)) (word main (32 * 7) (r - src g 1))
        (word main (32 * 6) (r - src g 2)) (word main (32 * 5) (r - src g 3))
        (msgWord main κx r) (msgWord main κy r) =
      (word main (32 * 4) r, word main (32 * 7) r, word main (32 * 6) r, word main (32 * 5) r) := by
  -- Inputs and current-row words.
  set A := word main (32 * 4) (r - src g 0)
  set B := word main (32 * 7) (r - src g 1)
  set C := word main (32 * 6) (r - src g 2)
  set D := word main (32 * 5) (r - src g 3)
  set X := msgWord main κx r
  set Y := msgWord main κy r
  have LA := fun h (hh : h ≤ 1) => limb_at hsat hr (k := src g 0) (hsr 0) (w := 4) (by norm_num) hh
  have LB := fun h (hh : h ≤ 1) => limb_at hsat hr (k := src g 1) (hsr 1) (w := 7) (by norm_num) hh
  have LC := fun h (hh : h ≤ 1) => limb_at hsat hr (k := src g 2) (hsr 2) (w := 6) (by norm_num) hh
  have L := fun w (hw : w < 8) h (hh : h ≤ 1) => limb_here hsat hr (w := w) hw (h := h) hh
  have MX := fun h => eval_msgLimb (n := n) (pc := pc) (pub := pub) (main := main) hr hκx hx h
  have MY := fun h => eval_msgLimb (n := n) (pc := pc) (pub := pub) (main := main) hr hκy hy h
  have cv := fun i => (ZMod.natCast_zmod_val (main i r)).symm
  have bc := fun base k => ofBits_lt (fun j => bit main (base + j) r) k
  have hb := fun (y : Word) h => half16_lt y h
  have hP : (2 : ℕ) ^ 20 < P := by norm_num [P]
  -- First half.
  have h1 : ∀ c ∈ gFirst g, c.eval n pc pub main r = 0 := fun c hc => hsat r hr c (mem_gFirst hg hc)
  have h2 : ∀ c ∈ gSecond, c.eval n pc pub main r = 0 := fun c hc => hsat r hr c (mem_gSecond hc)
  unfold gFirst at h1
  unfold gSecond at h2
  simp only [outW, srcOff, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
  have eA0 := h1 _ (Or.inl (Or.inl (Or.inl rfl)))
  have eA1 := h1 _ (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
  have eC0 := h1 _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
  have eC1 := h1 _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))
  have eD := fun c hc => h1 c (Or.inl (Or.inr hc))
  have eB := fun c hc => h1 c (Or.inr hc)
  have fA0 := h2 _ (Or.inl (Or.inl (Or.inl rfl)))
  have fA1 := h2 _ (Or.inl (Or.inl (Or.inr (Or.inl rfl))))
  have fC0 := h2 _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inl rfl)))))
  have fC1 := h2 _ (Or.inl (Or.inl (Or.inr (Or.inr (Or.inr rfl)))))
  have fD := fun c hc => h2 c (Or.inl (Or.inr hc))
  have fB := fun c hc => h2 c (Or.inr hc)
  have xv := fun h (hh : h ≤ 1) => (ZMod.natCast_zmod_val (main (ML κx h) r)).symm
  have yv := fun h (hh : h ≤ 1) => (ZMod.natCast_zmod_val (main (ML κy h) r)).symm
  set W0 := word main (32 * 0) r
  set W1 := word main (32 * 1) r
  set W2 := word main (32 * 2) r
  set W3 := word main (32 * 3) r
  set W4 := word main (32 * 4) r
  set W5 := word main (32 * 5) r
  set W6 := word main (32 * 6) r
  set W7 := word main (32 * 7) r
  -- a₁ = a + b + x
  set c1l := ofBits (fun j => bit main (CA1_LO + j) r) 2
  set c1h := ofBits (fun j => bit main (CA1_HI + j) r) 2
  have n0 := addC_nat eA0 hG (ts := [half16 A 0, half16 B 0, (main (ML κx 0) r).val])
    (by simp only [List.map_cons, List.map_nil, LA 0 (by norm_num), LB 0 (by norm_num), MX 0, ZMod.natCast_zmod_val]; rfl)
    (L 0 (by norm_num) 0 (by norm_num)) (carry_at hsat hr (by decide) (by decide))
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb A 0, hb B 0, hm κx hκx 0 (by norm_num)])
    (by linarith [hb W0 0, bc CA1_LO 2])
  have n1 := addC_nat eA1 hG (ts := [half16 A 1, half16 B 1, (main (ML κx 1) r).val, c1l])
    (by simp only [List.map_cons, List.map_nil, LA 1 (by norm_num), LB 1 (by norm_num), MX 1, ZMod.natCast_zmod_val,
          carry_at hsat hr (base := CA1_LO) (k := 2) (by decide) (by decide)]; rfl)
    (L 0 (by norm_num) 1 (by norm_num)) (carry_at hsat hr (by decide) (by decide))
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb A 1, hb B 1, hm κx hκx 1 (by norm_num), bc CA1_LO 2])
    (by linarith [hb W0 1, bc CA1_HI 2])
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at n0 n1
  replace n0 : half16 A 0 + (half16 B 0 + (main (ML κx 0) r).val) = half16 W0 0 + 65536 * c1l := n0
  replace n1 : half16 A 1 + (half16 B 1 + ((main (ML κx 1) r).val + c1l)) = half16 W0 1 + 65536 * c1h := n1
  have hW0 : W0 = A + B + X := add_words (zl := (main (ML κx 0) r).val) (zh := (main (ML κx 1) r).val)
    (cl := c1l) (ch := c1h) (by omega) (by omega) (msgWord_toNat (hm κx hκx 0 (by norm_num)) (hm κx hκx 1 (by norm_num)))
    (hm κx hκx 0 (by norm_num))
  -- d₁ = (d ⊕ a₁) ⋙ 16
  have hW1 : W1 = (D ^^^ W0).rotateRight 16 :=
    bitsEq_word hr eD hG (word_bits hsat hr (w := 1) (by norm_num)) (fun i hi =>
      eval_rotXor (wrap_back (k := src g 3) (hsr 3) hr) (wrap_zero hr)
        (word_bits hsat (by omega) (w := 5) (by norm_num)) (word_bits hsat hr (w := 0) (by norm_num)) (by norm_num) hi)
  have cc := fun i (hi : 288 ≤ i ∧ i < 300) => bool_val hsat hr (c := i) (Or.inr hi)
  have c0 := fun i => eval_col0_val (n := n) (pc := pc) (pub := pub) (main := main) (i := i) hr
  -- c₁ = c + d₁
  have m0 := addC_nat eC0 hG (ts := [half16 C 0, half16 W1 0])
    (by simp only [List.map_cons, List.map_nil, LC 0 (by norm_num), L 1 (by norm_num) 0 (by norm_num)]; rfl)
    (L 2 (by norm_num) 0 (by norm_num)) (c0 CC1_LO)
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb C 0, hb W1 0])
    (by linarith [hb W2 0, cc CC1_LO (by decide)])
  have m1 := addC_nat eC1 hG (ts := [half16 C 1, half16 W1 1, (main CC1_LO r).val])
    (by simp only [List.map_cons, List.map_nil, LC 1 (by norm_num), L 1 (by norm_num) 1 (by norm_num), c0]; rfl)
    (L 2 (by norm_num) 1 (by norm_num)) (c0 CC1_HI)
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb C 1, hb W1 1, cc CC1_LO (by decide)])
    (by linarith [hb W2 1, cc CC1_HI (by decide)])
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at m0 m1
  replace m0 : half16 C 0 + half16 W1 0 = half16 W2 0 + 65536 * (main CC1_LO r).val := m0
  replace m1 : half16 C 1 + (half16 W1 1 + (main CC1_LO r).val) = half16 W2 1 + 65536 * (main CC1_HI r).val := m1
  have hW2 : W2 = C + W1 := add2_words (cl := (main CC1_LO r).val) (ch := (main CC1_HI r).val) (by omega) (by omega)
  -- b₁ = (b ⊕ c₁) ⋙ 12
  have hW3 : W3 = (B ^^^ W2).rotateRight 12 :=
    bitsEq_word hr eB hG (word_bits hsat hr (w := 3) (by norm_num)) (fun i hi =>
      eval_rotXor (wrap_back (k := src g 1) (hsr 1) hr) (wrap_zero hr)
        (word_bits hsat (by omega) (w := 7) (by norm_num)) (word_bits hsat hr (w := 2) (by norm_num)) (by norm_num) hi)
  -- a₂ = a₁ + b₁ + y
  set c2l := ofBits (fun j => bit main (CA2_LO + j) r) 2
  set c2h := ofBits (fun j => bit main (CA2_HI + j) r) 2
  have p0 := addC_nat fA0 hI (ts := [half16 W0 0, half16 W3 0, (main (ML κy 0) r).val])
    (by simp only [List.map_cons, List.map_nil, L 0 (by norm_num) 0 (by norm_num), L 3 (by norm_num) 0 (by norm_num),
          MY 0, ZMod.natCast_zmod_val]; rfl)
    (L 4 (by norm_num) 0 (by norm_num)) (carry_at hsat hr (by decide) (by decide))
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb W0 0, hb W3 0, hm κy hκy 0 (by norm_num)])
    (by linarith [hb W4 0, bc CA2_LO 2])
  have p1 := addC_nat fA1 hI (ts := [half16 W0 1, half16 W3 1, (main (ML κy 1) r).val, c2l])
    (by simp only [List.map_cons, List.map_nil, L 0 (by norm_num) 1 (by norm_num), L 3 (by norm_num) 1 (by norm_num),
          MY 1, ZMod.natCast_zmod_val, carry_at hsat hr (base := CA2_LO) (k := 2) (by decide) (by decide)]; rfl)
    (L 4 (by norm_num) 1 (by norm_num)) (carry_at hsat hr (by decide) (by decide))
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb W0 1, hb W3 1, hm κy hκy 1 (by norm_num), bc CA2_LO 2])
    (by linarith [hb W4 1, bc CA2_HI 2])
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at p0 p1
  replace p0 : half16 W0 0 + (half16 W3 0 + (main (ML κy 0) r).val) = half16 W4 0 + 65536 * c2l := p0
  replace p1 : half16 W0 1 + (half16 W3 1 + ((main (ML κy 1) r).val + c2l)) = half16 W4 1 + 65536 * c2h := p1
  have hW4 : W4 = W0 + W3 + Y := add_words (zl := (main (ML κy 0) r).val) (zh := (main (ML κy 1) r).val)
    (cl := c2l) (ch := c2h) (by omega) (by omega) (msgWord_toNat (hm κy hκy 0 (by norm_num)) (hm κy hκy 1 (by norm_num)))
    (hm κy hκy 0 (by norm_num))
  -- d₂ = (d₁ ⊕ a₂) ⋙ 8
  have hW5 : W5 = (W1 ^^^ W4).rotateRight 8 :=
    bitsEq_word hr fD hI (word_bits hsat hr (w := 5) (by norm_num)) (fun i hi =>
      eval_rotXor (wrap_zero hr) (wrap_zero hr)
        (word_bits hsat hr (w := 1) (by norm_num)) (word_bits hsat hr (w := 4) (by norm_num)) (by norm_num) hi)
  -- c₂ = c₁ + d₂
  have q0 := addC_nat fC0 hI (ts := [half16 W2 0, half16 W5 0])
    (by simp only [List.map_cons, List.map_nil, L 2 (by norm_num) 0 (by norm_num), L 5 (by norm_num) 0 (by norm_num)]; rfl)
    (L 6 (by norm_num) 0 (by norm_num)) (c0 CC2_LO)
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb W2 0, hb W5 0])
    (by linarith [hb W6 0, cc CC2_LO (by decide)])
  have q1 := addC_nat fC1 hI (ts := [half16 W2 1, half16 W5 1, (main CC2_LO r).val])
    (by simp only [List.map_cons, List.map_nil, L 2 (by norm_num) 1 (by norm_num), L 5 (by norm_num) 1 (by norm_num), c0]; rfl)
    (L 6 (by norm_num) 1 (by norm_num)) (c0 CC2_HI)
    (by simp only [List.sum_cons, List.sum_nil]; linarith [hb W2 1, hb W5 1, cc CC2_LO (by decide)])
    (by linarith [hb W6 1, cc CC2_HI (by decide)])
  simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at q0 q1
  replace q0 : half16 W2 0 + half16 W5 0 = half16 W6 0 + 65536 * (main CC2_LO r).val := q0
  replace q1 : half16 W2 1 + (half16 W5 1 + (main CC2_LO r).val) = half16 W6 1 + 65536 * (main CC2_HI r).val := q1
  have hW6 : W6 = W2 + W5 := add2_words (cl := (main CC2_LO r).val) (ch := (main CC2_HI r).val) (by omega) (by omega)
  -- b₂ = (b₁ ⊕ c₂) ⋙ 7
  have hW7 : W7 = (W3 ^^^ W6).rotateRight 7 :=
    bitsEq_word hr fB hI (word_bits hsat hr (w := 7) (by norm_num)) (fun i hi =>
      eval_rotXor (wrap_zero hr) (wrap_zero hr)
        (word_bits hsat hr (w := 3) (by norm_num)) (word_bits hsat hr (w := 6) (by norm_num)) (by norm_num) hi)
  simp only [Spec.Blake2s.mix]
  rw [hW7, hW6, hW5, hW4, hW3, hW2, hW1, hW0]

end GStep

/-! ## Layouts and half-rounds -/

/-- The output word of `role` at `row`. -/
def rw4 (main : ℕ → ℕ → F) (row role : ℕ) : Word := word main (32 * outW role) row

/-- A G row's facts, as `g_step` gives them. -/
def GOK (main : ℕ → ℕ → F) (r g : ℕ) (X Y : Word) : Prop :=
  Spec.Blake2s.mix (rw4 main (r - src g 0) 0) (rw4 main (r - src g 1) 1) (rw4 main (r - src g 2) 2)
    (rw4 main (r - src g 3) 3) X Y = (rw4 main r 0, rw4 main r 1, rw4 main r 2, rw4 main r 3)

/-- Slot `i` of the state held by four diagonal rows `b … b+3` (row `k` holds `gIdx (4+k)`). -/
def diagSlot (main : ℕ → ℕ → F) (b : ℕ) : ℕ → Word
  | 0 => rw4 main b 0 | 1 => rw4 main (b + 1) 0 | 2 => rw4 main (b + 2) 0 | 3 => rw4 main (b + 3) 0
  | 4 => rw4 main (b + 3) 1 | 5 => rw4 main b 1 | 6 => rw4 main (b + 1) 1 | 7 => rw4 main (b + 2) 1
  | 8 => rw4 main (b + 2) 2 | 9 => rw4 main (b + 3) 2 | 10 => rw4 main b 2 | 11 => rw4 main (b + 1) 2
  | 12 => rw4 main (b + 1) 3 | 13 => rw4 main (b + 2) 3 | 14 => rw4 main (b + 3) 3 | _ => rw4 main b 3

/-- Slot `i` of the state held by four column rows `b … b+3` (row `g` holds `gIdx g`). -/
def colSlot (main : ℕ → ℕ → F) (b i : ℕ) : Word := rw4 main (b + i % 4) (i / 4)

theorem getD_set (v : List Word) (i j : ℕ) (x : Word) (hi : i < v.length) :
    (v.set i x).getD j 0 = if i = j then x else v.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_set]
  split_ifs <;> simp_all

theorem gStep_length (m : ℕ → Word) (v : List Word) (ρ g : ℕ) : (Spec.Blake2s.gStep m v ρ g).length = v.length := by
  simp [Spec.Blake2s.gStep]

/-- **Column half-round.** From the diagonal layout of rows `b … b+3`, G positions 0–3 (rows
`b+4 … b+7`) produce the column layout of rows `b+4 … b+7`. -/
theorem col_half {main : ℕ → ℕ → F} {m : ℕ → Word} {v : List Word} {b ρ : ℕ} (hlen : v.length = 16)
    (hv : ∀ i < 16, v.getD i 0 = diagSlot main b i)
    (hG : ∀ g < 4, GOK main (b + 4 + g) g (m (Spec.Blake2s.sigma ρ (2 * g))) (m (Spec.Blake2s.sigma ρ (2 * g + 1)))) :
    ∀ i < 16, (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m v ρ 0) ρ 1) ρ 2) ρ 3).getD i 0 =
      colSlot main (b + 4) i := by
  have G0 := hG 0 (by norm_num)
  have G1 := hG 1 (by norm_num)
  have G2 := hG 2 (by norm_num)
  have G3 := hG 3 (by norm_num)
  simp only [GOK, src, show b + 4 + 0 - 4 = b by omega, show b + 4 + 0 - 1 = b + 3 by omega,
    show b + 4 + 0 - 2 = b + 2 by omega, show b + 4 + 0 - 3 = b + 1 by omega, show b + 4 + 1 - 4 = b + 1 by omega,
    show b + 4 + 1 - 5 = b by omega, show b + 4 + 1 - 2 = b + 3 by omega, show b + 4 + 1 - 3 = b + 2 by omega,
    show b + 4 + 2 - 4 = b + 2 by omega, show b + 4 + 2 - 5 = b + 1 by omega, show b + 4 + 2 - 6 = b by omega,
    show b + 4 + 2 - 3 = b + 3 by omega, show b + 4 + 3 - 4 = b + 3 by omega, show b + 4 + 3 - 5 = b + 2 by omega,
    show b + 4 + 3 - 6 = b + 1 by omega, show b + 4 + 3 - 7 = b by omega, Nat.add_zero, Nat.mul_zero, Nat.mul_one] at G0 G1 G2 G3
  norm_num at G0 G1 G2 G3
  have hvl : v = (List.range 16).map (diagSlot main b) := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    have := hv i (by omega)
    rw [List.getD_eq_getElem _ _ h1] at this
    simpa using this
  subst hvl
  intro i hi
  interval_cases i <;>
    simp [Spec.Blake2s.gStep, Spec.Blake2s.gIdx, List.range_succ, diagSlot, colSlot, G0, G1, G2, G3]

/-- **Diagonal half-round.** From the column layout of rows `b … b+3`, G positions 4–7 (rows
`b+4 … b+7`) produce the diagonal layout of rows `b+4 … b+7`. -/
theorem diag_half {main : ℕ → ℕ → F} {m : ℕ → Word} {v : List Word} {b ρ : ℕ} (hlen : v.length = 16)
    (hv : ∀ i < 16, v.getD i 0 = colSlot main b i)
    (hG : ∀ k < 4, GOK main (b + 4 + k) (4 + k) (m (Spec.Blake2s.sigma ρ (2 * (4 + k))))
      (m (Spec.Blake2s.sigma ρ (2 * (4 + k) + 1)))) :
    ∀ i < 16, (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m v ρ 4) ρ 5) ρ 6) ρ 7).getD i 0 =
      diagSlot main (b + 4) i := by
  have G0 := hG 0 (by norm_num)
  have G1 := hG 1 (by norm_num)
  have G2 := hG 2 (by norm_num)
  have G3 := hG 3 (by norm_num)
  simp only [GOK, src, Nat.add_zero] at G0 G1 G2 G3
  simp only [show b + 4 - 4 = b by omega, show b + 4 - 3 = b + 1 by omega, show b + 4 - 2 = b + 2 by omega,
    show b + 4 - 1 = b + 3 by omega, show b + 4 + 1 - 4 = b + 1 by omega, show b + 4 + 1 - 3 = b + 2 by omega,
    show b + 4 + 1 - 2 = b + 3 by omega, show b + 4 + 1 - 5 = b by omega, show b + 4 + 2 - 4 = b + 2 by omega,
    show b + 4 + 2 - 3 = b + 3 by omega, show b + 4 + 2 - 6 = b by omega, show b + 4 + 2 - 5 = b + 1 by omega,
    show b + 4 + 3 - 4 = b + 3 by omega, show b + 4 + 3 - 7 = b by omega, show b + 4 + 3 - 6 = b + 1 by omega,
    show b + 4 + 3 - 5 = b + 2 by omega] at G0 G1 G2 G3
  norm_num at G0 G1 G2 G3
  have hvl : v = (List.range 16).map (colSlot main b) := by
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    have := hv i (by omega)
    rw [List.getD_eq_getElem _ _ h1] at this
    simpa using this
  subst hvl
  intro i hi
  interval_cases i <;>
    simp [Spec.Blake2s.gStep, Spec.Blake2s.gIdx, List.range_succ, diagSlot, colSlot, G0, G1, G2, G3]

theorem steps_succ' (m : ℕ → Word) (v0 : List Word) (ρ j : ℕ) (hj : j < 8) :
    Spec.Blake2s.steps m v0 (8 * ρ + j + 1) = Spec.Blake2s.gStep m (Spec.Blake2s.steps m v0 (8 * ρ + j)) ρ j := by
  show Spec.Blake2s.gStep m _ ((8 * ρ + j) / 8) ((8 * ρ + j) % 8) = _
  rw [show (8 * ρ + j) / 8 = ρ by omega, show (8 * ρ + j) % 8 = j by omega]

theorem steps_length (m : ℕ → Word) (v0 : List Word) : ∀ k, (Spec.Blake2s.steps m v0 k).length = v0.length
  | 0 => rfl
  | k + 1 => by rw [Spec.Blake2s.steps, gStep_length, steps_length m v0 k]

/-- **Rounds.** If the initial state is the diagonal layout of rows `s … s+3` and every G row of
the period satisfies `GOK`, then after `ρ` rounds the state is the diagonal layout of rows
`s + 8ρ … s + 8ρ + 3`. -/
theorem steps_rounds {main : ℕ → ℕ → F} {m : ℕ → Word} {v0 : List Word} {s : ℕ} (hlen : v0.length = 16)
    (hv0 : ∀ i < 16, v0.getD i 0 = diagSlot main s i)
    (hG : ∀ ρ < 10, ∀ g < 8, GOK main (s + 4 + 8 * ρ + g) g (m (Spec.Blake2s.sigma ρ (2 * g)))
      (m (Spec.Blake2s.sigma ρ (2 * g + 1)))) :
    ∀ ρ ≤ 10, ∀ i < 16, (Spec.Blake2s.steps m v0 (8 * ρ)).getD i 0 = diagSlot main (s + 8 * ρ) i := by
  intro ρ hρ
  induction ρ with
  | zero => intro i hi; simpa [Spec.Blake2s.steps] using hv0 i hi
  | succ ρ ih =>
    have hprev := ih (by omega)
    have l0 : (Spec.Blake2s.steps m v0 (8 * ρ)).length = 16 := by rw [steps_length, hlen]
    have half1 := col_half (b := s + 8 * ρ) (ρ := ρ) l0 hprev (fun g hg => by
      have := hG ρ (by omega) g (by omega)
      rwa [show s + 4 + 8 * ρ + g = s + 8 * ρ + 4 + g by ring] at this)
    have e4 : Spec.Blake2s.steps m v0 (8 * ρ + 4) =
        Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m
          (Spec.Blake2s.steps m v0 (8 * ρ)) ρ 0) ρ 1) ρ 2) ρ 3 := by
      rw [show 8 * ρ + 4 = 8 * ρ + 3 + 1 by ring, steps_succ' m v0 ρ 3 (by norm_num),
        show 8 * ρ + 3 = 8 * ρ + 2 + 1 by ring, steps_succ' m v0 ρ 2 (by norm_num),
        show 8 * ρ + 2 = 8 * ρ + 1 + 1 by ring, steps_succ' m v0 ρ 1 (by norm_num)]
      have := steps_succ' m v0 ρ 0 (by norm_num)
      rw [Nat.add_zero] at this
      rw [this, Nat.add_zero]
    rw [← e4] at half1
    have l4 : (Spec.Blake2s.steps m v0 (8 * ρ + 4)).length = 16 := by rw [steps_length, hlen]
    have half2 := diag_half (b := s + 8 * ρ + 4) (ρ := ρ) l4 half1 (fun k hk => by
      have := hG ρ (by omega) (4 + k) (by omega)
      rwa [show s + 4 + 8 * ρ + (4 + k) = s + 8 * ρ + 4 + 4 + k by ring] at this)
    have e8 : Spec.Blake2s.steps m v0 (8 * (ρ + 1)) =
        Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m (Spec.Blake2s.gStep m
          (Spec.Blake2s.steps m v0 (8 * ρ + 4)) ρ 4) ρ 5) ρ 6) ρ 7 := by
      rw [show 8 * (ρ + 1) = 8 * ρ + 7 + 1 by ring, steps_succ' m v0 ρ 7 (by norm_num),
        show 8 * ρ + 7 = 8 * ρ + 6 + 1 by ring, steps_succ' m v0 ρ 6 (by norm_num),
        show 8 * ρ + 6 = 8 * ρ + 5 + 1 by ring, steps_succ' m v0 ρ 5 (by norm_num),
        show 8 * ρ + 5 = 8 * ρ + 4 + 1 by ring, steps_succ' m v0 ρ 4 (by norm_num)]
    intro i hi
    rw [e8, half2 i hi, show s + 8 * ρ + 4 + 4 = s + 8 * (ρ + 1) by ring]

/-! ## Preprocessed values at aligned rows -/

/-- Preprocessed column `i` at row `p` of a period. -/
def bPre (i p : ℕ) : F := (preCols.getD i (.periodic [0])).eval PERIOD p

theorem ind_eval (q : ℕ → Bool) {p : ℕ} (hp : p < PERIOD) :
    (PreCol.periodic ((List.range PERIOD).map fun r => if q r then 1 else 0)).eval PERIOD p =
      if q p then 1 else 0 := by
  simp only [PreCol.eval, List.length_map, List.length_range, Nat.mod_eq_of_lt hp]
  rw [List.getD_eq_getElem _ _ (by simpa using hp)]
  simp only [List.getElem_map, List.getElem_range]
  split <;> simp

theorem preCols_getD {i : ℕ} (hi : i < 50) :
    preCols.getD i (.periodic [0]) = .periodic ((List.range PERIOD).map fun r => if preQ i r then 1 else 0) := by
  unfold preCols
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

theorem bPre_eq {i p : ℕ} (hi : i < 50) (hp : p < PERIOD) : bPre i p = if preQ i p then 1 else 0 := by
  unfold bPre; rw [preCols_getD hi, ind_eval _ hp]

/-- At an aligned row `s + p`, a preprocessed column takes its period value. -/
theorem pre_at {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} {s p i : ℕ} (hs : s % PERIOD = 0) (hp : p < PERIOD)
    (hn : s + p < n) (hi : i < 50) : (pre i).eval n preCols pub main (s + p) = bPre i p := by
  simp only [pre, Expr.eval, wrap_zero hn, bPre, preCols_getD hi, PreCol.eval, List.length_map, List.length_range]
  rw [show (s + p) % PERIOD = p % PERIOD by simp only [PERIOD] at hs ⊢; omega]

theorem bPre_G {g j : ℕ} (hg : g < 8) (hj : j < 80) : bPre (P_G g) (4 + j) = if j % 8 = g then 1 else 0 := by
  rw [bPre_eq (by simp [P_G]; omega) (by simp [PERIOD]; omega)]
  simp only [preQ, P_G]
  by_cases h : j % 8 = g <;> simp [h, show ¬ 4 + g < 4 by omega, show 4 + g < 12 by omega, show 4 + j < 84 by omega] <;> omega

theorem bPre_ISG {j : ℕ} (hj : j < 80) : bPre P_ISG (4 + j) = 1 := by
  rw [bPre_eq (by simp [P_ISG]) (by simp [PERIOD]; omega)]
  simp [preQ, P_ISG, show 4 + j < 84 by omega]

theorem bPre_X {k j : ℕ} (hk : k < 16) (hj : j < 80) :
    bPre (P_XSEL 0 + k) (4 + j) = if k = Spec.Blake2s.sigma (j / 8) (2 * (j % 8)) then 1 else 0 := by
  rw [bPre_eq (by simp [P_XSEL]; omega) (by simp [PERIOD]; omega), show P_XSEL 0 + k = 17 + k by simp [P_XSEL]]
  have hq : preQ (17 + k) (4 + j) = (Spec.Blake2s.sigma (j / 8) (2 * (j % 8)) == k) := by
    simp only [preQ]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp [show 4 ≤ 4 + j from by omega, show 4 + j < 84 from by omega]
  simp only [hq, beq_iff_eq]
  by_cases h : k = Spec.Blake2s.sigma (j / 8) (2 * (j % 8))
  · simp [h]
  · simp [h, Ne.symm h]

theorem bPre_Y {k j : ℕ} (hk : k < 16) (hj : j < 80) :
    bPre (P_YSEL 0 + k) (4 + j) = if k = Spec.Blake2s.sigma (j / 8) (2 * (j % 8) + 1) then 1 else 0 := by
  rw [bPre_eq (by simp [P_YSEL]; omega) (by simp [PERIOD]; omega), show P_YSEL 0 + k = 33 + k by simp [P_YSEL]]
  have hq : preQ (33 + k) (4 + j) = (Spec.Blake2s.sigma (j / 8) (2 * (j % 8) + 1) == k) := by
    simp only [preQ]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
    simp [show 4 ≤ 4 + j from by omega, show 4 + j < 84 from by omega]
  simp only [hq, beq_iff_eq]
  by_cases h : k = Spec.Blake2s.sigma (j / 8) (2 * (j % 8) + 1)
  · simp [h]
  · simp [h, Ne.symm h]

theorem bPre_COPY {p : ℕ} (h1 : 1 ≤ p) (hp : p < PERIOD) : bPre P_COPY p = 1 := by
  rw [bPre_eq (by simp [P_COPY]) hp]; simp [preQ, P_COPY, h1]

theorem bPre_INIT {k p : ℕ} (hk : k < 4) (hp : p < PERIOD) : bPre (P_INIT k) p = if p = k then 1 else 0 := by
  rw [bPre_eq (by simp [P_INIT]; omega) hp]; simp [preQ, P_INIT, hk]

theorem bPre_FIN {k p : ℕ} (hk : k < 4) (hp : p < PERIOD) : bPre (P_FIN k) p = if p = 84 + k then 1 else 0 := by
  rw [bPre_eq (by simp [P_FIN]; omega) hp]
  simp [preQ, P_FIN, show ¬ 12 + k < 4 by omega, show ¬ 12 + k < 12 by omega, show 12 + k < 16 by omega]

/-! ## Message limbs over a period -/

section Period

variable {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : BlakeSat n preCols pub main)
include hsat

theorem msg_copy {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) {k h : ℕ} (hk : k < 16) (hh : h ≤ 1) :
    ∀ p < PERIOD, main (ML k h) (s + p) = main (ML k h) s := by
  intro p hp
  induction p with
  | zero => rfl
  | succ p ih =>
    have hc : Expr.mul (pre P_COPY) (.sub (col (MSG + (2 * k + h))) (col (MSG + (2 * k + h)) (-1))) ∈ copy :=
      List.mem_map.mpr ⟨2 * k + h, List.mem_range.mpr (by omega), rfl⟩
    have := hsat (s + (p + 1)) (by omega) _ (mem_copy hc)
    rw [show s + (p + 1) = s + (p + 1) from rfl] at this
    simp only [Expr.eval] at this
    have hP : PERIOD = 88 := rfl
    have hw : wrap n (s + (p + 1)) (-1) = s + p := by
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, wrap_back (by omega) (by omega)]; omega
    rw [pre_at hs hp (by omega) (by simp [P_COPY]), bPre_COPY (by omega) hp, one_mul, sub_eq_zero, eval_col, eval_col,
      wrap_zero (by omega), hw] at this
    simp only [ML, MSG] at this ⊢
    rw [show 256 + 2 * k + h = 256 + (2 * k + h) by ring, this, ← show 256 + 2 * k + h = 256 + (2 * k + h) by ring]
    exact ih (by omega)

theorem init_word {s k w : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) (hk : k < 4) (hw : w < 8)
    {val : ℕ → Expr} {Y : Word} (hmem : ∀ c ∈ bitsEq (pre (P_INIT k)) w val, c ∈ init)
    (hval : ∀ i < 32, (val i).eval n preCols pub main (s + k) = ((Y.getLsbD i).toNat : F)) :
    word main (32 * w) (s + k) = Y := by
  have hP : PERIOD = 88 := rfl
  exact bitsEq_word (by omega) (fun c hc => hsat (s + k) (by omega) c (mem_init (hmem c hc)))
    (by rw [pre_at hs (by omega) (by omega) (by simp [P_INIT]; omega), bPre_INIT hk (by omega), if_pos rfl])
    (word_bits hsat (by omega) hw) hval

end Period

theorem IV_getLsbD (k i : ℕ) (hi : i < 32) : (Spec.Blake2s.IV k).getLsbD i = ivBit k i := by
  unfold Spec.Blake2s.IV ivBit
  rw [BitVec.getLsbD_ofNat]
  simp [hi]

theorem eval_xorC {n : ℕ} {pc : List PreCol} {pub : ℕ → F} {main : ℕ → ℕ → F} {r : ℕ} {x : Expr} {a : Bool}
    (hx : x.eval n pc pub main r = (a.toNat : F)) (c : Bool) :
    (xorC x c).eval n pc pub main r = ((a ^^ c).toNat : F) := by
  unfold xorC
  cases c <;> cases a <;> simp_all [Expr.eval, eval_cst]

/-- The d-role values of the init rows (as `init` writes them). -/
def initD (k i : ℕ) : Expr :=
  if k = 0 then cst (ivBit 7 i).toNat
  else if k = 1 then xorC (col (WB 0 i) (-1)) (ivBit 4 i)
  else if k = 2 then xorC (col (WB 1 i) (-2)) (ivBit 5 i)
  else xorC (col (WB 2 0) (-3)) (ivBit 6 i)

theorem init_mem_c {k : ℕ} (hk : k < 4) :
    ∀ c ∈ bitsEq (pre (P_INIT k)) (outW 2) (fun i => cst (ivBit ([2, 3, 0, 1].getD k 0) i).toNat), c ∈ init := by
  intro c hc
  simp only [init, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl ⟨k, hk, Or.inl hc⟩

theorem init_mem_d {k : ℕ} (hk : k < 4) : ∀ c ∈ bitsEq (pre (P_INIT k)) (outW 3) (initD k), c ∈ init := by
  intro c hc
  simp only [init, List.mem_append, List.mem_flatMap, List.mem_range]
  exact Or.inl ⟨k, hk, Or.inr hc⟩

/-- `t`'s low and high words and the final flag, as row 0 of the period holds them. -/
def fBit (main : ℕ → ℕ → F) (s : ℕ) : Bool := bit main (32 * 2) s

section Init

variable {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : BlakeSat n preCols pub main)
include hsat

theorem init_c {s k : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) (hk : k < 4) :
    rw4 main (s + k) 2 = Spec.Blake2s.IV ([2, 3, 0, 1].getD k 0) :=
  init_word hsat hs hn hk (by decide) (init_mem_c hk) (fun i hi => by rw [eval_cst, IV_getLsbD _ _ hi])

theorem init_d {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) :
    rw4 main s 3 = Spec.Blake2s.IV 7 ∧
    rw4 main (s + 1) 3 = Spec.Blake2s.IV 4 ^^^ word main (32 * 0) s ∧
    rw4 main (s + 2) 3 = Spec.Blake2s.IV 5 ^^^ word main (32 * 1) s ∧
    rw4 main (s + 3) 3 = Spec.Blake2s.IV 6 ^^^ (if fBit main s then BitVec.allOnes 32 else 0) := by
  have hP : PERIOD = 88 := rfl
  have wb := fun w (hw : w < 8) => word_bits hsat (r := s) (by omega) hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := init_word hsat hs hn (k := 0) (by norm_num) (by decide) (init_mem_d (by norm_num))
      (Y := Spec.Blake2s.IV 7) (fun i hi => by simp [initD, eval_cst, IV_getLsbD _ _ hi])
    simpa [rw4] using this
  · exact init_word hsat hs hn (k := 1) (by norm_num) (by decide) (init_mem_d (by norm_num)) (fun i hi => by
      simp only [initD, show (1 : ℕ) ≠ 0 by decide, if_false, if_true]
      rw [eval_xorC (eval_bitcol (show wrap n (s + 1) (-1) = s by
        rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, wrap_back (by omega) (by omega)]; omega) (wb 0 (by norm_num)) hi)]
      rw [BitVec.getLsbD_xor, IV_getLsbD _ _ hi, Bool.xor_comm])
  · exact init_word hsat hs hn (k := 2) (by norm_num) (by decide) (init_mem_d (by norm_num)) (fun i hi => by
      simp only [initD, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide, if_false, if_true]
      rw [eval_xorC (eval_bitcol (show wrap n (s + 2) (-2) = s by
        rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) by norm_num, wrap_back (by omega) (by omega)]; omega) (wb 1 (by norm_num)) hi)]
      rw [BitVec.getLsbD_xor, IV_getLsbD _ _ hi, Bool.xor_comm])
  · exact init_word hsat hs hn (k := 3) (by norm_num) (by decide) (init_mem_d (by norm_num)) (fun i hi => by
      simp only [initD, show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false]
      rw [eval_xorC (eval_bitcol (show wrap n (s + 3) (-3) = s by
        rw [show (-3 : ℤ) = -((3 : ℕ) : ℤ) by norm_num, wrap_back (by omega) (by omega)]; omega) (wb 2 (by norm_num))
        (show 0 < 32 by norm_num))]
      rw [BitVec.getLsbD_xor, IV_getLsbD _ _ hi, word_getLsbD _ _ (show 0 < 32 by norm_num)]
      unfold fBit
      cases hf : bit main (32 * 2 + 0) s
      · simp [hf]
      · simp only [hf, if_true, BitVec.getLsbD_allOnes, hi, decide_true]
        cases ivBit 6 i <;> rfl)

theorem final_mem {k : ℕ} (hk : k < 4) {c : Expr} :
    (c ∈ bitsEq (pre (P_FIN k)) 2 (fun i => xor2 (col (WB (outW 0) i) (-84)) (col (WB (outW 0) i) (-4))) ∨
     c ∈ bitsEq (pre (P_FIN k)) 0 (fun i => xor2 (col (WB 2 i)) (col (WB (outW 2) i) (finOff k))) ∨
     c ∈ bitsEq (pre (P_FIN k)) 3 (fun i => xor2 (col (WB (outW 1) i) (-84)) (col (WB (outW 1) i) (-4))) ∨
     c ∈ bitsEq (pre (P_FIN k)) 1 (fun i => xor2 (col (WB 3 i)) (col (WB (outW 3) i) (finOff k)))) → c ∈ final := by
  intro hc
  simp only [final, List.mem_flatMap, List.mem_range, List.mem_append]
  exact ⟨k, hk, by tauto⟩

/-- An xor of two bit words, read at offsets landing on rows `r1`, `r2`. -/
theorem xor_word {s k w wx wy r1 r2 : ℕ} {ox oy : ℤ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) (hk : k < 4)
    (hw : w < 8) (hwx : wx < 8) (hwy : wy < 8) (h1 : wrap n (s + 84 + k) ox = r1) (h2 : wrap n (s + 84 + k) oy = r2)
    (hr1 : r1 < n) (hr2 : r2 < n)
    (hall : ∀ c ∈ bitsEq (pre (P_FIN k)) w (fun i => xor2 (col (WB wx i) ox) (col (WB wy i) oy)), c ∈ final) :
    word main (32 * w) (s + 84 + k) = word main (32 * wx) r1 ^^^ word main (32 * wy) r2 := by
  have hP : PERIOD = 88 := rfl
  refine bitsEq_word (by omega) (fun c hc => hsat _ (by omega) c (mem_final (hall c hc)))
    (by rw [show s + 84 + k = s + (84 + k) by ring, pre_at hs (by omega) (by omega) (by simp [P_FIN]; omega),
      bPre_FIN hk (by omega), if_pos rfl]) (word_bits hsat (by omega) hw) (fun i hi => ?_)
  rw [eval_xor2 (eval_bitcol h1 (word_bits hsat hr1 hwx) hi) (eval_bitcol h2 (word_bits hsat hr2 hwy) hi),
    BitVec.getLsbD_xor]

/-- `b(4+k)`: the second word final row `k` outputs. -/
def bOf (k : ℕ) : ℕ := [5, 6, 7, 4].getD k 0

theorem final_out {s k : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) (hk : k < 4) :
    word main (32 * 0) (s + 84 + k) = diagSlot main s k ^^^ diagSlot main (s + 80) k ^^^ diagSlot main (s + 80) (k + 8) ∧
    word main (32 * 1) (s + 84 + k) =
      diagSlot main s (bOf k) ^^^ diagSlot main (s + 80) (bOf k) ^^^ diagSlot main (s + 80) (bOf k + 8) := by
  have hP : PERIOD = 88 := rfl
  have back : ∀ d : ℕ, d ≤ s + 84 + k → wrap n (s + 84 + k) (-(d : ℤ)) = s + 84 + k - d :=
    fun d hd => wrap_back hd (by omega)
  have W2 := xor_word hsat (k := k) (w := 2) (wx := 4) (wy := 4) hs hn hk (by norm_num) (by norm_num) (by norm_num)
    (back 84 (by omega)) (back 4 (by omega)) (by omega) (by omega)
    (fun c hc => final_mem hsat hk (Or.inl (by simpa [outW] using hc)))
  have W3 := xor_word hsat (k := k) (w := 3) (wx := 7) (wy := 7) hs hn hk (by norm_num) (by norm_num) (by norm_num)
    (back 84 (by omega)) (back 4 (by omega)) (by omega) (by omega)
    (fun c hc => final_mem hsat hk (Or.inr (Or.inr (Or.inl (by simpa [outW] using hc)))))
  have hfo : finOff k = -((if k < 2 then 2 else 6 : ℕ) : ℤ) := by unfold finOff; split_ifs <;> simp
  have W0 := xor_word hsat (k := k) (w := 0) (wx := 2) (wy := 6) (ox := 0) (oy := finOff k)
    (r2 := s + 84 + k - (if k < 2 then 2 else 6)) hs hn hk (by norm_num) (by norm_num) (by norm_num)
    (wrap_zero (by omega)) (by rw [hfo]; exact back _ (by split_ifs <;> omega)) (by omega) (by split_ifs <;> omega)
    (fun c hc => final_mem hsat hk (Or.inr (Or.inl (by simpa [outW] using hc))))
  have W1 := xor_word hsat (k := k) (w := 1) (wx := 3) (wy := 5) (ox := 0) (oy := finOff k)
    (r2 := s + 84 + k - (if k < 2 then 2 else 6)) hs hn hk (by norm_num) (by norm_num) (by norm_num)
    (wrap_zero (by omega)) (by rw [hfo]; exact back _ (by split_ifs <;> omega)) (by omega) (by split_ifs <;> omega)
    (fun c hc => final_mem hsat hk (Or.inr (Or.inr (Or.inr (by simpa [outW] using hc)))))
  rw [show 32 * 2 = 32 * 2 from rfl] at W0
  constructor
  · rw [W0, W2]
    interval_cases k <;> simp [diagSlot, rw4, outW, show s + 84 + 0 - 84 = s by omega, show s + 84 + 1 - 84 = s + 1 by omega,
      show s + 84 + 2 - 84 = s + 2 by omega, show s + 84 + 3 - 84 = s + 3 by omega] <;> congr 2 <;> omega
  · rw [W1, W3]
    interval_cases k <;> simp [diagSlot, rw4, outW, bOf, show s + 84 + 0 - 84 = s by omega, show s + 84 + 1 - 84 = s + 1 by omega,
      show s + 84 + 2 - 84 = s + 2 by omega, show s + 84 + 3 - 84 = s + 3 by omega] <;> congr 2 <;> omega

end Init

/-! ## The compression -/

theorem sigma_lt (r i : ℕ) : Spec.Blake2s.sigma r i < 16 := by
  have hall : ∀ l ∈ Spec.Blake2s.SIGMA, ∀ x ∈ l, x < 16 := by decide
  unfold Spec.Blake2s.sigma
  have h2 : ∀ l : List ℕ, (∀ x ∈ l, x < 16) → l.getD i 0 < 16 := by
    intro l hl
    by_cases hi : i < l.length
    · rw [List.getD_eq_getElem _ _ hi]; exact hl _ (List.getElem_mem _)
    · rw [List.getD_eq_default _ _ (by omega)]; norm_num
  by_cases hr : r < Spec.Blake2s.SIGMA.length
  · rw [List.getD_eq_getElem _ _ hr]; exact h2 _ (hall _ (List.getElem_mem _))
  · rw [List.getD_eq_default Spec.Blake2s.SIGMA [] (by omega)]; simp

theorem src_le {g : ℕ} (hg : g < 8) (role : ℕ) : src g role ≤ 4 + g := by
  interval_cases g <;> rcases role with _ | _ | _ | role <;> simp [src]

/-- The counter `t` a period reads: row 0's `W0` (low) and `W1` (high). -/
def inT (main : ℕ → ℕ → F) (s : ℕ) : ℕ := (word main (32 * 0) s).toNat + 2 ^ 32 * (word main (32 * 1) s).toNat

/-- Output word `i` of a period: final row `i` (`W0`) for `i < 4`, else final row `(i+3) mod 4` (`W1`). -/
def outWord (main : ℕ → ℕ → F) (s i : ℕ) : Word :=
  if i < 4 then word main (32 * 0) (s + 84 + i) else word main (32 * 1) (s + 84 + (i + 3) % 4)

section Main

variable {n : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : BlakeSat n preCols pub main)
include hsat

theorem init_state {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) :
    ∀ i < 16, (Spec.Blake2s.initV (diagSlot main s) (inT main s) (fBit main s)).getD i 0 = diagSlot main s i := by
  obtain ⟨d0, d1, d2, d3⟩ := init_d hsat hs hn
  have c0 := init_c hsat (k := 0) hs hn (by norm_num)
  have c1 := init_c hsat (k := 1) hs hn (by norm_num)
  have c2 := init_c hsat (k := 2) hs hn (by norm_num)
  have c3 := init_c hsat (k := 3) hs hn (by norm_num)
  have tlo : BitVec.ofNat 32 (inT main s) = word main (32 * 0) s := by
    apply BitVec.eq_of_toNat_eq
    simp only [inT, BitVec.toNat_ofNat]
    have := (word main (32 * 0) s).isLt
    omega
  have thi : BitVec.ofNat 32 (inT main s / 2 ^ 32) = word main (32 * 1) s := by
    apply BitVec.eq_of_toNat_eq
    simp only [inT, BitVec.toNat_ofNat]
    have := (word main (32 * 0) s).isLt
    have := (word main (32 * 1) s).isLt
    rw [show ((word main (32 * 0) s).toNat + 2 ^ 32 * (word main (32 * 1) s).toNat) / 2 ^ 32 =
      (word main (32 * 1) s).toNat by omega]
    omega
  intro i hi
  interval_cases i <;> simp_all [Spec.Blake2s.initV, diagSlot]

theorem msgWord_copy {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) {k p : ℕ} (hk : k < 16)
    (hp : p < PERIOD) : msgWord main k (s + p) = msgWord main k s := by
  unfold msgWord
  rw [msg_copy hsat hs hn hk (by norm_num) p hp, msg_copy hsat hs hn hk (by norm_num) p hp]

/-- Every G row of an aligned period computes `mix` on the period's message words. -/
theorem g_rows {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n)
    (hm : ∀ k < 16, ∀ h ≤ 1, (main (ML k h) s).val < 65536) :
    ∀ ρ < 10, ∀ g < 8, GOK main (s + 4 + 8 * ρ + g) g (msgWord main (Spec.Blake2s.sigma ρ (2 * g)) s)
      (msgWord main (Spec.Blake2s.sigma ρ (2 * g + 1)) s) := by
  intro ρ hρ g hg
  have hP : PERIOD = 88 := rfl
  have hrow : s + 4 + 8 * ρ + g = s + (4 + (8 * ρ + g)) := by ring
  have hj : 8 * ρ + g < 80 := by omega
  have hj8 : (8 * ρ + g) / 8 = ρ := by omega
  have hjm : (8 * ρ + g) % 8 = g := by omega
  have pa := fun i (hi : i < 50) => pre_at (n := n) (pub := pub) (main := main) (s := s) (p := 4 + (8 * ρ + g)) hs
    (by omega) (by omega) hi
  have key := g_step hsat (r := s + (4 + (8 * ρ + g))) (κx := Spec.Blake2s.sigma ρ (2 * g))
    (κy := Spec.Blake2s.sigma ρ (2 * g + 1)) (by omega) (fun role => by have := src_le hg role; omega) hg
    (by rw [pa _ (by simp [P_G]; omega), bPre_G hg hj, if_pos hjm])
    (by rw [pa _ (by simp [P_ISG]), bPre_ISG hj])
    (fun k hk => by rw [pa _ (by simp [P_XSEL]; omega), bPre_X hk hj, hj8, hjm])
    (sigma_lt _ _)
    (fun k hk => by rw [pa _ (by simp [P_YSEL]; omega), bPre_Y hk hj, hj8, hjm])
    (sigma_lt _ _)
    (fun k hk h hh => by rw [msg_copy hsat hs hn hk hh _ (by omega)]; exact hm k hk h hh)
  rw [msgWord_copy hsat hs hn (sigma_lt _ _) (by omega), msgWord_copy hsat hs hn (sigma_lt _ _) (by omega)] at key
  unfold GOK
  rw [hrow]
  exact key

omit hsat in
theorem compress_eq (h m : ℕ → Word) (t : ℕ) (f : Bool) (i : ℕ) :
    Spec.Blake2s.compress h m t f i =
      h i ^^^ (Spec.Blake2s.steps m (Spec.Blake2s.initV h t f) 80).getD i 0 ^^^
        (Spec.Blake2s.steps m (Spec.Blake2s.initV h t f) 80).getD (i + 8) 0 := rfl

/-- **Blake2s compression soundness for `Blake2s.air`.** In any trace satisfying the AIR, every
aligned 88-row period computes RFC 7693's `F(h, m, t, f)`: `h` is read from the init rows, `m`
from the message limbs (which must be 16-bit), `t` and `f` from row 0, and the output from the
final rows. -/
theorem compress_sound {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n)
    (hm : ∀ k < 16, ∀ h ≤ 1, (main (ML k h) s).val < 65536) :
    ∀ i < 8, Spec.Blake2s.compress (diagSlot main s) (fun k => msgWord main k s) (inT main s) (fBit main s) i =
      outWord main s i := by
  intro i hi
  have hlen : (Spec.Blake2s.initV (diagSlot main s) (inT main s) (fBit main s)).length = 16 := by
    simp [Spec.Blake2s.initV]
  have hst := steps_rounds (main := main) (m := fun k => msgWord main k s)
    (v0 := Spec.Blake2s.initV (diagSlot main s) (inT main s) (fBit main s)) (s := s)
    hlen (init_state hsat hs hn) (g_rows hsat hs hn hm) 10 le_rfl
  rw [show 8 * 10 = 80 from rfl] at hst
  rw [compress_eq, hst i (by omega), hst (i + 8) (by omega)]
  unfold outWord
  split_ifs with h4
  · exact (final_out hsat hs hn h4).1.symm
  · have := (final_out hsat hs hn (k := (i + 3) % 4) (by omega)).2
    interval_cases i <;> simpa [bOf] using this.symm

end Main

/-- **Blake2s compression soundness for `Blake2s.air`**, as satisfaction of the exported AIR. -/
theorem compress_sound_air {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F}
    (hsat : air.Satisfied logSize pub main) {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ 2 ^ logSize)
    (hm : ∀ k < 16, ∀ h ≤ 1, (main (ML k h) s).val < 65536) :
    ∀ i < 8, Spec.Blake2s.compress (diagSlot main s) (fun k => msgWord main k s) (inT main s) (fBit main s) i =
      outWord main s i :=
  compress_sound (fun r hr c hc => hsat r hr c hc) hs hn hm

end StarkedAir.Blake2s
