/-
**Header tree soundness (HC-HASHTREE).** In any instance of the two-component system
(`headers`, `tree`) that is satisfied and balanced together with the verifier's public entry
`node(K, 0, T)`, `T` is the perfect Blake2s tree root over the segment's `2^K` block hashes in
order: `T = rootAt (hashAt main) K 0`.

Argument: membership (`used_in_table_ext`) turns every looked-up tuple into a table site with a
nonzero multiplicity. Header sites with nonzero multiplicity sit at row 215 of a header and carry
`(0, j, hash j)`; tree yield sites sit at row 87 of a period, whose Blake2s compression
(`compress_sound`) hashes the two tuples its row 0 looks up. Induction on the level, downward
from the root, gives every reachable node its correct value; positions stay below `2^K`, so no
field wrap-around occurs.
-/
import StarkedAir.Gadgets.HeaderTree
import StarkedAir.Gadgets.Blake2sSound
import StarkedAir.Gadgets.TopSound

namespace StarkedAir.HeaderTree

open StarkedAir Spec.HeaderTree

/-- The system: component 0 = headers, 1 = tree. -/
def sys : System := ⟨2, fun i => if i = 0 then headers else tree⟩

/-- The 16 limbs (lo/hi interleaved) of a state's words. -/
def limbsOf (st : Spec.Sha256.State) : List F :=
  (List.range 16).map fun j => ((Sha256.half16 (stWord st (j / 2)) (j % 2) : ℕ) : F)

theorem sites_mem {inst : ℕ → Inst} {s : Site} :
    s ∈ sites sys inst ↔ s.1 < 2 ∧ s.2.1 < 2 ^ (inst s.1).logSize ∧ s.2.2 < (sys.comp s.1).lookups.length := by
  obtain ⟨i, r, k⟩ := s
  simp [sites, sys]

theorem header_lookups : (sys.comp 0).lookups.length = 1 := rfl
theorem tree_lookups : (sys.comp 1).lookups.length = 3 := rfl

/-! ## The header component -/

section Headers

variable {L : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} (hh : HeaderChain.air.Satisfied L pub M) (hL : 8 ≤ L)
include hh hL

/-- Public inputs 32, 33 are the first header's height limbs. -/
theorem pub_first : pub 32 + 65536 * pub 33 = ((HeaderChain.heightAt M 0 : ℕ) : F) := by
  have hj : 256 * (0 + 1) ≤ 2 ^ L := by
    calc 256 * (0 + 1) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hb := HeaderChain.state_sat hh hj
  have hsel := HeaderChain.ev_stateSel hh hj
  have hfirst := HeaderChain.ev_first hh hj
  simp only [Nat.mul_zero, Nat.zero_add, if_true] at hb hsel hfirst
  have hr : 218 < 2 ^ L := by omega
  have hbits := HeaderChain.bits (HeaderChain.chainSat_of hh) hr (base := Sha256.A) (by decide)
  have l0 := Sha256.eval_limb (pc := HeaderChain.preCols) (pub := pub) (wrap_zero hr) hbits (half := 0) (by norm_num)
  have l1 := Sha256.eval_limb (pc := HeaderChain.preCols) (pub := pub) (wrap_zero hr) hbits (half := 1) (by norm_num)
  have m0 : (Expr.mul (.mul HeaderChain.stateSel (Sha256.pre HeaderChain.FIRST)) (.sub (Sha256.limb Sha256.A 0) (.pub 32)))
      ∈ HeaderChain.stateCs := List.mem_append_left _ (by unfold HeaderChain.stateBase; simp)
  have m1 : (Expr.mul (.mul HeaderChain.stateSel (Sha256.pre HeaderChain.FIRST)) (.sub (Sha256.limb Sha256.A 1) (.pub 33)))
      ∈ HeaderChain.stateCs := List.mem_append_left _ (by unfold HeaderChain.stateBase; simp)
  have e0 := hb _ m0
  have e1 := hb _ m1
  simp only [Expr.eval, hsel, hfirst, one_mul, l0, l1, sub_eq_zero] at e0 e1
  rw [← e0, ← e1, HeaderChain.heightAt, Sha256.half16_split (Sha256.word M Sha256.A 218)]
  push_cast; ring

/-- The height bits at row 218 of header `j` give its height. -/
theorem relHeight_eval {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ L) :
    relHeight.eval (2 ^ L) HeaderChain.preCols pub M (256 * j + 215) = (j : F) := by
  have hj0 : 256 * (0 + 1) ≤ 2 ^ L := by
    calc 256 * (0 + 1) = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hH : 2 ^ L / 256 * 256 = 2 ^ L := Nat.div_mul_cancel (by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num]; exact pow_dvd_pow 2 hL)
  have hjH : j < 2 ^ L / 256 := by omega
  have h0H : 0 < 2 ^ L / 256 := by omega
  have hr : 256 * j + 218 < 2 ^ L := by omega
  have hbits := HeaderChain.bits (HeaderChain.chainSat_of hh) hr (base := Sha256.A) (by decide)
  have hw : wrap (2 ^ L) (256 * j + 215) 3 = 256 * j + 218 := by
    rw [Sha256.wrap_eq (by omega) (by exact_mod_cast (show 256 * j + 215 + 3 < 2 ^ L by omega))]; omega
  have hb : (HeaderChain.bitsAt Sha256.A 30 3).eval (2 ^ L) HeaderChain.preCols pub M (256 * j + 215) =
      ((ofBits (fun i => Sha256.bit M (Sha256.A + i) (256 * j + 218)) 30 : ℕ) : F) :=
    Sha256.eval_sumPow_bits _ _ 30 (fun i hi => by rw [Sha256.eval_col, hw]; exact Sha256.eq_bit (hbits i (by omega)))
  -- The height is below 2^30, so its 30 low bits are the whole word.
  have hlt := (HeaderChain.state_sound hh hL).1 j hjH
  have hfull : HeaderChain.heightAt M j = ofBits (fun i => Sha256.bit M (Sha256.A + i) (256 * j + 218)) 30 := by
    have e := HeaderChain.ofBits_add (fun i => (Sha256.word M Sha256.A (256 * j + 218)).getLsbD i) 30 2
    have hw32 : (Sha256.word M Sha256.A (256 * j + 218)).toNat =
        ofBits (fun i => (Sha256.word M Sha256.A (256 * j + 218)).getLsbD i) 32 := toNat_eq_ofBits _
    have hc : ofBits (fun i => (Sha256.word M Sha256.A (256 * j + 218)).getLsbD i) 30 =
        ofBits (fun i => Sha256.bit M (Sha256.A + i) (256 * j + 218)) 30 :=
      ofBits_congr (fun i hi => Sha256.word_getLsbD _ _ (by omega))
    unfold HeaderChain.heightAt at hlt ⊢
    simp only [show (30 + 2 : ℕ) = 32 from rfl] at e
    have := ofBits_lt (fun i => (Sha256.word M Sha256.A (256 * j + 218)).getLsbD (30 + i)) 2
    rw [← hc]; omega
  have hhe := HeaderChain.height_eq hh hL
  unfold relHeight
  simp only [Expr.eval, hb, ← hfull, Sha256.eval_cst]
  rw [show (pub 32 + (65536 : ℕ) * pub 33 : F) = pub 32 + 65536 * pub 33 by push_cast; ring, pub_first hh hL,
    hhe j hjH, hhe 0 h0H]
  push_cast; ring

omit hh hL in
theorem stWord_hashAt {M : ℕ → ℕ → F} {j k : ℕ} (hk : k < 8) :
    stWord (HeaderChain.hashAt M j) k =
      if k < 4 then Sha256.word M Sha256.A (256 * j + 215 - k) else Sha256.word M Sha256.E (256 * j + 215 - (k - 4)) := by
  simp only [HeaderChain.hashAt, Sha256.outputAt, Sha256.stAt, show 256 * j + 144 + 71 = 256 * j + 215 by ring]
  interval_cases k <;> rfl

theorem hashLimbs_eval {j : ℕ} (hj : 256 * (j + 1) ≤ 2 ^ L) :
    hashLimbs.map (·.eval (2 ^ L) HeaderChain.preCols pub M (256 * j + 215)) = limbsOf (HeaderChain.hashAt M j) := by
  have hr : 256 * j + 215 < 2 ^ L := by omega
  have hb := fun (base : ℕ) (hb : base + 32 ≤ 96) (k : ℕ) (hk : k ≤ 3) =>
    HeaderChain.bits (HeaderChain.chainSat_of hh) (r := 256 * j + 215 - k) (by omega) hb
  have LA := fun (k : ℕ) (hk : k ≤ 3) (h : ℕ) (hh' : h ≤ 1) =>
    Sha256.eval_limb (pc := HeaderChain.preCols) (pub := pub) (base := Sha256.A) (off := -(k : ℤ))
      (Sha256.wrap_back (by omega) hr) (hb Sha256.A (by decide) k hk) hh'
  have LE := fun (k : ℕ) (hk : k ≤ 3) (h : ℕ) (hh' : h ≤ 1) =>
    Sha256.eval_limb (pc := HeaderChain.preCols) (pub := pub) (base := Sha256.E) (off := -(k : ℤ))
      (Sha256.wrap_back (by omega) hr) (hb Sha256.E (by decide) k hk) hh'
  unfold hashLimbs limbsOf
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp]
  rw [stWord_hashAt (by omega)]
  split_ifs with hk
  · exact LA (i / 2) (by omega) (i % 2) (by omega)
  · exact LE (i / 2 - 4) (by omega) (i % 2) (by omega)

end Headers

/-! ## The tree component -/

theorem compress_congr {h h' : ℕ → Spec.Blake2s.Word} (m : ℕ → Spec.Blake2s.Word) (t : ℕ) (f : Bool)
    (e : ∀ i < 8, h i = h' i) {i : ℕ} (hi : i < 8) :
    Spec.Blake2s.compress h m t f i = Spec.Blake2s.compress h' m t f i := by
  have hv : Spec.Blake2s.initV h t f = Spec.Blake2s.initV h' t f := by
    unfold Spec.Blake2s.initV
    apply List.map_congr_left
    intro k _
    by_cases hk : k < 8
    · simp [hk, e k hk]
    · simp [hk]
  unfold Spec.Blake2s.compress
  rw [hv, e i hi]

section Tree

open StarkedAir.Blake2s (bPre pre_at PERIOD diagSlot rw4 inT fBit outWord msgWord BlakeSat P_COPY P_INIT P_FIN ML outW)
open StarkedAir.Sha256 (col pre cst)

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (ht : ∀ r < n, ∀ c ∈ treeConstraints, c.eval n Blake2s.preCols pub M r = 0)
include ht

theorem blakeSat : BlakeSat n Blake2s.preCols pub M :=
  fun r hr c hc => ht r hr c (by unfold treeConstraints; simp [hc])

theorem tree_pre {r i : ℕ} (hr : r < n) (hi : i < 50) :
    (pre i).eval n Blake2s.preCols pub M r = bPre i (r % 88) := by
  have := pre_at (n := n) (pub := pub) (main := M) (s := r - r % 88) (p := r % 88) (i := i)
    (by simp only [PERIOD]; omega) (by simp only [PERIOD]; omega) (by omega) hi
  rwa [show r - r % 88 + r % 88 = r by omega] at this

theorem level_ne {r : ℕ} (hr : r < n) : M LVL r ≠ 0 := by
  have := ht r hr (.sub (.mul (col LVL) (col LVL_INV)) (cst 1)) (by unfold treeConstraints levelCs; simp)
  simp only [Expr.eval, Sha256.eval_col, wrap_zero hr, Sha256.eval_cst, Nat.cast_one, sub_eq_zero] at this
  intro h0; rw [h0, zero_mul] at this; exact zero_ne_one this

/-- `LVL` and `POS` are constant over an aligned period. -/
theorem level_copy {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) (c : ℕ) (hc : c = LVL ∨ c = POS) :
    ∀ p < PERIOD, M c (s + p) = M c s := by
  have hP : PERIOD = 88 := rfl
  intro p hp
  induction p with
  | zero => rfl
  | succ p ih =>
    have mem : Expr.mul (pre P_COPY) (.sub (col c) (col c (-1))) ∈ treeConstraints := by
      unfold treeConstraints levelCs; rcases hc with rfl | rfl <;> simp
    have := ht (s + (p + 1)) (by omega) _ mem
    have hw : wrap n (s + (p + 1)) (-1) = s + p := by
      rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num, Sha256.wrap_back (by omega) (by omega)]; omega
    simp only [Expr.eval, Sha256.eval_col, wrap_zero (show s + (p + 1) < n by omega), hw] at this
    rw [pre_at hs (by omega) (by omega) (by simp [P_COPY]), Blake2s.bPre_COPY (by omega) (by omega), one_mul,
      sub_eq_zero] at this
    rw [this]; exact ih (by omega)

theorem const_word {s k w : ℕ} {c : ℕ → Bool} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) (hk : k < 4) (hw : w < 8)
    (hmem : ∀ x ∈ bitsConst (pre (P_INIT k)) w c, x ∈ treeConstraints) :
    Sha256.word M (32 * w) (s + k) = BitVec.ofNat 32 (ofBits c 32) := by
  have hP : PERIOD = 88 := rfl
  refine Blake2s.bitsEq_word (by omega) (fun x hx => ht _ (by omega) x (hmem x hx))
    (by rw [pre_at hs (by omega) (by omega) (by simp [P_INIT]; omega), Blake2s.bPre_INIT hk (by omega), if_pos rfl])
    (Blake2s.word_bits (blakeSat ht) (by omega) hw) (fun i hi => ?_)
  rw [Sha256.eval_cst, BitVec.getLsbD_ofNat, testBit_ofBits]
  simp [hi]

omit ht in
theorem ofBits_testBit (x : ℕ) (hx : x < 2 ^ 32) : ofBits (fun i => x.testBit i) 32 = x := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_ofBits]
  by_cases hi : i < 32
  · simp [hi]
  · simp only [hi, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by omega)))).symm

omit ht in
theorem h0_word (k : ℕ) : BitVec.ofNat 32 (ofBits (fun i => (h0Nat k).testBit i) 32) = Spec.Blake2s.h0 k := by
  rw [ofBits_testBit (h0Nat k) (by unfold h0Nat; exact (Spec.Blake2s.h0 k).isLt)]; simp [h0Nat]

theorem tree_h {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) : ∀ i < 8, diagSlot M s i = Spec.Blake2s.h0 i := by
  have memA : ∀ k < 4, ∀ x ∈ bitsConst (pre (P_INIT k)) (outW 0) (fun i => (h0Nat k).testBit i), x ∈ treeConstraints :=
    fun k hk x hx => by
      unfold treeConstraints constIn
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨k, hk, Or.inl hx⟩))))
  have memB : ∀ k < 4, ∀ x ∈ bitsConst (pre (P_INIT k)) (outW 1) (fun i => (h0Nat (bOf k)).testBit i), x ∈ treeConstraints :=
    fun k hk x hx => by
      unfold treeConstraints constIn
      simp only [List.mem_append, List.mem_flatMap, List.mem_range]
      exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inl ⟨k, hk, Or.inr hx⟩))))
  have WA := fun k (hk : k < 4) => (const_word ht hs hn hk (by decide) (memA k hk)).trans (h0_word k)
  have WB := fun k (hk : k < 4) => (const_word ht hs hn hk (by decide) (memB k hk)).trans (h0_word (bOf k))
  intro i hi
  have a0 := WA 0 (by norm_num); have a1 := WA 1 (by norm_num); have a2 := WA 2 (by norm_num); have a3 := WA 3 (by norm_num)
  have b0 := WB 0 (by norm_num); have b1 := WB 1 (by norm_num); have b2 := WB 2 (by norm_num); have b3 := WB 3 (by norm_num)
  simp only [Nat.add_zero, outW, bOf] at a0 a1 a2 a3 b0 b1 b2 b3
  interval_cases i <;> simp_all [diagSlot, rw4, outW]

theorem tree_t {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) : inT M s = 64 := by
  have m64 : ∀ x ∈ bitsConst (pre (P_INIT 0)) 0 (fun i => (64 : ℕ).testBit i), x ∈ treeConstraints := fun x hx => by
    unfold treeConstraints constIn; simp only [List.mem_append]; exact Or.inl (Or.inr (Or.inl (Or.inl (Or.inr hx))))
  have m0 : ∀ x ∈ bitsConst (pre (P_INIT 0)) 1 (fun _ => false), x ∈ treeConstraints := fun x hx => by
    unfold treeConstraints constIn; simp only [List.mem_append]; exact Or.inl (Or.inr (Or.inl (Or.inr hx)))
  have w0 := const_word ht hs hn (k := 0) (by norm_num) (by norm_num) m64
  have w1 := const_word ht hs hn (k := 0) (by norm_num) (by norm_num) m0
  rw [ofBits_testBit 64 (by norm_num)] at w0
  have : ofBits (fun _ => false) 32 = 0 := by
    have := ofBits_testBit 0 (by norm_num); simpa using this
  rw [this] at w1
  simp only [Nat.add_zero] at w0 w1
  unfold inT; rw [w0, w1]; rfl

theorem tree_f {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) : fBit M s = true := by
  have hP : PERIOD = 88 := rfl
  have := ht s (by omega) (.mul (pre (P_INIT 0)) (.sub (col (32 * 2)) (cst 1)))
    (by unfold treeConstraints constIn; simp only [List.mem_append, List.mem_singleton]; simp)
  have hpre := pre_at (n := n) (pub := pub) (main := M) (s := s) (p := 0) (i := P_INIT 0) hs (by omega) (by omega)
    (by simp [P_INIT])
  rw [Nat.add_zero, Blake2s.bPre_INIT (by norm_num) (by omega), if_pos rfl] at hpre
  simp only [Expr.eval, hpre, one_mul, Sha256.eval_col, wrap_zero (show s < n by omega), Sha256.eval_cst, Nat.cast_one,
    sub_eq_zero] at this
  unfold fBit Sha256.bit; rw [this, ZMod.val_one]; rfl

/-- **A tree period** computes `F(h₀, message, 64, final)`. -/
theorem tree_period {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n)
    (hm : ∀ k < 16, ∀ h ≤ 1, (M (ML k h) s).val < 65536) :
    ∀ i < 8, outWord M s i = Spec.Blake2s.compress Spec.Blake2s.h0 (fun k => msgWord M k s) 64 true i := by
  intro i hi
  rw [← Blake2s.compress_sound (blakeSat ht) hs hn hm i hi, tree_t ht hs hn, tree_f ht hs hn]
  exact compress_congr _ _ _ (tree_h ht hs hn) hi

omit ht in
theorem stWord_toState (w : ℕ → Spec.Blake2s.Word) {k : ℕ} (hk : k < 8) : stWord (toState w) k = w k := by
  interval_cases k <;> rfl

theorem outLimbs_eval {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) :
    outLimbs.map (·.eval n Blake2s.preCols pub M (s + 87)) = limbsOf (toState (outWord M s)) := by
  have hP : PERIOD = 88 := rfl
  have hw : ∀ a ≤ 87, wrap n (s + 87) ((a : ℕ) - (87 : ℤ)) = s + a := fun a ha => by
    have h1 : (0 : ℤ) ≤ ((s + 87 : ℕ) : ℤ) + ((a : ℕ) - (87 : ℤ)) := by omega
    have h2 : ((s + 87 : ℕ) : ℤ) + ((a : ℕ) - (87 : ℤ)) < (n : ℤ) := by
      have : s + a < n := by omega
      omega
    rw [Sha256.wrap_eq h1 h2]; omega
  have L := fun (w : ℕ) (hw8 : w < 8) (a : ℕ) (ha : a ≤ 87) (h : ℕ) (hh : h ≤ 1) =>
    Sha256.eval_limb (n := n) (pc := Blake2s.preCols) (pub := pub) (main := M) (r := s + 87) (base := 32 * w)
      (off := (a : ℕ) - (87 : ℤ)) (hw a ha) (Blake2s.word_bits (blakeSat ht) (r := s + a) (by omega) hw8) hh
  unfold outLimbs limbsOf
  rw [List.map_map]
  apply List.map_congr_left
  intro j hj
  rw [List.mem_range] at hj
  simp only [Function.comp]
  rw [stWord_toState _ (by omega)]
  unfold outWord
  split_ifs with h4
  · have := L 0 (by norm_num) (84 + j / 2) (by omega) (j % 2) (by omega)
    rw [← Nat.add_assoc] at this; exact this
  · have := L 1 (by norm_num) (84 + (j / 2 + 3) % 4) (by omega) (j % 2) (by omega)
    rw [← Nat.add_assoc] at this; exact this

omit ht in
theorem limbsOf_get {X : Spec.Sha256.State} {j : ℕ} (hj : j < 16) :
    (limbsOf X).getD j 0 = ((Sha256.half16 (stWord X (j / 2)) (j % 2) : ℕ) : F) := by
  unfold limbsOf; rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp

omit ht in
/-- Message limbs that equal a state's limbs give 16-bit limbs and that state's words. -/
theorem msg_from_limbs {s half : ℕ} {X : Spec.Sha256.State}
    (h : (List.range 16).map (fun j => M (ML (8 * half + j / 2) (j % 2)) s) = limbsOf X) :
    (∀ k < 8, ∀ hh ≤ 1, (M (ML (8 * half + k) hh) s).val < 65536) ∧
      ∀ k < 8, msgWord M (8 * half + k) s = stWord X k := by
  have get : ∀ k < 8, ∀ hh ≤ 1, M (ML (8 * half + k) hh) s = ((Sha256.half16 (stWord X k) hh : ℕ) : F) := by
    intro k hk hh hh1
    have := congrArg (fun l => l.getD (2 * k + hh) 0) h
    rw [limbsOf_get (by omega), List.getD_eq_getElem _ _ (by simp; omega)] at this
    simp only [List.getElem_map, List.getElem_range] at this
    rwa [show (2 * k + hh) / 2 = k by omega, show (2 * k + hh) % 2 = hh by omega] at this
  have hv : ∀ k < 8, ∀ hh ≤ 1, (M (ML (8 * half + k) hh) s).val = Sha256.half16 (stWord X k) hh := by
    intro k hk hh hh1
    rw [get k hk hh hh1, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans (Sha256.half16_lt _ _) (by norm_num [P]))]
  refine ⟨fun k hk hh hh1 => by rw [hv k hk hh hh1]; exact Sha256.half16_lt _ _, fun k hk => ?_⟩
  unfold msgWord
  rw [hv k hk 0 (by norm_num), hv k hk 1 (by norm_num), ← Sha256.half16_split]
  simp

omit ht in
theorem steps_congr_m {m m' : ℕ → Spec.Blake2s.Word} (e : ∀ k < 16, m k = m' k) (v : List Spec.Blake2s.Word) :
    ∀ k, Spec.Blake2s.steps m v k = Spec.Blake2s.steps m' v k
  | 0 => rfl
  | k + 1 => by
    simp only [Spec.Blake2s.steps, Spec.Blake2s.gStep, steps_congr_m e v k,
      e _ (Blake2s.sigma_lt _ _)]

omit ht in
theorem compress_congr_m {m m' : ℕ → Spec.Blake2s.Word} (h : ℕ → Spec.Blake2s.Word) (t : ℕ) (f : Bool)
    (e : ∀ k < 16, m k = m' k) (i : ℕ) : Spec.Blake2s.compress h m t f i = Spec.Blake2s.compress h m' t f i := by
  unfold Spec.Blake2s.compress; rw [steps_congr_m e]

/-- **Node step.** A tree period whose message halves are the limbs of `l` and `r` outputs
`hnode l r`. -/
theorem node_step {s : ℕ} (hs : s % PERIOD = 0) (hn : s + PERIOD ≤ n) {l r : Spec.Sha256.State}
    (hl : (List.range 16).map (fun j => M (ML (8 * 0 + j / 2) (j % 2)) s) = limbsOf l)
    (hr : (List.range 16).map (fun j => M (ML (8 * 1 + j / 2) (j % 2)) s) = limbsOf r) :
    toState (outWord M s) = hnode l r := by
  obtain ⟨bl, wl⟩ := msg_from_limbs hl
  obtain ⟨br, wr⟩ := msg_from_limbs hr
  have hm : ∀ k < 16, ∀ h ≤ 1, (M (ML k h) s).val < 65536 := by
    intro k hk h hh
    by_cases k8 : k < 8
    · have := bl k k8 h hh; simpa using this
    · have := br (k - 8) (by omega) h hh; rwa [show 8 * 1 + (k - 8) = k by omega] at this
  have hmsg : ∀ k < 16, msgWord M k s = (fun k => if k < 8 then stWord l k else stWord r (k - 8)) k := by
    intro k hk
    by_cases k8 : k < 8
    · have := wl k k8; simp only [Nat.mul_zero, Nat.zero_add] at this; simp [k8, this]
    · have := wr (k - 8) (by omega); rw [show 8 * 1 + (k - 8) = k by omega] at this; simp [k8, this]
  have hp := tree_period ht hs hn hm
  unfold hnode toState
  congr 1 <;> rw [hp _ (by norm_num), compress_congr_m _ _ _ hmsg]

end Tree

/-! ## The system -/

section System

open StarkedAir.Blake2s (bPre PERIOD outWord P_INIT P_FIN ML)
open StarkedAir.Sha256 (pre col cst)

theorem sites_length {inst : ℕ → Inst} {L : ℕ} (h0L : (inst 0).logSize = L) (h1L : (inst 1).logSize = L) :
    (sites sys inst).length = 4 * 2 ^ L := by
  simp [sites, sys, h0L, h1L, List.length_flatMap, headers, tree, treeLookups, List.sum_range_succ]
  ring

theorem site_hdr_mult {inst : ℕ → Inst} {pub : ℕ → F} {r : ℕ} :
    siteMult sys inst pub (0, r, 0) =
      (pre (HeaderChain.OUT0 + 3)).eval (2 ^ (inst 0).logSize) HeaderChain.preCols pub (inst 0).main r *
        (inst 0).main HMULT (wrap (2 ^ (inst 0).logSize) r 0) := rfl

theorem site_hdr_vals {inst : ℕ → Inst} {pub : ℕ → F} {r : ℕ} :
    siteVals sys inst pub (0, r, 0) =
      (cst 0 :: relHeight :: hashLimbs).map (·.eval (2 ^ (inst 0).logSize) HeaderChain.preCols pub (inst 0).main r) := rfl

theorem site_tree_mult {inst : ℕ → Inst} {pub : ℕ → F} {r k : ℕ} (hk : k < 3) :
    siteMult sys inst pub (1, r, k) = (treeLookups.getD k ⟨0, .const 0, []⟩).mult.eval (2 ^ (inst 1).logSize)
      Blake2s.preCols pub (inst 1).main r := by
  interval_cases k <;> rfl

theorem site_tree_vals {inst : ℕ → Inst} {pub : ℕ → F} {r k : ℕ} (hk : k < 3) :
    siteVals sys inst pub (1, r, k) = (treeLookups.getD k ⟨0, .const 0, []⟩).vals.map
      (·.eval (2 ^ (inst 1).logSize) Blake2s.preCols pub (inst 1).main r) := by
  interval_cases k <;> rfl

theorem site_rel {inst : ℕ → Inst} {s : Site} (hs : s ∈ sites sys inst) : siteRel sys s = REL_NODE := by
  obtain ⟨i, r, k⟩ := s
  have := sites_mem.mp hs
  simp only at this
  rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
  · have : k = 0 := by simpa [sys, headers] using this.2.2
    subst this; rfl
  · have : k < 3 := by simpa [sys, tree, treeLookups] using this.2.2
    interval_cases k <;> rfl

theorem limbsOf_inj {a b : Spec.Sha256.State} (h : limbsOf a = limbsOf b) : a = b := by
  have hw : ∀ k < 8, stWord a k = stWord b k := by
    intro k hk
    have get : ∀ hh ≤ 1, Sha256.half16 (stWord a k) hh = Sha256.half16 (stWord b k) hh := by
      intro hh hh1
      have := congrArg (fun l => l.getD (2 * k + hh) 0) h
      simp only [limbsOf_get (show 2 * k + hh < 16 by omega), show (2 * k + hh) / 2 = k by omega,
        show (2 * k + hh) % 2 = hh by omega] at this
      exact natCast_inj_of_lt (lt_trans (Sha256.half16_lt _ _) (by norm_num [P]))
        (lt_trans (Sha256.half16_lt _ _) (by norm_num [P])) this
    apply BitVec.eq_of_toNat_eq
    rw [Sha256.half16_split (stWord a k), Sha256.half16_split (stWord b k), get 0 (by norm_num), get 1 (by norm_num)]
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩ := a
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩ := b
  have := hw 0 (by norm_num); have := hw 1 (by norm_num); have := hw 2 (by norm_num); have := hw 3 (by norm_num)
  have := hw 4 (by norm_num); have := hw 5 (by norm_num); have := hw 6 (by norm_num); have := hw 7 (by norm_num)
  simp_all [stWord]

/-- Header `i`'s block hash (the leaf at position `i`). -/
abbrev leafHash (inst : ℕ → Inst) (i : ℕ) : Spec.Sha256.State := HeaderChain.hashAt (inst 0).main i

theorem msgLimbs_eval {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r half : ℕ} (hr : r < n) :
    (msgLimbs half).map (·.eval n Blake2s.preCols pub M r) =
      (List.range 16).map (fun j => M (ML (8 * half + j / 2) (j % 2)) r) := by
  unfold msgLimbs; rw [List.map_map]; apply List.map_congr_left; intro j _
  simp [Sha256.eval_col, wrap_zero hr]

/-- **Header tree soundness.** If the system (headers, tree) with `2^L` rows per component is
satisfied and balanced together with the public entry `node(L − 8, 0, x)`, then `x` is the limbs of
the perfect Blake2s tree root over the segment's `2^(L−8)` block hashes, in order. -/
theorem tree_root_limbs {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ} {x : List F}
    (h0L : (inst 0).logSize = L) (h1L : (inst 1).logSize = L) (hL : 8 ≤ L) (hL28 : L ≤ 28)
    (hsat : sys.SatisfiedExt inst pub [(REL_NODE, ((L - 8 : ℕ) : F) :: 0 :: x, -1)]) :
    x = limbsOf (rootAt (leafHash inst) (L - 8) 0) := by
  obtain ⟨hcomp, hb⟩ := hsat
  have hh : HeaderChain.air.Satisfied L pub (inst 0).main := by
    have := hcomp 0 (by decide); rw [h0L] at this; exact this
  have ht : ∀ r < 2 ^ L, ∀ c ∈ treeConstraints, c.eval (2 ^ L) Blake2s.preCols pub (inst 1).main r = 0 := by
    have := hcomp 1 (by decide); rw [h1L] at this; exact this
  set K := L - 8 with hKdef
  have hK : 2 ^ L = 256 * 2 ^ K := by
    rw [show L = 8 + K by omega, pow_add]; norm_num
  have hPL : 4 * 2 ^ L + 1 < P := by
    have : 2 ^ L ≤ 2 ^ 28 := Nat.pow_le_pow_right (by norm_num) hL28
    unfold P; omega
  -- Uses: the tree's two child lookups, multiplicity −1 at period starts, else 0.
  have hinit : ∀ r < 2 ^ L, (pre (P_INIT 0)).eval (2 ^ L) Blake2s.preCols pub (inst 1).main r =
      if r % 88 = 0 then 1 else 0 := fun r hr => by
    rw [tree_pre ht hr (by simp [P_INIT]), Blake2s.bPre_INIT (by norm_num) (by simp [PERIOD]; omega)]
  have huse : ∀ s ∈ sites sys inst, (s.1 = 1 ∧ s.2.2 < 2) →
      siteMult sys inst pub s = -1 ∨ siteMult sys inst pub s = 0 := by
    rintro ⟨i, r, k⟩ hs ⟨rfl, hk⟩
    simp only at hk
    have hr := (sites_mem.mp hs).2.1
    simp only [h1L] at hr
    rw [site_tree_mult (by omega), h1L]
    have : (treeLookups.getD k ⟨0, .const 0, []⟩).mult = .neg (pre (P_INIT 0)) := by
      interval_cases k <;> rfl
    rw [this]
    simp only [Expr.eval, hinit r hr]
    split_ifs <;> simp
  have hcount : ((sites sys inst).filter fun s => s.1 = 1 ∧ s.2.2 < 2).length +
      [(REL_NODE, ((L - 8 : ℕ) : F) :: 0 :: x, (-1 : F))].length < P := by
    have := List.length_filter_le (fun s : Site => decide (s.1 = 1 ∧ s.2.2 < 2)) (sites sys inst)
    rw [sites_length h0L h1L] at this
    simp only [List.length_singleton]; omega
  have mem := fun {R : ℕ} {v : List F} (h0 : _) =>
    used_in_table_ext hb (use := fun i k => i = 1 ∧ k < 2) huse (by simp) hcount (R := R) (v := v) h0
  have hPbig : ∀ a < 2 ^ 30, a < P := fun a ha => by unfold P; omega
  have hKL : 2 ^ K ≤ 2 ^ 20 := by rw [hKdef]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  -- Facts about table sites with nonzero multiplicity.
  have hdr : ∀ r < 2 ^ L, siteMult sys inst pub (0, r, 0) ≠ 0 → ∃ j : ℕ, 256 * (j + 1) ≤ 2 ^ L ∧
      siteVals sys inst pub (0, r, 0) = (0 : F) :: (j : F) :: limbsOf (leafHash inst j) := by
    intro r hr hm
    rw [site_hdr_mult, h0L, HeaderChain.eval_oneRow (show HeaderChain.preCols.getD (HeaderChain.OUT0 + 3) (.periodic [0]) =
      HeaderChain.oneRow 215 from rfl) hr] at hm
    have h215 : r % 256 = 215 := by by_contra h; simp [h] at hm
    obtain ⟨j, rfl⟩ : ∃ j, r = 256 * j + 215 := ⟨r / 256, by omega⟩
    refine ⟨j, by omega, ?_⟩
    rw [site_hdr_vals, h0L]
    simp only [List.map_cons, Sha256.eval_cst, Nat.cast_zero, relHeight_eval hh hL (j := j) (by omega),
      hashLimbs_eval hh hL (j := j) (by omega)]
  have tyield : ∀ r < 2 ^ L, siteMult sys inst pub (1, r, 2) ≠ 0 → r % 88 = 87 := by
    intro r hr hm
    rw [site_tree_mult (by norm_num), h1L] at hm
    simp only [treeLookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval] at hm
    rw [tree_pre ht hr (by simp [P_FIN]), Blake2s.bPre_FIN (by norm_num) (by simp [PERIOD]; omega)] at hm
    by_contra h; simp [show ¬ r % 88 = 84 + 3 by omega] at hm
  have hcast0 : ∀ a : ℕ, a < P → (0 : F) = (a : F) → a = 0 := fun a ha h =>
    (natCast_inj_of_lt (by unfold P; norm_num) ha (by simpa using h)).symm
  -- Every looked-up node at level ℓ ≤ K, position p < 2^(K−ℓ) holds its subtree root.
  have claim : ∀ ℓ : ℕ, ℓ ≤ K → ∀ p : ℕ, p < 2 ^ (K - ℓ) → ∀ x : List F,
      (∃ s ∈ sites sys inst, ¬ (s.1 = 1 ∧ s.2.2 < 2) ∧ siteMult sys inst pub s ≠ 0 ∧ siteRel sys s = REL_NODE ∧
        siteVals sys inst pub s = (ℓ : F) :: (p : F) :: x) → x = limbsOf (rootAt (leafHash inst) ℓ p) := by
    intro ℓ
    induction ℓ with
    | zero =>
      rintro - p hp x ⟨⟨i, r, k⟩, hs, hnu, hm, -, hv⟩
      simp only [Nat.sub_zero] at hp
      obtain ⟨hi, hr, hk⟩ := sites_mem.mp hs
      simp only at hi hr hk hnu
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · have hk0 : k = 0 := by simpa [sys, headers] using hk
        subst hk0
        rw [h0L] at hr
        obtain ⟨j, hj, hvj⟩ := hdr r hr hm
        rw [hvj] at hv
        simp only [List.cons.injEq] at hv
        obtain ⟨-, hjp, hx⟩ := hv
        have hjK : j < 2 ^ K := by omega
        have : j = p := natCast_inj_of_lt (hPbig j (by omega)) (hPbig p (by omega)) hjp
        subst this
        rw [← hx]; rfl
      · have hk3 : k < 3 := by simpa [sys, tree, treeLookups] using hk
        have hk2 : k = 2 := by omega
        subst hk2
        rw [h1L] at hr
        rw [site_tree_vals (by norm_num), h1L] at hv
        simp only [treeLookups, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.cons.injEq,
          Sha256.eval_col, wrap_zero hr, Nat.cast_zero] at hv
        exact absurd hv.1 (level_ne ht hr)
    | succ ℓ ih =>
      rintro hℓ p hp x ⟨⟨i, r, k⟩, hs, hnu, hm, -, hv⟩
      obtain ⟨hi, hr, hk⟩ := sites_mem.mp hs
      simp only at hi hr hk hnu
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · have hk0 : k = 0 := by simpa [sys, headers] using hk
        subst hk0
        rw [h0L] at hr
        obtain ⟨j, hj, hvj⟩ := hdr r hr hm
        rw [hvj] at hv
        simp only [List.cons.injEq] at hv
        have := hcast0 (ℓ + 1) (hPbig _ (by omega)) hv.1
        omega
      · have hk3 : k < 3 := by simpa [sys, tree, treeLookups] using hk
        have hk2 : k = 2 := by omega
        subst hk2
        rw [h1L] at hr
        have h87 := tyield r hr hm
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 87 := ⟨r - 87, by omega⟩
        have hs0 : s % PERIOD = 0 := by simp only [PERIOD]; omega
        have hsn : s + PERIOD ≤ 2 ^ L := by simp only [PERIOD]; omega
        have hsL : s < 2 ^ L := by omega
        rw [site_tree_vals (by norm_num), h1L] at hv
        simp only [treeLookups, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, List.cons.injEq,
          Sha256.eval_col, wrap_zero hr] at hv
        obtain ⟨hlvl, hpos, hx⟩ := hv
        rw [level_copy ht hs0 hsn LVL (Or.inl rfl) 87 (by simp [PERIOD])] at hlvl
        rw [level_copy ht hs0 hsn POS (Or.inr rfl) 87 (by simp [PERIOD])] at hpos
        rw [outLimbs_eval ht hs0 hsn] at hx
        -- The two children, looked up at the period's first row.
        have child : ∀ c < 2, ∃ y, y = (List.range 16).map (fun j => (inst 1).main (ML (8 * c + j / 2) (j % 2)) s) ∧
            y = limbsOf (rootAt (leafHash inst) ℓ (2 * p + c)) := by
          intro c hc
          refine ⟨_, rfl, ?_⟩
          have hmem : ((1, s, c) : Site) ∈ sites sys inst := sites_mem.mpr ⟨by norm_num, by rw [h1L]; exact hsL,
            by simp [sys, tree, treeLookups]; omega⟩
          have hmult : siteMult sys inst pub (1, s, c) = -1 := by
            rw [site_tree_mult (by omega), h1L]
            have : (treeLookups.getD c ⟨0, .const 0, []⟩).mult = .neg (pre (P_INIT 0)) := by
              interval_cases c <;> rfl
            rw [this]; simp only [Expr.eval, hinit s hsL, show s % 88 = 0 by simp only [PERIOD] at hs0; omega, if_true]
          have hvals : siteVals sys inst pub (1, s, c) =
              (ℓ : F) :: ((2 * p + c : ℕ) : F) :: (List.range 16).map (fun j => (inst 1).main (ML (8 * c + j / 2) (j % 2)) s) := by
            rw [site_tree_vals (by omega), h1L]
            interval_cases c <;>
              simp only [treeLookups, List.getD_cons_succ, List.getD_cons_zero, List.map_cons, Expr.eval,
                Sha256.eval_col, Sha256.eval_cst, wrap_zero hsL, hlvl, hpos, msgLimbs_eval hsL] <;> push_cast <;> ring_nf
          obtain ⟨s', hs', hnu', hm', hrel', hv'⟩ := mem (R := REL_NODE)
            (v := (ℓ : F) :: ((2 * p + c : ℕ) : F) :: (List.range 16).map (fun j => (inst 1).main (ML (8 * c + j / 2) (j % 2)) s))
            (Or.inl ⟨(1, s, c), hmem, ⟨rfl, hc⟩, hmult, site_rel hmem, hvals⟩)
          exact ih (by omega) (2 * p + c) (by
              have : 2 ^ (K - ℓ) = 2 * 2 ^ (K - (ℓ + 1)) := by
                rw [show K - ℓ = (K - (ℓ + 1)) + 1 by omega, pow_succ]; ring
              omega) _ ⟨s', hs', hnu', hm', hrel', hv'⟩
        obtain ⟨yl, hyl, hyl'⟩ := child 0 (by norm_num)
        obtain ⟨yr, hyr, hyr'⟩ := child 1 (by norm_num)
        rw [hyl'] at hyl; rw [hyr'] at hyr
        simp only [Nat.add_zero] at hyl
        rw [← hx, node_step ht hs0 hsn hyl.symm hyr.symm]
        rfl
  obtain ⟨s, hs, hnu, hm, -, hv⟩ := mem (R := REL_NODE) (v := ((L - 8 : ℕ) : F) :: 0 :: x)
    (Or.inr (List.mem_singleton_self _))
  exact claim K le_rfl 0 (by positivity) x ⟨s, hs, hnu, hm, site_rel hs, by rw [hv]; simp [hKdef]⟩

/-- `tree_root_limbs` for an entry given as a root `T`. -/
theorem tree_root_sound {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ} {T : Spec.Sha256.State}
    (h0L : (inst 0).logSize = L) (h1L : (inst 1).logSize = L) (hL : 8 ≤ L) (hL28 : L ≤ 28)
    (hsat : sys.SatisfiedExt inst pub [(REL_NODE, ((L - 8 : ℕ) : F) :: 0 :: limbsOf T, -1)]) :
    T = rootAt (leafHash inst) (L - 8) 0 :=
  limbsOf_inj (tree_root_limbs h0L h1L hL hL28 hsat)

end System

end StarkedAir.HeaderTree
