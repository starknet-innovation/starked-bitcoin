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

end Tree

end StarkedAir.HeaderTree
