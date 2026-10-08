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

end StarkedAir.HeaderTree
