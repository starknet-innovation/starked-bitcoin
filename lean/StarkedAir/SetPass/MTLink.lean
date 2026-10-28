/-
**The segment's Merkle tree in the system (D-050).** `set_mt`'s node yields carry the output limbs of a
used period (`mt_yield`); by strong induction from the bottom of the heap, a yield of node `j`
(`1 ≤ j < 2·HALF`) carries `node HALF ls j`'s words (`node_ok`), its children read from the tree's own
yields or from the leaves (`set_lc`'s yields, the hypothesis `hleaf`) and zero past the record count; the
public root is node 1's (`root_ok`).
-/
import StarkedAir.SetPass.MTSound
import StarkedAir.SetPass.Facts
import StarkedAir.Spec.SetMerkle
import StarkedAir.Circuit.NodeSound

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst half16)
open StarkedAir.Spec.HeaderTree (hnode stWord toState)
open StarkedAir.Blake2s (outWord msgWord)

namespace MT

/-- The word index node yield `k` (2–9) carries. -/
def widx (k : ℕ) : ℕ := if (k - 2) % 2 = 0 then (k - 2) / 2 else Block.B2s.bidx ((k - 2) / 2)

theorem widx_lt {k : ℕ} (h2 : 2 ≤ k) (h10 : k < 10) : widx k < 8 := by
  unfold widx; interval_cases k <;> decide

theorem pow2_mod88 : ∀ L : ℕ, 2 ^ L % 88 ≤ 80 := by
  have closed : ∀ x ∈ ({1, 2, 4, 8, 16, 32, 64, 40, 80, 72, 56, 24, 48} : Finset ℕ),
      (x * 2) % 88 ∈ ({1, 2, 4, 8, 16, 32, 64, 40, 80, 72, 56, 24, 48} : Finset ℕ) := by decide
  have key : ∀ L : ℕ, 2 ^ L % 88 ∈ ({1, 2, 4, 8, 16, 32, 64, 40, 80, 72, 56, 24, 48} : Finset ℕ) := by
    intro L
    induction L with
    | zero => decide
    | succ L ih =>
      rw [pow_succ, Nat.mul_mod, Nat.mod_eq_of_lt (show 2 < 88 by norm_num)]
      exact closed _ ih
  intro L
  have := key L
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

/-- A row in a period's final rows lies in a full period (`2^L mod 88 ≤ 80`). -/
theorem full_period {L r : ℕ} (hr : r < 2 ^ L) (h84 : 84 ≤ r % 88) : r - r % 88 + 88 ≤ 2 ^ L := by
  have := pow2_mod88 L
  by_contra hc
  have h1 : 2 ^ L - (r - r % 88) < 88 := by omega
  have h2 : (r - r % 88) % 88 = 0 := by omega
  have h3 : 2 ^ L % 88 = 2 ^ L - (r - r % 88) := by
    have : 2 ^ L = (r - r % 88) + (2 ^ L - (r - r % 88)) := by omega
    rw [this, Nat.add_mod, h2, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt h1]
    omega
  omega

/-- A message word from its limbs' halves. -/
theorem msgWord_halves {M : ℕ → ℕ → F} {kk s : ℕ} {X : Spec.Blake2s.Word}
    (h0 : M (Blake2s.ML kk 0) s = ((half16 X 0 : ℕ) : F)) (h1 : M (Blake2s.ML kk 1) s = ((half16 X 1 : ℕ) : F)) :
    msgWord M kk s = X := by
  have v : ∀ h, ((half16 X h : ℕ) : F).val = half16 X h := fun h =>
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (Sha256.half16_lt X h) (by unfold P; norm_num))
  unfold msgWord
  rw [h0, h1, v, v, ← Sha256.half16_split]
  simp

end MT

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
include hL hsat

omit hL hsat in
theorem mt_lk {r k : ℕ} : siteLookup segSys ((11, r, k) : Site) = MT.lookups.getD k ⟨0, .const 0, []⟩ := rfl

omit hsat in
theorem mt_ysite {r k : ℕ} (hr : r < 2 ^ Ls 11) (hk2 : 2 ≤ k) (hk10 : k < 10) :
    siteMult segSys inst pub (11, r, k) = (inst 11).main MT.USEW r *
      (MT.p (Blake2s.P_FIN ((k - 2) / 2))).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r ∧
    siteVals segSys inst pub (11, r, k) = [(inst 11).main MT.ID r, ((MT.widx k : ℕ) : F),
      (Blake2s.limb (if (k - 2) % 2 = 0 then 0 else 1) 0).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r,
      (Blake2s.limb (if (k - 2) % 2 = 0 then 0 else 1) 1).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r] := by
  have ev : ∀ c, (MT.k c).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r = (inst 11).main c r := fun c =>
    MT.ev_k (pub := pub) (M := (inst 11).main) hr
  interval_cases k <;>
    simp [siteMult, siteVals, siteEval, siteLookup, segSys, comps, hL 11 (by decide), MT.mt, MT.lookups, Expr.eval, ev,
      MT.widx, Block.B2s.bidx, StarkedAir.Sha256.eval_cst, MT.p, List.range_succ, List.flatMap_append]

/-- **A node yield** is a full used period's output word `widx k`, as limbs, with the period's `ID`. -/
theorem mt_yield {r k : ℕ} (hr : r < 2 ^ Ls 11) (hk2 : 2 ≤ k) (hk10 : k < 10)
    (hm : siteMult segSys inst pub (11, r, k) ≠ 0) :
    (r - r % 88) % 88 = 0 ∧ r - r % 88 + 88 ≤ 2 ^ Ls 11 ∧ (inst 11).main MT.USEW (r - r % 88) = 1 ∧
    siteVals segSys inst pub (11, r, k) = [(inst 11).main MT.ID (r - r % 88), ((MT.widx k : ℕ) : F),
      ((half16 (outWord (inst 11).main (r - r % 88) (MT.widx k)) 0 : ℕ) : F),
      ((half16 (outWord (inst 11).main (r - r % 88) (MT.widx k)) 1 : ℕ) : F)] := by
  have ms := mt_sat hL hsat
  obtain ⟨em, ev⟩ := mt_ysite hL (pub := pub) (inst := inst) hr hk2 hk10
  set j := (k - 2) / 2 with hj
  have hj4 : j < 4 := by omega
  set s' := r - r % 88 with hs'
  have hrs : r = s' + r % 88 := by omega
  have hfin : (MT.p (Blake2s.P_FIN j)).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r =
      if r % 88 = 84 + j then 1 else 0 := by
    rw [MT.p, MT.eval_pre_gadget (by simp [Blake2s.P_FIN]; omega)]
    conv_lhs => rw [hrs]
    rw [Blake2s.pre_at (s := s') (by simp [Blake2s.PERIOD]; omega) (by simp [Blake2s.PERIOD]; omega) (by omega)
      (by simp [Blake2s.P_FIN]; omega), Blake2s.bPre_FIN hj4 (by simp [Blake2s.PERIOD]; omega)]
  rw [em, hfin] at hm
  have h84 : r % 88 = 84 + j := by by_contra h; rw [if_neg h, mul_zero] at hm; exact hm rfl
  rw [if_pos h84, mul_one] at hm
  have hfull := MT.full_period hr (by omega)
  have hs88 : s' % 88 = 0 := by omega
  have hrow : r = s' + (84 + j) := by omega
  have hu : (inst 11).main MT.USEW r = 1 := (MT.bool_flag ms (c := MT.USEW) (by simp) hr).resolve_left hm
  have hus : (inst 11).main MT.USEW s' = 1 := by
    rw [← MT.usew_const ms hs88 (84 + j) (by omega) (by omega), ← hrow, hu]
  have hid : (inst 11).main MT.ID r = (inst 11).main MT.ID s' := by
    rw [hrow]; exact MT.per_const ms (by simp [MT.perConst]) hs88 _ (by omega) (by omega)
  refine ⟨hs88, hfull, hus, ?_⟩
  rw [ev, hid]
  have hbits := fun w (hw : w < 8) => MT.bits4 ms hr w hw
  have lim : ∀ w < 2, ∀ h ≤ 1, (Blake2s.limb w h).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r =
      ((half16 (Sha256.word (inst 11).main (32 * w) r) h : ℕ) : F) := by
    intro w hw h hh
    exact StarkedAir.Sha256.eval_limb (wrap_zero hr) (hbits w (by omega)) hh
  by_cases h0 : (k - 2) % 2 = 0
  · rw [if_pos h0, lim 0 (by norm_num) 0 (by norm_num), lim 0 (by norm_num) 1 (by norm_num)]
    have : Sha256.word (inst 11).main (32 * 0) r = outWord (inst 11).main s' (MT.widx k) := by
      rw [show MT.widx k = j by simp [MT.widx, h0, hj], outWord, if_pos hj4, hrow]; ring_nf
    rw [this]
  · rw [if_neg h0, lim 1 (by norm_num) 0 (by norm_num), lim 1 (by norm_num) 1 (by norm_num)]
    have hb : Block.B2s.bidx j < 8 ∧ 4 ≤ Block.B2s.bidx j ∧ (Block.B2s.bidx j + 3) % 4 = j := by
      interval_cases j <;> decide
    have : Sha256.word (inst 11).main (32 * 1) r = outWord (inst 11).main s' (MT.widx k) := by
      rw [show MT.widx k = Block.B2s.bidx j by simp [MT.widx, h0, hj], outWord, if_neg (by omega), hb.2.2, hrow]
      ring_nf
    rw [this]

end System

end StarkedAir.SetPass
