/-
**Aggregation soundness, at the level of public inputs.** A recursion node verifies two child
proofs with public inputs `pL`, `pR`, checks `PubLink pL pR` (the right child continues the left
one) and outputs `combine pL pR` (left's input state, right's output state). `pub_compose` shows
validity is preserved, `leaf_valid` shows every header-chain trace yields valid public inputs, and
`chain_from_genesis` reads off the guarantee at the root. `PubLink` lists exactly the checks the
node circuit makes (`src/recursion/node.zig`), so the two can be compared line by line.
-/
import StarkedAir.Gadgets.TopSound
import StarkedAir.Spec.Compose

namespace StarkedAir.HeaderChain

open StarkedAir StarkedAir.Sha256 StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

/-- Input-work limbs are 16-bit (the obligation of `header_chain_sound`). -/
def WorkInOk (p : ℕ → F) : Prop := ∀ l < 10, (p (88 + l)).val < 65536

/-- Output-work limbs are 16-bit. -/
def WorkOutOk (p : ℕ → F) : Prop := ∀ l < 10, (p (98 + l)).val < 65536

/-- **Proven public inputs.** If the input-work limbs are 16-bit, the output-work limbs are too,
and some headers form a valid segment from `p`'s input state to its output state, for every
real window that matches `p`'s window inputs. -/
def PubValid (p : ℕ → F) : Prop :=
  WorkInOk p → WorkOutOk p ∧ ∃ H hs, ∀ w : List ℕ, pubWindow p = (w ++ sentinel).take 11 →
    SegmentValid H hs (decodeIn p w) (decodeOut p)

/-- The indices of the input state: prev-hash, height, prev nBits and pst, prev time, MTP
window, work. All others are the output state. -/
def isIn (k : ℕ) : Bool :=
  k < 16 || (32 ≤ k && k < 38) || k == 44 || k == 45 || (48 ≤ k && k < 68) || (88 ≤ k && k < 98)

/-- The node's public inputs: the left child's input state and the right child's output state. -/
def combine (pL pR : ℕ → F) (k : ℕ) : F := if isIn k then pL k else pR k

/-- **The node's link checks**: the right child's input state equals the left child's output
state, limb by limb; the heights differ by one (16-bit limbs, carry `c`). -/
def PubLink (pL pR : ℕ → F) : Prop :=
  (∀ k < 16, pR k = pL (16 + k)) ∧
  pR 34 = pL 40 ∧ pR 35 = pL 41 ∧ pR 36 = pL 42 ∧ pR 37 = pL 43 ∧ pR 44 = pL 46 ∧ pR 45 = pL 47 ∧
  (∀ k < 20, pR (48 + k) = pL (68 + k)) ∧
  (∀ l < 10, pR (88 + l) = pL (98 + l)) ∧
  (pR 32).val < 65536 ∧ (pR 33).val < 65536 ∧ (pL 38).val < 65536 ∧ (pL 39).val < 65536 ∧
  ∃ c : F, (c = 0 ∨ c = 1) ∧ pR 32 = pL 38 + 1 - 65536 * c ∧ pR 33 = pL 39 + c

theorem comb_in {pL pR : ℕ → F} {k : ℕ} (h : isIn k = true) : combine pL pR k = pL k := by
  simp [combine, h]

theorem comb_out {pL pR : ℕ → F} {k : ℕ} (h : isIn k = false) : combine pL pR k = pR k := by
  simp [combine, h]

theorem decodeIn_combine (pL pR : ℕ → F) (w : List ℕ) : decodeIn (combine pL pR) w = decodeIn pL w := by
  have hw : pubWork (combine pL pR) 88 = pubWork pL 88 := by
    unfold pubWork
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    rw [comb_in (by simp [isIn]; omega)]
  simp only [decodeIn, hw, pubState, pubWord, combine, isIn]
  norm_num

theorem decodeOut_combine (pL pR : ℕ → F) : decodeOut (combine pL pR) = decodeOut pR := by
  have hw : pubWork (combine pL pR) 98 = pubWork pR 98 := by
    unfold pubWork
    refine Finset.sum_congr rfl (fun l hl => ?_)
    rw [Finset.mem_range] at hl
    rw [comb_out (by simp [isIn]; omega)]
  have hwin : ((List.range 10).map fun k => leN (pubWord (combine pL pR) (68 + 2 * k))) =
      (List.range 10).map fun k => leN (pubWord pR (68 + 2 * k)) := by
    refine List.map_congr_left (fun k hk => ?_)
    rw [List.mem_range] at hk
    unfold pubWord
    rw [comb_out (by simp [isIn]; omega), comb_out (by simp [isIn]; omega)]
  simp only [decodeOut]
  rw [hw, hwin]
  simp only [pubState, pubWord, combine, isIn]
  norm_num

theorem pubWindow_combine (pL pR : ℕ → F) : pubWindow (combine pL pR) = pubWindow pL := by
  unfold pubWindow
  have e : ((List.range 10).map fun k => leN (pubWord (combine pL pR) (48 + 2 * k))) =
      (List.range 10).map fun k => leN (pubWord pL (48 + 2 * k)) := by
    refine List.map_congr_left (fun k hk => ?_)
    rw [List.mem_range] at hk
    unfold pubWord
    rw [comb_in (by simp [isIn]; omega), comb_in (by simp [isIn]; omega)]
  rw [e]; rfl

theorem workIn_combine {pL pR : ℕ → F} : WorkInOk (combine pL pR) ↔ WorkInOk pL := by
  unfold WorkInOk
  refine forall_congr' (fun l => imp_congr_right (fun hl => ?_))
  rw [comb_in (by simp [isIn]; omega)]

theorem workOut_combine {pL pR : ℕ → F} : WorkOutOk (combine pL pR) ↔ WorkOutOk pR := by
  unfold WorkOutOk
  refine forall_congr' (fun l => imp_congr_right (fun hl => ?_))
  rw [comb_out (by simp [isIn]; omega)]

/-- The limb-wise increment with carry is the numeric increment. -/
theorem limb_inc {a b c d k : F} (ha : a.val < 65536) (hb : b.val < 65536) (hc : c.val < 65536)
    (hd : d.val < 65536) (hk : k = 0 ∨ k = 1) (h1 : c = a + 1 - 65536 * k) (h2 : d = b + k) :
    c.val + 65536 * d.val = a.val + 65536 * b.val + 1 := by
  have hP : (P : ℕ) = 2147483647 := rfl
  rcases hk with rfl | rfl
  · simp only [mul_zero, sub_zero, add_zero] at h1 h2
    subst h1 h2
    rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by have := hP; omega)]
    ring
  · have ha' : a = c + 65535 := by rw [h1]; ring
    subst ha' h2
    have e1 : (c + 65535 : F).val = c.val + 65535 := by
      rw [ZMod.val_add, show ((65535 : F)).val = 65535 from rfl, Nat.mod_eq_of_lt (by have := hP; omega)]
    have e2 : (b + 1 : F).val = b.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt (by have := hP; omega)]
    rw [e1, e2]; ring

theorem pubWord_congr {p q : ℕ → F} {i j : ℕ} (h0 : p i = q j) (h1 : p (i + 1) = q (j + 1)) :
    pubWord p i = pubWord q j := by
  unfold pubWord; rw [h0, h1]

theorem prevTimes_succ (g : ℕ → ℕ → Word) (v : List ℕ) (n : ℕ) :
    prevTimes g v (n + 1) = timeOf (g n) :: prevTimes g v n := by
  simp [prevTimes, List.range_succ]

/-- **Composition.** A node over two proven children that passes the link checks has proven
public inputs. -/
theorem pub_compose {pL pR : ℕ → F} (vL : PubValid pL) (vR : PubValid pR) (l : PubLink pL pR) :
    PubValid (combine pL pR) := by
  obtain ⟨lhash, l34, l35, l36, l37, l44, l45, lwin, lwork, r32, r33, l38, l39, c, hc, h32, h33⟩ := l
  intro hin
  rw [workIn_combine] at hin
  obtain ⟨outL, H1, hs1, fL⟩ := vL hin
  have hinR : WorkInOk pR := fun k hk => by rw [lwork k hk]; exact outL k hk
  obtain ⟨outR, H2, hs2, fR⟩ := vR hinR
  refine ⟨workOut_combine.mpr outR, H1 + H2, catHs H1 hs1 hs2, fun w hw => ?_⟩
  rw [pubWindow_combine] at hw
  rw [decodeIn_combine, decodeOut_combine]
  have v1 := fL w hw
  obtain ⟨p1, -, -, -, tip1, -, oh1, -, -, -, -, nb1, time1, pst1, win1, -⟩ := v1
  -- The right child's window inputs are the left child's real window advanced by its headers.
  have hwR : pubWindow pR = (prevTimes hs1 w H1 ++ sentinel).take 11 := by
    have e : pubWindow pR = (decodeOut pL).time :: (decodeOut pL).window := by
      unfold pubWindow decodeOut
      dsimp only
      rw [pubWord_congr l44 l45]
      congr 1
      refine List.map_congr_left (fun k hk => ?_)
      rw [List.mem_range] at hk
      rw [pubWord_congr (lwin (2 * k) (by omega)) (by rw [show 48 + 2 * k + 1 = 48 + (2 * k + 1) by ring,
        show 68 + 2 * k + 1 = 68 + (2 * k + 1) by ring]; exact lwin (2 * k + 1) (by omega))]
    rw [e, time1, win1, show H1 = (H1 - 1) + 1 by omega, prevTimes_succ]
    simp only [List.cons_append, List.take_succ_cons]
    rfl
  have v2 := fR _ hwR
  refine segment_compose (fL w hw) v2 ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_⟩
  · show pubState pR 0 = (decodeOut pL).tip
    unfold pubState decodeOut
    dsimp only
    congr 1 <;> exact pubWord_congr (by rw [lhash _ (by norm_num)]) (by rw [lhash _ (by norm_num)])
  · show (pubWord pR 32).toNat = (pubWord pL 38).toNat + 1
    have e := limb_inc l38 l39 r32 r33 hc h32 h33
    unfold pubWord
    simp only [Nat.reduceAdd]
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, e, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · show leN (pubWord pR 34) = (decodeOut pL).nBits
    exact congrArg leN (pubWord_congr l34 l35)
  · show leN (pubWord pR 44) = (decodeOut pL).time
    exact congrArg leN (pubWord_congr l44 l45)
  · show leN (pubWord pR 36) = (decodeOut pL).pst
    exact congrArg leN (pubWord_congr l36 l37)
  · show pubWork pR 88 = pubWork pL 98
    unfold pubWork
    exact Finset.sum_congr rfl (fun k hk => by rw [lwork k (Finset.mem_range.mp hk)])

section Leaf

variable {logSize : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : air.Satisfied logSize pub main)
include hsat

/-- **Leaves.** The public inputs of any trace satisfying the header-chain AIR are proven. -/
theorem leaf_valid (hlog : 8 ≤ logSize) : PubValid pub := by
  intro hin
  have h256 : 256 ≤ 2 ^ logSize := by
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ logSize := Nat.pow_le_pow_right (by norm_num) hlog
  have hH : 0 < 2 ^ logSize / 256 := Nat.div_pos h256 (by norm_num)
  have hlast : 2 ^ logSize = 256 * (2 ^ logSize / 256 - 1 + 1) := by
    rw [Nat.sub_add_cancel hH]
    exact (Nat.mul_div_cancel' (by rw [show (256 : ℕ) = 2 ^ 8 by norm_num]; exact pow_dvd_pow 2 hlog)).symm
  refine ⟨fun l hl => ?_, _, _, fun w hw => header_chain_sound hsat hlog w hw hin⟩
  rw [w_out hsat (by omega) hlast hl]
  unfold wl
  have := fieldVal_lt main (2 ^ logSize / 256 - 1) wSlots 8 4 0 (2 * l)
  have := fieldVal_lt main (2 ^ logSize / 256 - 1) wSlots 8 4 0 (2 * l + 1)
  unfold wd
  omega

end Leaf

/-- **The root.** Proven public inputs whose input state is genesis' (no previous block, height
0, sentinel window, zero work) give a valid chain of headers from genesis to the decoded tip. -/
theorem chain_from_genesis {p : ℕ → F} (v : PubValid p)
    (hhash : ∀ k < 16, p k = 0) (hh : p 32 = 0 ∧ p 33 = 0) (hwin : pubWindow p = sentinel)
    (hwork : ∀ l < 10, p (88 + l) = 0) :
    ∃ H hs, SegmentValid H hs
      ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩
      (decodeOut p) ∧ pubState p 0 = pubState (fun _ => 0) 0 := by
  obtain ⟨-, H, hs, f⟩ := v (fun l hl => by rw [hwork l hl]; simp)
  refine ⟨H, hs, ?_, ?_⟩
  · have := f [] (by rw [hwin]; rfl)
    have e : decodeIn p [] = ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩ := by
      unfold decodeIn pubWork
      congr 1
      · unfold pubWord; rw [hh.1, hh.2]; rfl
      · exact Finset.sum_eq_zero (fun l hl => by rw [hwork l (Finset.mem_range.mp hl)]; simp)
    rwa [e] at this
  · unfold pubState pubWord
    simp only [hhash 0 (by norm_num), hhash 1 (by norm_num), hhash 2 (by norm_num), hhash 3 (by norm_num),
      hhash 4 (by norm_num), hhash 5 (by norm_num), hhash 6 (by norm_num), hhash 7 (by norm_num),
      hhash 8 (by norm_num), hhash 9 (by norm_num), hhash 10 (by norm_num), hhash 11 (by norm_num),
      hhash 12 (by norm_num), hhash 13 (by norm_num), hhash 14 (by norm_num), hhash 15 (by norm_num)]

end StarkedAir.HeaderChain
