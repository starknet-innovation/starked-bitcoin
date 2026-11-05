/-
**A set root opened in the seal, as a pass** (`ChainSeal.setOpen`, SEAL-LEAN).

The seal opens each set root child's 48 summary limbs to the pass's start vector (`inVec`: `begin(count)`
under the epoch's challenge) and final vector (`outVec`: the final state guessed at `n`). Here those
vectors are read as the public inputs `SetPass.set_root_sound` speaks of:
- `pbOf ρ chl cnt` (incoming) and `pfOf ρ chl n` (outgoing): public-input functions over the segment
  system's layout, from the seal's registers;
- `setOpen_summ`: the child's limbs are `summ2 pb pf R` (`R` its root limbs): the first 16 are the halves
  of Blake2s of `pb`'s incoming vector, the next 16 of `pf`'s outgoing one;
- `setOpen_begin`: `pb` encodes `begin 1 cnt` (`EncIn`), `cnt` the file's count from its 4 bytes, below
  `2^30`;
- `setOpen_out`: for any state `S` that `pf` encodes (`EncOut`): `S.i = cnt` (in the field), the Blake2s
  finish of `S`'s Blake2s state is the opening's `fin` (`hashBlocks`), and the end facts' words: the
  count, the highest height, the amount (3 words), the SHA-256 state's digest;
- `setOpen_mroot`: the Merkle root words are the root state's words.
-/
import StarkedAir.Circuit.ChainSealSound
import StarkedAir.SetPass.PassChainW

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q Spec.Blake2s
open StarkedAir.Circuit.SetTree (vecW withOne summ sd vals32 inIdx outIdx NV NP vec_digest pubsDigest_res_pack
  pubsDigest_length)
open StarkedAir.SetPass (summ2 EncIn EncOut EncB2 EncSha)
open StarkedAir.Spec.QM31 (QM toQ)
open StarkedAir.Circuit.BlockRec (H wordsOf_eq)
open StarkedAir.Circuit.EpochRoot (m2u_word)
open StarkedAir.HeaderTree (limbsOf)

variable {ρ : ℕ → Q}

/-! ### The opening's pieces -/

/-- A set opening's inputs. -/
structure SOIn where
  n : ℕ
  c : ChildRegs
  chl : List ℕ
  e : ℕ
  C : Consts

section
variable (I : SOIn)

def oSt : Out StRegs := stateOpen I.n I.e
def oBy : Out Unit := bytes (oSt I).next I.C.c256 ((oSt I).res.amt ++ (oSt I).res.cnt ++ (oSt I).res.pend)
def oCnt : Out ℕ := count (oBy I).next (oSt I).res.cnt I.C
def oDout : Out (List ℕ) := pubsDigest (oCnt I).next [] (outVec I.chl (oSt I).res I.C)
def oEqOut : List Op := packEq (oDout I).next (fun k => I.c.pubs (16 + k)) (oDout I).res I.C
def oDin : Out (List ℕ) := pubsDigest ((oDout I).next + 16) [] (inVec I.chl (oSt I).res I.C)
def oEqIn : List Op := packEq (oDin I).next I.c.pubs (oDin I).res I.C
def oOh : Out (List ℕ) := oneHot65 ((oDin I).next + 16) (oSt I).res.plen I.C
def oLt : Out (List ℕ) := ltMask (oOh I).next (oOh I).res I.C
def oMk : Out (List ℕ) := mask (oLt I).next (oSt I).res.pend (oLt I).res
def oM : Out (List ℕ) := packBytes (oMk I).next (oMk I).res 16 I.C
def oH : Out (List ℕ) := packW (oM I).next (oSt I).res.b2h I.C
def oCt : Out (ℕ × ℕ) := counter (oH I).next (oSt I).res.nb (oSt I).res.plen I.C
def oFin : Out (List ℕ) := compressFinal (oCt I).next (oH I).res (oM I).res (oCt I).res.1 (oCt I).res.2
def oMr : Out (List ℕ) := packW (oFin I).next ((List.range 16).map fun k => I.c.pubs (32 + k)) I.C
def oSd : Out (List ℕ) := pubsDigest (oMr I).next [] (oSt I).res.sha
def oAw : Out (List ℕ) := packBytes (oSd I).next (oSt I).res.amt 3 I.C

theorem setOpen_ops : (setOpen I.n I.c I.chl I.e I.C).ops =
    (oSt I).ops ++ (oBy I).ops ++ (oCnt I).ops ++ [.eq (oSt I).res.i (oCnt I).res] ++ (oDout I).ops ++ oEqOut I ++
      (oDin I).ops ++ oEqIn I ++ (oOh I).ops ++ (oLt I).ops ++ (oMk I).ops ++ (oM I).ops ++ (oH I).ops ++
      (oCt I).ops ++ (oFin I).ops ++ (oMr I).ops ++ (oSd I).ops ++ (oAw I).ops ++
      [.m2u (oAw I).next (oCnt I).res, .m2u ((oAw I).next + 1) (oSt I).res.maxh] := rfl

theorem setOpen_res : (setOpen I.n I.c I.chl I.e I.C).res =
    ⟨(oSt I).res, (oCnt I).res, (oAw I).next, (oAw I).res, (oAw I).next + 1, (oMr I).res, (oSd I).res, (oFin I).res⟩ :=
  rfl

/-- The opening's parts hold separately. -/
structure OHolds (ρ : ℕ → Q) : Prop where
  st : Holds ρ (oSt I).ops
  by1 : Holds ρ (oBy I).ops
  cnt : Holds ρ (oCnt I).ops
  icnt : ρ (oSt I).res.i = ρ (oCnt I).res
  dout : Holds ρ (oDout I).ops
  eqOut : Holds ρ (oEqOut I)
  din : Holds ρ (oDin I).ops
  eqIn : Holds ρ (oEqIn I)
  oh : Holds ρ (oOh I).ops
  lt : Holds ρ (oLt I).ops
  msk : Holds ρ (oMk I).ops
  m : Holds ρ (oM I).ops
  h : Holds ρ (oH I).ops
  ct : Holds ρ (oCt I).ops
  fin : Holds ρ (oFin I).ops
  mr : Holds ρ (oMr I).ops
  sd : Holds ρ (oSd I).ops
  aw : Holds ρ (oAw I).ops
  cw : (Op.m2u (oAw I).next (oCnt I).res).holds ρ
  mw : (Op.m2u ((oAw I).next + 1) (oSt I).res.maxh).holds ρ

theorem setOpen_holds (h : Holds ρ (setOpen I.n I.c I.chl I.e I.C).ops) : OHolds I ρ := by
  rw [setOpen_ops] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩,
    h17⟩, h18⟩, h19⟩ := h
  exact ⟨h1, h2, h3, h4 _ List.mem_cons_self, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19 _ List.mem_cons_self, h19 _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩

end

/-! ### The final state's registers -/

theorem stateOpen_res (n e : ℕ) : (stateOpen n e).res =
    ⟨n, (List.range 36).map (n + 1 + ·), n + 37, (List.range 4).map (n + 38 + ·), (List.range 12).map (n + 42 + ·),
     (List.range 82).map (n + 54 + ·), (List.range 82).map (n + 136 + ·), (List.range 4).map (n + 218 + ·)⟩ := rfl

/-- Which final-state values are u16 (bytes, hash limbs). -/
def u16Kind (k : ℕ) : Prop := (42 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 70) ∨ k = 71 ∨ (72 ≤ k ∧ k < 136) ∨
    (136 ≤ k ∧ k < 152) ∨ k = 153 ∨ (154 ≤ k ∧ k < 222)

/-- **The final state's registers are base, the u16 ones below `2^16`.** -/
theorem stateOpen_base {n e : ℕ} (h : Holds ρ (stateOpen n e).ops) :
    ∀ k < NST, IsBase (ρ (n + k)) ∧ (u16Kind k → (ρ (n + k)).a.val < 65536) := by
  intro k hk
  have := h _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  by_cases hu : u16Kind k
  · have hd : decide ((42 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 70) ∨ k = 71 ∨ (72 ≤ k ∧ k < 136) ∨
        (136 ≤ k ∧ k < 152) ∨ k = 153 ∨ (154 ≤ k ∧ k < 222)) = true := decide_eq_true hu
    simp only [hd, if_true, Op.holds] at this
    exact ⟨this.1, fun _ => this.2⟩
  · have hd : decide ((42 ≤ k ∧ k < 54) ∨ (54 ≤ k ∧ k < 70) ∨ k = 71 ∨ (72 ≤ k ∧ k < 136) ∨
        (136 ≤ k ∧ k < 152) ∨ k = 153 ∨ (154 ≤ k ∧ k < 222)) = false := decide_eq_false hu
    simp only [hd, Bool.false_eq_true, if_false, Op.holds] at this
    exact ⟨this, fun h => absurd h hu⟩

/-! ### The public-input functions -/

/-- **The incoming public values** (the start vector `inVec`): the challenge `chl`, Blake2s's `h0` halves,
pending length 4 and the count bytes `cnt`, SHA-256's IV halves; zero elsewhere. -/
noncomputable def pbOf (ρ : ℕ → Q) (chl cnt : List ℕ) (k : ℕ) : F :=
  if 41 ≤ k ∧ k < 153 then (ρ (chl.getD (k - 41) 0)).a
  else if 222 ≤ k ∧ k < 238 then (((b2ivWords.flatMap halves).getD (k - 222) 0 : ℕ) : F)
  else if k = 239 then 4
  else if 240 ≤ k ∧ k < 244 then (ρ (cnt.getD (k - 240) 0)).a
  else if 386 ≤ k ∧ k < 402 then (((shaIvWords.flatMap halves).getD (k - 386) 0 : ℕ) : F)
  else 0

/-- **The outgoing public values** (the final vector `outVec`): the challenge `chl`, then the final state
at `n` (`stateOpen n e`); zero elsewhere. -/
noncomputable def pfOf (ρ : ℕ → Q) (chl : List ℕ) (n : ℕ) (k : ℕ) : F :=
  if 41 ≤ k ∧ k < 153 then (ρ (chl.getD (k - 41) 0)).a
  else if k = 2 then (ρ n).a
  else if 186 ≤ k ∧ k < 222 then (ρ (n + 1 + (k - 186))).a
  else if k = 161 then (ρ (n + 37)).a
  else if 157 ≤ k ∧ k < 161 then (ρ (n + 38 + (k - 157))).a
  else if 174 ≤ k ∧ k < 186 then (ρ (n + 42 + (k - 174))).a
  else if 304 ≤ k ∧ k < 386 then (ρ (n + 54 + (k - 304))).a
  else if 468 ≤ k ∧ k < 550 then (ρ (n + 136 + (k - 468))).a
  else 0

/-! ### The vectors -/

theorem vecW_append (q : ℕ → F) (a b : List ℕ) : vecW q (a ++ b) = vecW q a ++ vecW q b := by
  simp [vecW]

theorem vecW_range (q : ℕ → F) (m : ℕ) (f : ℕ → ℕ) :
    vecW q ((List.range m).map f) = (List.range m).map fun j => BitVec.ofNat 32 (q (f j)).val := by
  simp [vecW]

theorem vecW_list (q : ℕ → F) (l : List ℕ) {m : ℕ} (hl : l.length = m) :
    vecW q l = (List.range m).map fun j => BitVec.ofNat 32 (q (l.getD j 0)).val := by
  apply List.ext_getElem (by simp [vecW, hl])
  intro i h1 h2
  have hi : i < l.length := by simpa [vecW] using h1
  simp only [vecW, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ hi]

theorem replicate_range (m x : ℕ) : List.replicate m x = (List.range m).map fun _ => x := by simp

theorem chal_eq : SetTree.chal = (List.range 112).map (41 + ·) := rfl

theorem app_congr {α : Type} {a b c d : List α} (h1 : a = c) (h2 : b = d) : a ++ b = c ++ d := by rw [h1, h2]

section
variable {chl : List ℕ} {n t : ℕ}

theorem pfOf_ch (ht : t < 112) : pfOf ρ chl n (41 + t) = (ρ (chl.getD t 0)).a := by
  unfold pfOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pfOf_i : pfOf ρ chl n 2 = (ρ n).a := by unfold pfOf; split_ifs <;> first | omega | rfl
theorem pfOf_last (ht : t < 36) : pfOf ρ chl n (186 + t) = (ρ (n + 1 + t)).a := by
  unfold pfOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pfOf_maxh : pfOf ρ chl n 161 = (ρ (n + 37)).a := by unfold pfOf; split_ifs <;> first | omega | rfl
theorem pfOf_sum (ht : t < 4) : pfOf ρ chl n (157 + t) = (ρ (n + 38 + t)).a := by
  unfold pfOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pfOf_amt (ht : t < 12) : pfOf ρ chl n (174 + t) = (ρ (n + 42 + t)).a := by
  unfold pfOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pfOf_b2 (ht : t < 82) : pfOf ρ chl n (304 + t) = (ρ (n + 54 + t)).a := by
  unfold pfOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pfOf_sha (ht : t < 82) : pfOf ρ chl n (468 + t) = (ρ (n + 136 + t)).a := by
  unfold pfOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]

theorem withOne_of {p : ℕ → F} {k : ℕ} (h : k ≠ 567) : withOne p k = p k := by
  simp [withOne, NP, h]

end

/-- **The outgoing vector's words are `pf`'s** (with the constant 1 at `NP`). -/
theorem outVec_words {chl : List ℕ} {n e : ℕ} {C : Consts} (hC : ConstsOk ρ C) (hl : chl.length = 112) :
    vecW (fun r => (ρ r).a) (outVec chl (stateOpen n e).res C) = vecW (withOne (pfOf ρ chl n)) outIdx := by
  have one : (ρ C.one).a = 1 := by rw [hC.one]; rfl
  simp only [outVec, stateOpen_res, outIdx, chal_eq, vecW_append, List.append_assoc]
  rw [vecW_list _ chl hl]
  simp only [vecW_range]
  refine app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ ?_))))))
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [withOne_of (by omega), pfOf_ch ht]
  · simp only [vecW, List.map_cons, List.map_nil, withOne_of (show 2 ≠ 567 by omega), pfOf_i]
    simp [withOne, one]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [withOne_of (by omega), pfOf_last ht]
  · simp only [vecW, List.map_cons, List.map_nil, withOne_of (show 161 ≠ 567 by omega), pfOf_maxh]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [withOne_of (by omega), pfOf_sum ht]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [withOne_of (by omega), pfOf_amt ht]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [withOne_of (by omega), pfOf_b2 ht]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [withOne_of (by omega), pfOf_sha ht]

theorem getD_app_lt {l l' : List ℕ} {k : ℕ} (h : k < l.length) : (l ++ l').getD k 0 = l.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_app_ge {l l' : List ℕ} {k : ℕ} (h : l.length ≤ k) : (l ++ l').getD k 0 = l'.getD (k - l.length) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

/-- The start vector's Blake2s block: `h0`'s halves, `0`, `4`, the count bytes, zeros. -/
def b2g (C : Consts) (cnt : List ℕ) : List ℕ := C.b2iv ++ [C.zero, C.four] ++ cnt ++ List.replicate 60 C.zero
/-- The start vector's SHA-256 block: the IV's halves, zeros. -/
def shag (C : Consts) : List ℕ := C.shaiv ++ [C.zero, C.zero] ++ List.replicate 64 C.zero

theorem inVec_split (chl : List ℕ) (s : StRegs) (C : Consts) : inVec chl s C =
    chl ++ [C.zero, C.zero] ++ List.replicate 36 C.zero ++ [C.zero] ++ List.replicate 4 C.zero ++
      List.replicate 12 C.zero ++ b2g C s.cnt ++ shag C := rfl

section
variable {chl cnt : List ℕ} {t : ℕ}

theorem pbOf_ch (ht : t < 112) : pbOf ρ chl cnt (41 + t) = (ρ (chl.getD t 0)).a := by
  unfold pbOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pbOf_zero {k : ℕ} (h1 : ¬ (41 ≤ k ∧ k < 153)) (h2 : ¬ (222 ≤ k ∧ k < 238)) (h3 : k ≠ 239)
    (h4 : ¬ (240 ≤ k ∧ k < 244)) (h5 : ¬ (386 ≤ k ∧ k < 402)) : pbOf ρ chl cnt k = 0 := by
  unfold pbOf; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
theorem pbOf_b2iv (ht : t < 16) : pbOf ρ chl cnt (222 + t) = (((b2ivWords.flatMap halves).getD t 0 : ℕ) : F) := by
  unfold pbOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pbOf_four : pbOf ρ chl cnt 239 = 4 := by unfold pbOf; split_ifs <;> first | omega | rfl
theorem pbOf_cnt (ht : t < 4) : pbOf ρ chl cnt (240 + t) = (ρ (cnt.getD t 0)).a := by
  unfold pbOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]
theorem pbOf_shaiv (ht : t < 16) : pbOf ρ chl cnt (386 + t) = (((shaIvWords.flatMap halves).getD t 0 : ℕ) : F) := by
  unfold pbOf; split_ifs <;> first | omega | simp only [Nat.add_sub_cancel_left]

end

theorem lit_a (a b c d : ℕ) : (lit a b c d).a = (a : F) := rfl

/-- **The incoming vector's words are `pb`'s.** -/
theorem inVec_words {chl : List ℕ} {n e : ℕ} {C : Consts} (hC : ConstsOk ρ C) (hl : chl.length = 112)
    (hb2 : C.b2iv.length = 16) (hsh : C.shaiv.length = 16) :
    vecW (fun r => (ρ r).a) (inVec chl (stateOpen n e).res C) =
      vecW (pbOf ρ chl ((List.range 4).map (n + 218 + ·))) inIdx := by
  have zero : (ρ C.zero).a = 0 := by rw [hC.zero, lit_a]; simp
  have four : (ρ C.four).a = 4 := by rw [hC.four, lit_a]; simp
  set cnt := (List.range 4).map (n + 218 + ·) with hcnt
  have hcl : cnt.length = 4 := by simp [hcnt]
  have hs : (stateOpen n e).res.cnt = cnt := rfl
  rw [inVec_split, hs]
  simp only [inIdx, chal_eq, vecW_append, List.append_assoc]
  rw [vecW_list _ chl hl]
  simp only [vecW_range, replicate_range]
  refine app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ (app_congr ?_ ?_))))))
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [pbOf_ch ht]
  · simp only [vecW, List.map_cons, List.map_nil, zero]
    rw [pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega),
      pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [zero, pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
  · simp only [vecW, List.map_cons, List.map_nil, zero]
    rw [pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [zero, pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
  · apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    rw [zero, pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [vecW_list (m := 82) _ (b2g C cnt) (by simp [b2g, hb2, hcl])]
    apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    congr 2
    unfold b2g
    by_cases h16 : t < 16
    · rw [getD_app_lt (by simp [hb2, hcl]; omega), getD_app_lt (by simp [hb2]; omega), getD_app_lt (by simp [hb2]; omega),
        hC.b2iv t h16, lit_a, pbOf_b2iv h16]
    by_cases h18 : t < 18
    · rw [getD_app_lt (by simp [hb2, hcl]; omega), getD_app_lt (by simp [hb2]; omega), getD_app_ge (by simp [hb2]; omega)]
      simp only [hb2]
      rcases (by omega : t = 16 ∨ t = 17) with rfl | rfl
      · simp only [show 16 - 16 = 0 by rfl, List.getD_cons_zero, zero]
        rw [pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
      · simp only [show 17 - 16 = 1 by rfl, List.getD_cons_succ, List.getD_cons_zero, four]
        rw [show 222 + 17 = 239 by rfl, pbOf_four]
    by_cases h22 : t < 22
    · rw [getD_app_lt (by simp [hb2, hcl]; omega), getD_app_ge (by simp [hb2]; omega)]
      simp only [List.length_append, hb2, List.length_cons, List.length_nil]
      rw [show 222 + t = 240 + (t - 18) by omega, pbOf_cnt (by omega)]
    · rw [getD_app_ge (by simp [hb2, hcl]; omega)]
      simp only [List.length_append, hb2, hcl, List.length_cons, List.length_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega), Option.getD_some, zero,
        pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
  · rw [vecW_list (m := 82) _ (shag C) (by simp [shag, hsh])]
    apply List.map_congr_left; intro t ht; simp only [List.mem_range] at ht
    congr 2
    unfold shag
    by_cases h16 : t < 16
    · rw [getD_app_lt (by simp [hsh]; omega), getD_app_lt (by simp [hsh]; omega), hC.shaiv t h16, lit_a, pbOf_shaiv h16]
    by_cases h18 : t < 18
    · rw [getD_app_lt (by simp [hsh]; omega), getD_app_ge (by simp [hsh]; omega)]
      simp only [hsh]
      rw [pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]
      rcases (by omega : t = 16 ∨ t = 17) with rfl | rfl
      · simp only [show 16 - 16 = 0 by rfl, List.getD_cons_zero, zero]
      · simp only [show 17 - 16 = 1 by rfl, List.getD_cons_succ, List.getD_cons_zero, zero]
    · rw [getD_app_ge (by simp [hsh]; omega)]
      simp only [List.length_append, hsh, List.length_cons, List.length_nil]
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega), Option.getD_some, zero,
        pbOf_zero (by omega) (by omega) (by omega) (by omega) (by omega)]

/-! ### The summary -/

theorem limbs_of_pack {x : Q} {W : Word} {l0 l1 : F} (hx : x = pack W) (hq : x = ⟨l0, l1, 0, 0⟩) :
    l0 = ((Sha256.half16 W 0 : ℕ) : F) ∧ l1 = ((Sha256.half16 W 1 : ℕ) : F) := by
  rw [hx] at hq
  have ha := congrArg Q.a hq
  have hb := congrArg Q.b hq
  simp only [pack] at ha hb
  exact ⟨ha.symm, hb.symm⟩

/-- A digest's packed limbs: limb `j` of 16 is half `j % 2` of word `j / 2`. -/
theorem packed_half {n : ℕ} {idx : List ℕ} {q : ℕ → F} {limbs : ℕ → ℕ} {m : ℕ} {C : Consts}
    (hd : Holds ρ (pubsDigest n [] idx).ops) (hq : ∀ k ∈ idx, (ρ k).a = q k) (hl : 4 * idx.length < 2 ^ 32)
    (he : Holds ρ (packEq m limbs (pubsDigest n [] idx).res C)) (hC : ConstsOk ρ C)
    (hb : ∀ j < 16, IsBase (ρ (limbs j))) :
    ∀ j < 16, (ρ (limbs j)).a = SetTree.half (H (vecW q idx)) j := by
  intro j hj
  have hw : j / 2 < 8 := by omega
  have e := packEq_sound he hC hb (j / 2) hw
  have p := pubsDigest_res_pack hd (j / 2) hw
  have v := vec_digest hd hq hl (j / 2) hw
  obtain ⟨l0, l1⟩ := limbs_of_pack p e
  rw [v] at l0 l1
  simp only [SetTree.half]
  rcases Nat.mod_two_eq_zero_or_one j with h0 | h1
  · rw [h0, show j = 2 * (j / 2) by omega]
    rw [show 2 * (j / 2) / 2 = j / 2 by omega]; exact l0
  · rw [h1, show j = 2 * (j / 2) + 1 by omega]
    rw [show (2 * (j / 2) + 1) / 2 = j / 2 by omega]; exact l1

/-- **The child's summary limbs are `summ2 pb pf R`**: the halves of the start vector's digest, of the
final vector's digest, then the root limbs. -/
theorem setOpen_summ (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) (hl : I.chl.length = 112)
    (hb2 : I.C.b2iv.length = 16) (hsh : I.C.shaiv.length = 16) (hp : ∀ k < 48, IsBase (ρ (I.c.pubs k))) :
    ∀ k < 48, (ρ (I.c.pubs k)).a = summ2 (pbOf ρ I.chl ((List.range 4).map (I.n + 218 + ·))) (pfOf ρ I.chl I.n)
      (fun j => (ρ (I.c.pubs (32 + j))).a) k := by
  intro k hk
  have lin : (inVec I.chl (oSt I).res I.C).length = 331 := by
    have hc : (oSt I).res.cnt.length = 4 := rfl
    rw [inVec_split]
    simp only [b2g, shag, List.length_append, List.length_cons, List.length_nil, List.length_replicate, hl, hb2, hsh, hc]
  have lout : (outVec I.chl (oSt I).res I.C).length = 331 := by
    have e : (oSt I).res = (stateOpen I.n I.e).res := rfl
    rw [e, stateOpen_res]
    simp only [outVec, List.length_append, List.length_cons, List.length_nil, List.length_map, List.length_range, hl]
  have hin := packed_half (q := fun r => (ρ r).a) h.din (fun _ _ => rfl) (by rw [lin]; norm_num) h.eqIn hC
    (fun j hj => hp j (by omega))
  have hout := packed_half (q := fun r => (ρ r).a) h.dout (fun _ _ => rfl) (by rw [lout]; norm_num) h.eqOut hC
    (fun j hj => hp (16 + j) (by omega))
  rw [show oSt I = stateOpen I.n I.e from rfl, inVec_words hC hl hb2 hsh] at hin
  rw [show oSt I = stateOpen I.n I.e from rfl, outVec_words hC hl] at hout
  simp only [summ2, summ]
  by_cases h16 : k < 16
  · rw [if_pos h16, if_pos h16]; exact hin k h16
  by_cases h32 : k < 32
  · rw [if_neg h16, if_pos h32, if_neg h16, if_pos h32]
    have := hout (k - 16) (by omega)
    rw [show 16 + (k - 16) = k by omega] at this
    exact this
  · rw [if_neg h16, if_neg h32, show 32 + (k - 32) = k by omega]

/-! ### The bytes and the count -/

theorem getD_map_range {f : ℕ → ℕ} {m k : ℕ} (hk : k < m) : ((List.range m).map f).getD k 0 = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp

theorem pend_getD {n e k : ℕ} (hk : k < 64) : (stateOpen n e).res.pend.getD k 0 = n + 72 + k := by
  rw [StRegs.pend, stateOpen_res]
  simp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map, List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.getD_some]
  omega

/-- **The amount, count and pending bytes are bytes.** -/
theorem setOpen_bytes (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) :
    (∀ j < 12, (ρ (I.n + 42 + j)).a.val < 256) ∧ (∀ j < 4, (ρ (I.n + 218 + j)).a.val < 256) ∧
      (∀ j < 64, (ρ (I.n + 72 + j)).a.val < 256) := by
  have hb := stateOpen_base h.st
  have hs : (oSt I).res = (stateOpen I.n I.e).res := rfl
  have bs := bytes_sound h.by1 hC.c256
  have hlen : ((oSt I).res.amt ++ (oSt I).res.cnt ++ (oSt I).res.pend).length = 80 := by
    rw [hs, StRegs.pend, stateOpen_res]; simp
  have reg : ∀ k < 80, ((oSt I).res.amt ++ (oSt I).res.cnt ++ (oSt I).res.pend).getD k 0 =
      if k < 12 then I.n + 42 + k else if k < 16 then I.n + 218 + (k - 12) else I.n + 72 + (k - 16) := by
    intro k hk
    have la : (oSt I).res.amt.length = 12 := by rw [hs, stateOpen_res]; simp
    have lc : (oSt I).res.cnt.length = 4 := by rw [hs, stateOpen_res]; simp
    by_cases h12 : k < 12
    · rw [if_pos h12, getD_app_lt (by simp [la, lc]; omega), getD_app_lt (by rw [la]; omega), hs, stateOpen_res]
      exact getD_map_range h12
    by_cases h16 : k < 16
    · rw [if_neg h12, if_pos h16, getD_app_lt (by simp [la, lc]; omega), getD_app_ge (by rw [la]; omega), la, hs,
        stateOpen_res]
      simp only
      rw [getD_map_range (by omega)]
    · rw [if_neg h12, if_neg h16, getD_app_ge (by simp [la, lc]; omega)]
      simp only [List.length_append, la, lc]
      rw [hs, pend_getD (by omega)]
  have each := bs (fun k hk => by
    rw [hlen] at hk
    rw [reg k hk]
    split_ifs with h1 h2
    · have := hb (42 + k) (by unfold NST; omega)
      rw [← Nat.add_assoc] at this
      exact ⟨this.1, this.2 (by unfold u16Kind; omega)⟩
    · have := hb (218 + (k - 12)) (by unfold NST; omega)
      rw [← Nat.add_assoc] at this
      exact ⟨this.1, this.2 (by unfold u16Kind; omega)⟩
    · have := hb (72 + (k - 16)) (by unfold NST; omega)
      rw [← Nat.add_assoc] at this
      exact ⟨this.1, this.2 (by unfold u16Kind; omega)⟩)
  rw [hlen] at each
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := each j (by omega); rw [reg j (by omega), if_pos hj] at this; exact this
  · have := each (12 + j) (by omega)
    rw [reg (12 + j) (by omega), if_neg (by omega), if_pos (by omega), show 12 + j - 12 = j by omega] at this
    exact this
  · have := each (16 + j) (by omega)
    rw [reg (16 + j) (by omega), if_neg (by omega), if_neg (by omega), show 16 + j - 16 = j by omega] at this
    exact this

/-- The count register's value from the count bytes, below `2^30`. -/
theorem setOpen_count (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) :
    IsBase (ρ (oCnt I).res) ∧
    (ρ (oCnt I).res).a.val = (ρ (I.n + 218)).a.val + 256 * (ρ (I.n + 218 + 1)).a.val +
      65536 * (ρ (I.n + 218 + 2)).a.val + 16777216 * (ρ (I.n + 218 + 3)).a.val ∧
    (ρ (oCnt I).res).a.val < 2 ^ 30 := by
  obtain ⟨-, hcb, -⟩ := setOpen_bytes I h hC
  have hb := stateOpen_base h.st
  have hc : (oSt I).res.cnt = (List.range 4).map (I.n + 218 + ·) := rfl
  have g : ∀ j < 4, (oSt I).res.cnt.getD j 0 = I.n + 218 + j := fun j hj => by rw [hc, getD_map_range hj]
  obtain ⟨b, v, c3⟩ := count_sound h.cnt hC (fun j hj => by
    rw [g j hj]
    have := hb (218 + j) (by unfold NST; omega)
    rw [← Nat.add_assoc] at this
    exact ⟨this.1, hcb j hj⟩)
  rw [g 0 (by norm_num), g 1 (by norm_num), g 2 (by norm_num), g 3 (by norm_num)] at v
  rw [g 3 (by norm_num)] at c3
  simp only [Nat.add_zero] at v
  refine ⟨b, v, ?_⟩
  have c0 := hcb 0 (by norm_num); have c1 := hcb 1 (by norm_num); have c2 := hcb 2 (by norm_num)
  simp only [Nat.add_zero] at c0
  show (ρ (count (oBy I).next (oSt I).res.cnt I.C).res).a.val < 2 ^ 30
  rw [v]; omega

theorem b2iv_halves : ∀ w < 8, ∀ h < 2, (b2ivWords.flatMap halves).getD (2 * w + h) 0 = Sha256.half16 (h0 w) h := by
  decide

theorem shaiv_halves : ∀ w < 8, ∀ h < 2,
    (shaIvWords.flatMap halves).getD (2 * w + h) 0 = Sha256.half16 (Spec.Bitcoin.stateWord Spec.Sha256.IV w) h := by
  decide

theorem toQ_zero' : toQ ⟨0, 0, 0, 0⟩ = 0 := by simp [toQ, Spec.QM31.emb]

/-- The incoming public values of the start vector at the count bytes. -/
theorem leBytes_byte {c0 c1 c2 c3 : ℕ} (h0 : c0 < 256) (h1 : c1 < 256) (h2 : c2 < 256) (h3 : c3 < 256) :
    ∀ q < 4, ((Spec.Block.leBytes 4 (c0 + 256 * c1 + 65536 * c2 + 16777216 * c3)).getD q 0).toNat =
      [c0, c1, c2, c3].getD q 0 := by
  intro q hq
  rw [Spec.Block.leBytes, List.getD_eq_getElem _ _ (by simpa using hq)]
  simp only [List.getElem_map, List.getElem_range]
  rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> simp <;> omega

/-- **The start vector encodes `begin 1 cnt`** (`EncIn`): the challenge aside, everything zero but the
Blake2s chaining value `h0` with the count's 4 bytes pending, and SHA-256's IV. -/
theorem setOpen_begin (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) :
    EncIn (pbOf ρ I.chl ((List.range 4).map (I.n + 218 + ·))) (Spec.SetFile.begin 1 (ρ (oCnt I).res).a.val) := by
  obtain ⟨-, hv, hlt⟩ := setOpen_count I h hC
  obtain ⟨-, hcb, -⟩ := setOpen_bytes I h hC
  set N := (ρ (oCnt I).res).a.val with hN
  set pb := pbOf ρ I.chl ((List.range 4).map (I.n + 218 + ·)) with hpb
  have z : ∀ k, ¬ (41 ≤ k ∧ k < 153) → ¬ (222 ≤ k ∧ k < 238) → k ≠ 239 → ¬ (240 ≤ k ∧ k < 244) →
      ¬ (386 ≤ k ∧ k < 402) → pb k = 0 := fun k h1 h2 h3 h4 h5 => pbOf_zero h1 h2 h3 h4 h5
  have hfeed : Spec.SetFile.b2Feed Spec.SetFile.b2Init (Spec.Block.leBytes 4 N) = ⟨h0, 0, Spec.Block.leBytes 4 N⟩ := by
    rw [Spec.SetFile.b2Feed, Spec.SetFile.b2Init]
    simp only [List.nil_append]
    rw [Spec.SetFile.b2Absorb_neg (by simp [Spec.Block.leBytes])]
  have hlen : (Spec.Block.leBytes 4 N).length = 4 := by simp [Spec.Block.leBytes]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show pb 1 = ((0 : ℕ) : F); rw [z 1 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
  · left
    refine ⟨z 3 (by omega) (by omega) (by omega) (by omega) (by omega), rfl, fun j hj => ?_⟩
    show pb (4 + j) = 0
    exact z _ (by omega) (by omega) (by omega) (by omega) (by omega)
  · intro j hj
    show (pb (4 + j)).val < 256
    rw [z _ (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
  · show (pb 40).val = 0
    rw [z 40 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
  · show 0 < 2 ^ 24; norm_num
  · intro j hj
    show (pb (162 + j)).val < 256
    rw [z _ (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
  · show (∑ j ∈ Finset.range 12, (pb (162 + j)).val * 256 ^ j) = 0
    apply Finset.sum_eq_zero; intro j hj; simp only [Finset.mem_range] at hj
    rw [z _ (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
  · show List.replicate 1 (0 : QM) = [Block.RunSum.pQ pb 153]
    simp only [Block.RunSum.pQ]
    rw [z 153 (by omega) (by omega) (by omega) (by omega) (by omega), z 154 (by omega) (by omega) (by omega) (by omega) (by omega),
      z 155 (by omega) (by omega) (by omega) (by omega) (by omega), z 156 (by omega) (by omega) (by omega) (by omega) (by omega),
      toQ_zero']
    rfl
  · show EncB2 pb 222 (Spec.SetFile.b2Feed Spec.SetFile.b2Init (Spec.Block.leBytes 4 N))
    rw [hfeed]
    refine ⟨fun w hw k hk => ?_, ?_, ?_, ?_, ?_, fun q hq => ?_⟩
    · show pb (222 + (2 * w + k)) = ((Sha256.half16 (h0 w) k : ℕ) : F)
      rw [hpb, pbOf_b2iv (by omega), b2iv_halves w hw k (by omega)]
    · show (pb 238).val < 2 ^ 30
      rw [z 238 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
    · show 0 = 64 * (pb 238).val
      rw [z 238 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
    · show (pb 239).val = (Spec.Block.leBytes 4 N).length
      rw [hpb, pbOf_four, hlen]; rfl
    · show (Spec.Block.leBytes 4 N).length ≤ 64
      rw [hlen]; norm_num
    · rw [hlen] at hq
      show (pb (222 + 18 + q)).val = ((Spec.Block.leBytes 4 N).getD q 0).toNat
      rw [show 222 + 18 + q = 240 + q by omega, hpb, pbOf_cnt hq, getD_map_range hq, hv,
        leBytes_byte (hcb 0 (by norm_num)) (hcb 1 (by norm_num)) (hcb 2 (by norm_num)) (hcb 3 (by norm_num)) q hq]
      rcases (by omega : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3) with rfl | rfl | rfl | rfl <;> rfl
  · show EncSha pb 386 Spec.SetFile.shaInit
    refine ⟨fun w hw k hk => ?_, ?_, ?_, rfl, fun q hq => absurd hq (by simp [Spec.SetFile.shaInit])⟩
    · show pb (386 + (2 * w + k)) = ((Sha256.half16 (Spec.Bitcoin.stateWord Spec.Sha256.IV w) k : ℕ) : F)
      rw [hpb, pbOf_shaiv (by omega), shaiv_halves w hw k (by omega)]
    · show pb 402 = (((0 : ℕ) / 64 : ℕ) : F)
      rw [z 402 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp
    · show (pb 403).val = 0 % 64
      rw [z 403 (by omega) (by omega) (by omega) (by omega) (by omega)]; simp

/-! ### The finish -/

/-- **A final block of at most 64 bytes**: one compression of the zero-padded bytes, counter `t + len`. -/
theorem hashBlocks_short (h : ℕ → Word) (t : ℕ) (b : List UInt8) (hb : b.length ≤ 64) :
    hashBlocks h t b = compress h (leWord (b ++ List.replicate (64 - b.length) 0)) (t + b.length) true := by
  rcases b with _ | ⟨x, xs⟩
  · rw [hashBlocks]
    have g : ∀ q, (List.replicate 64 (0 : UInt8)).getD q 0 = 0 := fun q => by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split_ifs <;> rfl
    have : leWord ([] ++ List.replicate (64 - 0) 0) = fun _ => 0 := by
      funext k; simp only [leWord, List.nil_append, Nat.sub_zero, g]; rfl
    simp only [List.length_nil, Nat.add_zero, this]
  · rw [hashBlocks, if_pos hb]
    simp

theorem getD_default {l : List ℕ} {j d : ℕ} (hj : j < l.length) : l.getD j d = l.getD j 0 := by
  rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hj]

theorem val_cast_lt {k : ℕ} (hk : k < 65536) : ((k : ℕ) : F).val = k := ZMod.val_natCast_of_lt (by unfold P; omega)

/-- **The finish**: for a Blake2s state `S` that `pf` encodes at `B2_OUT`, the opening's `fin` is
`hashBlocks` of it: one compression of the pending bytes zero-padded, counter `t + len`, last flag. -/
theorem setOpen_finish (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) {S : Spec.SetFile.B2}
    (hS : EncB2 (pfOf ρ I.chl I.n) 304 S) :
    ∀ i < 8, word (ρ ((oFin I).res.getD i 0)) = hashBlocks S.h S.t S.pend i := by
  obtain ⟨hl, hnb, ht, hpl, h64, hpend⟩ := hS
  obtain ⟨-, -, hpb⟩ := setOpen_bytes I h hC
  have hb := stateOpen_base h.st
  have hs : (oSt I).res = (stateOpen I.n I.e).res := rfl
  set n := I.n
  set len := S.pend.length with hlen
  -- the registers
  have b2r : ∀ t < 82, (oSt I).res.b2.getD t 0 = n + 54 + t := fun t ht => by rw [hs, stateOpen_res]; exact getD_map_range ht
  have hnbR : (oSt I).res.nb = n + 70 := by rw [StRegs.nb, b2r 16 (by norm_num)]
  have hplR : (oSt I).res.plen = n + 71 := by rw [StRegs.plen, b2r 17 (by norm_num)]
  have hpendR : ∀ j < 64, (oSt I).res.pend.getD j 0 = n + 72 + j := fun j hj => by rw [hs]; exact pend_getD hj
  have hhR : ∀ j < 16, (oSt I).res.b2h.getD j 0 = n + 54 + j := fun j hj => by
    rw [StRegs.b2h, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, ← List.getD_eq_getElem?_getD, b2r j (by omega)]
  simp only [SetPass.H_LIMB, SetPass.H_NB, SetPass.H_PLEN, SetPass.H_PEND] at hl hnb ht hpl hpend
  rw [pfOf_b2 (by norm_num), show n + 54 + 16 = n + 70 by omega] at hnb ht
  rw [pfOf_b2 (by norm_num), show n + 54 + 17 = n + 71 by omega] at hpl
  -- the pending length: the one-hot's `k` is `len`
  obtain ⟨k, hk, hkx, hbits⟩ := oneHot65_sound h.oh hC
  rw [hplR] at hkx
  have hkl : k = len := by
    have : (ρ (n + 71)).a.val = k := by rw [hkx]; exact ZMod.val_natCast_of_lt (by unfold P; omega)
    rw [← this, ← hpl]
  subst hkl
  have hbitsR : ∀ j < 65, (oOh I).res.getD j 0 = (oDin I).next + 16 + j := fun j hj => getD_map_range hj
  have hlt := ltMask_sound h.lt hC hk (fun j hj => by rw [hbitsR j hj]; exact hbits j hj)
  have hltR : ∀ j < 64, (oLt I).res.getD j 0 = (oOh I).next + j := fun j hj => getD_map_range hj
  have hpendB : ∀ j < 64, IsBase (ρ ((oSt I).res.pend.getD j 0)) := by
    intro j hj
    rw [hpendR j hj]
    have := hb (72 + j) (by unfold NST; omega)
    rw [← Nat.add_assoc] at this
    exact this.1
  have hmk : ∀ j < 64, IsBase (ρ ((oMk I).res.getD j 0)) ∧
      (ρ ((oMk I).res.getD j 0)).a = if j < len then (ρ ((oSt I).res.pend.getD j 0)).a else 0 :=
    mask_sound h.msk hpendB (fun j hj => by rw [hltR j hj]; exact hlt j hj)
  -- the masked bytes are the padded block's bytes
  have hpad : ∀ j < 64, (ρ ((oMk I).res.getD j 0)).a.val = ((S.pend ++ List.replicate (64 - len) 0).getD j 0).toNat := by
    intro j hj
    rw [(hmk j hj).2]
    by_cases hjl : j < len
    · rw [if_pos hjl, hpendR j hj, List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
      have := hpend j hjl
      rw [show 304 + 18 + j = 304 + (18 + j) by omega, pfOf_b2 (by omega), show n + 54 + (18 + j) = n + 72 + j by omega]
        at this
      exact this
    · rw [if_neg hjl, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), List.getElem?_replicate,
        if_pos (by omega)]
      simp
  have hmB : ∀ j < 4 * 16, IsBase (ρ ((oMk I).res.getD j 0)) ∧ (ρ ((oMk I).res.getD j 0)).a.val < 256 := by
    intro j hj
    refine ⟨(hmk j (by omega)).1, ?_⟩
    rw [hpad j (by omega)]
    exact UInt8.toNat_lt _
  have hm : ∀ w < 16, IsU32 (ρ ((oM I).res.getD w 0)) ∧
      word (ρ ((oM I).res.getD w 0)) =
        BitVec.ofNat 32 ((ρ ((oMk I).res.getD (4 * w) 0)).a.val + 256 * (ρ ((oMk I).res.getD (4 * w + 1) 0)).a.val +
          65536 * ((ρ ((oMk I).res.getD (4 * w + 2) 0)).a.val + 256 * (ρ ((oMk I).res.getD (4 * w + 3) 0)).a.val)) :=
    packBytes_sound h.m hC hmB
  have hhB : ∀ j < 16, IsBase (ρ ((oSt I).res.b2h.getD j 0)) := by
    intro j hj
    rw [hhR j hj]
    have := hb (54 + j) (by unfold NST; omega)
    rw [← Nat.add_assoc] at this
    exact this.1
  have hh : ∀ w < 8, ρ ((oH I).res.getD w 0) =
      ⟨(ρ ((oSt I).res.b2h.getD (2 * w) 0)).a, (ρ ((oSt I).res.b2h.getD (2 * w + 1) 0)).a, 0, 0⟩ :=
    packW_sound h.h hC hhB
  have hpl64 : (ρ (oSt I).res.plen).a.val ≤ 64 := by rw [hplR, hpl]; exact h64
  obtain ⟨-, -, -, ht0, ht1⟩ := counter_sound h.ct hC hpl64
  rw [hnbR, hplR, hpl] at ht0 ht1
  -- the compression
  have hz : word (ρ (oCt I).next) = 0 := by
    have := h.fin (constU32 (oCt I).next 0) (by simp [oFin, compressFinal])
    rw [const_word this (by norm_num)]; rfl
  have hfin := compressFinal_sound (H := S.h) (M := leWord (S.pend ++ List.replicate (64 - len) 0))
    (t := 64 * (ρ (n + 70)).a.val + len) h.fin
    (fun i hi => by
      rw [hh i hi, hhR (2 * i) (by omega), hhR (2 * i + 1) (by omega)]
      have e0 := hl i hi 0 (by norm_num)
      have e1 := hl i hi 1 (by norm_num)
      rw [pfOf_b2 (by omega)] at e0 e1
      simp only [word]
      rw [show n + 54 + (2 * i + 1) = n + 54 + (2 * i + 1) from rfl] at e1
      rw [show (n + 54 + 2 * i) = n + 54 + (2 * i + 0) by omega, e0, e1, val_cast_lt (Sha256.half16_lt _ _),
        val_cast_lt (Sha256.half16_lt _ _), ← Sha256.half16_split]
      simp)
    (fun j => by
      by_cases hj : j < 16
      · rw [getD_default (by simp [oM, packBytes]; omega), (hm j hj).2]
        simp only [leWord]
        rw [hpad (4 * j) (by omega), hpad (4 * j + 1) (by omega), hpad (4 * j + 2) (by omega), hpad (4 * j + 3) (by omega)]
        congr 1; ring
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [oM, packBytes]; omega), Option.getD_none, hz]
        simp only [leWord]
        have g : ∀ q, 64 ≤ q → (S.pend ++ List.replicate (64 - len) 0).getD q 0 = 0 := fun q hq => by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; rfl
        rw [g (4 * j) (by omega), g (4 * j + 1) (by omega), g (4 * j + 2) (by omega), g (4 * j + 3) (by omega)]
        rfl)
    ht0 ht1
  intro i hi
  have e := hfin i hi
  rw [hashBlocks_short _ _ _ h64, ht]
  exact e

/-! ### The end facts' words -/

/-- **`i` is the count** (in the field). -/
theorem setOpen_i (I : SOIn) (h : OHolds I ρ) {S : Spec.SetFile.St QM} (hS : EncOut (pfOf ρ I.chl I.n) S) :
    (S.i : F) = ((ρ (oCnt I).res).a.val : F) := by
  rw [← hS.i, show SetPass.PUB_I_OUT = 2 from rfl, pfOf_i, ZMod.natCast_zmod_val]
  exact congrArg Q.a h.icnt

theorem setOpen_cntW (I : SOIn) (h : OHolds I ρ) :
    word (ρ (oAw I).next) = BitVec.ofNat 32 (ρ (oCnt I).res).a.val := m2u_word h.cw

theorem setOpen_maxhW (I : SOIn) (h : OHolds I ρ) {S : Spec.SetFile.St QM} (hS : EncOut (pfOf ρ I.chl I.n) S) :
    word (ρ ((oAw I).next + 1)) = BitVec.ofNat 32 S.maxHeight := by
  rw [m2u_word h.mw, ← hS.maxh, show SetPass.PUB_MAXH_OUT = 161 from rfl, pfOf_maxh]
  rfl

/-- **The amount's words**: little-endian, `amount / 2^(32 w)` truncated. -/
theorem setOpen_amtW (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) {S : Spec.SetFile.St QM}
    (hS : EncOut (pfOf ρ I.chl I.n) S) :
    ∀ w < 3, word (ρ ((oAw I).res.getD w 0)) = BitVec.ofNat 32 (S.amount / 2 ^ (32 * w)) := by
  obtain ⟨hab, -, -⟩ := setOpen_bytes I h hC
  have hb := stateOpen_base h.st
  have hs : (oSt I).res = (stateOpen I.n I.e).res := rfl
  have ar : ∀ j < 12, (oSt I).res.amt.getD j 0 = I.n + 42 + j := fun j hj => by
    rw [hs, stateOpen_res]; exact getD_map_range hj
  have hB : ∀ j < 4 * 3, IsBase (ρ ((oSt I).res.amt.getD j 0)) ∧ (ρ ((oSt I).res.amt.getD j 0)).a.val < 256 := by
    intro j hj
    rw [ar j hj]
    have := hb (42 + j) (by unfold NST; omega)
    rw [← Nat.add_assoc] at this
    exact ⟨this.1, hab j hj⟩
  have hw := packBytes_sound h.aw hC hB
  have amt := hS.amt
  simp only [SetPass.Rec.pubAmt, SetPass.PUB_AMT_OUT] at amt
  have e : ∀ j < 12, (pfOf ρ I.chl I.n (174 + j)).val = (ρ (I.n + 42 + j)).a.val := fun j hj => by rw [pfOf_amt hj]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.zero_add] at amt
  rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num), e 3 (by norm_num), e 4 (by norm_num),
    e 5 (by norm_num), e 6 (by norm_num), e 7 (by norm_num), e 8 (by norm_num), e 9 (by norm_num),
    e 10 (by norm_num), e 11 (by norm_num)] at amt
  have b := fun j (hj : j < 12) => hab j hj
  have b0 := b 0 (by norm_num); have b1 := b 1 (by norm_num); have b2 := b 2 (by norm_num)
  have b3 := b 3 (by norm_num); have b4 := b 4 (by norm_num); have b5 := b 5 (by norm_num)
  have b6 := b 6 (by norm_num); have b7 := b 7 (by norm_num); have b8 := b 8 (by norm_num)
  have b9 := b 9 (by norm_num); have b10 := b 10 (by norm_num); have b11 := b 11 (by norm_num)
  intro w hw3
  show word (ρ ((packBytes (oSd I).next (oSt I).res.amt 3 I.C).res.getD w 0)) = _
  rw [(hw w hw3).2, ar (4 * w) (by omega), ar (4 * w + 1) (by omega), ar (4 * w + 2) (by omega), ar (4 * w + 3) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [← amt]
  simp only [Nat.add_zero] at b0 ⊢
  norm_num at b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 ⊢
  rcases (by omega : w = 0 ∨ w = 1 ∨ w = 2) with rfl | rfl | rfl <;> simp <;> omega

/-- **The SHA-256 state's digest**: Blake2s of its 82 limbs, which encode the final state's SHA-256
state (`EncSha … 0`). -/
theorem setOpen_shaDg (I : SOIn) (h : OHolds I ρ) {S : Spec.SetFile.St QM} (hS : EncOut (pfOf ρ I.chl I.n) S) :
    wordsOf ρ (oSd I).res = H ((List.range 82).map fun j => BitVec.ofNat 32 (pfOf ρ I.chl I.n (468 + j)).val) ∧
      EncSha (fun j => pfOf ρ I.chl I.n (468 + j)) 0 S.sha := by
  have hs : (oSt I).res.sha = (List.range 82).map (I.n + 136 + ·) := rfl
  refine ⟨?_, SetPass.encSha_congr (fun j _ => by simp [SetPass.SHA_OUT]) hS.sha⟩
  have hd := h.sd
  rw [show oSd I = pubsDigest (oMr I).next [] (oSt I).res.sha from rfl] at hd ⊢
  rw [wordsOf_eq (pubsDigest_length _ _ _) (fun i hi => vec_digest hd (q := fun r => (ρ r).a) (fun _ _ => rfl)
    (by rw [hs]; simp) i hi)]
  have : vecW (fun r => (ρ r).a) (oSt I).res.sha =
      (List.range 82).map fun j => BitVec.ofNat 32 (pfOf ρ I.chl I.n (468 + j)).val := by
    rw [hs, vecW_range]
    exact List.map_congr_left fun j hj => by rw [pfOf_sha (by simpa using hj)]
  rw [this]
  simp only [H, List.getD_eq_getElem?_getD]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp at h1
  simp [h1]

/-- **The Merkle root's words** are the root state's, when its limbs are. -/
theorem setOpen_mroot (I : SOIn) (h : OHolds I ρ) (hC : ConstsOk ρ I.C) (hp : ∀ k < 48, IsBase (ρ (I.c.pubs k)))
    {st : Spec.Sha256.State} (hR : (List.range 16).map (fun j => (ρ (I.c.pubs (32 + j))).a) = limbsOf st) :
    ∀ w < 8, word (ρ ((oMr I).res.getD w 0)) = Spec.HeaderTree.stWord st w := by
  have hl : ∀ j < 16, ((List.range 16).map fun k => I.c.pubs (32 + k)).getD j 0 = I.c.pubs (32 + j) :=
    fun j hj => getD_map_range hj
  have hw := packW_sound h.mr hC (fun j hj => by rw [hl j hj]; exact hp _ (by omega))
  have lim : ∀ j < 16, (ρ (I.c.pubs (32 + j))).a = ((Sha256.half16 (Spec.HeaderTree.stWord st (j / 2)) (j % 2) : ℕ) : F) := by
    intro j hj
    have := congrArg (fun l => l.getD j 0) hR
    rw [List.getD_eq_getElem _ _ (by simpa using hj)] at this
    simp only [List.getElem_map, List.getElem_range] at this
    rw [this, StarkedAir.HeaderTree.limbsOf_get hj]
  intro w hw8
  show word (ρ ((packW (oFin I).next ((List.range 16).map fun k => I.c.pubs (32 + k)) I.C).res.getD w 0)) = _
  rw [hw w hw8, hl (2 * w) (by omega), hl (2 * w + 1) (by omega)]
  simp only [word]
  rw [lim (2 * w) (by omega), lim (2 * w + 1) (by omega), show 2 * w / 2 = w by omega, show (2 * w + 1) / 2 = w by omega,
    show 2 * w % 2 = 0 by omega, show (2 * w + 1) % 2 = 1 by omega, val_cast_lt (Sha256.half16_lt _ _),
    val_cast_lt (Sha256.half16_lt _ _), ← Sha256.half16_split]
  simp

end StarkedAir.Circuit.ChainSeal
