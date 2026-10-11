/-
**The block aggregation node's glue (BLOCK-REC), Lean-first.** A node joins two adjacent ranges of
equal size `n` (so every range is a perfect subtree of `2^k` blocks; the outer verifier checks the
top-level ranges against the aligned decomposition of the epoch, D-043). A range summary is 51 base
limbs:

| limbs | field |
|---|---|
| 0 | `lo`, the first height |
| 1 | `n`, the block count |
| 2–5 | `s`, the summed partial sum (QM31) |
| 6 | `nin`, the summed input count |
| 7–18 | `(γ, z, α)` |
| 19–34 | the block-hash subtree root (the header tree's node over block hashes) |
| 35–50 | the seed subtree root (over `Blake2s(hash ‖ C_h)` leaves) |

`nodeP`: the right range starts where the left ends and has its size, the challenges are equal; the
output is the left's start, twice the size, the summed `s` and `nin`, the left's challenge, and the
two roots folded with the header tree's node gadget (`treeNode`). `lo`, `n` and `nin` are checked
below `2^30` (`lt30`), so the sums never wrap mod P. `node_sound` states all of it.
-/
import StarkedAir.Circuit.NodeSound
import StarkedAir.Circuit.CompositionLogUp

namespace StarkedAir.Circuit.BlockNode

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Spec.QM31 (QM toQ emb)

def LO : ℕ := 0
def NN : ℕ := 1
def SS : ℕ := 2
def NIN : ℕ := 6
def CH : ℕ := 7
def HR : ℕ := 19
def SR : ℕ := 35
def NSUM : ℕ := 51

/-- `x < 2^30` (registers `m … m+10`): `x = a + 2^16·b` with `a`, `b` guessed u16 and `4b` u16. -/
def lt30 (m x : ℕ) : List Op :=
  [.m2u m x, .guessU16 (m + 1) (.coord 0 (.reg m)), .guessU16 (m + 2) (.coord 1 (.reg m)),
   .const (m + 3) 65536 0 0 0, .mul (m + 4) (m + 2) (m + 3), .add (m + 5) (m + 1) (m + 4), .eq x (m + 5),
   .const (m + 6) 4 0 0 0, .mul (m + 7) (m + 2) (m + 6)] ++ range16 (m + 8) (m + 7)

variable {ρ : ℕ → Q}

theorem mul_base (x y : Q) (hx : IsBase x) (hy : IsBase y) : x * y = ⟨x.a * y.a, 0, 0, 0⟩ := by
  obtain ⟨b1, c1, d1⟩ := hx
  obtain ⟨b2, c2, d2⟩ := hy
  ext <;> simp [Q.mul_def, cmul, b1, c1, d1, b2, c2, d2]

theorem lt30_sound {m x : ℕ} (h : Holds ρ (lt30 m x)) : IsBase (ρ x) ∧ (ρ x).a.val < 2 ^ 30 := by
  have g := fun (o : Op) (ho : o ∈ lt30 m x) => h o ho
  have u1 := g (.guessU16 (m + 1) (.coord 0 (.reg m))) (by simp [lt30])
  have u2 := g (.guessU16 (m + 2) (.coord 1 (.reg m))) (by simp [lt30])
  have c3 := g (.const (m + 3) 65536 0 0 0) (by simp [lt30])
  have m4 := g (.mul (m + 4) (m + 2) (m + 3)) (by simp [lt30])
  have a5 := g (.add (m + 5) (m + 1) (m + 4)) (by simp [lt30])
  have e := g (.eq x (m + 5)) (by simp [lt30])
  have c6 := g (.const (m + 6) 4 0 0 0) (by simp [lt30])
  have m7 := g (.mul (m + 7) (m + 2) (m + 6)) (by simp [lt30])
  have hr := range16_sound (fun o ho => g o (by simp only [lt30]; exact List.mem_append_right _ ho))
  simp only [Op.holds] at u1 u2 c3 m4 a5 e c6 m7
  have bc3 : IsBase (ρ (m + 3)) := by rw [c3]; exact ⟨rfl, rfl, rfl⟩
  have bc6 : IsBase (ρ (m + 6)) := by rw [c6]; exact ⟨rfl, rfl, rfl⟩
  rw [mul_base _ _ u2.1 bc6, c6] at m7
  rw [mul_base _ _ u2.1 bc3, c3] at m4
  set A := (ρ (m + 1)).a.val with hA
  set B := (ρ (m + 2)).a.val with hB
  have eA : (ρ (m + 1)).a = (A : F) := (ZMod.natCast_zmod_val _).symm
  have eB : (ρ (m + 2)).a = (B : F) := (ZMod.natCast_zmod_val _).symm
  have hb4 : B * 4 < 65536 := by
    have := hr.2
    rw [m7] at this
    simp only [lit] at this
    rw [eB, show ((B : F) * ((4 : ℕ) : F)) = ((B * 4 : ℕ) : F) by push_cast; ring,
      ZMod.val_natCast_of_lt (by unfold P; omega)] at this
    exact this
  have hx : ρ x = ⟨((A + B * 65536 : ℕ) : F), 0, 0, 0⟩ := by
    rw [e, a5, m4]; obtain ⟨b1, c1, d1⟩ := u1.1
    ext <;> simp [b1, c1, d1, lit, eA, eB]
  refine ⟨by rw [hx]; exact ⟨rfl, rfl, rfl⟩, ?_⟩
  rw [hx]
  simp only
  rw [ZMod.val_natCast_of_lt (by unfold P; omega)]
  omega

/-! ### The node -/

/-- The hash-root and seed-root folds (`treeNode` over the children's root limbs). -/
def hrNode (pl pr : ℕ → ℕ) (n : ℕ) : Out (List ℕ) := treeNode n (fun k => pl (HR + (k - TB))) (fun k => pr (HR + (k - TB)))
def srNode (pl pr : ℕ → ℕ) (n : ℕ) : Out (List ℕ) := treeNode n (fun k => pl (SR + (k - TB))) (fun k => pr (SR + (k - TB)))

/-- The link checks and sums, with the children's summary limbs at `pl i`, `pr i`, from register `b`. -/
def linkOps (pl pr : ℕ → ℕ) (b : ℕ) : List Op :=
  [.eq (pr NN) (pl NN), .add b (pl LO) (pl NN), .eq (pr LO) b, .add (b + 1) (pl NN) (pl NN)] ++
  (List.range 12).map (fun i => Op.eq (pr (CH + i)) (pl (CH + i))) ++
  (List.range 4).map (fun i => Op.add (b + 2 + i) (pl (SS + i)) (pr (SS + i))) ++
  [.add (b + 6) (pl NIN) (pr NIN)] ++ lt30 (b + 7) (pl LO) ++ lt30 (b + 16) (b + 1) ++ lt30 (b + 25) (b + 6)

/-- The output summary's register for limb `i`. -/
def outReg (pl pr : ℕ → ℕ) (b i : ℕ) : ℕ :=
  if i = 0 then pl LO else if i = 1 then b + 1 else if i < 6 then b + i else if i = 6 then b + 6
  else if i < 19 then pl i
  else if i < 35 then (hrNode pl pr (b + 34)).res.getD (i - 19) 0
  else (srNode pl pr (hrNode pl pr (b + 34)).next).res.getD (i - 35) 0

def nodeOut (pl pr : ℕ → ℕ) (b : ℕ) : Out (List ℕ) :=
  let h := hrNode pl pr (b + 34)
  let r := srNode pl pr h.next
  ⟨linkOps pl pr b ++ h.ops ++ r.ops, (List.range NSUM).map (outReg pl pr b), r.next⟩

variable {ρ : ℕ → Q}

/-- **The node is sound.** If its ops hold, the right range starts where the left one ends and has
its size and challenge; the output starts at the left's start, has twice the size, the summed limbs
of `s` and `nin` (all three below `2^30`), the left's challenge, and the roots `hnode` of the
children's roots. -/
theorem node_sound {pl pr : ℕ → ℕ} {b : ℕ} (h : Holds ρ (nodeOut pl pr b).ops) :
    ρ (pr NN) = ρ (pl NN) ∧ ρ (pr LO) = ρ (pl LO) + ρ (pl NN) ∧ (∀ i < 12, ρ (pr (CH + i)) = ρ (pl (CH + i))) ∧
    ρ (b + 1) = ρ (pl NN) + ρ (pl NN) ∧ (∀ i < 4, ρ (b + 2 + i) = ρ (pl (SS + i)) + ρ (pr (SS + i))) ∧
    ρ (b + 6) = ρ (pl NIN) + ρ (pr NIN) ∧
    (IsBase (ρ (pl LO)) ∧ (ρ (pl LO)).a.val < 2 ^ 30) ∧ (IsBase (ρ (b + 1)) ∧ (ρ (b + 1)).a.val < 2 ^ 30) ∧
    (IsBase (ρ (b + 6)) ∧ (ρ (b + 6)).a.val < 2 ^ 30) ∧
    (∀ {x y : Spec.Sha256.State}, HeaderTree.pubT (fun k => (ρ (pl (HR + (k - TB)))).a) = HeaderTree.limbsOf x →
      HeaderTree.pubT (fun k => (ρ (pr (HR + (k - TB)))).a) = HeaderTree.limbsOf y →
      ∀ j < 16, (ρ ((hrNode pl pr (b + 34)).res.getD j 0)).a = (HeaderTree.limbsOf (Spec.HeaderTree.hnode x y)).getD j 0) ∧
    (∀ {x y : Spec.Sha256.State}, HeaderTree.pubT (fun k => (ρ (pl (SR + (k - TB)))).a) = HeaderTree.limbsOf x →
      HeaderTree.pubT (fun k => (ρ (pr (SR + (k - TB)))).a) = HeaderTree.limbsOf y →
      ∀ j < 16, (ρ ((srNode pl pr (hrNode pl pr (b + 34)).next).res.getD j 0)).a =
        (HeaderTree.limbsOf (Spec.HeaderTree.hnode x y)).getD j 0) := by
  unfold nodeOut at h
  simp only at h
  rw [holds_append, holds_append] at h
  obtain ⟨⟨hl, hh⟩, hs⟩ := h
  unfold linkOps at hl
  simp only [holds_append] at hl
  obtain ⟨⟨⟨⟨⟨⟨h4, hch⟩, hsum⟩, hnin⟩, l1⟩, l2⟩, l3⟩ := hl
  have g4 := fun (o : Op) (ho : o ∈ _) => h4 o ho
  have e1 := g4 (.eq (pr NN) (pl NN)) (by simp)
  have a2 := g4 (.add b (pl LO) (pl NN)) (by simp)
  have e3 := g4 (.eq (pr LO) b) (by simp)
  have a4 := g4 (.add (b + 1) (pl NN) (pl NN)) (by simp)
  have a6 := hnin (.add (b + 6) (pl NIN) (pr NIN)) (by simp)
  simp only [Op.holds] at e1 a2 e3 a4 a6
  refine ⟨e1, e3.trans a2, fun i hi => ?_, a4, fun i hi => ?_, a6, lt30_sound l1, lt30_sound l2, lt30_sound l3,
    fun ha hb => treeNode_sound hh ha hb, fun ha hb => treeNode_sound hs ha hb⟩
  · have := hch (Op.eq (pr (CH + i)) (pl (CH + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa [Op.holds] using this
  · have := hsum (Op.add (b + 2 + i) (pl (SS + i)) (pr (SS + i))) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
    simpa [Op.holds] using this

/-! ### The node program: two verified children, the glue, the digest -/

/-- A child's external values: its 51 summary limbs, key words, preprocessed root. -/
def EXT_B : ℕ := NSUM + 16

/-- A child's section (as the header node's `child`, with 51 summary limbs). -/
def bchild (n i : ℕ) : Out ChildRegs :=
  let e := EXT_B * i
  let pubsOps := (List.range NSUM).map (fun k => Op.guessM31 (n + k) (.ext (e + k)))
  let key := guessHash (n + NSUM) (e + NSUM)
  let dg := pubsDigest key.next key.res ((List.range NSUM).map (n + ·))
  let root := guessHash dg.next (e + NSUM + 8)
  let ch := (List.range 8).map (root.next + ·)
  ⟨pubsOps ++ key.ops ++ dg.ops ++ root.ops ++ [.hook i (root.res ++ dg.res) ch],
   ⟨(n + ·), key.res, dg.res, ch⟩, root.next + 8⟩

def bC0 : Out ChildRegs := bchild 0 0
def bC1 : Out ChildRegs := bchild bC0.next 1
def bJoin : Out (List ℕ) := nodeOut bC0.res.pubs bC1.res.pubs bC1.next
def bKey : Out (List ℕ) :=
  blake2s bJoin.next (bC0.res.chash ++ bC0.res.key ++ bC1.res.chash ++ bC1.res.key) 128
def bDigest : Out (List ℕ) := pubsDigest bKey.next bKey.res bJoin.res

/-- **The block node program.** Results: the output digest's 8 words. -/
def blockNodeProgram : Program :=
  ⟨"block_node_glue", bC0.ops ++ bC1.ops ++ bJoin.ops ++ bKey.ops ++ bDigest.ops, bDigest.res⟩

/-- The block leaf's summary checks: hook 0 binds the height and the input count; both below `2^30`;
the result is the constant 1 (the leaf's block count). -/
def leafSumOps : List Op := [.hook 0 [] [0, 1]] ++ lt30 2 0 ++ lt30 11 1 ++ [.const 20 1 0 0 0]

def nodeJson : String := blockNodeProgram.toJson
def leafSumJson : String :=
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (leafSumOps.map Op.toJson)}],\"results\":[20]}"

end StarkedAir.Circuit.BlockNode
