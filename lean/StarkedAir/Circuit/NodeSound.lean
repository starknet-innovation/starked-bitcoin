/-
**The node glue is sound.** If the node program's ops hold, the children's public inputs satisfy
`PubLink` and the node's public inputs are `NodeOut` of them: the two hypotheses of
`pub_compose_T` (AggregateTree.lean) are consequences of the node circuit's glue gates.
-/
import StarkedAir.Circuit.BlakeSound
import StarkedAir.Gadgets.AggregateTree

namespace StarkedAir.Circuit

open StarkedAir Q Spec.Blake2s
open StarkedAir.HeaderTree (pubT NodeOut Low limbsOf limbsOf_get compress_congr compress_congr_m)
open StarkedAir.Spec.HeaderTree (hnode stWord toState)

/-! ### QM31 facts -/

namespace Q

theorem mul_def (x y : Q) : x * y =
    ⟨(cmul x.a x.b y.a y.b).1 + (cmul 2 1 (cmul x.c x.d y.c y.d).1 (cmul x.c x.d y.c y.d).2).1,
     (cmul x.a x.b y.a y.b).2 + (cmul 2 1 (cmul x.c x.d y.c y.d).1 (cmul x.c x.d y.c y.d).2).2,
     (cmul x.a x.b y.c y.d).1 + (cmul x.c x.d y.a y.b).1,
     (cmul x.a x.b y.c y.d).2 + (cmul x.c x.d y.a y.b).2⟩ := rfl

/-- `lo + hi·i` for base `lo`, `hi`: the wire `(lo, hi, 0, 0)`. -/
theorem lohi {lo hi : Q} (hl : IsBase lo) (hh : IsBase hi) :
    lo + hi * lit 0 1 0 0 = ⟨lo.a, hi.a, 0, 0⟩ := by
  obtain ⟨l1, l2, l3⟩ := hl
  obtain ⟨h1, h2, h3⟩ := hh
  ext <;> simp [mul_def, cmul, lit, l1, l2, l3, h1, h2, h3]

theorem word_mk {x y : F} :
    word ⟨x, y, 0, 0⟩ = BitVec.ofNat 32 (x.val + 65536 * y.val) := rfl

end Q

theorem val_lt_P (x : F) : x.val < P := ZMod.val_lt x

/-! ### Gadget lemmas -/

theorem range16_sound {ρ : ℕ → Q} {n x : ℕ} (h : Holds ρ (range16 n x)) :
    IsBase (ρ x) ∧ (ρ x).a.val < 65536 := by
  have h1 := h _ (List.mem_cons_self)
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [Op.holds] at h1 h2
  obtain ⟨hb, hm⟩ := h1
  rw [h2] at hm
  refine ⟨hb, ?_⟩
  have e := congrArg Q.b hm
  simp only [Q.m2u, hb.1] at e
  have : (ρ x).a.val / 65536 = 0 :=
    (natCast_inj_of_lt (by unfold P; norm_num) (lt_of_le_of_lt (Nat.div_le_self _ _) (val_lt_P _))
      (by simpa using e)).symm
  omega

/-! ### Link checks -/

/-- **`linkChecks` enforces `PubLink`** on the base coordinates of the children's inputs. -/
theorem link_sound {ρ : ℕ → Q} {n : ℕ} {pl pr : ℕ → ℕ} (h : Holds ρ (linkChecks n pl pr).ops) :
    HeaderChain.PubLink (fun k => (ρ (pl k)).a) (fun k => (ρ (pr k)).a) := by
  dsimp only [linkChecks] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨heq16, hpairs⟩, heq20⟩, heq10⟩, hr32⟩, hr33⟩, hl38⟩, hl39⟩, hc⟩ := h
  have eqOf : ∀ {x y : ℕ}, (Op.eq x y).holds ρ → (ρ x).a = (ρ y).a := fun e => by
    simp only [Op.holds] at e; rw [e]
  have r32 := range16_sound hr32
  have r33 := range16_sound hr33
  have r38 := range16_sound hl38
  have r39 := range16_sound hl39
  have hcAt := fun (op : Op) (hm : op ∈ _) => hc op hm
  have gc := hcAt (.guessM31 (n + 4) (.isEq (.coord 0 (.reg (pl 38))) 0xffff)) (by simp)
  have g1 := hcAt (ONE (n + 5)) (by simp)
  have gs := hcAt (.sub (n + 6) (n + 4) (n + 5)) (by simp)
  have gm := hcAt (.mul (n + 7) (n + 4) (n + 6)) (by simp)
  have g0 := hcAt (.const (n + 8) 0 0 0 0) (by simp)
  have ge := hcAt (.eq (n + 7) (n + 8)) (by simp)
  have gb := hcAt (.const (n + 9) 65536 0 0 0) (by simp)
  have ga := hcAt (.add (n + 10) (pl 38) (n + 5)) (by simp)
  have gm2 := hcAt (.mul (n + 11) (n + 9) (n + 4)) (by simp)
  have gs2 := hcAt (.sub (n + 12) (n + 10) (n + 11)) (by simp)
  have ge2 := hcAt (.eq (pr 32) (n + 12)) (by simp)
  have ga3 := hcAt (.add (n + 13) (pl 39) (n + 4)) (by simp)
  have ge3 := hcAt (.eq (pr 33) (n + 13)) (by simp)
  simp only [Op.holds, ONE] at gc g1 gs gm g0 ge gb ga gm2 gs2 ge2 ga3 ge3
  obtain ⟨cb1, cb2, cb3⟩ := gc
  refine ⟨fun k hk => eqOf (heq16 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)),
    eqOf (hpairs _ (by simp)), eqOf (hpairs _ (by simp)), eqOf (hpairs _ (by simp)),
    eqOf (hpairs _ (by simp)), eqOf (hpairs _ (by simp)), eqOf (hpairs _ (by simp)),
    fun k hk => eqOf (heq20 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)),
    fun l hl => eqOf (heq10 _ (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩)),
    r32.2, r33.2, r38.2, r39.2, (ρ (n + 4)).a, ?_, ?_, ?_⟩
  · -- c (c − 1) = 0
    have e := congrArg Q.a (ge.symm.trans (gm.trans (by rw [gs, g1])))
    rw [g0] at e
    simp [mul_def, cmul, lit, cb1, cb2, cb3] at e
    rcases e with e | e
    · exact Or.inl e
    · exact Or.inr (by linear_combination e)
  · have e := congrArg Q.a (ge2.trans (gs2.trans (by rw [ga, gm2, g1, gb])))
    simp [mul_def, cmul, lit, cb1, cb2, cb3] at e
    exact e
  · have e := congrArg Q.a (ge3.trans ga3)
    simpa using e

/-! ### The tree root -/

theorem stWord_hnode (a b : Spec.Sha256.State) {w : ℕ} (hw : w < 8) :
    stWord (hnode a b) w =
      compress h0 (fun k => if k < 8 then stWord a k else stWord b (k - 8)) 64 true w := by
  unfold hnode toState
  interval_cases w <;> rfl

theorem limb_val {X : Spec.Sha256.State} {j : ℕ} (hj : j < 16) :
    ((limbsOf X).getD j 0).val = Sha256.half16 (stWord X (j / 2)) (j % 2) := by
  rw [limbsOf_get hj, Q.val_cast (lt_trans (Sha256.half16_lt _ _) (by unfold P; norm_num))]

theorem pubT_getD {p : ℕ → F} {j : ℕ} (hj : j < 16) : (pubT p).getD j 0 = p (TB + j) := by
  unfold pubT; rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp [TB]

/-- **`treeNode` computes `hnode`** of the children's roots, limb by limb. -/
theorem treeNode_sound {ρ : ℕ → Q} {n : ℕ} {pl pr : ℕ → ℕ} (h : Holds ρ (treeNode n pl pr).ops)
    {a b : Spec.Sha256.State}
    (ha : pubT (fun k => (ρ (pl k)).a) = limbsOf a) (hb : pubT (fun k => (ρ (pr k)).a) = limbsOf b) :
    ∀ j < 16, (ρ ((treeNode n pl pr).res.getD j 0)).a = (limbsOf (hnode a b)).getD j 0 := by
  dsimp only [treeNode] at h ⊢
  set msg := (List.range 16).map (fun q => n + 1 + 4 * q + 3) with hmsg
  set H := blake2s (n + 65) msg 64 with hH
  rw [List.cons_append, List.cons_append] at h
  have hiC : ρ n = lit 0 1 0 0 := by
    have := h _ List.mem_cons_self; simpa [Op.holds] using this
  have hrest : Holds ρ _ := fun op hm => h op (List.mem_cons_of_mem _ hm)
  simp only [holds_append] at hrest
  obtain ⟨⟨hpack, hblake⟩, hsplit⟩ := hrest
  -- The message words: the children's root words.
  have hm : ∀ q < 16, word (ρ (msg.getD q (n + 65))) =
      if q < 8 then stWord a q else stWord b (q - 8) := by
    intro q hq
    rw [hmsg, List.getD_eq_getElem _ _ (by simpa using hq)]
    simp only [List.getElem_map, List.getElem_range]
    have hq' := fun (op : Op) (hop : op ∈ _) => hpack op (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, hop⟩)
    set c := q / 8
    set w := q % 8
    set src : ℕ → ℕ := if c = 0 then pl else pr
    have rl := range16_sound (n := n + 1 + 4 * q) (x := src (TB + 2 * w)) (fun op hop => hq' op (by simp_all [src]))
    have rh := range16_sound (n := n + 1 + 4 * q + 1) (x := src (TB + 2 * w + 1)) (fun op hop => hq' op (by simp_all [src]))
    have gmul := hq' (.mul (n + 1 + 4 * q + 2) (src (TB + 2 * w + 1)) n) (by simp [src])
    have gadd := hq' (.add (n + 1 + 4 * q + 3) (src (TB + 2 * w)) (n + 1 + 4 * q + 2)) (by simp [src])
    simp only [Op.holds] at gmul gadd
    rw [gadd, gmul, hiC, lohi rl.1 rh.1, word_mk]
    -- The limbs are those of the child's root word `w`.
    have key : ∀ (X : Spec.Sha256.State) (p : ℕ → ℕ), pubT (fun k => (ρ (p k)).a) = limbsOf X →
        BitVec.ofNat 32 ((ρ (p (TB + 2 * w))).a.val + 65536 * (ρ (p (TB + 2 * w + 1))).a.val) = stWord X w := by
      intro X p hX
      have e0 := congrArg (fun l => (List.getD l (2 * w) 0).val) hX
      have e1 := congrArg (fun l => (List.getD l (2 * w + 1) 0).val) hX
      simp only [pubT_getD (show 2 * w < 16 by omega), pubT_getD (show 2 * w + 1 < 16 by omega),
        limb_val (show 2 * w < 16 by omega), limb_val (show 2 * w + 1 < 16 by omega)] at e0 e1
      rw [← Nat.add_assoc] at e1
      rw [e0, e1, show (2 * w) / 2 = w by omega, show (2 * w + 1) / 2 = w by omega,
        show 2 * w % 2 = 0 by omega, show (2 * w + 1) % 2 = 1 by omega, ← Sha256.half16_split]
      exact BitVec.eq_of_toNat_eq (by simp)
    by_cases hc : q < 8
    · have : c = 0 := by simp [c]; omega
      simp only [src, this, if_true, if_pos hc] at *
      rw [key a pl ha, show w = q by simp [w]; omega]
    · have : c ≠ 0 := by simp [c]; omega
      simp only [src, this, if_false, if_neg hc] at *
      rw [key b pr hb, show w = q - 8 by simp [w]; omega]
  -- The hash.
  have hw := blake2s_sound hblake (by norm_num)
  have hpk := blake2s_res_pack hblake
  have hword : ∀ w < 8, word (ρ (H.res.getD w 0)) = stWord (hnode a b) w := by
    intro w hw8
    rw [hw w hw8, show nBlocks 64 = 0 + 1 from rfl, hashW_succ hw8, stWord_hnode a b hw8]
    rw [compress_congr _ _ _ (fun i hi => hashW_zero hi) hw8]
    exact compress_congr_m _ _ _ (fun k hk => by simpa using hm k hk) w
  -- The split.
  intro j hj
  set w := j / 2
  have hw8 : w < 8 := by omega
  have hs := fun (op : Op) (hop : op ∈ _) => hsplit op (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw8, hop⟩)
  set r := H.next + 4 * w
  have g0 := hs (.guessU16 r (.coord 0 (.reg (H.res.getD w 0)))) (by simp [r])
  have g1 := hs (.guessU16 (r + 1) (.coord 1 (.reg (H.res.getD w 0)))) (by simp [r])
  have gm := hs (.mul (r + 2) (r + 1) n) (by simp [r])
  have ga := hs (.add (r + 3) r (r + 2)) (by simp [r])
  have ge := hs (.eq (r + 3) (H.res.getD w 0)) (by simp [r])
  simp only [Op.holds] at g0 g1 gm ga ge
  rw [ga, gm, hiC, lohi g0.1 g1.1, hpk w hw8, hword w hw8] at ge
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]
  rw [limbsOf_get hj]
  have ea := congrArg Q.a ge
  have eb := congrArg Q.b ge
  simp only [pack] at ea eb
  rcases Nat.mod_two_eq_zero_or_one j with h2 | h2
  · rw [h2, Nat.add_zero, ea]; rfl
  · rw [h2, show H.next + 4 * (j / 2) + 1 = r + 1 from rfl, eb]; rfl

/-! ### The node program -/

theorem isIn_eq (k : ℕ) : isIn k = HeaderChain.isIn k := rfl

/-- The children's and the node's public inputs (base coordinates of their wires). -/
def nodePL (ρ : ℕ → Q) (k : ℕ) : F := (ρ (nodeC0.res.pubs k)).a
def nodePR (ρ : ℕ → Q) (k : ℕ) : F := (ρ (nodeC1.res.pubs k)).a
def nodeOut (ρ : ℕ → Q) (k : ℕ) : F := (ρ (nodeOuts.getD k 0)).a

/-- **Node glue soundness.** If the node program's ops hold, the children's public inputs satisfy
`PubLink`, and the node's are `NodeOut` of them: `pub_compose_T`'s hypotheses. -/
theorem node_sound {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    HeaderChain.PubLink (nodePL ρ) (nodePR ρ) ∧ NodeOut (nodePL ρ) (nodePR ρ) (nodeOut ρ) := by
  simp only [nodeProgram, holds_append] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, hlink⟩, -⟩, htree⟩, -⟩ := h
  refine ⟨link_sound hlink, fun k hk => ?_, fun a b ha hb => ?_⟩
  · simp only [nodeOut, nodeOuts, HeaderChain.combine, ← isIn_eq]
    rw [List.getD_eq_getElem _ _ (by simp [N_PUB]; omega)]
    simp only [List.getElem_map, List.getElem_range, show k < TB by simp [TB]; omega, if_true]
    split_ifs <;> simp_all [nodePL, nodePR]
  · apply List.ext_getElem (by simp [pubT, limbsOf])
    intro j hj _
    simp only [pubT, List.length_map, List.length_range] at hj
    have := treeNode_sound htree ha hb j hj
    rw [← List.getD_eq_getElem _ (0 : F), ← List.getD_eq_getElem _ (0 : F), pubT_getD hj, ← this]
    simp only [nodeOut, nodeOuts]
    rw [List.getD_eq_getElem _ _ (by simp [N_PUB, TB]; omega)]
    simp only [List.getElem_map, List.getElem_range, show ¬ TB + j < TB by omega, if_false, Nat.add_sub_cancel_left]
    rfl

/-- **Composition, glue included.** A node whose glue gates hold, over children with proven
public inputs, has proven public inputs. -/
theorem node_compose {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops)
    (vL : HeaderTree.PubValidT (nodePL ρ)) (vR : HeaderTree.PubValidT (nodePR ρ)) :
    HeaderTree.PubValidT (nodeOut ρ) :=
  HeaderTree.pub_compose_T vL vR (node_sound h).1 (node_sound h).2

/-! ### Digests and keys -/

/-- Words of wires. -/
def wordsOf (ρ : ℕ → Q) (rs : List ℕ) : List Word := rs.map (word ∘ ρ)

/-- Base values of wires, as words. -/
def valsOf (ρ : ℕ → Q) (rs : List ℕ) : List Word := rs.map fun r => BitVec.ofNat 32 (ρ r).a.val

theorem child_digest {ρ : ℕ → Q} {n i : ℕ} (h : Holds ρ (child n i).ops) :
    ∀ w < 8, word (ρ ((child n i).res.digest.getD w 0)) =
      blake2sWords (wordsOf ρ (child n i).res.key ++ valsOf ρ ((List.range N_PUB).map (n + ·))) 528 w := by
  dsimp only [child] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨-, -⟩, hdg⟩, -⟩, -⟩ := h
  intro w hw
  rw [pubsDigest_sound hdg (by simp [guessHash, N_PUB]) w hw]
  simp [guessHash, N_PUB, wordsOf, valsOf]

/-- **What each child's verifier checks against**: the digest of the child's key and public
inputs (the same wires `PubLink` and `NodeOut` speak about). -/
theorem node_child_digests {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    (∀ w < 8, word (ρ (nodeC0.res.digest.getD w 0)) =
      blake2sWords (wordsOf ρ nodeC0.res.key ++ valsOf ρ ((List.range N_PUB).map nodeC0.res.pubs)) 528 w) ∧
    (∀ w < 8, word (ρ (nodeC1.res.digest.getD w 0)) =
      blake2sWords (wordsOf ρ nodeC1.res.key ++ valsOf ρ ((List.range N_PUB).map nodeC1.res.pubs)) 528 w) := by
  simp only [nodeProgram, holds_append] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, -⟩, -⟩, -⟩, -⟩ := h
  exact ⟨child_digest h0, child_digest h1⟩

/-- **The node key**: Blake2s of `hL ‖ kL ‖ hR ‖ kR`. -/
theorem node_key {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    ∀ w < 8, word (ρ (nodeKey.res.getD w 0)) =
      blake2sWords (wordsOf ρ (nodeC0.res.chash ++ nodeC0.res.key ++ nodeC1.res.chash ++ nodeC1.res.key)) 128 w := by
  simp only [nodeProgram, holds_append] at h
  obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hk⟩, -⟩, -⟩ := h
  exact blake2s_words hk (by norm_num)

/-- **The node's output digest**: Blake2s of the node key and the node's public inputs. -/
theorem node_digest {ρ : ℕ → Q} (h : Holds ρ nodeProgram.ops) :
    ∀ w < 8, word (ρ (nodeProgram.results.getD w 0)) =
      blake2sWords (wordsOf ρ nodeKey.res ++ valsOf ρ nodeOuts) 528 w := by
  simp only [nodeProgram, holds_append] at h
  obtain ⟨-, hd⟩ := h
  intro w hw
  rw [show nodeProgram.results = nodeDigest.res from rfl, nodeDigest,
    pubsDigest_sound hd (by simp [nodeKey, blake2s, nodeOuts, N_PUB]) w hw]
  simp [nodeKey, blake2s, nodeOuts, N_PUB, wordsOf, valsOf]

/-- **The leaf's output digest**: Blake2s of the zero key and the leaf's public inputs. -/
theorem leaf_digest {ρ : ℕ → Q} (h : Holds ρ leafProgram.ops) :
    ∀ w < 8, word (ρ (leafProgram.results.getD w 0)) =
      blake2sWords (List.replicate 8 0 ++ valsOf ρ ((List.range N_PUB).map (2 + ·))) 528 w := by
  dsimp only [leafProgram] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨-, -⟩, -⟩, hz⟩, hd⟩ := h
  intro w hw
  have e1 : ((List.range 8).map (2 + N_PUB + ·)).map (word ∘ ρ) = List.replicate 8 0 := by
    apply List.ext_getElem (by simp)
    intro j hj _
    simp only [List.length_map, List.length_range] at hj
    have := hz _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    simp only [List.getElem_map, List.getElem_range, Function.comp, const_word this (by norm_num), List.getElem_replicate]
    rfl
  have e2 : 4 * (((List.range 8).map (2 + N_PUB + ·)).length + ((List.range N_PUB).map (2 + ·)).length) = 528 := by
    simp [N_PUB]
  rw [pubsDigest_sound hd (by rw [e2]; norm_num) w hw, e1, e2]
  rfl

end StarkedAir.Circuit
