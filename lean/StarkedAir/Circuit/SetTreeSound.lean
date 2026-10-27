/-
**The set tree's glue is sound (set-pass step 4).**

- `leafOut_sound`: if the set leaf's output program holds and hook 0 returned the public inputs `p`,
  the output is `pubsDigest(0, summ p)`: the halves of `H` of the incoming and outgoing state vectors.
- `node_sound` and the node program's digests, key and link (`SetNode`): the right child's incoming
  digest limbs are the left's outgoing ones, and the output digest is over (left's incoming, right's
  outgoing).
- `stree_sound`: under the recursion `Trust` (as the block and header trees), a satisfied tree circuit
  with the expected hash and key outputs the digest of a chain of proven segments (`Chain`), or Blake2s
  has a collision.
-/
import StarkedAir.Circuit.SetTree
import StarkedAir.Circuit.HeaderRec

namespace StarkedAir.Circuit.SetTree

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec Q Spec.Blake2s

/-- A state vector's words. -/
def vecW (p : ℕ → F) (idx : List ℕ) : List Word := idx.map fun k => BitVec.ofNat 32 (p k).val

/-- `p` with the constant 1 at `NP` (the outgoing `HASLAST`). -/
def withOne (p : ℕ → F) (k : ℕ) : F := if k = NP then 1 else p k

/-- Limb `j` (16 bits) of digest words `ws`. -/
def half (ws : List Word) (j : ℕ) : F := ((Sha256.half16 (ws.getD (j / 2) 0) (j % 2) : ℕ) : F)

/-- A segment's summary: the limbs of `H` of its incoming vector, then of its outgoing one. -/
def summ (p : ℕ → F) (j : ℕ) : F :=
  if j < 16 then half (H (vecW p inIdx)) j else half (H (vecW (withOne p) outIdx)) (j - 16)

/-- A summary's 32 limbs as words. -/
def vals32 (v : ℕ → F) : List Word := (List.range NS).map fun i => BitVec.ofNat 32 (v i).val

/-- `pubsDigest(key, v)` over a 32-limb summary. -/
def sd (key : List Word) (v : ℕ → F) : List Word := H (key ++ vals32 v)

set_option maxRecDepth 100000 in
theorem inIdx_all : inIdx.all (fun k => decide (k < NP)) = true := by rfl
set_option maxRecDepth 100000 in
theorem outIdx_all : outIdx.all (fun k => decide (k ≤ NP)) = true := by rfl
theorem inIdx_lt : ∀ k ∈ inIdx, k < NP := fun k hk => by simpa using List.all_eq_true.mp inIdx_all k hk
theorem outIdx_le : ∀ k ∈ outIdx, k ≤ NP := fun k hk => by simpa using List.all_eq_true.mp outIdx_all k hk

theorem pubsDigest_res_pack {ρ : ℕ → Q} {n : ℕ} {key pubs : List ℕ} (h : Holds ρ (pubsDigest n key pubs).ops) :
    ∀ i < 8, ρ ((pubsDigest n key pubs).res.getD i 0) = pack (word (ρ ((pubsDigest n key pubs).res.getD i 0))) := by
  dsimp only [pubsDigest] at h ⊢
  rw [holds_append] at h
  exact blake2s_res_pack h.2

theorem pubsDigest_length (n : ℕ) (key pubs : List ℕ) : (pubsDigest n key pubs).res.length = 8 := by
  simp [pubsDigest, blake2s]

/-- A state vector's digest, from the gadget. -/
theorem vec_digest {ρ : ℕ → Q} {n : ℕ} {idx : List ℕ} {q : ℕ → F} (h : Holds ρ (pubsDigest n [] idx).ops)
    (hq : ∀ k ∈ idx, (ρ k).a = q k) (hl : 4 * idx.length < 2 ^ 32) :
    ∀ i < 8, word (ρ ((pubsDigest n [] idx).res.getD i 0)) = (H (vecW q idx)).getD i 0 := by
  intro i hi
  rw [pubsDigest_sound h (by simpa using hl) i hi]
  have e : ([] : List ℕ).map (word ∘ ρ) ++ idx.map (fun p => BitVec.ofNat 32 (ρ p).a.val) = vecW q idx := by
    simp only [List.map_nil, List.nil_append, vecW]
    exact List.map_congr_left fun k hk => by rw [hq k hk]
  rw [e, H, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp [vecW]

/-- The split into u16 limbs: limb `j` is half `j % 2` of word `j / 2`. -/
theorem split16_sound {ρ : ℕ → Q} {n : ℕ} {ws : List ℕ} (h : Holds ρ (split16 n ws).ops)
    (hpk : ∀ w < 8, ρ (ws.getD w 0) = pack (word (ρ (ws.getD w 0)))) :
    ∀ j < 16, (ρ ((split16 n ws).res.getD j 0)).a = ((Sha256.half16 (word (ρ (ws.getD (j / 2) 0))) (j % 2) : ℕ) : F) := by
  dsimp only [split16] at h ⊢
  have hiC : ρ n = lit 0 1 0 0 := by
    have := h _ List.mem_cons_self; simpa [Op.holds] using this
  have hs0 : Holds ρ _ := fun op hm => h op (List.mem_cons_of_mem _ hm)
  intro j hj
  set w := j / 2
  have hw8 : w < 8 := by omega
  have hs := fun (op : Op) (hop : op ∈ _) => hs0 op (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw8, hop⟩)
  set r := n + 1 + 4 * w
  have g0 := hs (.guessU16 r (.coord 0 (.reg (ws.getD w 0)))) (by simp [r])
  have g1 := hs (.guessU16 (r + 1) (.coord 1 (.reg (ws.getD w 0)))) (by simp [r])
  have gm := hs (.mul (r + 2) (r + 1) n) (by simp [r])
  have ga := hs (.add (r + 3) r (r + 2)) (by simp [r])
  have ge := hs (.eq (r + 3) (ws.getD w 0)) (by simp [r])
  simp only [Op.holds] at g0 g1 gm ga ge
  rw [ga, gm, hiC, lohi g0.1 g1.1, hpk w hw8] at ge
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]
  have ea := congrArg Q.a ge
  have eb := congrArg Q.b ge
  simp only [pack] at ea eb
  rcases Nat.mod_two_eq_zero_or_one j with h2 | h2
  · rw [h2, Nat.add_zero, ea]; rfl
  · rw [h2, show n + 1 + 4 * (j / 2) + 1 = r + 1 from rfl, eb]; rfl

theorem split16_len (n : ℕ) (ws : List ℕ) : (split16 n ws).res.length = 16 := by simp [split16]

theorem vals32_length (v : ℕ → F) : (vals32 v).length = NS := by simp [vals32]

/-- **The set leaf's output is sound.** -/
theorem leafOut_sound {ρ : ℕ → Q} (h : Holds ρ leafOutOps) {p : ℕ → F} (hp : ∀ j < NP, (ρ j).a = p j) :
    wordsOf ρ setLeafOut.results = sd zeroKey (summ p) := by
  simp only [leafOutOps, holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, hi⟩, ho⟩, hsi⟩, hso⟩, hk⟩, hd⟩ := h
  have hone : (ρ NP).a = 1 := by
    have := h0 _ (List.mem_cons_of_mem _ List.mem_cons_self)
    simp only [Op.holds] at this
    rw [this]; simp [lit]
  have din : ∀ i < 8, word (ρ (hIn.res.getD i 0)) = (H (vecW p inIdx)).getD i 0 := vec_digest (q := p) hi (fun k hk => hp k (inIdx_lt k hk)) (by simp [inIdx, chal])
  have dout : ∀ i < 8, word (ρ (hOut.res.getD i 0)) = (H (vecW (withOne p) outIdx)).getD i 0 :=
    vec_digest (q := withOne p) ho (fun k hk => by
    unfold withOne
    split_ifs with e
    · rw [e, hone]
    · exact hp k (lt_of_le_of_ne (outIdx_le k hk) e)) (by simp [outIdx, chal])
  have sin : ∀ j < 16, (ρ (sIn.res.getD j 0)).a = ((Sha256.half16 (word (ρ (hIn.res.getD (j / 2) 0))) (j % 2) : ℕ) : F) :=
    split16_sound hsi (pubsDigest_res_pack hi)
  have sout : ∀ j < 16, (ρ (sOut.res.getD j 0)).a = ((Sha256.half16 (word (ρ (hOut.res.getD (j / 2) 0))) (j % 2) : ℕ) : F) :=
    split16_sound hso (pubsDigest_res_pack ho)
  have hz : wordsOf ρ leafKey = zeroKey := by
    apply List.ext_getElem (by simp [wordsOf, leafKey, zeroKey])
    intro j hj _
    have hj8 : j < 8 := by simpa [wordsOf, leafKey] using hj
    have := hk _ (List.mem_map.mpr ⟨sOut.next + j, List.mem_map.mpr ⟨j, List.mem_range.mpr hj8, rfl⟩, rfl⟩)
    simp only [wordsOf, leafKey, List.getElem_map, List.getElem_range, Function.comp, const_word this (by norm_num),
      zeroKey, List.getElem_replicate]
    rfl
  have hres : (sIn.res ++ sOut.res).length = NS := by
    rw [List.length_append, (show sIn.res.length = 16 from split16_len _ _), (show sOut.res.length = 16 from split16_len _ _)]; rfl
  have e2 : (sIn.res ++ sOut.res).map (fun r => BitVec.ofNat 32 (ρ r).a.val) = vals32 (summ p) := by
    apply List.ext_getElem (by rw [List.length_map, hres, vals32_length])
    intro j h1 h2
    have hj : j < NS := by simpa [vals32] using h2
    simp only [List.getElem_map, vals32, List.getElem_range]
    congr 2
    by_cases hlt : j < 16
    · rw [List.getElem_append_left (by rw [(show sIn.res.length = 16 from split16_len _ _)]; omega), summ, if_pos hlt, half,
        ← List.getD_eq_getElem _ 0, sin j hlt, din _ (by omega)]
    · rw [List.getElem_append_right (by rw [(show sIn.res.length = 16 from split16_len _ _)]; omega), summ, if_neg hlt, half,
        ← List.getD_eq_getElem _ 0]
      rw [(show sIn.res.length = 16 from split16_len _ _)]
      rw [sout (j - 16) (by have : NS = 32 := rfl; omega), dout _ (by have : NS = 32 := rfl; omega)]
  have hz' : leafKey.map (word ∘ ρ) = zeroKey := hz
  have hlen : 4 * (leafKey.length + (sIn.res ++ sOut.res).length) = 4 * (zeroKey ++ vals32 (summ p)).length := by
    rw [hres]; simp [leafKey, zeroKey, vals32, NS]
  show wordsOf ρ leafDg.res = _
  rw [leafDg, wordsOf_eq (pubsDigest_length _ _ _) (pubsDigest_sound hd (by rw [hlen]; simp [zeroKey, vals32, NS])),
    sd, H, hz', e2, hlen]

/-! ### The node -/

theorem vals32_inj {v w : ℕ → F} (h : vals32 v = vals32 w) : ∀ i < NS, v i = w i := by
  intro i hi
  have := congrArg (fun l => l.getD i 0) h
  simp only [vals32, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.getD_some] at this
  exact ofNat_val_inj this

/-- Digests of `key ++ summary` with 8-word keys agree: equal keys and summaries, or a collision. -/
theorem sd_eq {k k' : List Word} {v w : ℕ → F} (hk : k.length = 8) (hk' : k'.length = 8) (h : sd k v = sd k' w) :
    (k = k' ∧ ∀ i < NS, v i = w i) ∨ Collision := by
  rcases H_eq (by simp [hk, vals32_length, NS]) (by simp [hk', vals32_length, NS]) h with e | c
  · obtain ⟨e1, e2⟩ := List.append_inj e (by rw [hk, hk'])
    exact Or.inl ⟨e1, vals32_inj e2⟩
  · exact Or.inr c

theorem pubsDigest_sd {ρ : ℕ → Q} {n : ℕ} {key : List ℕ} {f : ℕ → ℕ} (hk : key.length = 8)
    (h : Holds ρ (pubsDigest n key ((List.range NS).map f)).ops) :
    wordsOf ρ (pubsDigest n key ((List.range NS).map f)).res = sd (wordsOf ρ key) (fun i => (ρ (f i)).a) := by
  rw [wordsOf_eq (pubsDigest_length _ _ _) (pubsDigest_sound h (by simp [hk, NS]))]
  simp only [sd, H, wordsOf, vals32, List.length_append, List.length_map, List.length_range, hk, List.map_map]
  rfl

/-- A child's summary limbs. -/
def childSum (ρ : ℕ → Q) (c : Out ChildRegs) : ℕ → F := fun k => (ρ (c.res.pubs k)).a

theorem schild_key_length (n i : ℕ) : (schild n i).res.key.length = 8 := by simp [schild, guessHash]
theorem schild_chash_length (n i : ℕ) : (schild n i).res.chash.length = 8 := by simp [schild]

theorem schild_digest {ρ : ℕ → Q} {n i : ℕ} (h : Holds ρ (schild n i).ops) :
    wordsOf ρ (schild n i).res.digest = sd (wordsOf ρ (schild n i).res.key) (childSum ρ (schild n i)) := by
  dsimp only [schild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨-, -⟩, hdg⟩, -⟩, -⟩ := h
  exact pubsDigest_sd (f := (n + ·)) (guessHash_length _ _) hdg

theorem schild_hook (n i : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (schild n i).res.digest) (schild n i).res.chash ∈ (schild n i).ops := by
  refine ⟨(guessHash (pubsDigest (guessHash (n + NS) (EXT * i + NS)).next
    (guessHash (n + NS) (EXT * i + NS)).res ((List.range NS).map (n + ·))).next (EXT * i + NS + 8)).res,
    guessHash_length _ _, ?_⟩
  simp [schild]

theorem snode_parts {ρ : ℕ → Q} (h : Holds ρ setNodeProgram.ops) :
    Holds ρ sC0.ops ∧ Holds ρ sC1.ops ∧ Holds ρ sLink ∧ Holds ρ sKey.ops ∧ Holds ρ sDigest.ops := by
  simp only [setNodeProgram, holds_append] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, hl⟩, hk⟩, hd⟩ := h
  exact ⟨h0, h1, hl, hk, hd⟩

theorem snode_key {ρ : ℕ → Q} (h : Holds ρ setNodeProgram.ops) :
    wordsOf ρ sKey.res = keyOf (wordsOf ρ sC0.res.chash) (wordsOf ρ sC0.res.key) (wordsOf ρ sC1.res.chash)
      (wordsOf ρ sC1.res.key) := by
  have hk := (snode_parts h).2.2.2.1
  rw [sKey, wordsOf_eq (blake2s_length _ _ _) (blake2s_words hk (by norm_num))]
  simp only [keyOf, H, wordsOf, List.map_append, List.length_append, List.length_map,
    schild_chash_length, schild_key_length, sC0, sC1]

/-- The node's output limb registers. -/
def outR (i : ℕ) : ℕ := if i < 16 then sC0.res.pubs i else sC1.res.pubs i

theorem sOuts_eq : sOuts = (List.range NS).map outR := by
  apply List.ext_getElem (by simp [sOuts, NS])
  intro i h1 h2
  have hi : i < 32 := by simpa [NS] using h2
  simp only [List.getElem_map, List.getElem_range, outR]
  by_cases hlt : i < 16
  · simp only [if_pos hlt, sOuts]; rw [List.getElem_append_left (by simp; omega)]; simp
  · simp only [if_neg hlt, sOuts]; rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    congr 1; omega

/-- The node's output summary. -/
def outSum (ρ : ℕ → Q) : ℕ → F := fun i => (ρ (outR i)).a

theorem snode_digest {ρ : ℕ → Q} (h : Holds ρ setNodeProgram.ops) :
    wordsOf ρ setNodeProgram.results = sd (wordsOf ρ sKey.res) (outSum ρ) := by
  have hd := (snode_parts h).2.2.2.2
  show wordsOf ρ sDigest.res = _
  rw [sDigest, sOuts_eq] at hd ⊢
  exact pubsDigest_sd (blake2s_length _ _ _) hd

/-- **The link**: the right child's incoming limbs are the left's outgoing ones. -/
theorem snode_link {ρ : ℕ → Q} (h : Holds ρ setNodeProgram.ops) :
    ∀ j < 16, childSum ρ sC1 j = childSum ρ sC0 (16 + j) := by
  have hl := (snode_parts h).2.2.1
  intro j hj
  have := hl _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Op.holds] at this
  simp only [childSum, this]

theorem shook_mem0 : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 0 (root ++ sC0.res.digest) sC0.res.chash ∈ setNodeProgram.ops := by
  obtain ⟨r, hr, hm⟩ := schild_hook 0 0
  exact ⟨r, hr, by simp only [setNodeProgram, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl hm)))⟩

theorem shook_mem1 : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 1 (root ++ sC1.res.digest) sC1.res.chash ∈ setNodeProgram.ops := by
  obtain ⟨r, hr, hm⟩ := schild_hook sC0.next 1
  exact ⟨r, hr, by simp only [setNodeProgram, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr hm)))⟩

/-! ### The tree -/

/-- Consecutive segments link: the next one's incoming digest is the previous one's outgoing digest. -/
def Links (p q : ℕ → F) : Prop := ∀ j < 16, summ p (16 + j) = summ q j

/-- **A chain of proven segments** with summary `v`: nonempty, each `SegOk`, linked, `v` the first's
incoming limbs and the last's outgoing ones. -/
def Chain (SegOk : (ℕ → F) → Prop) (v : ℕ → F) : Prop :=
  ∃ ps : List (ℕ → F), ∃ p0 pk : ℕ → F, ps.head? = some p0 ∧ ps.getLast? = some pk ∧ (∀ p ∈ ps, SegOk p) ∧
    ps.IsChain Links ∧ (∀ j < 16, v j = summ p0 j) ∧ (∀ j < 16, v (16 + j) = summ pk (16 + j))

/-- A set leaf's guarantee: its output is the digest of a proven segment's summary. -/
def LeafOkS (SegOk : (ℕ → F) → Prop) (d : List Word) : Prop := ∃ p, SegOk p ∧ d = sd zeroKey (summ p)

theorem chain_congr {SegOk : (ℕ → F) → Prop} {v w : ℕ → F} (h : ∀ i < NS, v i = w i) (hv : Chain SegOk v) :
    Chain SegOk w := by
  obtain ⟨ps, p0, pk, h0, hk, hok, hc, hi, ho⟩ := hv
  exact ⟨ps, p0, pk, h0, hk, hok, hc, fun j hj => by rw [← h j (by unfold NS; omega)]; exact hi j hj,
    fun j hj => by rw [← h (16 + j) (by unfold NS; omega)]; exact ho j hj⟩

theorem chain_join {SegOk : (ℕ → F) → Prop} {u v w : ℕ → F} (hu : Chain SegOk u) (hv : Chain SegOk v)
    (hl : ∀ j < 16, v j = u (16 + j)) (hw : ∀ i < NS, w i = if i < 16 then u i else v i) : Chain SegOk w := by
  obtain ⟨as, a0, ak, ha0, hak, haok, hac, hai, hao⟩ := hu
  obtain ⟨bs, b0, bk, hb0, hbk, hbok, hbc, hbi, hbo⟩ := hv
  refine ⟨as ++ bs, a0, bk, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.head?_append, ha0]; rfl
  · rw [List.getLast?_append, hbk]; rfl
  · intro p hp
    rcases List.mem_append.mp hp with h | h
    · exact haok p h
    · exact hbok p h
  · rw [List.isChain_append]
    refine ⟨hac, hbc, fun x hx y hy => ?_⟩
    rw [hak] at hx; rw [hb0] at hy
    cases hx; cases hy
    intro j hj
    rw [← hao j hj, ← hl j hj, hbi j hj]
  · intro j hj; rw [hw j (by unfold NS; omega), if_pos hj]; exact hai j hj
  · intro j hj; rw [hw (16 + j) (by unfold NS; omega), if_neg (by omega)]; exact hbo j hj

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {SegOk : (ℕ → F) → Prop}

/-- **A set tree is sound.** A satisfied circuit with the hash and key of tree shape `t`, outputting
`pubsDigest(key, v)`, has `v` the summary of a chain of proven, linked segments (or Blake2s has a
collision). -/
theorem stree_sound (T : Trust Acc SatC VGates leafH nodeH setNodeProgram (LeafOkS SegOk))
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : BlockRec.Tree) (v : ℕ → F), SatC (t.hash leafH nodeH) (sd (t.key leafH nodeH) v) → Chain SegOk v ∨ Collision
  | .leaf L, v, hs => by
    obtain ⟨p, hp, hd⟩ := T.leafSound L _ hs
    rcases sd_eq (Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · refine Or.inl ⟨[p], p, p, rfl, rfl, by simpa using hp, List.isChain_singleton _, fun j hj => e j (by unfold NS; omega),
        fun j hj => e (16 + j) (by unfold NS; omega)⟩
    · exact Or.inr c
  | .node l r, v, hs => by
    obtain ⟨ρ, hρ, hres, hg⟩ := T.nodeCircuit _ hs
    obtain ⟨r0, hr0, hm0⟩ := shook_mem0
    obtain ⟨r1, hr1, hm1⟩ := shook_mem1
    have s0 := T.recVerifies ρ _ _ _ (hg _ _ _ hm0)
    have s1 := T.recVerifies ρ _ _ _ (hg _ _ _ hm1)
    rw [List.drop_left' hr0] at s0
    rw [List.drop_left' hr1] at s1
    obtain ⟨h0, h1, -, -, -⟩ := snode_parts hρ
    have d0 : wordsOf ρ sC0.res.digest = sd (wordsOf ρ sC0.res.key) (childSum ρ sC0) := schild_digest h0
    have d1 : wordsOf ρ sC1.res.digest = sd (wordsOf ρ sC1.res.key) (childSum ρ sC1) := schild_digest h1
    rw [d0] at s0
    rw [d1] at s1
    rw [snode_digest hρ] at hres
    have kl : (wordsOf ρ sKey.res).length = 8 := by rw [wordsOf_length]; exact blake2s_length _ _ _
    rcases sd_eq kl (Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr c
    rw [snode_key hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eq (w8 _ (schild_chash_length _ _)) (w8 _ (schild_key_length _ _)) (w8 _ (schild_chash_length _ _))
      (w8 _ (schild_key_length _ _)) (by cases l <;> simp [Tree.hash, hl, hn]) (Tree.key_length leafH nodeH l)
      (by cases r <;> simp [Tree.hash, hl, hn]) (Tree.key_length leafH nodeH r) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr c
    have e1' : wordsOf ρ sC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ sC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ sC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ sC1.res.key = r.key leafH nodeH := e4
    have s0' : SatC (l.hash leafH nodeH) (sd (l.key leafH nodeH) (childSum ρ sC0)) := by
      rw [← e1', ← e2']; exact s0
    have s1' : SatC (r.hash leafH nodeH) (sd (r.key leafH nodeH) (childSum ρ sC1)) := by
      rw [← e3', ← e4']; exact s1
    rcases stree_sound T hl hn l _ s0' with cl | c
    swap; · exact Or.inr c
    rcases stree_sound T hl hn r _ s1' with cr | c
    swap; · exact Or.inr c
    refine Or.inl (chain_join cl cr (snode_link hρ) fun i hi => ?_)
    rw [← ev i hi]
    simp only [outSum, outR, childSum]
    split_ifs <;> rfl

end

end StarkedAir.Circuit.SetTree
