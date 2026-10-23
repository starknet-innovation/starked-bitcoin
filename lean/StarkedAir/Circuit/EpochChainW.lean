/-
**The epoch root and the chain of epochs, up to a named collision** (`RecCR`'s style for
`EpochRootSound.rootK_epoch` and `EpochChainSound`).

`rootK_epoch`, `root_range`, `chain_sound`, `chain_cover` and `chain_verify` conclude `… ∨ Collision`,
which `RecCR.collision_true` makes vacuous. Here they are restated as in `RecCR`:
- **Witness-explicit named hypotheses**: the block trees' `RecCR.TrustKW` (node assignments and leaf
  public inputs as functions of the claimed digest), and for the chain `TrustEW`, which adds the epoch
  root's and the join's assignments as functions `rootWit M prevV s d`, `joinWit v d` of the circuit
  and its output digest (`TrustEW.toTrustE` and `TrustE.exists_w`: the same hypothesis as `TrustE`).
- **Conclusions `… ∨ Collides ps`**, `ps` a finite list of message pairs computed from the shapes, the
  given assignment / digests and the witness functions (`rootPairs`, `childPairs`, `chainPairs`,
  `accPairs`): the pairs the proof compares. `Collides ps` says one of them differs and has one Blake2s
  digest: a concrete collision, found by checking the pairs.
- The chain's opening is itself computed from the witnesses (`extract`): `chain_soundW` states that the
  chain `extract joinWit c d` is valid and has digest `d`.
-/
import StarkedAir.Circuit.EpochChainSound
import StarkedAir.Circuit.RecCR

namespace StarkedAir.Circuit.EpochChain

open StarkedAir StarkedAir.Circuit Q
local notation "Word" => Spec.Blake2s.Word
open StarkedAir.Circuit.BlockTree (SumOkP)
open StarkedAir.Circuit.BlockRec (H H_length HookGates childSum wordsOf_eq wordsOf_length)
open StarkedAir.Block (RngOkP)
open StarkedAir.Circuit.BlockNodeK (TreeK keyOfK kid kid_hook kid_digest kid_ops_mem kid_holds kid_chash_length
  kid_key_length)
open StarkedAir.Circuit.EpochRoot (epochRoot parts digestWords root_parts links_sound val_add_lt30 root_digest
  digestWords_length results_length kids_sub root_sound streamWord seedWords semSeed seedMsg linked_of_idx
  root_seedWords)
open StarkedAir.Circuit.RecCR (TrustKW LeafAt Collides CollidesAt collides_head collides_second H_eqC keyOfK_eqC
  pairsK treeK_soundW)

/-! ### The epoch root -/

/-- **The pairs the epoch root's soundness compares**, for the root assignment `ρ` and the digest's
expected rest `rest`: the root's digest message against `K ‖ rest` (`K` the verifier's key over the
trees `ts`), the key message (children's circuit hashes and keys) against the trees' hashes and keys,
then each child tree's pairs under the summary `ρ` gives it. -/
noncomputable def rootPairs (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (nw : ℕ → ℕ → List Word → ℕ → Q)
    (lw : ℕ → List Word → ℕ → F) (M : ℕ) (prevV : Bool) (ts : ℕ → TreeK) (ρ : ℕ → Q) (rest : List Word) :
    List (List Word × List Word) :=
  (digestWords ρ M prevV, keyOfK M (fun i => (ts i).hash leafH nodeH) (fun i => (ts i).key leafH nodeH) ++ rest) ::
  ((List.range M).flatMap (fun i => wordsOf ρ (kid i).res.chash ++ wordsOf ρ (kid i).res.key),
    (List.range M).flatMap (fun i => (ts i).hash leafH nodeH ++ (ts i).key leafH nodeH)) ::
  (List.range M).flatMap fun i => pairsK leafH nodeH nw lw (ts i) (childSum ρ (kid i))

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {nw : ℕ → ℕ → List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

/-- **The children are proven, up to a named collision** (`EpochRoot.root_children`). -/
theorem root_childrenW {ok : (ℕ → F) → Prop} (T : TrustKW Acc SatC VGates leafH nodeH (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    {M : ℕ} {prevV : Bool} (hM : 64 * M < 2 ^ 32) (hR : 4 * (parts M prevV).dpubs.length < 2 ^ 32)
    (ts : ℕ → TreeK) (hok : ∀ i < M, (ts i).Ok) {ρ : ℕ → Q}
    (h : Holds ρ (epochRoot M prevV).ops) (hg : HookGates VGates ρ (epochRoot M prevV).ops) (rest : List Word)
    (hd : wordsOf ρ (epochRoot M prevV).results =
      H (keyOfK M (fun i => (ts i).hash leafH nodeH) (fun i => (ts i).key leafH nodeH) ++ rest)) :
    ((∀ i < M, SumOkP ok (childSum ρ (kid i))) ∧ (digestWords ρ M prevV).drop 8 = rest) ∨
      Collides (rootPairs leafH nodeH nw lw M prevV ts ρ rest) := by
  by_cases col : Collides (rootPairs leafH nodeH nw lw M prevV ts ρ rest)
  · exact Or.inr col
  left
  obtain ⟨hdig, -, hkey⟩ := root_digest h hR hM
  have hdl := digestWords_length (ρ := ρ) (M := M) (prevV := prevV)
  have hres : wordsOf ρ (epochRoot M prevV).results = H (digestWords ρ M prevV) := by
    rw [wordsOf_eq results_length hdig, H, hdl]
  rw [hres] at hd
  have hlenK : (keyOfK M (fun i => (ts i).hash leafH nodeH) (fun i => (ts i).key leafH nodeH)).length = 8 := H_length _
  have e := (H_eqC _ _ hd).resolve_right fun c => col (collides_head c)
  have hk8 : (parts M prevV).key.res.length = 8 := by show ((List.range 8).map _).length = 8; simp
  have hsplit : digestWords ρ M prevV = (parts M prevV).key.res.map (word ∘ ρ) ++ (digestWords ρ M prevV).drop 8 := by
    conv_lhs => rw [← List.take_append_drop 8 (digestWords ρ M prevV)]
    congr 1
  rw [hsplit] at e
  obtain ⟨eK, eR⟩ := List.append_inj e (by rw [List.length_map, hk8, hlenK])
  refine ⟨fun i hi => ?_, eR⟩
  have hKc : (parts M prevV).key.res.map (word ∘ ρ) =
      keyOfK M (fun i => wordsOf ρ (kid i).res.chash) (fun i => wordsOf ρ (kid i).res.key) := by
    have : (parts M prevV).key.res.map (word ∘ ρ) = wordsOf ρ (parts M prevV).key.res := rfl
    rw [this, wordsOf_eq hk8 hkey, keyOfK, H, ← BlockNodeK.keyMsg_words M, List.length_map]
    rw [show 4 * (BlockNodeK.keyMsg M).length = 64 * M by
      have := congrArg List.length (BlockNodeK.keyMsg_words (ρ := ρ) M)
      rw [List.length_map, BlockNodeK.flat_length (fun i => by simp [wordsOf, kid_chash_length])
        (fun i => by simp [wordsOf, kid_key_length])] at this
      omega]
  rw [hKc] at eK
  have hkh : ∀ t : TreeK, (t.hash leafH nodeH).length = 8 := fun t => by cases t <;> simp [TreeK.hash, hl, hn]
  have eks := (keyOfK_eqC (fun i => by rw [wordsOf_length, kid_chash_length])
    (fun i => by rw [wordsOf_length, kid_key_length]) (fun i => hkh (ts i))
    (fun i => TreeK.key_length leafH nodeH (ts i)) eK).resolve_right fun c => col (collides_second c)
  obtain ⟨r, hr, hm⟩ := kid_hook i
  have s := T.recVerifies ρ _ _ _ (hg _ _ _ (kids_sub (kid_ops_mem hi hm)))
  rw [List.drop_left' hr, kid_digest (kid_holds hi (root_parts h).1), (eks i hi).1, (eks i hi).2] at s
  exact (treeK_soundW T hl hn (ts i) (hok i hi) _ s).resolve_right fun c => col (c.mono fun x hx =>
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hx⟩)))

/-- **The epoch root, composed, up to a named collision** (`EpochRoot.rootK_epoch`). With the root's
assignment `ρ` (its ops and hook gates hold) and output digest `H (K ‖ rest)` (`K` the verifier's key
over the trees `ts`): the digest's rest is `rest`; the `M` children are proven ranges, consecutive from
`lo` to `hi + 1`, so their union is a proven range (`RngOkP`) from `lo` with child 0's challenge; that
challenge is the low 31 bits of the stream over the seed, the seed being Blake2s of the semantic message
`semSeed`. Or two of `rootPairs` collide. -/
theorem rootK_epochW {ok : (ℕ → F) → Prop} (T : TrustKW Acc SatC VGates leafH nodeH (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    {M : ℕ} {prevV : Bool} (hM0 : 0 < M) (hM : 64 * M < 2 ^ 32)
    (hR : 4 * (parts M prevV).dpubs.length < 2 ^ 32)
    (hS : 4 * (seedMsg M prevV).length < 2 ^ 32)
    (ts : ℕ → TreeK) (hok : ∀ i < M, (ts i).Ok) {ρ : ℕ → Q}
    (h : Holds ρ (epochRoot M prevV).ops) (hg : HookGates VGates ρ (epochRoot M prevV).ops) (rest : List Word)
    (hd : wordsOf ρ (epochRoot M prevV).results =
      H (keyOfK M (fun i => (ts i).hash leafH nodeH) (fun i => (ts i).key leafH nodeH) ++ rest)) :
    let v : ℕ → ℕ → F := fun i => childSum ρ (kid i)
    ((digestWords ρ M prevV).drop 8 = rest ∧
      (∃ n, 0 < n ∧ RngOkP ok ⟨(ρ (parts M prevV).inp.res.lo).a.val, n,
        Block.RunSum.pQ (v 0) 2 + (((List.range (M - 1)).map fun i => v (i + 1)).map fun w => Block.RunSum.pQ w 2).sum,
        (v 0 6).val + (((List.range (M - 1)).map fun i => v (i + 1)).map fun w => (w 6).val).sum,
        Block.RunSum.pQ (v 0) 7, Block.RunSum.pQ (v 0) 11, Block.RunSum.pQ (v 0) 15⟩) ∧
      (ρ ((kid (M - 1)).res.pubs BlockNode.LO) + ρ ((kid (M - 1)).res.pubs BlockNode.NN) = ρ (parts M prevV).inp.res.hi + lit 1 0 0 0) ∧
      (∀ j < 12, (v 0 (7 + j)).val = (streamWord ρ M prevV j).toNat % 2 ^ 31) ∧
      seedWords ρ M prevV = (List.range 8).map (blake2sWords (semSeed ρ M prevV) (4 * (semSeed ρ M prevV).length))) ∨
    Collides (rootPairs leafH nodeH nw lw M prevV ts ρ rest) := by
  intro v
  rcases root_childrenW T hl hn hM hR ts hok h hg rest hd with ⟨hkids, hrest'⟩ | col
  swap; · exact Or.inr col
  have bnd : ∀ i < M, (v i 0).val < 2 ^ 30 ∧ (v i 1).val < 2 ^ 30 ∧ (v i 6).val < 2 ^ 30 := fun i hi => by
    obtain ⟨_, _, _, h0, h1, h6, _⟩ := hkids i hi
    exact ⟨h0, h1, h6⟩
  have rs := root_sound hM0 h hS (fun i hi => (bnd i hi).2.2)
  obtain ⟨⟨e0, elink, eend, -, -, -⟩, ech, ech0, -⟩ := rs
  left
  refine ⟨hrest', ?_, eend, fun j hj => (ech0 j hj).1, root_seedWords h⟩
  have hlink : BlockTree.Linked' (v 0) ((List.range (M - 1)).map fun i => v (i + 1)) := by
    have := linked_of_idx v (M - 1) 0 (fun i hi => by
      have e := congrArg Q.a (elink i (by omega))
      simp only [Nat.zero_add]
      show ((ρ ((kid (i + 1)).res.pubs BlockNode.LO)).a).val = ((ρ ((kid i).res.pubs BlockNode.LO)).a).val + ((ρ ((kid i).res.pubs BlockNode.NN)).a).val
      rw [e, add_a]
      exact val_add_lt30 (bnd i (by omega)).1 (bnd i (by omega)).2.1)
    simpa using this
  have hch : ∀ w ∈ (List.range (M - 1)).map (fun i => v (i + 1)), ∀ j < 12, w (7 + j) = v 0 (7 + j) := by
    intro w hw j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
    exact congrArg Q.a (ech (i + 1) (by have := List.mem_range.mp hi; omega) j hj)
  obtain ⟨n, hn0, hr⟩ := BlockRec.forest_rng'P _ (v 0) (hkids 0 hM0)
    (fun w hw => by obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw; exact hkids (i + 1) (by have := List.mem_range.mp hi; omega))
    hlink hch
  refine ⟨n, hn0, ?_⟩
  have elo : (v 0 0).val = (ρ (parts M prevV).inp.res.lo).a.val := by
    show ((ρ ((kid 0).res.pubs BlockNode.LO)).a).val = _
    rw [e0]
  rw [← elo]; exact hr

/-- **An epoch root bounds its range, up to a named collision** (`root_range`). -/
theorem root_rangeW {ok : (ℕ → F) → Prop} (T : TrustKW Acc SatC VGates leafH nodeH (LeafAt ok) nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    {M : ℕ} {prevV : Bool} (hM0 : 0 < M) (hM : 68 + 64 * M < 2 ^ 32)
    (ts : ℕ → TreeK) (hok : ∀ i < M, (ts i).Ok) {ρ : ℕ → Q}
    (h : Holds ρ (epochRoot M prevV).ops) (hg : HookGates VGates ρ (epochRoot M prevV).ops) (rest : List Word)
    (hd : wordsOf ρ (epochRoot M prevV).results =
      H (keyOfK M (fun i => (ts i).hash leafH nodeH) (fun i => (ts i).key leafH nodeH) ++ rest)) :
    ((digestWords ρ M prevV).drop 8 = rest ∧
      (ρ (parts M prevV).inp.res.lo).a.val ≤ (ρ (parts M prevV).inp.res.hi).a.val ∧
      (ρ (parts M prevV).inp.res.hi).a.val < 2 ^ 30) ∨ Collides (rootPairs leafH nodeH nw lw M prevV ts ρ rest) := by
  have hR : 4 * (parts M prevV).dpubs.length < 2 ^ 32 := by rw [dpubs_length]; omega
  rcases root_childrenW T hl hn (by omega) hR ts hok h hg rest hd with ⟨hkids, hrest'⟩ | col
  swap; · exact Or.inr col
  left
  refine ⟨hrest', ?_⟩
  have bnd : ∀ i < M, ((ρ ((kid i).res.pubs BlockNode.LO)).a).val < 2 ^ 30 ∧
      1 ≤ ((ρ ((kid i).res.pubs BlockNode.NN)).a).val ∧ ((ρ ((kid i).res.pubs BlockNode.NN)).a).val < 2 ^ 30 := by
    intro i hi
    obtain ⟨ℓ, _, e1, h0, h1, -⟩ := hkids i hi
    exact ⟨h0, by
      show 1 ≤ (childSum ρ (kid i) 1).val
      rw [e1]; exact Nat.one_le_two_pow, h1⟩
  obtain ⟨e0, elink, eend, ⟨-, -⟩, -, hhi1⟩ := links_sound (ρ := ρ) (p := fun i => (kid i).res.pubs) hM0 (root_parts h).2.2.1
  change ρ ((kid 0).res.pubs BlockNode.LO) = ρ (parts M prevV).inp.res.lo at e0
  change ρ ((kid (M - 1)).res.pubs BlockNode.LO) + ρ ((kid (M - 1)).res.pubs BlockNode.NN) =
    ρ (parts M prevV).inp.res.hi + lit 1 0 0 0 at eend
  change ((ρ (parts M prevV).inp.res.hi + lit 1 0 0 0).a).val < 2 ^ 30 at hhi1
  have mono : ∀ i < M, (ρ (parts M prevV).inp.res.lo).a.val ≤ ((ρ ((kid i).res.pubs BlockNode.LO)).a).val := by
    intro i
    induction i with
    | zero => intro _; rw [e0]
    | succ i ih =>
      intro hi
      have e := congrArg Q.a (elink i hi)
      rw [add_a] at e
      rw [e, val_add_lt30 (bnd i (by omega)).1 (bnd i (by omega)).2.2]
      exact le_add_right (ih (by omega))
  have m1 : M - 1 < M := by omega
  have e := congrArg Q.a eend
  rw [add_a, add_a] at e
  have hS := val_add_lt30 (bnd _ m1).1 (bnd _ m1).2.2
  rw [e] at hS
  rw [add_a] at hhi1
  have h1 : (lit 1 0 0 0).a = ((1 : ℕ) : F) := rfl
  rw [h1] at hS hhi1
  have hx := ZMod.val_lt (ρ (parts M prevV).inp.res.hi).a
  have hva := ZMod.val_add (ρ (parts M prevV).inp.res.hi).a ((1 : ℕ) : F)
  rw [EpochJoin.one_val] at hva
  have hm := mono _ m1
  have hb := bnd _ m1
  by_cases hc : (ρ (parts M prevV).inp.res.hi).a.val + 1 < P
  · rw [Nat.mod_eq_of_lt hc] at hva
    rw [hva] at hS hhi1
    constructor <;> omega
  · have : (ρ (parts M prevV).inp.res.hi).a.val + 1 = P := by omega
    rw [this, Nat.mod_self] at hva
    rw [hva] at hS
    omega

end

/-! ### The chain's named hypotheses, with witnesses -/

open StarkedAir.Circuit.EpochJoin (Variant epochJoin rootChild left right joinWords outWords keyWords accWords
  rootChild_lengths rootChild_out rootWords_length)

/-- **`TrustE` with explicit witnesses** (`RecCR.TrustKW`, plus): a satisfied epoch root circuit with
identity `rootH M prevV s` and output `d` is satisfied by the assignment `rootWit M prevV s d`, a join with
identity `joinH v` by `joinWit v d` (what an extractor computes from the proofs), with their hook gates. -/
structure TrustEW (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (rootH : ℕ → Bool → ℕ → List Word)
    (joinH : Variant → List Word) (LeafW : List Word → (ℕ → F) → Prop)
    (nodeWit : ℕ → ℕ → List Word → ℕ → Q) (leafWit : ℕ → List Word → ℕ → F)
    (rootWit : ℕ → Bool → ℕ → List Word → ℕ → Q) (joinWit : Variant → List Word → ℕ → Q) : Prop
    extends TrustKW Acc SatC VGates leafH nodeH LeafW nodeWit leafWit where
  rootCircuit : ∀ M prevV s d, SatC (rootH M prevV s) d →
    Holds (rootWit M prevV s d) (epochRoot M prevV).ops ∧ wordsOf (rootWit M prevV s d) (epochRoot M prevV).results = d ∧
      HookGates VGates (rootWit M prevV s d) (epochRoot M prevV).ops
  joinCircuit : ∀ v d, SatC (joinH v) d →
    Holds (joinWit v d) (epochJoin v).ops ∧ wordsOf (joinWit v d) (epochJoin v).results = d ∧
      HookGates VGates (joinWit v d) (epochJoin v).ops

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {LeafW : List Word → (ℕ → F) → Prop}

theorem TrustEW.toTrustE {nw : ℕ → ℕ → List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}
    {rootW : ℕ → Bool → ℕ → List Word → ℕ → Q} {joinW : Variant → List Word → ℕ → Q}
    (T : TrustEW Acc SatC VGates leafH nodeH rootH joinH LeafW nw lw rootW joinW) :
    TrustE Acc SatC VGates leafH nodeH rootH joinH (fun d => ∃ p, LeafW d p) :=
  { T.toTrustKW.toTrustK with
    rootCircuit := fun M p s d h => ⟨rootW M p s d, T.rootCircuit M p s d h⟩
    joinCircuit := fun v d h => ⟨joinW v d, T.joinCircuit v d h⟩ }

/-- `TrustE` gives witness functions (by choice): `TrustEW` trusts nothing more. -/
theorem TrustE.exists_w (T : TrustE Acc SatC VGates leafH nodeH rootH joinH (fun d => ∃ p, LeafW d p)) :
    ∃ nw lw rootW joinW, TrustEW Acc SatC VGates leafH nodeH rootH joinH LeafW nw lw rootW joinW := by
  classical
  refine ⟨fun a v d => if h : SatC (nodeH a v) d then Classical.choose (T.nodeCircuit a v d h) else fun _ => Q.lit 0 0 0 0,
    fun L d => if h : SatC (leafH L) d then Classical.choose (T.leafSound L d h) else fun _ => 0,
    fun M p s d => if h : SatC (rootH M p s) d then Classical.choose (T.rootCircuit M p s d h) else fun _ => Q.lit 0 0 0 0,
    fun v d => if h : SatC (joinH v) d then Classical.choose (T.joinCircuit v d h) else fun _ => Q.lit 0 0 0 0,
    { stwoSound := T.stwoSound, nodeCircuit := fun a v d h => ?_, recVerifies := T.recVerifies,
      leafSound := fun L d h => ?_, rootCircuit := fun M p s d h => ?_, joinCircuit := fun v d h => ?_ }⟩
  · simp only [dif_pos h]; exact Classical.choose_spec (T.nodeCircuit a v d h)
  · simp only [dif_pos h]; exact Classical.choose_spec (T.leafSound L d h)
  · simp only [dif_pos h]; exact Classical.choose_spec (T.rootCircuit M p s d h)
  · simp only [dif_pos h]; exact Classical.choose_spec (T.joinCircuit v d h)

end

/-! ### The pairs a chain's soundness compares -/

theorem collides_two {a b : List Word × List Word} {ps : List (List Word × List Word)} (c : Collides [a, b]) :
    Collides (a :: b :: ps) :=
  c.mono fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact List.mem_cons_of_mem _ List.mem_cons_self
      · simp at hx

theorem collides_third {a b x : List Word × List Word} {ps : List (List Word × List Word)} (c : CollidesAt x.1 x.2) :
    Collides (a :: b :: x :: ps) :=
  ⟨x, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), c⟩

/-- **An epoch root child's pairs**: those of its root (`rootPairs`), for the root assignment
`rootWit M p s d` of its digest `d` (that of the child's opening as the join guessed it, `rootOpen`). -/
noncomputable def childPairs (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (nw : ℕ → ℕ → List Word → ℕ → Q)
    (lw : ℕ → List Word → ℕ → F) (rootW : ℕ → Bool → ℕ → List Word → ℕ → Q) (e : EpS) (p : Bool) (ρ : ℕ → Q)
    (ch : EpochJoin.Child) : List (List Word × List Word) :=
  rootPairs leafH nodeH nw lw e.M p e.ts (rootW e.M p e.s (Ep.out leafH nodeH ⟨e, rootOpen ρ ch⟩ p))
    (rootRest p (rootOpen ρ ch))

/-- A join child's opening after its key: `start ‖ end ‖ a ‖ b ‖ acc`. -/
def joinRest (ρ : ℕ → Q) (c : EpochJoin.Child) : List Word :=
  wordsOf ρ c.first ++ wordsOf ρ c.last ++ [BitVec.ofNat 32 (ρ c.lo).a.val, BitVec.ofNat 32 (ρ c.hi).a.val] ++
    wordsOf ρ c.tail

/-- **The chain of openings the witnesses give**: a join with output `d` is satisfied by `joinWit v d`; its
right child (and a base's left) is an epoch root opened as that assignment guessed it (`rootOpen`), a step's
left child is the chain extracted from the left's output digest. -/
noncomputable def extract (joinW : Variant → List Word → ℕ → Q) : Chain EpS → List Word → Chain Ep
  | .base g e0 e1, d => .base g ⟨e0, rootOpen (joinW (.base g) d) (left (.base g)).res⟩
      ⟨e1, rootOpen (joinW (.base g) d) (right (.base g)).res⟩
  | .step c e, d => .step (extract joinW c (wordsOf (joinW .step d) (left .step).res.out))
      ⟨e, rootOpen (joinW .step d) (right .step).res⟩

/-- **The pairs a chain's soundness compares** (output `d`, expected rest `rest`), for `ρ = joinWit v d`:
the join's output message against `key ‖ rest`, its key message against the pinned identities and keys,
for a step the left child's opening against the extracted chain's message and the left chain's pairs,
then the epoch root children's pairs. -/
noncomputable def chainPairs (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (rootH : ℕ → Bool → ℕ → List Word)
    (joinH : Variant → List Word) (nw : ℕ → ℕ → List Word → ℕ → Q) (lw : ℕ → List Word → ℕ → F)
    (rootW : ℕ → Bool → ℕ → List Word → ℕ → Q) (joinW : Variant → List Word → ℕ → Q) :
    Chain EpS → List Word → List Word → List (List Word × List Word)
  | .base g e0 e1, d, rest =>
    (outWords (joinW (.base g) d) (.base g),
      H (rootH e0.M g e0.s ++ e0.key leafH nodeH ++ rootH e1.M true e1.s ++ e1.key leafH nodeH) ++ rest) ::
    (keyWords (joinW (.base g) d) (.base g),
      rootH e0.M g e0.s ++ e0.key leafH nodeH ++ rootH e1.M true e1.s ++ e1.key leafH nodeH) ::
    (childPairs leafH nodeH nw lw rootW e0 g (joinW (.base g) d) (left (.base g)).res ++
      childPairs leafH nodeH nw lw rootW e1 true (joinW (.base g) d) (right (.base g)).res)
  | .step c e, d, rest =>
    (outWords (joinW .step d) .step,
      H (joinH c.variant ++ c.key leafH nodeH rootH joinH ++ rootH e.M true e.s ++ e.key leafH nodeH) ++ rest) ::
    (keyWords (joinW .step d) .step,
      joinH c.variant ++ c.key leafH nodeH rootH joinH ++ rootH e.M true e.s ++ e.key leafH nodeH) ::
    (joinWords (joinW .step d) (left .step).res,
      (extract joinW c (wordsOf (joinW .step d) (left .step).res.out)).msg leafH nodeH rootH joinH) ::
    (chainPairs leafH nodeH rootH joinH nw lw rootW joinW c (wordsOf (joinW .step d) (left .step).res.out)
        (joinRest (joinW .step d) (left .step).res) ++
      childPairs leafH nodeH nw lw rootW e true (joinW .step d) (right .step).res)

/-! ### The children of a join -/

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {nw : ℕ → ℕ → List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}
  {rootW : ℕ → Bool → ℕ → List Word → ℕ → Q} {joinW : Variant → List Word → ℕ → Q}

/-- **An epoch root child of a join is a proven root, up to a named collision** (`rootChild_ok`). -/
theorem rootChild_okW {ok : (ℕ → F) → Prop} (T : TrustEW Acc SatC VGates leafH nodeH rootH joinH (LeafAt ok) nw lw rootW joinW)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    {i n : ℕ} {p : Bool} {ρ : ℕ → Q} (hc : Holds ρ (rootChild i n p).ops) {root : List ℕ} (hroot : root.length = 8)
    (hv : VGates ρ i (root ++ (rootChild i n p).res.out) (rootChild i n p).res.chash)
    (e : EpS) (he : e.Ok) (hch : wordsOf ρ (rootChild i n p).res.chash = rootH e.M p e.s)
    (hk : wordsOf ρ (rootChild i n p).res.key = e.key leafH nodeH) :
    (RootOk leafH nodeH rootH SatC ⟨e, rootOpen ρ (rootChild i n p).res⟩ p ∧
      wordsOf ρ (rootChild i n p).res.out = Ep.out leafH nodeH ⟨e, rootOpen ρ (rootChild i n p).res⟩ p) ∨
    Collides (childPairs leafH nodeH nw lw rootW e p ρ (rootChild i n p).res) := by
  obtain ⟨hkl, hfl, hll, htl, hol, -⟩ := rootChild_lengths i n p
  have hout : wordsOf ρ (rootChild i n p).res.out = Ep.out leafH nodeH ⟨e, rootOpen ρ (rootChild i n p).res⟩ p := by
    rw [Ep.out, ← hk, ← rootWords_eq]
    exact wordsOf_H hol (by rw [rootWords_length hkl hfl hll htl]) (rootChild_out hc)
  have hwf : (rootOpen ρ (rootChild i n p).res).WF := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [rootOpen, wordsOf_length, hll, hfl, htl]
  have s := T.recVerifies ρ _ _ _ hv
  rw [List.drop_left' hroot, hch, hout] at s
  obtain ⟨h', hres, hg'⟩ := T.rootCircuit _ _ _ _ s
  have hres' : wordsOf (rootW e.M p e.s (Ep.out leafH nodeH ⟨e, rootOpen ρ (rootChild i n p).res⟩ p)) (epochRoot e.M p).results =
      H (e.key leafH nodeH ++ rootRest p (rootOpen ρ (rootChild i n p).res)) := by
    rw [hres, Ep.out, rootMsg_split]
  obtain ⟨hM0, hM, hok⟩ := he
  rcases root_rangeW T.toTrustKW hl hn hM0 hM e.ts hok h' hg' _ hres' with ⟨hdrop, hle, hlt⟩ | col
  swap; · exact Or.inr col
  rw [digestWords_drop] at hdrop
  have hf8 : (parts e.M p).inp.res.fin.length = 8 := by show ((List.range 8).map _).length = 8; simp
  have hp8 : (parts e.M p).inp.res.prev.length = 8 := by show ((List.range 8).map _).length = 8; simp
  unfold rootRest at hdrop
  obtain ⟨h1, -⟩ := List.append_inj hdrop (by cases p <;> simp [rootOpen, wordsOf_length, hf8, hp8, hll, hfl])
  obtain ⟨-, h2⟩ := List.append_inj h1 (by cases p <;> simp [rootOpen, wordsOf_length, hf8, hp8, hll, hfl])
  simp only [List.cons.injEq, and_true] at h2
  obtain ⟨xl, xh⟩ := h2
  have elo := ofNat_inj (val_lt32 _) (val_lt32 _) xl
  have ehi := ofNat_inj (val_lt32 _) (val_lt32 _) xh
  refine Or.inl ⟨⟨s, hwf, ?_, ?_⟩, hout⟩
  · show (ρ (rootChild i n p).res.lo).a.val ≤ (ρ (rootChild i n p).res.hi).a.val
    rw [← elo, ← ehi]; exact hle
  · show (ρ (rootChild i n p).res.hi).a.val < 2 ^ 30
    rw [← ehi]; exact hlt

/-- **A join with a pinned identity and key, up to a named collision** (`join_open`): the witness
`joinWit v d` satisfies the join with its hook gates, outputs `H (outWords)`, and its children's circuit
hashes and keys are `A`, `B`, `C`, `D` (`A`, `B`, `C` of 8 words). -/
theorem join_openW {ok : (ℕ → F) → Prop} (T : TrustEW Acc SatC VGates leafH nodeH rootH joinH (LeafAt ok) nw lw rootW joinW)
    {v : Variant} {d : List Word} (hs : SatC (joinH v) d) {A B C D rest : List Word} (hA : A.length = 8)
    (hB : B.length = 8) (hC : C.length = 8)
    (hd : d = H (H (A ++ B ++ C ++ D) ++ rest)) :
    (Holds (joinW v d) (epochJoin v).ops ∧ HookGates VGates (joinW v d) (epochJoin v).ops ∧
      d = H (outWords (joinW v d) v) ∧
      wordsOf (joinW v d) (left v).res.chash = A ∧ wordsOf (joinW v d) (left v).res.key = B ∧
      wordsOf (joinW v d) (right v).res.chash = C ∧ wordsOf (joinW v d) (right v).res.key = D) ∨
    Collides [(outWords (joinW v d) v, H (A ++ B ++ C ++ D) ++ rest), (keyWords (joinW v d) v, A ++ B ++ C ++ D)] := by
  by_cases col : Collides [(outWords (joinW v d) v, H (A ++ B ++ C ++ D) ++ rest),
    (keyWords (joinW v d) v, A ++ B ++ C ++ D)]
  · exact Or.inr col
  obtain ⟨h, hres, hg⟩ := T.joinCircuit v d hs
  have ho := join_out h
  rw [hres] at ho
  have e := (H_eqC _ _ (ho.symm.trans hd)).resolve_right fun c => col (collides_head c)
  generalize hK : A ++ B ++ C ++ D = K at e col
  rw [outWords_eq] at e
  simp only [List.append_assoc] at e
  obtain ⟨ek, -⟩ := List.append_inj e (by rw [H_length, H_length])
  have ek' := (H_eqC _ _ ek).resolve_right fun c => col (collides_second c)
  subst hK
  obtain ⟨k, -, -, -, -, c⟩ := EpochJoin.left_lengths v
  obtain ⟨k', -, -, -, -, c'⟩ := rootChild_lengths 1 (left v).next true
  have k' : (right v).res.key.length = 8 := k'
  have c' : (right v).res.chash.length = 8 := c'
  unfold keyWords at ek'
  simp only [List.append_assoc] at ek'
  obtain ⟨e1, ek'⟩ := List.append_inj ek' (by simp [wordsOf_length, c, hA])
  obtain ⟨e2, ek'⟩ := List.append_inj ek' (by simp [wordsOf_length, k, hB])
  obtain ⟨e3, e4⟩ := List.append_inj ek' (by simp [wordsOf_length, c', hC])
  exact Or.inl ⟨h, hg, ho, e1, e2, e3, e4⟩

/-! ### The chain, composed -/

/-- **A chain of joins is sound, up to a named collision** (`chain_sound`). Under `TrustEW`, a satisfied
join circuit with the pinned identity of `c`'s top join, whose output digest is `H(Chain.key c ‖ rest)`,
outputs the digest of the chain of openings the witnesses give (`extract joinWit c d`), which is over `c`'s
shapes and `Valid`; or two of `chainPairs c d rest` collide. -/
theorem chain_soundW {ok : (ℕ → F) → Prop} (T : TrustEW Acc SatC VGates leafH nodeH rootH joinH (LeafAt ok) nw lw rootW joinW)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    (hr : ∀ M p s, (rootH M p s).length = 8) (hj : ∀ v, (joinH v).length = 8) :
    ∀ (c : Chain EpS), c.Ok → ∀ (d rest : List Word),
      SatC (joinH c.variant) d → d = H (c.key leafH nodeH rootH joinH ++ rest) →
      ((extract joinW c d).map Ep.sh = c ∧ (extract joinW c d).Valid leafH nodeH rootH SatC ∧
        d = (extract joinW c d).digest leafH nodeH rootH joinH) ∨
      Collides (chainPairs leafH nodeH rootH joinH nw lw rootW joinW c d rest)
  | .base g e0 e1, ⟨ok0, ok1⟩, d, rest, hs, hd => by
    by_cases col : Collides (chainPairs leafH nodeH rootH joinH nw lw rootW joinW (.base g e0 e1) d rest)
    · exact Or.inr col
    left
    rw [chainPairs] at col
    rw [extract]
    obtain ⟨h, hg, hdo, ech0, ek0, ech1, ek1⟩ := (join_openW T (v := .base g) hs (hr _ _ _) (EpS.key_length e0)
      (hr _ _ _) hd).resolve_right fun c => col (collides_two c)
    set ρ := joinW (.base g) d with eρ
    have h' := h
    rw [EpochJoin.epochJoin_ops] at h'
    simp only [holds_append] at h'
    obtain ⟨⟨⟨⟨⟨⟨hL, hR⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
    obtain ⟨⟨-, rl, hrl, hml⟩, ⟨-, rr, hrr, hmr⟩, ⟨elink, -, elo, -, -⟩, -, -, -, -⟩ := EpochJoin.join_sound h
    obtain ⟨ok0', hout0⟩ := (rootChild_okW T hl hn (i := 0) (n := 0) (p := g) hL hrl (hg _ _ _ hml) e0 ok0 ech0
      ek0).resolve_right fun c => col (c.mono fun x hx =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))
    obtain ⟨ok1', hout1⟩ := (rootChild_okW T hl hn (i := 1) (n := (left (.base g)).next) (p := true) hR hrr
      (hg _ _ _ hmr) e1 ok1 ech1 ek1).resolve_right fun c => col (c.mono fun x hx =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx)))
    refine ⟨rfl, ⟨ok0', fun hg0 => ?_, ok1', elink, elo ok0'.2.2.2⟩, ?_⟩
    · subst hg0; exact EpochJoin.rootChild_zeros hL
    · rw [hdo, Chain.digest]
      congr 1
      have hk : keyWords ρ (.base g) =
          rootH e0.M g e0.s ++ e0.key leafH nodeH ++ rootH e1.M true e1.s ++ e1.key leafH nodeH := by
        unfold keyWords; rw [ech0, ek0, ech1, ek1]
      have ha : accWords ρ (.base g) = Ep.out leafH nodeH ⟨e0, rootOpen ρ (left (.base g)).res⟩ g ++
          Ep.out leafH nodeH ⟨e1, rootOpen ρ (right (.base g)).res⟩ true := by
        show wordsOf ρ (left (.base g)).res.out ++ wordsOf ρ (right (.base g)).res.out = _
        exact congrArg₂ (· ++ ·) hout0 hout1
      rw [outWords_eq, hk, ha]
      rfl
  | .step c0 e, ⟨okc, oke⟩, d, rest, hs, hd => by
    by_cases col : Collides (chainPairs leafH nodeH rootH joinH nw lw rootW joinW (.step c0 e) d rest)
    · exact Or.inr col
    left
    rw [chainPairs] at col
    rw [extract]
    obtain ⟨h, hg, hdo, ech0, ek0, ech1, ek1⟩ := (join_openW T (v := .step) hs (hj _) (Chain.key_length c0)
      (hr _ _ _) hd).resolve_right fun c => col (collides_two c)
    set ρ := joinW .step d with eρ
    have h' := h
    rw [EpochJoin.epochJoin_ops] at h'
    simp only [holds_append] at h'
    obtain ⟨⟨⟨⟨⟨⟨-, hR⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
    obtain ⟨⟨hlo, rl, hrl, hml⟩, ⟨-, rr, hrr, hmr⟩, ⟨elink, -, elo, -, -⟩, -, -, -, -⟩ := EpochJoin.join_sound h
    -- The left child: a join over `c0`, its identity and key pinned.
    obtain ⟨lk, lf, ll, lt, lo, -⟩ := EpochJoin.joinChild_lengths 0 0
    have lk : (left .step).res.key.length = 8 := lk
    have lf : (left .step).res.first.length = 8 := lf
    have ll : (left .step).res.last.length = 8 := ll
    have lt : (left .step).res.tail.length = 8 := lt
    have lo : (left .step).res.out.length = 8 := lo
    have hlout : wordsOf ρ (left .step).res.out = H (joinWords ρ (left .step).res) :=
      wordsOf_H lo rfl hlo
    have s := T.recVerifies ρ _ _ _ (hg _ _ _ hml)
    rw [List.drop_left' hrl, ech0] at s
    have hjw := joinWords_split ρ (left .step).res
    rw [ek0] at hjw
    have hd' : wordsOf ρ (left .step).res.out =
        H (c0.key leafH nodeH rootH joinH ++ joinRest ρ (left .step).res) := by
      rw [hlout, hjw, joinRest]
    rcases chain_soundW T hl hn hr hj c0 okc _ _ s hd' with ⟨hmap, hval, hdig⟩ | c
    swap; · exact absurd (c.mono fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_append_left _ hx)))) col
    set c'' := extract joinW c0 (wordsOf ρ (left .step).res.out) with ec''
    -- Its opening is `c''`'s.
    obtain ⟨-, ⟨-, hfp, -⟩, -, -⟩ := Chain.Valid.first_ok hval
    obtain ⟨-, ⟨hlf, -, -⟩, -, hlh⟩ := Chain.Valid.last_ok hval
    have em := (H_eqC _ _ (hlout.symm.trans hdig : H (joinWords ρ (left .step).res) =
      H (c''.msg leafH nodeH rootH joinH))).resolve_right fun c => col (collides_third c)
    unfold joinWords Chain.msg at em
    have hkey := Chain.key_length (leafH := leafH) (nodeH := nodeH) (rootH := rootH) (joinH := joinH) (c''.map Ep.sh)
    obtain ⟨em, eacc⟩ := List.append_inj em (by simp [wordsOf_length, lk, lf, ll, hkey, hfp, hlf])
    obtain ⟨em, exy⟩ := List.append_inj em (by simp [wordsOf_length, lk, lf, ll, hkey, hfp, hlf])
    obtain ⟨em, eL⟩ := List.append_inj em (by simp [wordsOf_length, lk, lf, hkey, hfp])
    obtain ⟨-, eF⟩ := List.append_inj em (by simp [wordsOf_length, lk, hkey])
    simp only [List.cons.injEq, and_true] at exy
    obtain ⟨ex, ey⟩ := exy
    have ehi := ofNat_inj (val_lt32 _) (by omega) ey
    -- The right child: an epoch root.
    obtain ⟨okE, hout1⟩ := (rootChild_okW T hl hn (i := 1) (n := (left .step).next) (p := true) hR hrr
      (hg _ _ _ hmr) e oke ech1 ek1).resolve_right fun c => col (c.mono fun x hx =>
        List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))))
    refine ⟨?_, ⟨hval, okE, elink.trans eL, ?_⟩, ?_⟩
    · show Chain.step (c''.map Ep.sh) e = _
      rw [hmap]
    · show (ρ (right .step).res.lo).a.val = c''.last.o.hi + 1
      rw [elo (by rw [ehi]; exact hlh), ehi]
    · rw [hdo, Chain.digest]
      congr 1
      have hk : keyWords ρ .step =
          joinH c0.variant ++ c0.key leafH nodeH rootH joinH ++ rootH e.M true e.s ++ e.key leafH nodeH := by
        unfold keyWords; rw [ech0, ek0, ech1, ek1]
      have ha : accWords ρ .step =
          c''.acc leafH nodeH ++ Ep.out leafH nodeH ⟨e, rootOpen ρ (right .step).res⟩ true := by
        show wordsOf ρ (left .step).res.tail ++ wordsOf ρ (right .step).res.out = _
        rw [eacc]
        exact congrArg (c''.acc leafH nodeH ++ ·) hout1
      rw [outWords_eq, hk, ha, eF, ex]
      simp only [Chain.msg, Chain.map, hmap]
      rfl

/-- **The chain, as one statement, up to a named collision** (`chain_cover`), for the chain of openings
the witnesses give (`c' = extract joinWit c d`). -/
theorem chain_coverW {ok : (ℕ → F) → Prop} (T : TrustEW Acc SatC VGates leafH nodeH rootH joinH (LeafAt ok) nw lw rootW joinW)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    (hr : ∀ M p s, (rootH M p s).length = 8) (hj : ∀ v, (joinH v).length = 8)
    (c : Chain EpS) (hok : c.Ok) (d rest : List Word)
    (hs : SatC (joinH c.variant) d) (hd : d = H (c.key leafH nodeH rootH joinH ++ rest)) :
    (∃ c' : Chain Ep, c' = extract joinW c d ∧ c'.map Ep.sh = c ∧
      d = H (c.key leafH nodeH rootH joinH ++ c'.first.o.prev ++ c'.last.o.fin ++
        [BitVec.ofNat 32 c'.first.o.lo, BitVec.ofNat 32 c'.last.o.hi] ++ c'.acc leafH nodeH) ∧
      (c.gen = false → c'.first.o.prev = List.replicate 8 0) ∧
      RootOk leafH nodeH rootH SatC c'.first c.gen ∧ (∀ e ∈ c'.epochs.tail, RootOk leafH nodeH rootH SatC e true) ∧
      List.IsChain Link c'.epochs ∧ c'.first.o.lo ≤ c'.last.o.hi ∧ c'.last.o.hi < 2 ^ 30 ∧
      ∃ e0 e1 es, c'.epochs = e0 :: e1 :: es ∧
        c'.acc leafH nodeH = es.foldl (fun a e => H (a ++ e.out leafH nodeH true))
          (H (e0.out leafH nodeH c.gen ++ e1.out leafH nodeH true))) ∨
      Collides (chainPairs leafH nodeH rootH joinH nw lw rootW joinW c d rest) := by
  rcases chain_soundW T hl hn hr hj c hok d rest hs hd with ⟨hmap, hval, hdig⟩ | col
  · refine Or.inl ⟨extract joinW c d, rfl, ?_⟩
    generalize extract joinW c d = c' at hmap hval hdig ⊢
    refine ⟨hmap, ?_, ?_, ?_, (Chain.Valid.roots hval).2, Chain.Valid.links hval,
      (Chain.Valid.range hval).1, (Chain.Valid.range hval).2, ?_⟩
    · rw [hdig, Chain.digest, Chain.msg, hmap]
    · have hg : c'.gen = c.gen := by rw [← hmap, Chain.gen_map]
      rw [← hg]
      clear hmap hdig hg
      induction c' with
      | base g e0 e1 => exact hval.2.1
      | step c e ih => exact ih hval.1
    · rw [← hmap, Chain.gen_map]; exact (Chain.Valid.roots hval).1
    · rw [← hmap, Chain.gen_map]; exact Chain.acc_fold c'
  · exact Or.inr col

end

/-! ### The verifier's openings -/

section
variable {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {SatC : List Word → List Word → Prop}

/-- **One digest, one opening, up to a named collision** (`out_inj`). -/
theorem out_injW {e e' : Ep} {p : Bool} (hs : e.sh = e'.sh) (hw : e.o.Fits) (hw' : e'.o.Fits)
    (h : e.out leafH nodeH p = e'.out leafH nodeH p) :
    (e.o.fin = e'.o.fin ∧ (p = true → e.o.prev = e'.o.prev) ∧ e.o.lo = e'.o.lo ∧ e.o.hi = e'.o.hi ∧
      e.o.rest = e'.o.rest) ∨
      CollidesAt (rootMsg (e.sh.key leafH nodeH) p e.o) (rootMsg (e'.sh.key leafH nodeH) p e'.o) := by
  have h' : H (rootMsg (e.sh.key leafH nodeH) p e.o) = H (rootMsg (e'.sh.key leafH nodeH) p e'.o) := h
  rcases H_eqC _ _ h' with e1 | c
  swap; · exact Or.inr c
  obtain ⟨⟨f, pr, -⟩, lo, hi⟩ := hw
  obtain ⟨⟨f', pr', -⟩, lo', hi'⟩ := hw'
  have hK' := EpS.key_length (leafH := leafH) (nodeH := nodeH) e'.sh
  unfold rootMsg at e1
  rw [hs] at e1
  obtain ⟨e1, er⟩ := List.append_inj e1 (by cases p <;> simp [f, pr, f', pr', hK'])
  obtain ⟨e1, exy⟩ := List.append_inj e1 (by cases p <;> simp [f, pr, f', pr', hK'])
  obtain ⟨e1, ep⟩ := List.append_inj e1 (by simp [f, f', hK'])
  obtain ⟨-, ef⟩ := List.append_inj e1 rfl
  simp only [List.cons.injEq, and_true] at exy
  exact Or.inl ⟨ef, fun hp => by subst hp; simpa using ep, ofNat_inj lo lo' exy.1, ofNat_inj hi hi' exy.2, er⟩

/-- **The pairs `acc` binding compares** (two chains of openings, same shapes): per join the `acc`
messages, and each epoch root's output message. -/
noncomputable def accPairs (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) :
    Chain Ep → Chain Ep → List (List Word × List Word)
  | .base g e0 e1, .base g' e0' e1' =>
    [(e0.out leafH nodeH g ++ e1.out leafH nodeH true, e0'.out leafH nodeH g' ++ e1'.out leafH nodeH true),
      (rootMsg (e0.sh.key leafH nodeH) g e0.o, rootMsg (e0'.sh.key leafH nodeH) g' e0'.o),
      (rootMsg (e1.sh.key leafH nodeH) true e1.o, rootMsg (e1'.sh.key leafH nodeH) true e1'.o)]
  | .step c e, .step c' e' =>
    (c.acc leafH nodeH ++ e.out leafH nodeH true, c'.acc leafH nodeH ++ e'.out leafH nodeH true) ::
      (rootMsg (e.sh.key leafH nodeH) true e.o, rootMsg (e'.sh.key leafH nodeH) true e'.o) :: accPairs leafH nodeH c c'
  | _, _ => []

/-- **`acc` binds every epoch's opening, up to a named collision** (`acc_valid`). -/
theorem acc_validW : ∀ (c c' : Chain Ep), c'.Valid leafH nodeH rootH SatC → c.map Ep.sh = c'.map Ep.sh →
    c.acc leafH nodeH = c'.acc leafH nodeH → c.All (fun e => e.o.Fits) → c'.All (fun e => e.o.Fits) →
    (c.gen = false → c.first.o.prev = List.replicate 8 0) →
    (c.Valid leafH nodeH rootH SatC ∧ c.last.o.fin = c'.last.o.fin ∧ c.last.o.hi = c'.last.o.hi) ∨
      Collides (accPairs leafH nodeH c c')
  | .base g e0 e1, .base g' e0' e1', hv, hm, ha, hw, hw', hgen => by
    by_cases col : Collides (accPairs leafH nodeH (.base g e0 e1) (.base g' e0' e1'))
    · exact Or.inr col
    left
    rw [accPairs] at col
    simp only [Chain.map, Chain.base.injEq] at hm
    obtain ⟨rfl, h0, h1⟩ := hm
    have ha' : H (e0.out leafH nodeH g ++ e1.out leafH nodeH true) = H (e0'.out leafH nodeH g ++ e1'.out leafH nodeH true) := ha
    have e := (H_eqC _ _ ha').resolve_right fun c => col (collides_head c)
    obtain ⟨o0, o1⟩ := List.append_inj e (by simp [Ep.out, H_length])
    obtain ⟨f0, -, l0, hi0, -⟩ := (out_injW h0 hw.1 hw'.1 o0).resolve_right fun c => col (collides_second c)
    obtain ⟨f1, p1, l1, hi1, -⟩ := (out_injW h1 hw.2 hw'.2 o1).resolve_right fun c => col (collides_third c)
    obtain ⟨r0, -, r1, ⟨lp, ll⟩⟩ := hv
    refine ⟨⟨rootOk_of h0 hw.1.1 o0 l0 hi0 r0, hgen, rootOk_of h1 hw.2.1 o1 l1 hi1 r1, ?_, ?_⟩, f1, hi1⟩
    · show e1.o.prev = e0.o.fin
      rw [p1 rfl, f0]; exact lp
    · show e1.o.lo = e0.o.hi + 1
      rw [l1, hi0]; exact ll
  | .step c e, .step c' e', hv, hm, ha, hw, hw', hgen => by
    by_cases col : Collides (accPairs leafH nodeH (.step c e) (.step c' e'))
    · exact Or.inr col
    left
    rw [accPairs] at col
    simp only [Chain.map, Chain.step.injEq] at hm
    obtain ⟨hm, h1⟩ := hm
    have ha' : H (c.acc leafH nodeH ++ e.out leafH nodeH true) = H (c'.acc leafH nodeH ++ e'.out leafH nodeH true) := ha
    have eq := (H_eqC _ _ ha').resolve_right fun x => col (collides_head x)
    obtain ⟨hac, o1⟩ := List.append_inj eq (by rw [Chain.acc_length, Chain.acc_length])
    obtain ⟨ihv, ihf, ihh⟩ := (acc_validW c c' hv.1 hm hac hw.1 hw'.1 hgen).resolve_right fun x =>
      col (x.mono fun y hy => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hy))
    obtain ⟨f1, p1, l1, hi1, -⟩ := (out_injW h1 hw.2 hw'.2 o1).resolve_right fun x => col (collides_second x)
    obtain ⟨-, r1, ⟨lp, ll⟩⟩ := hv
    refine ⟨⟨ihv, rootOk_of h1 hw.2.1 o1 l1 hi1 r1, ?_, ?_⟩, f1, hi1⟩
    · show e.o.prev = c.last.o.fin
      rw [p1 rfl, ihf]; exact lp
    · show e.o.lo = c.last.o.hi + 1
      rw [l1, ihh]; exact ll
  | .base _ _ _, .step _ _, _, hm, _, _, _, _ => by simp [Chain.map] at hm
  | .step _ _, .base _ _ _, _, hm, _, _, _, _ => by simp [Chain.map] at hm

/-- The verifier's join message after the key: `start ‖ end ‖ a ‖ b ‖ acc`. -/
def verRest (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (c : Chain Ep) : List Word :=
  c.first.o.prev ++ c.last.o.fin ++ [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++ c.acc leafH nodeH

end

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {nw : ℕ → ℕ → List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}
  {rootW : ℕ → Bool → ℕ → List Word → ℕ → Q} {joinW : Variant → List Word → ℕ → Q}

/-- **The chain verifier, composed, up to a named collision** (`chain_verify`). The verifier's chain of
openings `c` (shapes pinned, within bounds), whose recomputed digest the one join proof is accepted with,
is valid; or two of the listed pairs collide: the chain's (`chainPairs`), the verifier's message against
the extracted chain's (`c' = extract joinWit …`), or `acc`'s (`accPairs c c'`). -/
theorem chain_verifyW {ok : (ℕ → F) → Prop} (T : TrustEW Acc SatC VGates leafH nodeH rootH joinH (LeafAt ok) nw lw rootW joinW)
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    (hr : ∀ M p s, (rootH M p s).length = 8) (hj : ∀ v, (joinH v).length = 8)
    (c : Chain Ep) (hok : (c.map Ep.sh).Ok) (hw : c.All (fun e => e.o.Fits))
    (hgen : c.gen = false → c.first.o.prev = List.replicate 8 0)
    (hs : SatC (joinH c.variant) (c.digest leafH nodeH rootH joinH)) :
    c.Valid leafH nodeH rootH SatC ∨
      Collides (chainPairs leafH nodeH rootH joinH nw lw rootW joinW (c.map Ep.sh) (c.digest leafH nodeH rootH joinH)
          (verRest leafH nodeH c) ++
        (c.msg leafH nodeH rootH joinH,
          (extract joinW (c.map Ep.sh) (c.digest leafH nodeH rootH joinH)).msg leafH nodeH rootH joinH) ::
        accPairs leafH nodeH c (extract joinW (c.map Ep.sh) (c.digest leafH nodeH rootH joinH))) := by
  have hf : c.first.o.prev.length = 8 := hw.first.1.2.1
  have hlf : c.last.o.fin.length = 8 := hw.last.1.1
  have hmsg : c.msg leafH nodeH rootH joinH = (c.map Ep.sh).key leafH nodeH rootH joinH ++ verRest leafH nodeH c := by
    simp [Chain.msg, verRest, List.append_assoc]
  rcases chain_soundW T hl hn hr hj (c.map Ep.sh) hok _ (verRest leafH nodeH c) (by rw [Chain.variant_map]; exact hs)
    (by rw [Chain.digest, hmsg]) with ⟨hmap, hval, hdig⟩ | col
  swap; · exact Or.inr (col.mono fun x hx => List.mem_append_left _ hx)
  have hw' := Chain.Valid.fits hval
  rcases H_eqC _ _ (hdig : H (c.msg leafH nodeH rootH joinH) =
      H ((extract joinW (c.map Ep.sh) (c.digest leafH nodeH rootH joinH)).msg leafH nodeH rootH joinH)) with em | col
  swap; · exact Or.inr ⟨_, List.mem_append_right _ List.mem_cons_self, col⟩
  unfold Chain.msg at em
  obtain ⟨-, hacc⟩ := List.append_inj em (by simp [Chain.key_length, hf, hlf, hw'.first.1.2.1, hw'.last.1.1])
  rcases acc_validW c _ hval hmap.symm hacc hw hw' hgen with ⟨v, -⟩ | col
  · exact Or.inl v
  · exact Or.inr (col.mono fun x hx => List.mem_append_right _ (List.mem_cons_of_mem _ hx))

end

end StarkedAir.Circuit.EpochChain
