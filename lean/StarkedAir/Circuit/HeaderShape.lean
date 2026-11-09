/-
**The header tree's shape (discharges `MmrT`, HC-HASHTREE).** The outer verifier fixes the header
tree's recursion shape: `store.rootExpect` checks the segment plan is aligned (`HT.validPlan`) and
keys the root over `node.expectedRoot`, the MMR fold of the plan's leaves (`HT.mmrFold`: push and
merge equal counts, then bag right to left). Here:

- `fill s xs`: the block-hash tree a recursion tree `s` builds over the hashes `xs` (a perfect tree
  per segment of log size `L`, `2^(L−8)` headers; a node per node);
- `PubValidS s p`: `PubValidT p` with that tree (`leaf_valid_S` for leaves, from the same facts as
  `leaf_valid_T`; `pub_compose_S` for nodes); `htree_soundWS` carries it up the recursion
  (`TrustWH`: `TrustW` whose leaf guarantee names the leaf's log size, as `leaf_valid_T` proves it);
- `planTree logs`: the tree `expectedRoot` keys (Lean mirror of `HT.mmrFold`); `planTree_fill`:
  over an aligned plan, `fill (planTree logs)` is the canonical MMR (`Spec.Mmr.fold_eq_mmr`);
- `PubValidM`: proven public inputs whose `T` is the canonical MMR root over the chain's block
  hashes (`PubValidS.toM`), and `chain_from_genesis_M`, the root theorem with it.

What stays native: the verifier's plan is `logs` and aligned, and the root key is `planTree logs`'s
(`PathNative.plan`, `PathNative.align` in `ChainSealTCompose.lean`).
-/
import StarkedAir.Circuit.RecCR
import StarkedAir.Spec.Mmr

namespace StarkedAir.HeaderTree

open StarkedAir StarkedAir.HeaderChain StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin Spec.HeaderTree
open StarkedAir.Spec.Mmr (bal bal_leaves mmr push bagB bag foldPlan Aligned Inv foldPlan_inv fold_eq_mmr zeroState)

/-! ### A recursion tree's block-hash tree -/

/-- Headers under a recursion tree: `2^(L−8)` per segment of log size `L`. -/
def cnt : Circuit.BlockRec.Tree → ℕ
  | .leaf g => 2 ^ (g - 8)
  | .node l r => cnt l + cnt r

/-- The block-hash tree recursion tree `s` builds over `xs`. -/
def fill : Circuit.BlockRec.Tree → List State → HTree
  | .leaf g, xs => bal (g - 8) xs
  | .node l r, xs => .node (fill l (xs.take (cnt l))) (fill r (xs.drop (cnt l)))

theorem fill_leaves : ∀ (s : Circuit.BlockRec.Tree) (xs : List State), xs.length = cnt s → (fill s xs).leaves = xs
  | .leaf g, xs, h => bal_leaves _ _ h
  | .node l r, xs, h => by
    simp only [cnt] at h
    simp only [fill, HTree.leaves]
    rw [fill_leaves l _ (by rw [List.length_take]; omega), fill_leaves r _ (by rw [List.length_drop]; omega),
      List.take_append_drop]

theorem bal_succ_append (k : ℕ) (A B : List State) (hA : A.length = 2 ^ k) :
    bal (k + 1) (A ++ B) = .node (bal k A) (bal k B) := by
  simp only [bal]
  rw [List.take_append_of_le_length (le_of_eq hA.symm), List.take_of_length_le (le_of_eq hA),
    List.drop_append_of_le_length (le_of_eq hA.symm), List.drop_of_length_le (le_of_eq hA), List.nil_append]

theorem perfect_eq_bal (f : ℕ → State) : ∀ ℓ p, perfect f ℓ p = bal ℓ (perfect f ℓ p).leaves
  | 0, p => by simp [perfect, HTree.leaves, bal]
  | ℓ + 1, p => by
    have hl : (perfect f ℓ (2 * p)).leaves.length = 2 ^ ℓ := by rw [perfect_leaves]; simp
    simp only [perfect, HTree.leaves]
    rw [bal_succ_append ℓ _ _ hl, ← perfect_eq_bal f ℓ (2 * p), ← perfect_eq_bal f ℓ (2 * p + 1)]

/-- **Proven public inputs with the tree of a recursion shape `s`.** -/
def PubValidS (s : Circuit.BlockRec.Tree) (p : ℕ → F) : Prop :=
  WorkInOk p → WorkOutOk p ∧ ∃ H hs, PubSeg p H hs ∧ H = cnt s ∧
    pubT p = limbsOf (fill s ((List.range H).map fun j => sha256d (hs j))).root

theorem PubValidS.toT {s : Circuit.BlockRec.Tree} {p : ℕ → F} (v : PubValidS s p) : PubValidT p := fun hin => by
  obtain ⟨o, H, hs, f, hH, rt⟩ := v hin
  exact ⟨o, H, hs, f, _, fill_leaves s _ (by simp [hH]), rt⟩

/-- **Leaves** (as `leaf_valid_T`): the tree is the perfect one over the segment's `2^(L−8)` headers. -/
theorem leaf_valid_S {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
    (h0L : (inst 0).logSize = L) (h1L : (inst 1).logSize = L) (hL : 8 ≤ L) (hL28 : L ≤ 28)
    (hsat : sys.SatisfiedExt inst pub [(REL_NODE, ((L - 8 : ℕ) : F) :: 0 :: pubT pub, -1)]) :
    PubValidS (.leaf L) pub := by
  have hh : HeaderChain.air.Satisfied L pub (inst 0).main := by
    have := hsat.1 0 (by decide); rw [h0L] at this; exact this
  have hx := tree_root_limbs h0L h1L hL hL28 hsat
  have hhash := (chain_sound_v2 hh hL).1
  have hK : 2 ^ (L - 8) = 2 ^ L / 256 := by
    rw [show (256 : ℕ) = 2 ^ 8 by norm_num, Nat.pow_div hL (by norm_num)]
  intro hin
  have hlv : (perfect (leafHash inst) (L - 8) 0).leaves =
      (List.range (2 ^ L / 256)).map (fun j => sha256d (headerWord (inst 0).main j)) := by
    rw [perfect_leaves, hK]
    exact List.map_congr_left (fun j hj => by
      rw [Nat.mul_zero, Nat.zero_add]; exact ((hhash j (List.mem_range.mp hj)).1).symm)
  refine ⟨(leaf_valid hh hL hin).1, 2 ^ L / 256, headerWord (inst 0).main,
    fun w hw => header_chain_sound hh hL w hw hin, by simp only [cnt]; exact hK.symm, ?_⟩
  simp only [fill]
  rw [← hlv, ← perfect_eq_bal, perfect_root]; exact hx

/-- **Nodes** (as `pub_compose_T`): the tree is the node over the children's. -/
theorem pub_compose_S {pL pR out : ℕ → F} {l r : Circuit.BlockRec.Tree} (vL : PubValidS l pL) (vR : PubValidS r pR)
    (lk : PubLink pL pR) (n : NodeOut pL pR out) : PubValidS (.node l r) out := by
  intro hin
  rw [workIn_low n.1, workIn_combine] at hin
  obtain ⟨outL, H1, hs1, fL, hH1, rt1⟩ := vL hin
  have hinR : WorkInOk pR := fun k hk => by rw [lk.2.2.2.2.2.2.2.2.1 k hk]; exact outL k hk
  obtain ⟨outR, H2, hs2, fR, hH2, rt2⟩ := vR hinR
  refine ⟨(workOut_low n.1).mpr (workOut_combine.mpr outR), H1 + H2, catHs H1 hs1 hs2,
    (pubSeg_low n.1).mpr (seg_compose fL fR lk), by simp only [cnt, hH1, hH2], ?_⟩
  rw [← leaves_cat H1 H2 hs1 hs2]
  have hl1 : ((List.range H1).map (fun j => sha256d (hs1 j))).length = cnt l := by simp [hH1]
  simp only [fill, HTree.root]
  rw [List.take_left' hl1, List.drop_left' hl1]
  exact n.2 _ _ rt1 rt2

/-! ### The verifier's plan is the canonical MMR -/

/-- Push onto a stack of (level, tree), top first, merging equal levels (`HT.pushPeak`). -/
def pushT : List (ℕ × Circuit.BlockRec.Tree) → ℕ × Circuit.BlockRec.Tree → List (ℕ × Circuit.BlockRec.Tree)
  | [], x => [x]
  | (k, A) :: rest, (j, B) => if k = j then pushT rest (k + 1, .node A B) else (j, B) :: (k, A) :: rest

/-- Bag a stack given bottom first (`HT.bagPeaks`). -/
def bagT : List (ℕ × Circuit.BlockRec.Tree) → Circuit.BlockRec.Tree
  | [] => .leaf 0
  | [e] => e.2
  | e :: rest => .node e.2 (bagT rest)

/-- Push the segments of log sizes `gs` (`2^(g−8)` headers each). -/
def foldT : List ℕ → List (ℕ × Circuit.BlockRec.Tree) → List (ℕ × Circuit.BlockRec.Tree)
  | [], st => st
  | g :: gs, st => foldT gs (pushT st (g - 8, .leaf g))

/-- **The tree `node.expectedRoot` keys** over segments of log sizes `logs` (`HT.mmrFold`). -/
def planTree (logs : List ℕ) : Circuit.BlockRec.Tree := bagT (foldT logs []).reverse

/-- A recursion peak and a spec peak agree: same level, `2^k` leaves, and the filled tree is perfect. -/
def PeakR (a : ℕ × Circuit.BlockRec.Tree) (b : ℕ × List State) : Prop :=
  a.1 = b.1 ∧ b.2.length = 2 ^ b.1 ∧ cnt a.2 = 2 ^ a.1 ∧ fill a.2 b.2 = bal b.1 b.2

theorem peakR_node {k : ℕ} {A B : Circuit.BlockRec.Tree} {A' B' : List State} (ha : PeakR (k, A) (k, A'))
    (hb : PeakR (k, B) (k, B')) : PeakR (k + 1, .node A B) (k + 1, A' ++ B') := by
  obtain ⟨-, la, ca, fa⟩ := ha
  obtain ⟨-, lb, cb, fb⟩ := hb
  simp only at la ca fa lb cb fb
  refine ⟨rfl, ?_, ?_, ?_⟩
  · simp only [List.length_append, la, lb, pow_succ]; ring
  · simp only [cnt, ca, cb, pow_succ]; ring
  · simp only [fill]
    rw [ca, bal_succ_append k A' B' la, List.take_left' la, List.drop_left' la, fa, fb]

theorem push_R : ∀ (sT : List (ℕ × Circuit.BlockRec.Tree)) (sS : List (ℕ × List State)) (x : ℕ × Circuit.BlockRec.Tree) (y : ℕ × List State),
    List.Forall₂ PeakR sT sS → PeakR x y → List.Forall₂ PeakR (pushT sT x) (push sS y)
  | [], [], x, y, _, hxy => by
    obtain ⟨j, B⟩ := x; obtain ⟨j', B'⟩ := y
    simp only [pushT, push]; exact List.Forall₂.cons hxy .nil
  | (k, A) :: rest, (k', A') :: rest', (j, B), (j', B'), h, hxy => by
    obtain ⟨hh, ht⟩ := List.forall₂_cons.mp h
    have e1 : k = k' := hh.1
    have e2 : j = j' := hxy.1
    subst e1 e2
    simp only [pushT, push]
    by_cases hkj : k = j
    · subst hkj
      simp only [if_true]
      exact push_R rest rest' _ _ ht (peakR_node hh hxy)
    · simp only [hkj, if_false]
      exact .cons hxy (.cons hh ht)
  | [], _ :: _, _, _, h, _ => by cases h
  | _ :: _, [], _, _, h, _ => by cases h

theorem fold_R (L : List State) : ∀ (gs : List ℕ) (m : ℕ) (sT : List (ℕ × Circuit.BlockRec.Tree)) (sS : List (ℕ × List State)),
    List.Forall₂ PeakR sT sS → m + ((gs.map (· - 8)).map (2 ^ ·)).sum ≤ L.length →
    List.Forall₂ PeakR (foldT gs sT) (foldPlan L m (gs.map (· - 8)) sS)
  | [], m, sT, sS, h, _ => by simpa [foldT, foldPlan] using h
  | g :: gs, m, sT, sS, h, hl => by
    simp only [List.map_cons, List.sum_cons] at hl
    simp only [foldT, List.map_cons, foldPlan]
    refine fold_R L gs (m + 2 ^ (g - 8)) _ _ (push_R _ _ _ _ h ⟨rfl, ?_, rfl, rfl⟩) (by omega)
    simp only [List.length_take, List.length_drop]; omega

theorem bag_R : ∀ (BT : List (ℕ × Circuit.BlockRec.Tree)) (BS : List (ℕ × List State)), List.Forall₂ PeakR BT BS → BS ≠ [] →
    cnt (bagT BT) = (BS.map Prod.snd).flatten.length ∧ fill (bagT BT) (BS.map Prod.snd).flatten = bagB BS
  | [], [], _, h => (h rfl).elim
  | [a], [b], h, _ => by
    obtain ⟨⟨e1, lb, ca, fa⟩, -⟩ := List.forall₂_cons.mp h
    simp only [bagT, bagB, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact ⟨by rw [ca, lb, e1], fa⟩
  | a :: a2 :: rest, b :: b2 :: rest', h, _ => by
    obtain ⟨hab, h2⟩ := List.forall₂_cons.mp h
    obtain ⟨e1, lb, ca, fa⟩ := hab
    obtain ⟨ihc, ihf⟩ := bag_R (a2 :: rest) (b2 :: rest') h2 (by simp)
    have hca : cnt a.2 = b.2.length := by rw [ca, lb, e1]
    simp only [bagT, bagB, List.map_cons, List.flatten_cons] at ihc ihf ⊢
    refine ⟨by simp only [cnt, List.length_append] at ihc ⊢; omega, ?_⟩
    simp only [fill]
    rw [hca, List.take_left' rfl, List.drop_left' rfl, fa, ihf]
  | [], _ :: _, h, _ => by cases h
  | _ :: _, [], h, _ => by cases h
  | [_], _ :: _ :: _, h, _ => by cases h with | cons _ h2 => cases h2
  | _ :: _ :: _, [_], h, _ => by cases h with | cons _ h2 => cases h2

/-- **Over an aligned plan, the recursion's tree is the canonical MMR.** -/
theorem planTree_fill (logs : List ℕ) (L : List State) (hL : L ≠ [])
    (ha : Aligned 0 (logs.map (· - 8))) (hs : ((logs.map (· - 8)).map (2 ^ ·)).sum = L.length) :
    fill (planTree logs) L = mmr L ∧ cnt (planTree logs) = L.length := by
  have hR := fold_R L logs 0 [] [] .nil (by omega)
  have hI := foldPlan_inv L (logs.map (· - 8)) 0 [] ⟨by simp, by simp, by simp⟩ ha (by omega)
  rw [zero_add, hs, List.take_length] at hI
  have hRr := List.forall₂_reverse_iff.mpr hR
  have hne : (foldPlan L 0 (logs.map (· - 8)) []).reverse ≠ [] := by
    intro h0
    have := hI.leaves
    rw [h0] at this
    simp only [List.map_nil, List.flatten_nil] at this
    exact hL this.symm
  obtain ⟨hc, hf⟩ := bag_R _ _ hRr hne
  rw [hI.leaves] at hc hf
  refine ⟨?_, hc⟩
  unfold planTree
  rw [hf]
  exact fold_eq_mmr L hL _ ha hs

theorem sum_pos {logs : List ℕ} (hne : logs ≠ []) : 0 < ((logs.map (· - 8)).map (2 ^ ·)).sum := by
  cases logs with
  | nil => exact absurd rfl hne
  | cons g gs =>
    simp only [List.map_cons, List.sum_cons]
    have := Nat.two_pow_pos (g - 8)
    omega

theorem cnt_planTree {logs : List ℕ} (hne : logs ≠ []) (ha : Aligned 0 (logs.map (· - 8))) :
    cnt (planTree logs) = ((logs.map (· - 8)).map (2 ^ ·)).sum := by
  have hp := sum_pos hne
  have := (planTree_fill logs (List.replicate (((logs.map (· - 8)).map (2 ^ ·)).sum) zeroState)
    (by rw [Ne, List.replicate_eq_nil_iff]; omega) ha (by rw [List.length_replicate])).2
  rwa [List.length_replicate] at this

/-- **Proven public inputs whose `T` is the canonical MMR root** over the chain's block hashes. -/
def PubValidM (p : ℕ → F) : Prop :=
  WorkInOk p → WorkOutOk p ∧ ∃ H hs, PubSeg p H hs ∧ 0 < H ∧
    pubT p = limbsOf (mmr ((List.range H).map fun j => sha256d (hs j))).root

theorem PubValidS.toM {logs : List ℕ} {p : ℕ → F} (v : PubValidS (planTree logs) p) (hne : logs ≠ [])
    (ha : Aligned 0 (logs.map (· - 8))) : PubValidM p := fun hin => by
  obtain ⟨o, H, hs, f, hH, rt⟩ := v hin
  have hc := cnt_planTree hne ha
  have hpos : 0 < H := by rw [hH, hc]; exact sum_pos hne
  have hl : ((List.range H).map fun j => sha256d (hs j)).length = H := by simp
  refine ⟨o, H, hs, f, hpos, ?_⟩
  rw [rt, (planTree_fill logs _ (fun e => by rw [e] at hl; simp at hl; omega) ha (by rw [hl, hH, hc])).1]

/-- **The root theorem with the canonical MMR** (`chain_from_genesis_checked` for `PubValidM`). -/
theorem chain_from_genesis_M {p : ℕ → F} (v : PubValidM p) (hc : ∀ c ∈ genesisChecks, (p c.1).val = c.2) :
    ∃ H hs, SegmentValid H hs
      ⟨pubState p 0, 0, leN (pubWord p 34), leN (pubWord p 44), leN (pubWord p 36), [], 0⟩
      (decodeOut p) ∧ pubState p 0 = pubState (fun _ => 0) 0 ∧ 0 < H ∧
      pubT p = limbsOf (mmr ((List.range H).map (fun j => sha256d (hs j)))).root := by
  obtain ⟨h1, h2, h3, h4⟩ := genesis_checks_sound hc
  obtain ⟨-, H, hs, f, hpos, rt⟩ := v (fun l hl => by rw [h4 l hl]; simp)
  exact ⟨H, hs, seg_from_genesis f h2 h3 h4, genesis_prev h1, hpos, rt⟩

end StarkedAir.HeaderTree

namespace StarkedAir.Circuit

/-- `node_compose` with the shape. -/
theorem node_composeS {ρ : ℕ → Q} {l r : BlockRec.Tree} (h : Holds ρ nodeProgram.ops)
    (vL : HeaderTree.PubValidS l (nodePL ρ)) (vR : HeaderTree.PubValidS r (nodePR ρ)) :
    HeaderTree.PubValidS (.node l r) (nodeOut ρ) :=
  HeaderTree.pub_compose_S vL vR (node_sound h).1 (node_sound h).2

end StarkedAir.Circuit

namespace StarkedAir.Circuit.RecCR

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.BlockRec Q Spec.Blake2s
open StarkedAir.Circuit.HeaderRec
open StarkedAir.HeaderTree (PubValidS)

/-- `PubValidS` depends only on the 124 public inputs. -/
theorem pubValidS_congr {s : BlockRec.Tree} {p q : ℕ → F} (h : ∀ k < N_PUB, p k = q k) (hp : PubValidS s p) :
    PubValidS s q := by
  have hl : HeaderTree.Low p q := fun k hk => h k (by unfold N_PUB; omega)
  have ht : HeaderTree.pubT p = HeaderTree.pubT q :=
    List.map_congr_left fun i hi => h _ (by have := List.mem_range.mp hi; unfold N_PUB; omega)
  intro hin
  rw [← HeaderTree.workIn_low hl] at hin
  obtain ⟨o, Hh, hs, f, hH, rt⟩ := hp hin
  exact ⟨(HeaderTree.workOut_low hl).mp o, Hh, hs, (HeaderTree.pubSeg_low hl).mp f, hH, ht ▸ rt⟩

/-- A header leaf's guarantee with its log size `L` (`leaf_valid_S`). -/
def LeafAtHS (L : ℕ) (d : List Word) (p : ℕ → F) : Prop := PubValidS (.leaf L) p ∧ d = pubDigest zeroKey p

/-- **`TrustW` for the header tree, its leaf guarantee naming the leaf's log size** (what
`leaf_valid_T` proves already: `leaf_valid_S`). `toTrustW` forgets the size. -/
structure TrustWH (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : List Word) (nodeWit : List Word → ℕ → Q) (leafWit : ℕ → List Word → ℕ → F) : Prop where
  stwoSound : ∀ h d, Acc h d → SatC h d
  nodeCircuit : ∀ d, SatC nodeH d →
    Holds (nodeWit d) nodeProgram.ops ∧ wordsOf (nodeWit d) nodeProgram.results = d ∧ HookGates VGates (nodeWit d) nodeProgram.ops
  recVerifies : ∀ ρ i args outs, VGates ρ i args outs → SatC (wordsOf ρ outs) (wordsOf ρ (args.drop 8))
  leafSound : ∀ L d, SatC (leafH L) d → LeafAtHS L d (leafWit L d)

variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : List Word} {nw : List Word → ℕ → Q} {lw : ℕ → List Word → ℕ → F}

theorem TrustWH.toTrustW (T : TrustWH Acc SatC VGates leafH nodeH nw lw) :
    TrustW Acc SatC VGates leafH nodeH nodeProgram LeafAtH nw lw :=
  ⟨T.stwoSound, T.nodeCircuit, T.recVerifies, fun L d h => ⟨(T.leafSound L d h).1.toT, (T.leafSound L d h).2⟩⟩

/-- **A header tree is sound with its shape, up to a named collision** (`htree_soundW` with `PubValidS`). -/
theorem htree_soundWS (T : TrustWH Acc SatC VGates leafH nodeH nw lw)
    (hl : ∀ L, (leafH L).length = 8) (hn : nodeH.length = 8) :
    ∀ (t : BlockRec.Tree) (p : ℕ → F), SatC (t.hash leafH nodeH) (pubDigest (t.key leafH nodeH) p) →
      PubValidS t p ∨ Collides (pairsH leafH nodeH nw lw t p)
  | .leaf L, p, hs => by
    obtain ⟨hq, hd⟩ := T.leafSound L _ hs
    rcases pubDigest_eqC (BlockRec.Tree.key_length leafH nodeH (.leaf L)) (by simp [zeroKey]) hd with ⟨-, e⟩ | c
    · exact Or.inl (pubValidS_congr (fun i hi => (e i hi).symm) hq)
    · exact Or.inr (collides_head c)
  | .node l r, p, hs => by
    obtain ⟨hρ, hres, hg⟩ := T.nodeCircuit _ hs
    set ρ := nw (pubDigest ((BlockRec.Tree.node l r).key leafH nodeH) p) with eρ
    have hp : pairsH leafH nodeH nw lw (.node l r) p =
        (wordsOf ρ nodeKey.res ++ valsH (StarkedAir.Circuit.nodeOut ρ), (BlockRec.Tree.node l r).key leafH nodeH ++ valsH p) ::
        (wordsOf ρ nodeC0.res.chash ++ wordsOf ρ nodeC0.res.key ++ wordsOf ρ nodeC1.res.chash ++ wordsOf ρ nodeC1.res.key,
          l.hash leafH nodeH ++ l.key leafH nodeH ++ r.hash leafH nodeH ++ r.key leafH nodeH) ::
        (pairsH leafH nodeH nw lw l (nodePL ρ) ++ pairsH leafH nodeH nw lw r (nodePR ρ)) := by
      rw [pairsH]
    rw [hp]
    obtain ⟨r0, hr0, hm0⟩ := HeaderRec.hook_mem0
    obtain ⟨r1, hr1, hm1⟩ := HeaderRec.hook_mem1
    have s0 := T.recVerifies ρ _ _ _ (hg _ _ _ hm0)
    have s1 := T.recVerifies ρ _ _ _ (hg _ _ _ hm1)
    rw [List.drop_left' hr0, hdigest0 hρ] at s0
    rw [List.drop_left' hr1, hdigest1 hρ] at s1
    rw [hdigest hρ] at hres
    have kl : (wordsOf ρ nodeKey.res).length = 8 := by rw [wordsOf_length]; simp [nodeKey, blake2s]
    rcases pubDigest_eqC kl (BlockRec.Tree.key_length leafH nodeH (.node l r)) hres with ⟨ek, ev⟩ | c
    swap; · exact Or.inr (collides_head c)
    rw [hkey hρ] at ek
    have w8 : ∀ rs : List ℕ, rs.length = 8 → (wordsOf ρ rs).length = 8 := fun rs h => by rw [wordsOf_length, h]
    rcases keyOf_eqC (w8 _ (child_chash_length _ _)) (w8 _ (child_key_length _ _)) (w8 _ (child_chash_length _ _))
      (by cases l <;> simp [BlockRec.Tree.hash, hl, hn]) (BlockRec.Tree.key_length leafH nodeH l)
      (by cases r <;> simp [BlockRec.Tree.hash, hl, hn]) ek with ⟨e1, e2, e3, e4⟩ | c
    swap; · exact Or.inr (collides_second c)
    have e1' : wordsOf ρ nodeC0.res.chash = l.hash leafH nodeH := e1
    have e2' : wordsOf ρ nodeC0.res.key = l.key leafH nodeH := e2
    have e3' : wordsOf ρ nodeC1.res.chash = r.hash leafH nodeH := e3
    have e4' : wordsOf ρ nodeC1.res.key = r.key leafH nodeH := e4
    rw [e1', e2'] at s0
    rw [e3', e4'] at s1
    rcases htree_soundWS T hl hn l _ s0 with vl | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    rcases htree_soundWS T hl hn r _ s1 with vr | c
    swap; · exact Or.inr (c.mono fun x hx => by simp [hx])
    exact Or.inl (pubValidS_congr ev (node_composeS hρ vl vr))

end StarkedAir.Circuit.RecCR
