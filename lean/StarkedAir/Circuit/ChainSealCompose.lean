/-
**The chain seal, composed (SEAL-LEAN).** One theorem for `verify-seal`: a seal proof accepted under
the pinned seal identity, with the digest the verifier recomputes from its chain of epoch openings
`c`, the pinned set tree shapes `ts` and the end set's facts `W`, gives (under the recursion trust
hypotheses: `EpochChainW.TrustEW` for the chain, `RecCR.TrustW` for the set trees, and the seal's own
circuit as a witness function `sealW`):
- the chain is valid (`EpochChain.Chain.Valid`, as `chain_verifyW`);
- per epoch `i`, `rest`'s preimage `x` (the epoch's sum `s`, input count, challenge, block-hash roots)
  and, under the fractions of that challenge (`fracOf x`), the end set's pass and (when the epoch has
  one) the start set's pass: from `begin 1 count`, records fold to final states `SE`, `SB` over
  segment trees of the pinned shapes; the epoch's final set digest is `SE`'s Blake2s finish and its
  previous one `SB`'s; the balance `SE.sums = s + SB.sums` (`= s` from genesis); the counts and the
  start set's highest height in range;
- the end facts `W` are the last end set's count, amount, highest height, Merkle root and SHA-256 state
  digest (and the first start set's, or zero words from genesis);

or two of the listed message pairs collide (`sealPairs`: the seal's, the chain's, `acc`'s, the epoch
roots' openings, the set trees'), a concrete Blake2s collision.
-/
import StarkedAir.Circuit.ChainSealSet
import StarkedAir.Circuit.EpochChainW

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q Spec.Blake2s
open StarkedAir.Circuit.BlockRec (H H_length wordsOf_eq wordsOf_length blake2s_length)
open StarkedAir.Circuit.SetTree (pubsDigest_length)
open StarkedAir.Circuit.RecCR (Collides CollidesAt collides_head H_eqC)
open StarkedAir.Circuit.EpochChain (Chain Ep EpS Open rootMsg)
open StarkedAir.Circuit.EpochRoot (chainOuts chainOuts_length)

variable {ρ : ℕ → Q}

/-! ### `acc` as a list fold, unfolded -/

/-- `acc` over output digests: `H(o₀ ‖ o₁)`, then `H(acc ‖ oₖ)`. -/
def accL : List (List Word) → List Word
  | o0 :: o1 :: os => os.foldl (fun a o => H (a ++ o)) (H (o0 ++ o1))
  | _ => []

/-- The message of the `k`-th hash of `acc`. -/
def accMsg (xs : List (List Word)) (k : ℕ) : List Word :=
  if k = 0 then xs.getD 0 [] ++ xs.getD 1 [] else accL (xs.take (k + 1)) ++ xs.getD (k + 1) []

/-- The pairs `acc`'s unfolding compares. -/
def accPairsL (xs ys : List (List Word)) : List (List Word × List Word) :=
  (List.range (xs.length - 1)).map fun k => (accMsg xs k, accMsg ys k)

theorem accL_take : ∀ (xs : List (List Word)) (k : ℕ), k + 2 ≤ xs.length → accL (xs.take (k + 2)) = H (accMsg xs k)
  | o0 :: o1 :: os, 0, _ => by simp [accL, accMsg]
  | o0 :: o1 :: os, k + 1, hk => by
    have hk' : k < os.length := by simp at hk; omega
    simp only [accMsg, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    rw [show k + 1 + 2 = (k + 1) + 2 from rfl, List.take_succ_cons, List.take_succ_cons]
    simp only [accL]
    rw [List.take_add_one, List.getElem?_eq_getElem hk', Option.toList_some, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    congr 2
    rw [List.getD_cons_succ, List.getD_cons_succ, List.getD_eq_getElem _ _ hk']
  | [], _, h => by simp at h
  | [_], _, h => by simp at h

theorem accL_length_eq (xs : List (List Word)) (k : ℕ) (hk : k + 2 ≤ xs.length) : (accL (xs.take (k + 2))).length = 8 := by
  rw [accL_take xs k hk, H_length]

/-- **`acc` unfolded**: equal `acc`s over equal-length lists of 8-word digests are equal digests, or two
of `accPairsL` collide. -/
theorem accL_inj {xs ys : List (List Word)} (hl : xs.length = ys.length)
    (hx : ∀ i < xs.length, (xs.getD i []).length = 8) (hy : ∀ i < ys.length, (ys.getD i []).length = 8) :
    ∀ K, K + 2 ≤ xs.length → accL (xs.take (K + 2)) = accL (ys.take (K + 2)) →
      (∀ i < K + 2, xs.getD i [] = ys.getD i []) ∨ Collides (accPairsL xs ys)
  | 0, hK, he => by
    rw [accL_take xs 0 hK, accL_take ys 0 (by omega)] at he
    rcases H_eqC _ _ he with e | c
    · simp only [accMsg] at e
      obtain ⟨e0, e1⟩ := List.append_inj e (by rw [hx 0 (by omega), hy 0 (by omega)])
      left; intro i hi
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact e0
      · exact e1
    · exact Or.inr ⟨_, List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), rfl⟩, c⟩
  | K + 1, hK, he => by
    rw [accL_take xs (K + 1) hK, accL_take ys (K + 1) (by omega)] at he
    rcases H_eqC _ _ he with e | c
    · simp only [accMsg, Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false] at e
      obtain ⟨e0, e1⟩ := List.append_inj e (by rw [accL_length_eq xs K (by omega), accL_length_eq ys K (by omega)])
      rcases accL_inj hl hx hy K (by omega) e0 with h | c
      · left; intro i hi
        by_cases hi' : i < K + 2
        · exact h i hi'
        · rw [show i = K + 1 + 1 by omega]; exact e1
      · exact Or.inr c
    · exact Or.inr ⟨_, List.mem_map.mpr ⟨K + 1, List.mem_range.mpr (by omega), rfl⟩, c⟩

/-! ### The chain's epochs as a list -/

/-- A default epoch (outside the chain). -/
def dEp : Ep := ⟨⟨0, 0, fun _ => .leaf 0⟩, ⟨[], [], 0, 0, []⟩⟩

/-- Epoch `i` of a chain. -/
def epAt (c : Chain Ep) (i : ℕ) : Ep := c.epochs.getD i dEp

/-- The epoch roots' output digests, in order (the first from its previous set when `c.gen`). -/
noncomputable def outsOf (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (c : Chain Ep) : List (List Word) :=
  (List.range c.epochs.length).map fun i => (epAt c i).out leafH nodeH (if i = 0 then c.gen else true)

theorem map_range_getD {α β : Type} (l : List α) (d : α) (g : α → β) :
    (List.range l.length).map (fun i => g (l.getD i d)) = l.map g := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simpa using h1)]

theorem accL_outs (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (c : Chain Ep) :
    accL (outsOf leafH nodeH c) = c.acc leafH nodeH := by
  obtain ⟨e0, e1, es, he, ha⟩ := EpochChain.Chain.acc_fold (leafH := leafH) (nodeH := nodeH) c
  rw [ha]
  simp only [outsOf, epAt, he, List.length_cons]
  rw [List.range_succ_eq_map, List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, if_pos, List.getD_cons_zero, Function.comp_def, Nat.succ_eq_add_one,
    Nat.zero_add, List.getD_cons_succ, show (0 + 1 = 0) = False by simp, if_false]
  simp only [accL, if_false, Nat.add_eq_zero_iff, one_ne_zero, and_false]
  rw [show (List.range es.length).map (fun x => (es.getD x dEp).out leafH nodeH true) = es.map (fun e => e.out leafH nodeH true)
    from map_range_getD es dEp (fun e => e.out leafH nodeH true), List.foldl_map]

theorem outsOf_length (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (c : Chain Ep) :
    (outsOf leafH nodeH c).length = c.epochs.length := by simp [outsOf]

theorem outsOf_getD (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (c : Chain Ep) {i : ℕ} (hi : i < c.epochs.length) :
    (outsOf leafH nodeH c).getD i [] = (epAt c i).out leafH nodeH (if i = 0 then c.gen else true) := by
  rw [outsOf, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-! ### The program's parts by index -/

theorem chainOuts_getD_holds {α : Type} {f : ℕ → ℕ → Out α} {n k i : ℕ} (hi : i < k) (d : Out α)
    (h : Holds ρ ((chainOuts f n k).flatMap (·.ops))) :
    ∃ r, (chainOuts f n k).getD i d = f i r ∧ Holds ρ (f i r).ops := by
  obtain ⟨r, hr, hh⟩ := EpochRoot.chainOuts_holds hi h
  exact ⟨r, by rw [List.getD_eq_getElem _ _ (by rw [chainOuts_length]; exact hi), hr], hh⟩

theorem chainOuts_getD_mem {α : Type} {f : ℕ → ℕ → Out α} {n k i : ℕ} (hi : i < k) (d : Out α) {o : Op}
    (ho : o ∈ ((chainOuts f n k).getD i d).ops) : o ∈ (chainOuts f n k).flatMap (·.ops) := by
  rw [List.getD_eq_getElem _ _ (by rw [chainOuts_length]; exact hi)] at ho
  exact List.mem_flatMap.mpr ⟨_, List.getElem_mem _, ho⟩

/-! ### An epoch root's opening split -/

theorem openWords_split {R : RootRegs} {prevV : Bool} {K : List Word} {o : Open}
    (hf : (wordsOf ρ R.fin).length = 8) (hp : (wordsOf ρ R.prev).length = 8)
    (hrs : (wordsOf ρ R.rest).length = 8) (hw : o.Fits)
    (e : openWords ρ R prevV = rootMsg K prevV o) :
    wordsOf ρ R.key = K ∧ wordsOf ρ R.fin = o.fin ∧ (prevV = true → wordsOf ρ R.prev = o.prev) ∧
      BitVec.ofNat 32 (ρ R.lo).a.val = BitVec.ofNat 32 o.lo ∧ BitVec.ofNat 32 (ρ R.hi).a.val = BitVec.ofNat 32 o.hi ∧
      wordsOf ρ R.rest = o.rest := by
  obtain ⟨⟨hf8, hp8, hr8⟩, -, -⟩ := hw
  simp only [openWords, rootMsg] at e
  obtain ⟨e1, eR⟩ := List.append_inj' e (by rw [hrs, hr8])
  obtain ⟨e2, eLH⟩ := List.append_inj' e1 (by simp)
  have eLH' := eLH
  simp only [List.cons.injEq, and_true] at eLH'
  cases prevV
  · simp only [Bool.false_eq_true, if_false, List.append_nil] at e2
    obtain ⟨eK, eF⟩ := List.append_inj' e2 (by rw [hf, hf8])
    exact ⟨eK, eF, fun h => absurd h (by simp), eLH'.1, eLH'.2, eR⟩
  · simp only [if_true] at e2
    obtain ⟨e3, eP⟩ := List.append_inj' e2 (by rw [hp, hp8])
    obtain ⟨eK, eF⟩ := List.append_inj' e3 (by rw [hf, hf8])
    exact ⟨eK, eF, fun _ => eP, eLH'.1, eLH'.2, eR⟩

/-! ### What the seal states -/

/-- Coordinate `j` of a QM31. -/
def coordQ (j : ℕ) (q : Q) : F := if j = 0 then q.a else if j = 1 then q.b else if j = 2 then q.c else q.d

/-- **The set system's challenge inputs from `rest`'s preimage `x`**: `γ`, `z` (limbs 5–12), then the
coordinates of `α^0 … α^25`, `α` the QM31 of limbs 13–16; zero elsewhere. -/
def chalPub (x : ℕ → F) (k : ℕ) : F :=
  if 41 ≤ k ∧ k < 49 then x (5 + (k - 41))
  else if 49 ≤ k ∧ k < 153 then coordQ ((k - 49) % 4) (qpow ⟨x 13, x 14, x 15, x 16⟩ ((k - 49) / 4))
  else 0

/-- **The fractions of the challenge in `rest`'s preimage `x`** (`SetPass.Rec.frac`). -/
noncomputable def fracOf (x : ℕ → F) : Spec.CoinEpoch.CEv → Spec.QM31.QM := SetPass.Rec.frac (chalPub x)

/-- A Blake2s state's finish, as words (`SetFile.b2Final` is its bytes). -/
def b2W (S : Spec.SetFile.B2) : List Word := (List.range 8).map (hashBlocks S.h S.t S.pend)

/-- **A proven coin-set pass**: the count below `2^30`; from `begin 1 cnt`, some records fold under `fr` to
`S`, in segments whose Merkle roots are the leaves of a segment tree of shape `t` with root `root`. -/
def PassOk (t : BlockRec.Tree) (fr : Spec.CoinEpoch.CEv → Spec.QM31.QM) (cnt : ℕ) (S : Spec.SetFile.St Spec.QM31.QM)
    (root : Spec.Sha256.State) : Prop :=
  cnt < 2 ^ 30 ∧ ∃ (segs : List (ℕ × List Spec.CoinEpoch.CEv)) (τ : SetTree.SegTree),
    S = ((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [fr]) (Spec.SetFile.begin 1 cnt) ∧
    τ.Fits t ∧ τ.segs.map SetTree.decodeRoot = Spec.SetMerkle.passRoots none segs ∧ τ.root = root

/-- **What the seal proves of epoch `i`** (opening `e`, `m` children): `rest` is Blake2s of the preimage
`x` (`s`, input count, challenge, block-hash roots); the end set's pass (count `cE`, final state `SE`, root
`rE`) under the challenge's fractions finishes to the epoch's final set digest; with a start set, its
pass finishes to the previous set digest, `SE.sums = s + SB.sums`, the counts below `2^30` with the input
count, and the start set's highest coin is below the epoch's first block; from genesis `SE.sums = s`. -/
def EpochOk (ts : ℕ → BlockRec.Tree) (gen : Bool) (i : ℕ) (e : Ep) (m : ℕ) (x : ℕ → F) (cE cB : ℕ)
    (SE SB : Spec.SetFile.St Spec.QM31.QM) (rE rB : Spec.Sha256.State) : Prop :=
  e.o.rest = H ((List.range (17 + 16 * m)).map fun j => BitVec.ofNat 32 (x j).val) ∧
  PassOk (ts (endIdx gen i)) (fracOf x) cE SE rE ∧ e.o.fin = b2W SE.b2 ∧ (SE.i : F) = cE ∧
  (hasStart gen i = true →
    PassOk (ts (startIdx gen i)) (fracOf x) cB SB rB ∧ e.o.prev = b2W SB.b2 ∧ (SB.i : F) = cB ∧
    (∃ y, SB.sums = [y] ∧ SE.sums = [Block.RunSum.pQ x 0 + y]) ∧
    (x 4 + (cE : F) + (cB : F)).val < 2 ^ 30 ∧ SB.maxHeight < e.o.lo) ∧
  (hasStart gen i = false → SE.sums = [Block.RunSum.pQ x 0] ∧ (x 4 + (cE : F)).val < 2 ^ 30)

/-- Blake2s of a SHA-256 state's 82 limbs. -/
def shaVec (v : ℕ → F) : List Word := H ((List.range 82).map fun j => BitVec.ofNat 32 (v j).val)

/-- **The end facts**: the count, the amount's three words, the highest height, the Merkle root, the
digest of the limbs of the SHA-256 state, then the start set's SHA-256 digest `shaS`. -/
def EndOk (W : List Word) (cE : ℕ) (SE : Spec.SetFile.St Spec.QM31.QM) (rE : Spec.Sha256.State) (shaS : List Word) : Prop :=
  ∃ v : ℕ → F, SetPass.EncSha v 0 SE.sha ∧
    W = [BitVec.ofNat 32 cE] ++ (List.range 3).map (fun w => BitVec.ofNat 32 (SE.amount / 2 ^ (32 * w))) ++
      [BitVec.ofNat 32 SE.maxHeight] ++ (List.range 8).map (Spec.HeaderTree.stWord rE) ++ shaVec v ++ shaS

/-- The verifier's side: the children's identities and witness functions. -/
structure Ctx where
  leafH : ℕ → List Word
  nodeH : ℕ → ℕ → List Word
  rootH : ℕ → Bool → ℕ → List Word
  joinH : EpochJoin.Variant → List Word
  nw : ℕ → ℕ → List Word → ℕ → Q
  lw : ℕ → List Word → ℕ → F
  rootW : ℕ → Bool → ℕ → List Word → ℕ → Q
  joinW : EpochJoin.Variant → List Word → ℕ → Q
  leafS : ℕ → List Word
  nodeS : List Word
  nwS : List Word → ℕ → Q
  lwS : ℕ → List Word → ℕ → F
  sealW : List Word → ℕ → Q

section
variable (X : Ctx) (ms : List ℕ) (gen : Bool) (c : Chain Ep) (ts : ℕ → BlockRec.Tree) (W : List Word)

/-- **The key the verifier expects**: the join's identity and key, each set tree's hash and key. -/
noncomputable def sealKeyMsg : List Word :=
  X.joinH c.variant ++ (c.map Ep.sh).key X.leafH X.nodeH X.rootH X.joinH ++
    (List.range (nSets ms.length gen)).flatMap (fun j => (ts j).hash X.leafS X.nodeS ++ (ts j).key X.leafS X.nodeS)

/-- **The seal's output message the verifier expects**: the key, the range, the start and end set digests,
`acc`, the end facts `W`. -/
noncomputable def sealMsg : List Word :=
  H (sealKeyMsg X ms gen c ts) ++ [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++ c.first.o.prev ++
    c.last.o.fin ++ c.acc X.leafH X.nodeH ++ W

/-- The seal's assignment for that digest. -/
noncomputable def sealRho : ℕ → Q := X.sealW (H (sealMsg X ms gen c ts W))

end

/-- The parts' gadgets by index (the defaults `parts` uses). -/
def setO (P : Parts) (j : ℕ) : Out ChildRegs := P.sets.getD j ⟨[], ⟨id, [], [], []⟩, 0⟩
def rootO (P : Parts) (i : ℕ) : Out RootRegs := P.roots.getD i ⟨[], ⟨[], [], [], 0, 0, [], []⟩, 0⟩
def restO (P : Parts) (i : ℕ) : Out RestRegs := P.rests.getD i ⟨[], ⟨[], 0, [], []⟩, 0⟩
def chalO (P : Parts) (i : ℕ) : Out (List ℕ) := P.chals.getD i ⟨[], [], 0⟩
def openO (P : Parts) (j : ℕ) : Out SetRegs :=
  P.opens.getD j ⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩

/-- The key message's registers. -/
def keyRegs (P : Parts) : List ℕ := P.J.res.chash ++ P.J.res.key ++ P.sets.flatMap (fun c => c.res.chash ++ c.res.key)

/-- Set child `j`'s incoming and outgoing public values and root limbs. -/
noncomputable def pbAt (ρ : ℕ → Q) (P : Parts) (gen : Bool) (j : ℕ) : ℕ → F :=
  pbOf ρ (chalO P (epochOf gen j)).res (openO P j).res.st.cnt
noncomputable def pfAt (ρ : ℕ → Q) (P : Parts) (gen : Bool) (j : ℕ) : ℕ → F :=
  pfOf ρ (chalO P (epochOf gen j)).res (openO P j).res.st.i
def RAt (ρ : ℕ → Q) (P : Parts) (j : ℕ) : ℕ → F := fun k => (ρ ((setO P j).res.pubs (32 + k))).a

/-- The chain's pairs (`chain_verifyW`'s). -/
noncomputable def chainV (X : Ctx) (c : Chain Ep) : List (List Word × List Word) :=
  EpochChain.chainPairs X.leafH X.nodeH X.rootH X.joinH X.nw X.lw X.rootW X.joinW (c.map Ep.sh)
      (c.digest X.leafH X.nodeH X.rootH X.joinH) (EpochChain.verRest X.leafH X.nodeH c) ++
    (c.msg X.leafH X.nodeH X.rootH X.joinH,
      (EpochChain.extract X.joinW (c.map Ep.sh) (c.digest X.leafH X.nodeH X.rootH X.joinH)).msg X.leafH X.nodeH X.rootH X.joinH) ::
    EpochChain.accPairs X.leafH X.nodeH c (EpochChain.extract X.joinW (c.map Ep.sh) (c.digest X.leafH X.nodeH X.rootH X.joinH))

/-- **Every pair the seal's soundness compares**: the output message, the key message, the chain's, `acc`'s
unfolding, each epoch root's opening, each set tree's. -/
noncomputable def sealPairs (X : Ctx) (ms : List ℕ) (gen : Bool) (c : Chain Ep) (ts : ℕ → BlockRec.Tree) (W : List Word) :
    List (List Word × List Word) :=
  let ρ := sealRho X ms gen c ts W
  let P := parts ms gen
  (wordsOf ρ P.msg, sealMsg X ms gen c ts W) :: (wordsOf ρ (keyRegs P), sealKeyMsg X ms gen c ts) ::
    (chainV X c ++ accPairsL ((List.range ms.length).map fun i => wordsOf ρ (rootO P i).res.out) (outsOf X.leafH X.nodeH c) ++
      (List.range ms.length).map (fun i => (openWords ρ (rootO P i).res (hasStart gen i),
        rootMsg ((epAt c i).sh.key X.leafH X.nodeH) (hasStart gen i) (epAt c i).o)) ++
      (List.range (nSets ms.length gen)).flatMap fun j =>
        SetPass.setPairs X.leafS X.nodeS X.nwS X.lwS (ts j) (pbAt ρ P gen j) (pfAt ρ P gen j) (RAt ρ P j))

/-- The start set's SHA-256 digest words in the seal's message. -/
def shaStartRegs (P : Parts) (gen : Bool) : List ℕ :=
  if gen then List.replicate 8 P.C.res.zero else (openO P 0).res.shaDg

/-! ### Helper facts -/

theorem epochs_two {α : Type} : ∀ c : Chain α, 2 ≤ c.epochs.length
  | .base _ _ _ => by simp [Chain.epochs]
  | .step c _ => by simp only [Chain.epochs, List.length_append, List.length_singleton]; have := epochs_two c; omega

theorem epAt_mem {c : Chain Ep} {i : ℕ} (hi : i < c.epochs.length) : epAt c i ∈ c.epochs := by
  rw [epAt, List.getD_eq_getElem _ _ hi]; exact List.getElem_mem _

theorem fits_at {c : Chain Ep} (hw : c.All (fun e => e.o.Fits)) {i : ℕ} (hi : i < c.epochs.length) : (epAt c i).o.Fits :=
  (Chain.all_iff _ c).mp hw _ (epAt_mem hi)

/-- A valid chain's epochs have `from ≤ to < 2^30`. -/
theorem valid_lohi {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
    {SatC : List Word → List Word → Prop} {c : Chain Ep} (hv : c.Valid leafH nodeH rootH SatC) {i : ℕ}
    (hi : i < c.epochs.length) : (epAt c i).o.lo ≤ (epAt c i).o.hi ∧ (epAt c i).o.hi < 2 ^ 30 := by
  obtain ⟨h0, ht⟩ := EpochChain.Chain.Valid.roots hv
  rcases i with _ | i
  · have : epAt c 0 = c.first := by
      have hh := Chain.epochs_head c
      rw [epAt, List.getD_eq_getElem _ _ hi]
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hi] at hh
      exact Option.some.inj hh
    rw [this]; exact ⟨h0.2.2.1, h0.2.2.2⟩
  · have hm : epAt c (i + 1) ∈ c.epochs.tail := by
      rw [epAt, List.getD_eq_getElem _ _ hi]
      have : c.epochs[i + 1] = c.epochs.tail[i]'(by rw [List.length_tail]; omega) := by simp
      rw [this]; exact List.getElem_mem _
    exact ⟨(ht _ hm).2.2.1, (ht _ hm).2.2.2⟩

theorem hasStart_eq {c : Chain Ep} {gen : Bool} (hcg : c.gen = !gen) (i : ℕ) :
    hasStart gen i = if i = 0 then c.gen else true := by
  rcases i with _ | i <;> cases gen <;> simp [hasStart, hcg]

/-- `a - b - 1` small with `a`, `b` small: `b < a`. -/
theorem lt_of_sub_one {a b : F} (ha : a.val < 2 ^ 30) (hb : b.val < 2 ^ 24) (h : (a - b - 1).val < 2 ^ 30) :
    b.val < a.val := by
  set z := a - b - 1 with hz
  have e : a = z + b + 1 := by rw [hz]; ring
  have h1 : (z + b).val = z.val + b.val := ZMod.val_add_of_lt (lt_P (by omega))
  have h2 : (z + b + 1).val = (z + b).val + (1 : F).val :=
    ZMod.val_add_of_lt (by rw [h1, ZMod.val_one]; exact lt_P (by omega))
  rw [← e, h1, ZMod.val_one] at h2
  omega

/-- Equal blocks of 16: a flatMap over a list against one over its indices. -/
theorem flatMap_blocks {α : Type} (d : α) (f : α → List Word) : ∀ (l : List α) (g : ℕ → List Word),
    (∀ a ∈ l, (f a).length = 16) → (∀ j, (g j).length = 16) → l.flatMap f = (List.range l.length).flatMap g →
      ∀ j < l.length, f (l.getD j d) = g j
  | [], _, _, _, _, j, hj => by simp at hj
  | a :: l, g, hf, hg, he, j, hj => by
    rw [List.flatMap_cons, List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map] at he
    obtain ⟨e0, e1⟩ := List.append_inj he (by rw [hf a List.mem_cons_self, hg 0])
    rcases j with _ | j
    · simpa using e0
    · have := flatMap_blocks d f l (fun j => g (j + 1)) (fun b hb => hf b (List.mem_cons_of_mem _ hb))
        (fun j => hg (j + 1)) (by simpa [Function.comp_def] using e1) j (by simp at hj; omega)
      simpa using this

theorem mem_chainOuts {α : Type} {f : ℕ → ℕ → Out α} {n k : ℕ} {a : Out α} (ha : a ∈ chainOuts f n k) :
    ∃ i r, i < k ∧ a = f i r := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  rw [chainOuts_length] at hi
  obtain ⟨r, hr⟩ := EpochRoot.chainOuts_get f n k i hi
  exact ⟨i, r, hi, hr⟩

theorem keyRegs_length (ms : List ℕ) (gen : Bool) :
    (keyRegs (parts ms gen)).length = 16 + 16 * nSets ms.length gen := by
  have hs : ∀ a ∈ (parts ms gen).sets, a.res.chash.length + a.res.key.length = 16 := by
    intro a ha
    obtain ⟨i, r, -, rfl⟩ := mem_chainOuts ha
    rw [setChild_key_length, setChild_chash_length]
  have hJ := EpochJoin.joinChild_lengths 0 0
  simp only [keyRegs, List.length_append, List.length_flatMap]
  rw [List.map_congr_left hs, List.map_const', List.sum_replicate, show (parts ms gen).J = EpochJoin.joinChild 0 0 from rfl,
    hJ.2.2.2.2.2, hJ.1, show (parts ms gen).sets.length = nSets ms.length gen from chainOuts_length _ _ _]
  simp; ring

theorem openO_get (ms : List ℕ) (gen : Bool) {j : ℕ} (hj : j < nSets ms.length gen) :
    ∃ r, openO (parts ms gen) j = setOpen r (setO (parts ms gen) j).res
      (chalO (parts ms gen) (epochOf gen j)).res (eState ms gen j) (parts ms gen).C.res := by
  have hlen : (parts ms gen).opens.length = nSets ms.length gen := chainOuts_length _ _ _
  obtain ⟨r, hr⟩ : ∃ r, (parts ms gen).opens[j]'(by rw [hlen]; exact hj) = setOpen r (setO (parts ms gen) j).res
      (chalO (parts ms gen) (epochOf gen j)).res (eState ms gen j) (parts ms gen).C.res :=
    EpochRoot.chainOuts_get _ _ _ j hj
  exact ⟨r, by rw [openO, List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]; exact hr⟩

theorem setO_get (ms : List ℕ) (gen : Bool) {j : ℕ} (hj : j < nSets ms.length gen) :
    ∃ r, setO (parts ms gen) j = setChild r (JEXT + SEXT * j) (j + 1) := by
  have hlen : (parts ms gen).sets.length = nSets ms.length gen := chainOuts_length _ _ _
  obtain ⟨r, hr⟩ : ∃ r, (parts ms gen).sets[j]'(by rw [hlen]; exact hj) = setChild r (JEXT + SEXT * j) (j + 1) :=
    EpochRoot.chainOuts_get _ _ _ j hj
  exact ⟨r, by rw [setO, List.getD_eq_getElem _ _ (by rw [hlen]; exact hj)]; exact hr⟩

theorem openO_lengths (ms : List ℕ) (gen : Bool) {j : ℕ} (hj : j < nSets ms.length gen) :
    (openO (parts ms gen) j).res.amtW.length = 3 ∧ (openO (parts ms gen) j).res.mroot.length = 8 ∧
      (openO (parts ms gen) j).res.shaDg.length = 8 ∧ (openO (parts ms gen) j).res.fin.length = 8 := by
  obtain ⟨r, hr⟩ := openO_get ms gen hj
  rw [hr]
  refine ⟨by simp [setOpen, packBytes], by simp [setOpen, packW], pubsDigest_length _ _ _, by simp [setOpen, compressFinal]⟩

theorem nSets_pos {n : ℕ} {gen : Bool} (hn : 2 ≤ n) : 3 ≤ nSets n gen := by
  cases gen <;> simp [nSets] <;> omega

/-- The output message's parts. -/
theorem parts_msg (ms : List ℕ) (gen : Bool) :
    (parts ms gen).msg = (parts ms gen).key.res ++ [(parts ms gen).key.next, (parts ms gen).key.next + 1] ++
      (parts ms gen).J.res.first ++ (parts ms gen).J.res.last ++ (parts ms gen).J.res.tail ++
      [(openO (parts ms gen) (nSets ms.length gen - 1)).res.cntW] ++ (openO (parts ms gen) (nSets ms.length gen - 1)).res.amtW ++
      [(openO (parts ms gen) (nSets ms.length gen - 1)).res.maxhW] ++ (openO (parts ms gen) (nSets ms.length gen - 1)).res.mroot ++
      (openO (parts ms gen) (nSets ms.length gen - 1)).res.shaDg ++ shaStartRegs (parts ms gen) gen := rfl

theorem msg_length {ms : List ℕ} {gen : Bool} (hn : 2 ≤ ms.length) : (parts ms gen).msg.length = 63 := by
  have h3 := nSets_pos (gen := gen) hn
  obtain ⟨a1, m1, s1, -⟩ := openO_lengths ms gen (j := nSets ms.length gen - 1) (by omega)
  obtain ⟨-, -, s0, -⟩ := openO_lengths ms gen (j := 0) (by omega)
  have hJ := EpochJoin.joinChild_lengths 0 0
  have hk : (parts ms gen).key.res.length = 8 := by simp [parts, blake2s]
  rw [parts_msg]
  simp only [List.length_append, List.length_cons, List.length_nil, a1, m1, s1, hk,
    show (parts ms gen).J = EpochJoin.joinChild 0 0 from rfl, hJ.2.1, hJ.2.2.1, hJ.2.2.2.1]
  cases gen <;> simp [shaStartRegs, s0]

/-- **`acc` in the circuit is the fold over the epoch roots' outputs.** -/
theorem accChain_words {rout : ℕ → List ℕ} {r K : ℕ} (h : Holds ρ ((accChain rout r K).flatMap (·.ops)))
    (hl : ∀ i ≤ K, (rout i).length = 8) :
    ∀ k (hk : k < K), wordsOf ρ ((accChain rout r K)[k]'(by rw [accChain_length]; exact hk)).res =
      accL (((List.range (K + 1)).map (fun i => wordsOf ρ (rout i))).take (k + 2)) := by
  have hres : ∀ k (hk : k < K), ((accChain rout r K)[k]'(by rw [accChain_length]; exact hk)).res.length = 8 :=
    fun k hk => by rw [accChain_get rout r K k hk]; exact blake2s_length _ _ _
  have step : ∀ k (hk : k < K), wordsOf ρ ((accChain rout r K)[k]'(by rw [accChain_length]; exact hk)).res =
      H (wordsOf ρ (accLeft rout r k) ++ wordsOf ρ (rout (k + 1))) := by
    intro k hk
    have hlen : (wordsOf ρ (accLeft rout r k) ++ wordsOf ρ (rout (k + 1))).length = 16 := by
      rcases k with _ | k
      · simp [accLeft, accChain, wordsOf, hl 0 (by omega), hl 1 (by omega)]
      · rw [accLeft_succ]; simp [wordsOf, accChain_get rout r (k + 1) k (by omega), blake2s_length, hl (k + 1 + 1) (by omega)]
    rw [wordsOf_eq (hres k hk) (accChain_sound h k hk), H, hlen]
  intro k hk
  induction k with
  | zero =>
    rw [step 0 hk]
    have : accLeft rout r 0 = rout 0 := rfl
    rw [this, show (0 : ℕ) + 2 = 0 + 2 from rfl, accL_take _ 0 (by simp; omega)]
    simp [accMsg, List.getD_eq_getElem?_getD, show 1 < K + 1 by omega, show 0 < K + 1 by omega]
  | succ k ih =>
    rw [step (k + 1) hk, accLeft_succ]
    have e : (accChain rout r (k + 1))[k]'(by rw [accChain_length]; omega) =
        (accChain rout r K)[k]'(by rw [accChain_length]; omega) := by
      rw [accChain_get rout r (k + 1) k (by omega), accChain_get rout r K k (by omega)]
    rw [e, ih (by omega), accL_take _ (k + 1) (by simp; omega), accMsg, if_neg (by omega)]
    congr 2
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp

/-- **The challenge limbs are `chalPub` of `rest`'s preimage.** -/
theorem chal_pub {nr nc : ℕ} {C : Consts} (h : Holds ρ (chal nc ((List.range 12).map (nr + 5 + ·)) C).ops)
    (hC : ConstsOk ρ C) (hb : ∀ j < 12, IsBase (ρ (nr + 5 + j))) :
    ∀ t < 112, (ρ ((chal nc ((List.range 12).map (nr + 5 + ·)) C).res.getD t 0)).a =
      chalPub (fun j => (ρ (nr + j)).a) (41 + t) := by
  have hc : 8 ≤ ((List.range 12).map (nr + 5 + ·)).length := by simp
  have hch : ∀ j < 12, IsBase (ρ (((List.range 12).map (nr + 5 + ·)).getD j 0)) := fun j hj => by
    rw [getD_map_range hj]; exact hb j hj
  have cs := chal_sound h hC hch hc
  intro t ht
  by_cases h8 : t < 8
  · rw [chal_res_take h8 hc, getD_map_range (by omega), chalPub, if_pos (by omega)]
    congr 2; omega
  · obtain ⟨w, j, hj4, rfl⟩ : ∃ w j, j < 4 ∧ t = 8 + 4 * w + j := ⟨(t - 8) / 4, (t - 8) % 4, by omega, by omega⟩
    obtain ⟨-, hq⟩ := cs w (by omega)
    have g8 : ∀ k < 4, ((List.range 12).map (nr + 5 + ·)).getD (8 + k) 0 = nr + (13 + k) := fun k hk => by
      rw [getD_map_range (by omega)]; omega
    rw [g8 0 (by norm_num), g8 1 (by norm_num), g8 2 (by norm_num), g8 3 (by norm_num)] at hq
    unfold chalPub
    rw [if_neg (by omega), if_pos (by omega), show 41 + (8 + 4 * w + j) - 49 = 4 * w + j by omega,
      show (4 * w + j) % 4 = j by omega, show (4 * w + j) / 4 = w by omega]
    dsimp only
    have hα : (⟨(ρ (nr + 13)).a, (ρ (nr + 14)).a, (ρ (nr + 15)).a, (ρ (nr + 16)).a⟩ : Q) =
        ⟨(ρ (nr + (13 + 0))).a, (ρ (nr + (13 + 1))).a, (ρ (nr + (13 + 2))).a, (ρ (nr + (13 + 3))).a⟩ := rfl
    rw [hα, ← hq]
    interval_cases j <;> simp [coordQ]

theorem endIdx_lt {n : ℕ} {gen : Bool} {i : ℕ} (hi : i < n) : endIdx gen i < nSets n gen := by
  cases gen <;> simp [endIdx, nSets] <;> omega
theorem startIdx_lt {n : ℕ} {gen : Bool} {i : ℕ} (hi : i < n) : startIdx gen i < nSets n gen := by
  cases gen <;> simp [startIdx, nSets] <;> omega
theorem epochOf_end (gen : Bool) (i : ℕ) : epochOf gen (endIdx gen i) = i := by
  cases gen <;> simp [epochOf, endIdx] <;> omega
theorem epochOf_start {gen : Bool} {i : ℕ} (h : hasStart gen i = true) : epochOf gen (startIdx gen i) = i := by
  cases gen <;> simp [epochOf, startIdx, hasStart] at h ⊢ <;> omega
theorem last_end {n : ℕ} {gen : Bool} (hn : 1 ≤ n) : nSets n gen - 1 = endIdx gen (n - 1) := by
  cases gen <;> simp [endIdx, nSets] <;> omega

theorem openAt_eq (P : Parts) (j : ℕ) : openAt (P.opens.map (·.res)) j = (openO P j).res := by
  show (P.opens.map (·.res)).getD j ((⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩ : Out SetRegs).res) = _
  rw [List.getD_map]; rfl
theorem rootAt_eq (P : Parts) (i : ℕ) : rootAt (P.roots.map (·.res)) i = (rootO P i).res := by
  show (P.roots.map (·.res)).getD i ((⟨[], ⟨[], [], [], 0, 0, [], []⟩, 0⟩ : Out RootRegs).res) = _
  rw [List.getD_map]; rfl
theorem restAt_eq (P : Parts) (i : ℕ) : restAt (P.rests.map (·.res)) i = (restO P i).res := by
  show (P.rests.map (·.res)).getD i ((⟨[], ⟨[], 0, [], []⟩, 0⟩ : Out RestRegs).res) = _
  rw [List.getD_map]; rfl

theorem ofNat_inj32 {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem wordsOf_eqN {l : List ℕ} {m : ℕ} (hl : l.length = m) {f : ℕ → Word} (h : ∀ i < m, word (ρ (l.getD i 0)) = f i) :
    wordsOf ρ l = (List.range m).map f := by
  apply List.ext_getElem (by simp [wordsOf, hl])
  intro i h1 h2
  have hi : i < m := by simpa [wordsOf, hl] using h1
  simp only [List.getElem_map, List.getElem_range]
  rw [← h i hi, List.getD_eq_getElem _ _ (by omega)]
  simp [wordsOf]

theorem pQ_eq (p : ℕ → F) (k : ℕ) : Block.RunSum.pQ p k = Spec.QM31.toQ ⟨p k, p (k + 1), p (k + 2), p (k + 3)⟩ := rfl

theorem mem_seal_J {ms : List ℕ} {gen : Bool} {o : Op} (h : o ∈ (parts ms gen).J.ops) : o ∈ (chainSeal ms gen).ops := by
  rw [chainSeal_ops]; simp only [List.mem_append]; tauto

theorem mem_seal_sets {ms : List ℕ} {gen : Bool} {o : Op} (h : o ∈ (parts ms gen).sets.flatMap (·.ops)) :
    o ∈ (chainSeal ms gen).ops := by
  rw [chainSeal_ops]; simp only [List.mem_append]; tauto

theorem tree_hash_length (leafH : ℕ → List Word) (nodeH : List Word) (hl : ∀ L, (leafH L).length = 8)
    (hn : nodeH.length = 8) (t : BlockRec.Tree) : (t.hash leafH nodeH).length = 8 := by
  cases t <;> simp [BlockRec.Tree.hash, hl, hn]

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}

set_option maxHeartbeats 4000000 in
/-- **The chain seal is sound, up to a named collision (SEAL-LEAN).** -/
theorem seal_soundW (X : Ctx) {ok : (ℕ → F) → Prop} {sealH : List Word} {ms : List ℕ} {gen : Bool}
    (T : EpochChain.TrustEW Acc SatC VGates X.leafH X.nodeH X.rootH X.joinH (RecCR.LeafAt ok) X.nw X.lw X.rootW X.joinW)
    (TS : RecCR.TrustW Acc SatC VGates X.leafS X.nodeS SetTree.setNodeProgram (SetPass.LeafAtS SetPass.SegOk) X.nwS X.lwS)
    (TC : ∀ d, SatC sealH d → Holds (X.sealW d) (chainSeal ms gen).ops ∧
      wordsOf (X.sealW d) (chainSeal ms gen).results = d ∧ BlockRec.HookGates VGates (X.sealW d) (chainSeal ms gen).ops)
    (hl : ∀ L, (X.leafH L).length = 8) (hn : ∀ a v, (X.nodeH a v).length = 8)
    (hr : ∀ M p s, (X.rootH M p s).length = 8) (hj : ∀ v, (X.joinH v).length = 8)
    (hlS : ∀ L, (X.leafS L).length = 8) (hnS : X.nodeS.length = 8)
    (c : Chain Ep) (hok : (c.map Ep.sh).Ok) (hw : c.All (fun e => e.o.Fits))
    (hgen : c.gen = false → c.first.o.prev = List.replicate 8 0)
    (hlen : c.epochs.length = ms.length) (hcg : c.gen = !gen) (hms : ∀ i < ms.length, ms.getD i 0 ≤ 64)
    (hB : 4 * (16 + 16 * nSets ms.length gen) < 2 ^ 32)
    (ts : ℕ → BlockRec.Tree) (W : List Word) (hW : W.length = 29)
    (hacc : Acc sealH (H (sealMsg X ms gen c ts W))) :
    (∃ (x : ℕ → ℕ → F) (cE cB : ℕ → ℕ) (SE SB : ℕ → Spec.SetFile.St Spec.QM31.QM) (rE rB : ℕ → Spec.Sha256.State),
      c.Valid X.leafH X.nodeH X.rootH SatC ∧
      (∀ i < ms.length, EpochOk ts gen i (epAt c i) (ms.getD i 0) (x i) (cE i) (cB i) (SE i) (SB i) (rE i) (rB i)) ∧
      EndOk W (cE (ms.length - 1)) (SE (ms.length - 1)) (rE (ms.length - 1))
        (wordsOf (sealRho X ms gen c ts W) (shaStartRegs (parts ms gen) gen)) ∧
      (gen = true → wordsOf (sealRho X ms gen c ts W) (shaStartRegs (parts ms gen) gen) = List.replicate 8 0) ∧
      (gen = false → ∃ v : ℕ → F, SetPass.EncSha v 0 (SB 0).sha ∧
        wordsOf (sealRho X ms gen c ts W) (shaStartRegs (parts ms gen) gen) = shaVec v)) ∨
    Collides (sealPairs X ms gen c ts W) := by
  set d := H (sealMsg X ms gen c ts W) with hd
  obtain ⟨hρ, hres, hg⟩ := TC d (T.stwoSound _ _ hacc)
  have hρdef : sealRho X ms gen c ts W = X.sealW d := rfl
  rw [hρdef]
  set ρ := X.sealW d with hρρ
  set P := parts ms gen with hP
  set n := ms.length with hnn
  set S := nSets n gen with hS
  by_cases col : Collides (sealPairs X ms gen c ts W)
  · exact Or.inr col
  left
  have hsp : sealPairs X ms gen c ts W = (wordsOf ρ P.msg, sealMsg X ms gen c ts W) ::
      (wordsOf ρ (keyRegs P), sealKeyMsg X ms gen c ts) ::
      (chainV X c ++ accPairsL ((List.range n).map fun i => wordsOf ρ (rootO P i).res.out) (outsOf X.leafH X.nodeH c) ++
        (List.range n).map (fun i => (openWords ρ (rootO P i).res (hasStart gen i),
          rootMsg ((epAt c i).sh.key X.leafH X.nodeH) (hasStart gen i) (epAt c i).o)) ++
        (List.range S).flatMap fun j =>
          SetPass.setPairs X.leafS X.nodeS X.nwS X.lwS (ts j) (pbAt ρ P gen j) (pfAt ρ P gen j) (RAt ρ P j)) := rfl
  have sub : ∀ x ∈ chainV X c ++ accPairsL ((List.range n).map fun i => wordsOf ρ (rootO P i).res.out) (outsOf X.leafH X.nodeH c) ++
        (List.range n).map (fun i => (openWords ρ (rootO P i).res (hasStart gen i),
          rootMsg ((epAt c i).sh.key X.leafH X.nodeH) (hasStart gen i) (epAt c i).o)) ++
        (List.range S).flatMap (fun j =>
          SetPass.setPairs X.leafS X.nodeS X.nwS X.lwS (ts j) (pbAt ρ P gen j) (pfAt ρ P gen j) (RAt ρ P j)),
      x ∈ sealPairs X ms gen c ts W := fun x hx => by
    rw [hsp]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx)
  have n2 : 2 ≤ n := hlen ▸ epochs_two c
  have S3 : 3 ≤ S := nSets_pos n2
  obtain ⟨hJ, hSe, hR, hT, hC, hCh, hO, hA, hK, hKey, hD⟩ := seal_parts hρ
  have hCo : ConstsOk ρ P.C.res := consts_sound hC
  have hJeq : P.J = EpochJoin.joinChild 0 0 := rfl
  have hJl := EpochJoin.joinChild_lengths 0 0
  rw [← hJeq] at hJl
  -- the output message
  have hml := msg_length (gen := gen) n2
  obtain ⟨hlo, hhi, hdg⟩ := seal_digest hρ (by rw [hml]; norm_num)
  have hdw : wordsOf ρ (chainSeal ms gen).results = H (wordsOf ρ P.msg) := by
    have hrl : (chainSeal ms gen).results.length = 8 :=
      blake2s_length ((parts ms gen).key.next + 2) (parts ms gen).msg (4 * (parts ms gen).msg.length)
    rw [wordsOf_eq hrl hdg, H, wordsOf_length]
  rw [hdw] at hres
  have hm : wordsOf ρ P.msg = sealMsg X ms gen c ts W := by
    rcases H_eqC _ _ hres with e | cc
    · exact e
    · exact absurd ⟨_, by rw [hsp]; exact List.mem_cons_self, cc⟩ col
  -- its parts
  have hFirst := (fits_at hw (i := 0) (by omega))
  have hfirst8 : c.first.o.prev.length = 8 := hw.first.1.2.1
  have hlast8 : c.last.o.fin.length = 8 := hw.last.1.1
  have hkey8 : (wordsOf ρ P.key.res).length = 8 := by rw [wordsOf_length]; simp [hP, parts, blake2s]
  obtain ⟨eKey, eAB, eFirst, eLast, eTail, eW⟩ : wordsOf ρ P.key.res = H (sealKeyMsg X ms gen c ts) ∧
      [word (ρ P.key.next), word (ρ (P.key.next + 1))] = [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ∧
      wordsOf ρ P.J.res.first = c.first.o.prev ∧ wordsOf ρ P.J.res.last = c.last.o.fin ∧
      wordsOf ρ P.J.res.tail = c.acc X.leafH X.nodeH ∧
      wordsOf ρ ([(openO P (S - 1)).res.cntW] ++ (openO P (S - 1)).res.amtW ++ [(openO P (S - 1)).res.maxhW] ++
        (openO P (S - 1)).res.mroot ++ (openO P (S - 1)).res.shaDg ++ shaStartRegs P gen) = W := by
    have e := hm
    rw [parts_msg] at e
    simp only [sealMsg, wordsOf, List.map_append, List.map_cons, List.map_nil, Function.comp_apply] at e
    simp only [List.append_assoc] at e
    obtain ⟨k1, e⟩ := List.append_inj e (by simpa [wordsOf] using hkey8.trans (H_length _).symm)
    obtain ⟨k2, e⟩ := List.append_inj e (by simp)
    have j1 : (parts ms gen).J.res.first.length = 8 := (EpochJoin.joinChild_lengths 0 0).2.1
    have j2 : (parts ms gen).J.res.last.length = 8 := (EpochJoin.joinChild_lengths 0 0).2.2.1
    have j3 : (parts ms gen).J.res.tail.length = 8 := (EpochJoin.joinChild_lengths 0 0).2.2.2.1
    obtain ⟨k3, e⟩ := List.append_inj e (by simp [j1, hfirst8])
    obtain ⟨k4, e⟩ := List.append_inj e (by simp [j2, hlast8])
    obtain ⟨k5, e⟩ := List.append_inj e (by simp [j3, EpochChain.Chain.acc_length])
    refine ⟨k1, ?_, k3, k4, k5, ?_⟩
    · simpa using k2
    · simpa [wordsOf, List.append_assoc] using e
  -- the key message: the children's identities and keys
  have hkl := keyRegs_length ms gen
  have hkw := seal_key hρ (by
    show 4 * (keyRegs (parts ms gen)).length < 2 ^ 32
    rw [hkl]; exact hB)
  have hkey : wordsOf ρ P.key.res = H (wordsOf ρ (keyRegs P)) := by
    rw [wordsOf_eq (by simp [hP, parts, blake2s]) hkw, H, wordsOf_length]; rfl
  rw [hkey] at eKey
  have hke : wordsOf ρ (keyRegs P) = sealKeyMsg X ms gen c ts := by
    rcases H_eqC _ _ eKey with e | cc
    · exact e
    · exact absurd ⟨_, by rw [hsp]; exact List.mem_cons_of_mem _ List.mem_cons_self, cc⟩ col
  have hsl : P.sets.length = S := chainOuts_length _ _ _
  obtain ⟨eJh, eJk, eSets⟩ : wordsOf ρ P.J.res.chash = X.joinH c.variant ∧
      wordsOf ρ P.J.res.key = (c.map Ep.sh).key X.leafH X.nodeH X.rootH X.joinH ∧
      ∀ j < S, wordsOf ρ (setO P j).res.chash = (ts j).hash X.leafS X.nodeS ∧
        wordsOf ρ (setO P j).res.key = (ts j).key X.leafS X.nodeS := by
    have e := hke
    simp only [keyRegs, sealKeyMsg, wordsOf, List.map_append, List.map_flatMap] at e
    obtain ⟨e1, e3⟩ := List.append_inj e (by simp [hJl.2.2.2.2.2, hJl.1, hj, EpochChain.Chain.key_length])
    obtain ⟨e1, e2⟩ := List.append_inj e1 (by simp [hJl.2.2.2.2.2, hj])
    refine ⟨e1, e2, fun j hjS => ?_⟩
    have hb := flatMap_blocks ⟨[], ⟨id, [], [], []⟩, 0⟩ (fun a => a.res.chash.map (word ∘ ρ) ++ a.res.key.map (word ∘ ρ))
      P.sets (fun j => (ts j).hash X.leafS X.nodeS ++ (ts j).key X.leafS X.nodeS)
      (fun a ha => by
        obtain ⟨i, r, -, rfl⟩ := mem_chainOuts ha
        simp [setChild_key_length, setChild_chash_length])
      (fun j => by simp [tree_hash_length _ _ hlS hnS, BlockRec.Tree.key_length])
      (by rw [hsl]; exact e3) j (by rw [hsl]; exact hjS)
    obtain ⟨r, hr⟩ := setO_get ms gen hjS
    have hch : (setO P j).res.chash.length = 8 := by rw [hP, hr]; exact setChild_chash_length _ _ _
    obtain ⟨b1, b2⟩ := List.append_inj hb (by simp only [List.length_map]; rw [tree_hash_length _ _ hlS hnS]; exact hch)
    exact ⟨b1, b2⟩
  -- the join: hook 0, a satisfied join with the chain's digest
  obtain ⟨jroot, hjroot, hjmem⟩ := EpochJoin.joinChild_hook 0 0
  have sJ := T.recVerifies ρ 0 _ _ (hg _ _ _ (mem_seal_J hjmem))
  rw [List.drop_left' hjroot] at sJ
  change SatC (wordsOf ρ P.J.res.chash) (wordsOf ρ P.J.res.out) at sJ
  have hjo := EpochJoin.joinChild_out hJ
  have hjw : wordsOf ρ P.J.res.out = H (EpochJoin.joinWords ρ P.J.res) := by
    rw [wordsOf_eq hJl.2.2.2.2.1 hjo, H, EpochJoin.joinWords_length hJl.1 hJl.2.1 hJl.2.2.1 hJl.2.2.2.1]; rfl
  have hab : BitVec.ofNat 32 (ρ P.J.res.lo).a.val = BitVec.ofNat 32 c.first.o.lo ∧
      BitVec.ofNat 32 (ρ P.J.res.hi).a.val = BitVec.ofNat 32 c.last.o.hi := by
    rw [← hlo, ← hhi]; simpa using eAB
  have hjm : EpochJoin.joinWords ρ P.J.res = c.msg X.leafH X.nodeH X.rootH X.joinH := by
    simp only [EpochJoin.joinWords, EpochChain.Chain.msg, eJk, eFirst, eLast, eTail, hab.1, hab.2]
  rw [hjw, hjm, eJh] at sJ
  have hValid : c.Valid X.leafH X.nodeH X.rootH SatC := by
    rcases EpochChain.chain_verifyW T hl hn hr hj c hok hw hgen sJ with v | cc
    · exact v
    · exact absurd (cc.mono fun x hx => sub x (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hx))))
        col
  -- `acc`: the join's opening is the fold over the epoch roots' outputs
  have hroots : ∀ i < n, ∃ r, rootO P i = rootOpen r (eRoot ms gen i) (hasStart gen i) ∧
      Holds ρ (rootOpen r (eRoot ms gen i) (hasStart gen i)).ops := fun i hi =>
    chainOuts_getD_holds hi _ hR
  have hout8 : ∀ i < n, (rootO P i).res.out.length = 8 := fun i hi => by
    obtain ⟨r, hr, -⟩ := hroots i hi; rw [hr]; exact (rootOpen_lengths _ _ _).2.2.2.2
  have hal : P.accs.length = n - 1 := accChain_length _ _ _
  set ins := (List.range n).map (fun i => wordsOf ρ (rootO P i).res.out) with hins
  have hinsl : ins.length = n := by simp [hins]
  have haw : wordsOf ρ (P.accs[n - 2]'(by rw [hal]; omega)).res = accL ins := by
    have h0 := accChain_words hA (fun i hi => hout8 i (by omega)) (n - 2) (by omega)
    refine h0.trans ?_
    have e1 : ms.length - 1 + 1 = ms.length := by omega
    have e2 : ms.length - 2 + 2 = ms.length := by omega
    simp only [e1, e2]
    rw [List.take_of_length_le (by simp; omega)]
    rfl
  obtain ⟨-, -, -, -, hjt⟩ := checks_join hK
  have htail : wordsOf ρ P.J.res.tail = accL ins := by
    rw [← haw]
    apply EpochJoin.wordsOf_ext hJl.2.2.2.1 (by
      show ((accChain _ _ (ms.length - 1))[n - 2]'(by rw [accChain_length]; omega)).res.length = 8
      rw [accChain_get _ _ _ _ (by omega)]; exact blake2s_length _ _ _)
    intro w hw
    refine (hjt w hw).trans ?_
    have hx : (P.accs.map (·.res)).getD (n - 2) [] = (P.accs[n - 2]'(by rw [hal]; omega)).res := by
      rw [List.getD_eq_getElem _ _ (by simp [hal]; omega)]; simp
    show ρ (((P.accs.map (·.res)).getD (n - 2) []).getD w 0) = _
    rw [hx]
  rw [eTail, ← accL_outs] at htail
  have hol : (outsOf X.leafH X.nodeH c).length = n := by rw [outsOf_length, hlen]
  have heq : ∀ i < n, ins.getD i [] = (outsOf X.leafH X.nodeH c).getD i [] := by
    rcases accL_inj (xs := ins) (ys := outsOf X.leafH X.nodeH c) (by rw [hinsl, hol])
      (fun i hi => by rw [hinsl] at hi; rw [List.getD_eq_getElem _ _ (by omega)]; simp [hins, wordsOf_length, hout8 i hi])
      (fun i hi => by rw [hol] at hi; rw [outsOf_getD _ _ c (by omega)]; exact H_length _)
      (n - 2) (by omega)
      (by rw [show n - 2 + 2 = n by omega, List.take_of_length_le (by omega), List.take_of_length_le (by omega)]
          exact htail.symm) with h | cc
    · exact fun i hi => h i (by omega)
    · exact absurd (cc.mono fun x hx => sub x (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ hx)))) col
  -- each epoch root's opening is the chain's
  have hopen : ∀ i < n, wordsOf ρ (rootO P i).res.fin = (epAt c i).o.fin ∧
      (hasStart gen i = true → wordsOf ρ (rootO P i).res.prev = (epAt c i).o.prev) ∧
      BitVec.ofNat 32 (ρ (rootO P i).res.lo).a.val = BitVec.ofNat 32 (epAt c i).o.lo ∧
      wordsOf ρ (rootO P i).res.rest = (epAt c i).o.rest := by
    intro i hi
    obtain ⟨r, hr, hh⟩ := hroots i hi
    have hlens := rootOpen_lengths r (eRoot ms gen i) (hasStart gen i)
    have hro := rootOpen_out hh
    have hw' : wordsOf ρ (rootO P i).res.out = H (openWords ρ (rootO P i).res (hasStart gen i)) := by
      rw [hr, wordsOf_eq hlens.2.2.2.2 hro, H]
      congr 2
      simp only [openWords, wordsOf, List.length_append, List.length_map, hlens.1, hlens.2.1, hlens.2.2.1,
        hlens.2.2.2.1, List.length_cons, List.length_nil]
      cases hasStart gen i <;> simp [(rootOpen_lengths r (eRoot ms gen i) true).2.2.1]
    have e := heq i hi
    rw [hins, List.getD_eq_getElem _ _ (by simp; omega), outsOf_getD _ _ c (by omega)] at e
    simp only [List.getElem_map, List.getElem_range] at e
    rw [hw', ← hasStart_eq hcg i] at e
    have e2 : H (openWords ρ (rootO P i).res (hasStart gen i)) =
        H (rootMsg ((epAt c i).sh.key X.leafH X.nodeH) (hasStart gen i) (epAt c i).o) := e
    rcases H_eqC _ _ e2 with e3 | cc
    · have l8 : ∀ l : List ℕ, l.length = 8 → (wordsOf ρ l).length = 8 := fun l h => by rw [wordsOf_length, h]
      rw [hr] at e3 ⊢
      obtain ⟨-, ef, ep, el, -, er⟩ := openWords_split (l8 _ hlens.2.1) (l8 _ hlens.2.2.1) (l8 _ hlens.2.2.2.1)
        (fits_at hw (by omega)) e3
      exact ⟨ef, ep, el, er⟩
    · exact absurd (sub _ (List.mem_append_left _ (List.mem_append_right _
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))) (fun hm => col ⟨_, hm, cc⟩)
  -- the rests and the challenges
  have hrests : ∀ i < n, ∃ r, restO P i = restOpen r (eRoot ms gen i + 34) (ms.getD i 0) (rootO P i).res.rest ∧
      Holds ρ (restOpen r (eRoot ms gen i + 34) (ms.getD i 0) (rootO P i).res.rest).ops := fun i hi =>
    chainOuts_getD_holds hi _ hT
  have hchals : ∀ i < n, ∃ r, chalO P i = chal r (restO P i).res.ch P.C.res ∧ Holds ρ (chal r (restO P i).res.ch P.C.res).ops :=
    fun i hi => chainOuts_getD_holds hi _ hCh
  have hchl : ∀ i < n, (chalO P i).res.length = 112 := by
    intro i hi
    obtain ⟨r, hr, -⟩ := hchals i hi
    obtain ⟨r', hr', -⟩ := hrests i hi
    rw [hr, hr']; simp [chal, restOpen]
  have hb2 : P.C.res.b2iv.length = 16 := by simp [hP, parts, consts]
  have hsh : P.C.res.shaiv.length = 16 := by simp [hP, parts, consts]
  have hepo : ∀ j < S, epochOf gen j < n := by
    intro j hj; simp only [hS, nSets] at hj; simp only [epochOf]; split_ifs at hj ⊢ <;> omega
  -- the set children
  have hset : ∀ j < S, ∃ (Sj : Spec.SetFile.St Spec.QM31.QM) (rj : Spec.Sha256.State),
      PassOk (ts j) (SetPass.Rec.frac (pbAt ρ P gen j)) (ρ (openO P j).res.n).a.val Sj rj ∧
      SetPass.EncOut (pfAt ρ P gen j) Sj ∧ (Sj.i : F) = ((ρ (openO P j).res.n).a.val : F) ∧
      wordsOf ρ (openO P j).res.fin = b2W Sj.b2 ∧
      (∀ w < 8, word (ρ ((openO P j).res.mroot.getD w 0)) = Spec.HeaderTree.stWord rj w) ∧
      word (ρ (openO P j).res.cntW) = BitVec.ofNat 32 (ρ (openO P j).res.n).a.val ∧
      (∀ w < 3, word (ρ ((openO P j).res.amtW.getD w 0)) = BitVec.ofNat 32 (Sj.amount / 2 ^ (32 * w))) ∧
      word (ρ (openO P j).res.maxhW) = BitVec.ofNat 32 Sj.maxHeight ∧
      (∃ v : ℕ → F, SetPass.EncSha v 0 Sj.sha ∧ wordsOf ρ (openO P j).res.shaDg = shaVec v) := by
    intro j hj
    obtain ⟨rc, hrc, hhc⟩ := chainOuts_getD_holds hj ⟨[], ⟨id, [], [], []⟩, 0⟩ hSe
    change setO P j = _ at hrc
    obtain ⟨ro, hro, hho⟩ := chainOuts_getD_holds hj ⟨[], ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩, 0⟩ hO
    change openO P j = setOpen ro (setO P j).res (chalO P (epochOf gen j)).res (eState ms gen j) P.C.res at hro
    set I : SOIn := ⟨ro, (setO P j).res, (chalO P (epochOf gen j)).res, eState ms gen j, P.C.res⟩ with hI
    have OH := setOpen_holds I hho
    have hp : ∀ k < 48, IsBase (ρ (I.c.pubs k)) := by
      intro k hk; show IsBase (ρ ((setO P j).res.pubs k)); rw [hrc]; exact setChild_base hhc k hk
    have hsum := setOpen_summ I OH hCo (hchl _ (hepo j hj)) hb2 hsh hp
    -- the hook
    obtain ⟨sroot, hsroot, hsmem⟩ := setChild_hook rc (JEXT + SEXT * j) (j + 1)
    have hmem : Op.hook (j + 1) (sroot ++ (setChild rc (JEXT + SEXT * j) (j + 1)).res.digest)
        (setChild rc (JEXT + SEXT * j) (j + 1)).res.chash ∈ (chainSeal ms gen).ops :=
      mem_seal_sets (chainOuts_getD_mem hj ⟨[], ⟨id, [], [], []⟩, 0⟩ (by rw [show (chainOuts _ _ _).getD j _ = _ from hrc]; exact hsmem))
    have sC := T.recVerifies ρ _ _ _ (hg _ _ _ hmem)
    rw [List.drop_left' hsroot, setChild_digest hhc] at sC
    obtain ⟨ehash, ekey⟩ := eSets j hj
    rw [hrc] at ehash ekey
    rw [ehash, ekey] at sC
    have hpb : pbAt ρ P gen j = pbOf ρ I.chl ((List.range 4).map (I.n + 218 + ·)) := by
      simp only [pbAt, hro]; rfl
    have hpf : pfAt ρ P gen j = pfOf ρ I.chl I.n := by simp only [pfAt, hro]; rfl
    have hRR : RAt ρ P j = fun k => (ρ (I.c.pubs (32 + k))).a := rfl
    have hv : SetTree.sd ((ts j).key X.leafS X.nodeS) (fun k => (ρ (rc + k)).a) =
        SetTree.sd ((ts j).key X.leafS X.nodeS) (SetPass.summ2 (pbAt ρ P gen j) (pfAt ρ P gen j) (RAt ρ P j)) := by
      rw [hpb, hpf, hRR]
      simp only [SetTree.sd, SetTree.vals32]
      congr 2
      apply List.map_congr_left
      intro k hk
      have hk' : k < 48 := by simpa [SetTree.NS] using hk
      have := hsum k hk'
      have e1 : I.c.pubs k = rc + k := by show (setO P j).res.pubs k = _; rw [hrc]; rfl
      rw [e1] at this
      rw [this]
    rw [hv] at sC
    have hbeg := setOpen_begin I OH hCo
    rw [← hpb] at hbeg
    rcases SetPass.set_root_soundW TS hlS hnS (ts j) _ _ _ _ hbeg sC with ⟨segs, hout, -, -, hfit, hroots, hR⟩ | cc
    swap
    · exact absurd (cc.mono fun x hx => sub x (List.mem_append_right _
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, hx⟩))) col
    set Sj := ((segs.map Prod.snd).flatten).foldl (Spec.SetFile.step [SetPass.Rec.frac (pbAt ρ P gen j)])
      (Spec.SetFile.begin 1 (ρ (oCnt I).res).a.val) with hSj
    have hcntE : (ρ (openO P j).res.n).a.val = (ρ (oCnt I).res).a.val := by rw [hro]; rfl
    rw [hpf] at hout
    obtain ⟨-, -, hc30⟩ := setOpen_count I OH hCo
    refine ⟨Sj, (SetPass.segOf X.leafS X.nodeS X.nwS X.lwS (ts j) _).root, ⟨by rw [hcntE]; exact hc30, segs, _, by rw [hcntE],
      hfit, hroots, rfl⟩, by rw [hpf]; exact hout, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcntE]; exact setOpen_i I OH hout
    · rw [hro]
      exact wordsOf_eq (by have := (openO_lengths ms gen hj).2.2.2; rwa [hro] at this) (setOpen_finish I OH hCo hout.b2)
    · rw [hro]
      exact setOpen_mroot I OH hCo hp hR
    · rw [hcntE, hro]; exact setOpen_cntW I OH
    · rw [hro]; exact setOpen_amtW I OH hCo hout
    · rw [hro]; exact setOpen_maxhW I OH hout
    · obtain ⟨hd, he⟩ := setOpen_shaDg I OH hout
      exact ⟨_, he, by rw [hro]; exact hd⟩
  have : Nonempty (Spec.SetFile.St Spec.QM31.QM) := ⟨Spec.SetFile.begin 1 0⟩
  have : Nonempty Spec.Sha256.State := ⟨Spec.Sha256.IV⟩
  choose! Sf rf hSf using hset
  -- per epoch
  have l8 : ∀ l : List ℕ, l.length = 8 → (wordsOf ρ l).length = 8 := fun l h => by rw [wordsOf_length, h]
  have hep : ∀ i < n, ∃ x : ℕ → F, EpochOk ts gen i (epAt c i) (ms.getD i 0) x
      (ρ (openO P (endIdx gen i)).res.n).a.val (ρ (openO P (startIdx gen i)).res.n).a.val
      (Sf (endIdx gen i)) (Sf (startIdx gen i)) (rf (endIdx gen i)) (rf (startIdx gen i)) := by
    intro i hi
    obtain ⟨rr, hrr, hhr⟩ := hrests i hi
    obtain ⟨rcl, hrcl, hhcl⟩ := hchals i hi
    obtain ⟨rbase, rhash⟩ := restOpen_sound hhr (hms i hi)
    obtain ⟨rro, hrro, -⟩ := hroots i hi
    obtain ⟨ef, ep, el, er⟩ := hopen i hi
    refine ⟨fun j => (ρ (rr + j)).a, ?_⟩
    have hch : (restO P i).res.ch = (List.range 12).map (rr + 5 + ·) := by rw [hrr]; rfl
    rw [hch] at hrcl hhcl
    have hcp := chal_pub hhcl hCo (fun k hk => by have := rbase (5 + k) (by omega); rwa [← Nat.add_assoc] at this)
    -- the fractions
    have hfr : ∀ j < S, epochOf gen j = i →
        SetPass.Rec.frac (pbAt ρ P gen j) = fracOf (fun j => (ρ (rr + j)).a) := by
      intro j hj he
      apply SetPass.frac_congr
      intro t ht
      simp only [pbAt, he]
      rw [pbOf_ch ht, hrcl]
      exact hcp t ht
    have hjE := endIdx_lt (gen := gen) hi
    obtain ⟨pE, oE, iE, fE, -, -, -, -, -⟩ := hSf _ hjE
    rw [hfr _ hjE (epochOf_end gen i)] at pE
    have hck := checks_epoch (J := P.J.res) (roots := P.roots.map (·.res)) (rests := P.rests.map (·.res))
      (opens := P.opens.map (·.res)) (accs := P.accs.map (·.res)) (C := P.C.res) hK hCo hi
    dsimp only at hck
    simp only [openAt_eq, rootAt_eq, restAt_eq] at hck
    obtain ⟨cfin, cstart, cgen⟩ := hck
    -- `rest`
    have hrest : (epAt c i).o.rest =
        H ((List.range (17 + 16 * ms.getD i 0)).map fun j => BitVec.ofNat 32 ((fun j => (ρ (rr + j)).a) j).val) := by
      rw [← er]
      have e1 : (rootO P i).res.rest.length = 8 := by rw [hrro]; exact (rootOpen_lengths _ _ _).2.2.2.1
      rw [wordsOf_eq e1 rhash, H]
      simp
    -- the end set finishes to `fin`
    have hfinE : (epAt c i).o.fin = b2W (Sf (endIdx gen i)).b2 := by
      rw [← ef, ← fE]
      have e1 : (rootO P i).res.fin.length = 8 := by rw [hrro]; exact (rootOpen_lengths _ _ _).2.1
      exact (EpochJoin.wordsOf_ext (openO_lengths ms gen hjE).2.2.2 e1 cfin).symm
    -- the sums as public values
    have hsumE : ∀ j < S, ∀ k < 4, pfAt ρ P gen j (157 + k) = (ρ ((openO P j).res.st.sum.getD k 0)).a := by
      intro j hj k hk
      obtain ⟨ro, hro⟩ := openO_get ms gen hj
      rw [← hP] at hro
      simp only [pfAt, hro]
      rw [pfOf_sum hk]
      show (ρ (ro + 38 + k)).a = (ρ (((List.range 4).map (ro + 38 + ·)).getD k 0)).a
      rw [getD_map_range hk]
    have hmaxB : ∀ j < S, pfAt ρ P gen j 161 = (ρ (openO P j).res.st.maxh).a := by
      intro j hj
      obtain ⟨ro, hro⟩ := openO_get ms gen hj
      rw [← hP] at hro
      simp only [pfAt, hro]; rw [pfOf_maxh]; rfl
    have hsE := oE.sums
    simp only [SetPass.PUB_SUM_OUT] at hsE
    refine ⟨hrest, pE, hfinE, iE, fun hs => ?_, fun hs => ?_⟩
    · -- with a start set
      have hjB := startIdx_lt (gen := gen) hi
      obtain ⟨pB, oB, iB, fB, -, -, -, -, -⟩ := hSf _ hjB
      rw [hfr _ hjB (epochOf_start hs)] at pB
      obtain ⟨cprev, cbal, crng, cmax⟩ := cstart hs
      have hsB := oB.sums
      simp only [SetPass.PUB_SUM_OUT] at hsB
      refine ⟨pB, ?_, iB, ⟨_, hsB, ?_⟩, ?_, ?_⟩
      · rw [← ep hs, ← fB]
        have e1 : (rootO P i).res.prev.length = 8 := by rw [hrro]; exact (rootOpen_lengths _ _ _).2.2.1
        exact (EpochJoin.wordsOf_ext (openO_lengths ms gen hjB).2.2.2 e1 cprev).symm
      · rw [hsE]
        congr 1
        rw [pQ_eq, pQ_eq, pQ_eq, ← Spec.QM31.toQ_add]
        congr 1
        have hT : ∀ k < 4, (restO P i).res.s.getD k 0 = rr + k := fun k hk => by rw [hrr]; exact getD_map_range hk
        have g := fun k (hk : k < 4) => by
          have := congrArg Q.a (cbal k hk)
          rw [add_a, hT k hk, ← hsumE _ hjE k hk, ← hsumE _ hjB k hk] at this
          exact this
        ext
        · simpa using g 0 (by norm_num)
        · simpa using g 1 (by norm_num)
        · simpa using g 2 (by norm_num)
        · simpa using g 3 (by norm_num)
      · obtain ⟨-, hv⟩ := crng
        rw [add_a, add_a] at hv
        have hnin : (restO P i).res.nin = rr + 4 := by rw [hrr]; rfl
        rw [hnin, ← ZMod.natCast_zmod_val (ρ (openO P (endIdx gen i)).res.n).a,
          ← ZMod.natCast_zmod_val (ρ (openO P (startIdx gen i)).res.n).a] at hv
        exact hv
      · obtain ⟨-, hv⟩ := cmax
        rw [sub_a, sub_a] at hv
        have hlo := valid_lohi hValid (i := i) (by omega)
        have elo : (ρ (rootO P i).res.lo).a.val = (epAt c i).o.lo := by
          rw [hrro] at el ⊢
          exact ofNat_inj32 (lt_trans (ZMod.val_lt _) (by unfold StarkedAir.P; norm_num)) (by omega) el
        have emax : (ρ (openO P (startIdx gen i)).res.st.maxh).a.val = (Sf (startIdx gen i)).maxHeight := by
          rw [← hmaxB _ hjB]; exact oB.maxh
        have hlt := lt_of_sub_one (a := (ρ (rootO P i).res.lo).a) (b := (ρ (openO P (startIdx gen i)).res.st.maxh).a)
          (by rw [elo]; omega) (by rw [emax]; exact oB.maxh_lt) (by simpa [lit] using hv)
        rw [elo, emax] at hlt
        exact hlt
    · -- from genesis
      obtain ⟨cbal, crng⟩ := cgen hs
      refine ⟨?_, ?_⟩
      · rw [hsE]
        congr 1
        rw [pQ_eq, pQ_eq]
        congr 1
        have hT : ∀ k < 4, (restO P i).res.s.getD k 0 = rr + k := fun k hk => by rw [hrr]; exact getD_map_range hk
        have g := fun k (hk : k < 4) => by
          have := congrArg Q.a (cbal k hk)
          rw [hT k hk, ← hsumE _ hjE k hk] at this
          exact this.symm
        ext
        · simpa using g 0 (by norm_num)
        · simpa using g 1 (by norm_num)
        · simpa using g 2 (by norm_num)
        · simpa using g 3 (by norm_num)
      · obtain ⟨-, hv⟩ := crng
        rw [add_a] at hv
        have hnin : (restO P i).res.nin = rr + 4 := by rw [hrr]; rfl
        rw [hnin, ← ZMod.natCast_zmod_val (ρ (openO P (endIdx gen i)).res.n).a] at hv
        exact hv
  choose! x hx using hep
  refine ⟨x, fun i => (ρ (openO P (endIdx gen i)).res.n).a.val, fun i => (ρ (openO P (startIdx gen i)).res.n).a.val,
    fun i => Sf (endIdx gen i), fun i => Sf (startIdx gen i), fun i => rf (endIdx gen i), fun i => rf (startIdx gen i),
    hValid, hx, ?_, ?_, ?_⟩
  · -- the end facts
    have hjl : endIdx gen (n - 1) < S := endIdx_lt (by omega)
    obtain ⟨-, -, -, -, hmr, hcw, ham, hmx, v, hv, hsd⟩ := hSf _ hjl
    obtain ⟨la, lm, -, -⟩ := openO_lengths ms gen hjl
    have hSl : S - 1 = endIdx gen (n - 1) := last_end (by omega)
    rw [hSl] at eW
    refine ⟨v, hv, ?_⟩
    rw [← eW]
    have e1 : ∀ (a : ℕ) (b : List ℕ) (m : ℕ) (d e f : List ℕ),
        wordsOf ρ ([a] ++ b ++ [m] ++ d ++ e ++ f) = [word (ρ a)] ++ wordsOf ρ b ++ [word (ρ m)] ++ wordsOf ρ d ++
          wordsOf ρ e ++ wordsOf ρ f := fun _ _ _ _ _ _ => by simp [wordsOf]
    rw [e1, hcw, wordsOf_eqN la ham, hmx, wordsOf_eqN lm hmr, hsd]
  · -- from genesis: zero words
    intro hgen'
    have z : word (ρ P.C.res.zero) = 0 := by rw [hCo.zero]; rfl
    simp only [shaStartRegs, hgen', if_true, wordsOf, List.map_replicate, Function.comp_apply, z]
  · -- otherwise: the first start set's SHA-256 digest
    intro hgen'
    have h0 : (0 : ℕ) < S := by omega
    obtain ⟨-, -, -, -, -, -, -, -, v, hv, hsd⟩ := hSf 0 h0
    have hs0 : startIdx gen 0 = 0 := by simp [startIdx, hgen']
    refine ⟨v, by simp only [hs0]; exact hv, ?_⟩
    simp only [shaStartRegs, hgen', Bool.false_eq_true, if_false]
    exact hsd


end

end StarkedAir.Circuit.ChainSeal
