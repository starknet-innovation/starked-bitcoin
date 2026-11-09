/-
**SEAL-T's paths, composed with the header chain (SEAL-T-LEAN, D-052).** From the seal's circuit
facts (`THolds`), the header root child's public inputs `p` being proven with `T` the canonical MMR
root over the chain's block hashes (`HeaderTree.PubValidM p`, which the header tree's trust record and
the verifier's aligned plan give: `RecCR.htree_soundWS`, `PubValidS.toM`) and what the verifier recomputes for each path
(`PathPubsOk`: `chain_seal.pathPubs`, and the child positions' alignment and bounds it checks natively):

- the header chain is a valid chain of `H` headers from genesis (`chain_from_genesis_M`), and
  when `H` is the verifier's header count `nH`:
- its block 0's hash is Bitcoin's genesis hash, and
- every epoch child's block-hash root (the packed words of its limbs in `rest`'s preimage) is the
  root of the perfect tree over the block hashes `pos … pos + 2^k − 1` of that chain
  (`BlockTree.rootFrom`, the block trees' own root),

or two of the node-hash inputs the paths compare collide (`tPairs`, named from the seal's witness and
the chain's leaves).
-/
import StarkedAir.Circuit.ChainSealTSound
import StarkedAir.Spec.MmrSub
import StarkedAir.Gadgets.RootChecks
import StarkedAir.Circuit.HeaderShape

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q Spec.Blake2s
open StarkedAir.Spec.HeaderTree (HTree hnode stWord toState)
open StarkedAir.Spec.Mmr (Step pathRoot bal mmr mmrSides CollidesIn subPairs pathPairsRev)
open StarkedAir.Circuit.EpochRoot (chainOuts chainOuts_length lastNext)
open StarkedAir.HeaderTree (PubValidT pubT limbsOf)

variable {ρ : ℕ → Q}

/-! ### Lists over ranges, and the block trees' root as a perfect tree -/

theorem map_range_take' (g : ℕ → Spec.Sha256.State) {a b : ℕ} (h : a ≤ b) :
    ((List.range b).map g).take a = (List.range a).map g := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2; simp

theorem map_range_drop (g : ℕ → Spec.Sha256.State) (N a : ℕ) :
    ((List.range N).map g).drop a = (List.range (N - a)).map (fun i => g (a + i)) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2; simp

theorem map_range_slice (g : ℕ → Spec.Sha256.State) {N pos m : ℕ} (h : pos + m ≤ N) :
    (((List.range N).map g).drop pos).take m = (List.range m).map (fun i => g (pos + i)) := by
  rw [map_range_drop, map_range_take' _ (by omega)]

/-- **`rootFrom` is the perfect tree's root** over `f s, …, f (s + 2^ℓ − 1)`. -/
theorem rootFrom_bal (f : ℕ → Spec.Sha256.State) : ∀ ℓ s,
    (bal ℓ ((List.range (2 ^ ℓ)).map fun i => f (s + i))).root = BlockTree.rootFrom f ℓ s
  | 0, s => by simp [bal, BlockTree.rootFrom, Spec.HeaderTree.HTree.root]
  | ℓ + 1, s => by
    simp only [bal, Spec.HeaderTree.HTree.root, BlockTree.rootFrom]
    rw [map_range_take' _ (by rw [pow_succ]; omega), map_range_drop,
      show 2 ^ (ℓ + 1) - 2 ^ ℓ = 2 ^ ℓ by rw [pow_succ]; omega, rootFrom_bal f ℓ s, ← rootFrom_bal f ℓ (s + 2 ^ ℓ)]
    simp only [Nat.add_assoc]

/-! ### Bits, small casts, words of limbs -/

theorem bits_lt (b : ℕ → Bool) : ∀ m, (∑ j ∈ Finset.range m, if b j then 2 ^ j else 0) < 2 ^ m
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, pow_succ]
    have := bits_lt b m
    split <;> omega

/-- Binary representations are unique. -/
theorem bits_inj (b c : ℕ → Bool) : ∀ m, (∑ j ∈ Finset.range m, if b j then 2 ^ j else 0) =
    (∑ j ∈ Finset.range m, if c j then 2 ^ j else 0) → ∀ j < m, b j = c j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, he, j, hj => by
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at he
    have hb := bits_lt b m
    have hc := bits_lt c m
    have top : b m = c m := by
      cases hbm : b m <;> cases hcm : c m <;> simp [hbm, hcm] at he <;> first | rfl | omega
    have he' : (∑ j ∈ Finset.range m, if b j then 2 ^ j else 0) = (∑ j ∈ Finset.range m, if c j then 2 ^ j else 0) := by
      rw [top] at he; omega
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact bits_inj b c m he' j hj
    · exact top

theorem cast_inj_small {a b : ℕ} (ha : a < 2 ^ 30) (hb : b < 2 ^ 30) (h : (a : F) = (b : F)) : a = b := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by unfold P; omega), ZMod.val_natCast_of_lt (by unfold P; omega)] at this

theorem word_halves (x : Word) :
    word ⟨((Sha256.half16 x 0 : ℕ) : F), ((Sha256.half16 x 1 : ℕ) : F), 0, 0⟩ = x := by
  unfold word
  simp only
  rw [val_cast_lt (Sha256.half16_lt x 0), val_cast_lt (Sha256.half16_lt x 1), ← Sha256.half16_split]
  apply BitVec.eq_of_toNat_eq
  simp

/-! ### `T` is the header tree's root -/

/-- The header root child's public inputs. -/
def hpub (ρ : ℕ → Q) (ms : List ℕ) (gen : Bool) (D : ℕ) : ℕ → F := fun k => (ρ ((partsT ms gen D).hc.res.pubs k)).a

/-- `T` (the packed limbs 108–123) is the state `R` whose limbs the public inputs carry. -/
theorem tState_eq {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) {R : Spec.Sha256.State}
    (hT : pubT (hpub ρ ms gen D) = limbsOf R) : tState ρ ms gen D = R := by
  apply state_ext
  intro w hw
  rw [tState, stWord_regState _ hw, sealT_T h w hw]
  have g : ∀ j < 16, hpub ρ ms gen D (108 + j) = ((Sha256.half16 (stWord R (j / 2)) (j % 2) : ℕ) : F) := by
    intro j hj
    have := congrArg (fun l => l.getD j 0) hT
    simpa [pubT, limbsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj] using this
  have g0 := g (2 * w) (by omega)
  have g1 := g (2 * w + 1) (by omega)
  rw [show 2 * w / 2 = w by omega, show 2 * w % 2 = 0 by omega] at g0
  rw [show (2 * w + 1) / 2 = w by omega, show (2 * w + 1) % 2 = 1 by omega] at g1
  simp only [hpub] at g0 g1
  rw [g0, show 108 + 2 * w + 1 = 108 + (2 * w + 1) by omega, g1]
  exact word_halves _

/-! ### A path's steps against the verifier's sides -/

/-- A path's first `L` steps as the circuit holds them: the guessed siblings and the side bits. -/
noncomputable def stepsOf (ρ : ℕ → Q) (n e D L : ℕ) : List Step := (List.range L).map fun s =>
  ⟨regState ρ ((((List.range D).map fun s => guessHash (n + 40 * s) (e + 8 * s)).getD s ⟨[], [], 0⟩).res),
   decide ((ρ (n + 40 * D + 4 * s)).a = 1)⟩

/-- The verifier's side words (`chain_seal.packSides`): bits `0..29` and `30..`. -/
def packLo (D : ℕ) (ss : List Bool) : ℕ := ∑ j ∈ Finset.range (min D 30), if ss.getD j false then 2 ^ j else 0
def packHi (D : ℕ) (ss : List Bool) : ℕ := ∑ j ∈ Finset.range (D - 30), if ss.getD (30 + j) false then 2 ^ j else 0

/-- **A path checked against the verifier's sides**: a path whose length and side words equal the
verifier's for sides `ss` has steps with exactly those sides, and `T` is its root. -/
theorem pathOk_steps {n e D : ℕ} {leaf Tst : Spec.Sha256.State} {pr : PathRegs} (hp : PathOk ρ n e D leaf Tst pr)
    (hD : D ≤ 60) (ss : List Bool) (hss : ss.length ≤ D) (hlen : (ρ pr.len).a = (ss.length : F))
    (hlo : (ρ pr.sLo).a = (packLo D ss : F)) (hhi : (ρ pr.sHi).a = (packHi D ss : F)) :
    (stepsOf ρ n e D ss.length).map Step.left = ss ∧ Tst = pathRoot leaf (stepsOf ρ n e D ss.length) := by
  obtain ⟨L, hL, hLx, hroot, hlo', hhi'⟩ := hp
  have hLe : L = ss.length := cast_inj_small (by omega) (by omega) (hLx.symm.trans hlen)
  subst hLe
  have p30 : ∀ m ≤ 30, 2 ^ m ≤ 2 ^ 30 := fun m hm => Nat.pow_le_pow_right (by norm_num) hm
  have blo := bits_inj (fun s => decide ((ρ (n + 40 * D + 4 * s)).a = 1)) (fun j => ss.getD j false) (min D 30)
    (cast_inj_small (lt_of_lt_of_le (bits_lt _ _) (p30 _ (min_le_right _ _)))
      (lt_of_lt_of_le (bits_lt _ _) (p30 _ (min_le_right _ _))) (hlo'.symm.trans hlo))
  have bhi := bits_inj (fun j => decide ((ρ (n + 40 * D + 4 * (30 + j))).a = 1)) (fun j => ss.getD (30 + j) false) (D - 30)
    (cast_inj_small (lt_of_lt_of_le (bits_lt _ _) (p30 _ (by omega)))
      (lt_of_lt_of_le (bits_lt _ _) (p30 _ (by omega))) (hhi'.symm.trans hhi))
  have hbit : ∀ s < D, decide ((ρ (n + 40 * D + 4 * s)).a = 1) = ss.getD s false := by
    intro s hs
    by_cases h30 : s < 30
    · exact blo s (by omega)
    · have := bhi (s - 30) (by omega)
      rwa [show 30 + (s - 30) = s by omega] at this
  refine ⟨?_, hroot hss⟩
  apply List.ext_getElem (by simp [stepsOf])
  intro i h1 h2
  simp only [stepsOf, List.map_map, List.getElem_map, List.getElem_range, Function.comp]
  rw [← List.getD_eq_getElem ss false h2]
  exact hbit i (by omega)

/-! ### The paths' registers, concretely -/

theorem chainOuts_getElem_last {α : Type} (f : ℕ → ℕ → Out α) (n : ℕ) :
    ∀ k i (hi : i < k), (chainOuts f n k)[i]'(by rw [chainOuts_length]; exact hi) = f i (lastNext (chainOuts f n i) n)
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    by_cases hik : i < k
    · simp only [chainOuts]
      rw [List.getElem_append_left (by rw [chainOuts_length]; exact hik)]
      exact chainOuts_getElem_last f n k i hik
    · have e : i = k := by omega
      subst e
      simp only [chainOuts]
      rw [List.getElem_append_right (by rw [chainOuts_length])]
      simp [chainOuts_length, lastNext]

/-- The function `cpathsT` chains. -/
def cpathF (ms : List ℕ) (gen : Bool) (D : ℕ) : ℕ → ℕ → Out PathRegs := fun p r =>
  let ic := (childIdx ms).getD p (0, 0)
  let lw := packN r (childLimbs (parts ms gen) ic.1 ic.2) 8 (parts ms gen).C.res
  let pa := pathOps lw.next (eState ms gen (nSets ms.length gen) + N_PUB + 16 + pathExt D * (p + 1)) lw.res D
    (parts ms gen).C.res (partsT ms gen D).pw
  (⟨lw.ops ++ pa.ops, pa.res, pa.next⟩ : Out PathRegs)

theorem cpathsT_eq (ms : List ℕ) (gen : Bool) (D : ℕ) :
    cpathsT ms gen D = chainOuts (cpathF ms gen D) (gpathT ms gen D).next (childIdx ms).length := rfl

/-- Child path `p`'s first register, its leaf (the packed limbs), its registers and external base. -/
def cReg (ms : List ℕ) (gen : Bool) (D p : ℕ) : ℕ :=
  lastNext (chainOuts (cpathF ms gen D) (gpathT ms gen D).next p) (gpathT ms gen D).next

def cLeaf (ms : List ℕ) (gen : Bool) (D p : ℕ) : Out (List ℕ) :=
  packN (cReg ms gen D p) (childLimbs (parts ms gen) ((childIdx ms).getD p (0, 0)).1 ((childIdx ms).getD p (0, 0)).2) 8
    (parts ms gen).C.res

def cN (ms : List ℕ) (gen : Bool) (D p : ℕ) : ℕ := (cLeaf ms gen D p).next
def cE (ms : List ℕ) (gen : Bool) (D p : ℕ) : ℕ := eState ms gen (nSets ms.length gen) + N_PUB + 16 + pathExt D * (p + 1)
def gN (ms : List ℕ) (gen : Bool) (D : ℕ) : ℕ := (partsT ms gen D).work.next + 8
def gE (ms : List ℕ) (gen : Bool) (D : ℕ) : ℕ := eState ms gen (nSets ms.length gen) + N_PUB + 16

/-- The empty path out (the default of `getD`). -/
def noPath : Out PathRegs := ⟨[], ⟨[], 0, 0, 0⟩, 0⟩

theorem cpath_getD {ms : List ℕ} {gen : Bool} {D p : ℕ} (hp : p < (childIdx ms).length) :
    (cpathsT ms gen D).getD p noPath = cpathF ms gen D p (cReg ms gen D p) := by
  rw [List.getD_eq_getElem _ _ (by rw [cpathsT, chainOuts_length]; exact hp)]
  exact chainOuts_getElem_last _ _ _ p hp

/-- **The genesis path**, with its registers. -/
theorem sealT_gpathC {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) (hD : D ≤ 60) :
    PathOk ρ (gN ms gen D) (gE ms gen D) D genesisState (tState ρ ms gen D) (gpathT ms gen D).res := by
  have hp : Holds ρ (gpathT ms gen D).ops := fun o ho => h.paths o (by
    rw [partsT_paths, List.flatMap_cons]; exact List.mem_append_left _ ho)
  have hmem : gpathT ms gen D ∈ (partsT ms gen D).paths := by rw [partsT_paths]; exact List.mem_cons_self
  have hleaf : regState ρ ((List.range 8).map ((partsT ms gen D).work.next + ·)) = genesisState := by
    apply state_ext
    intro w hw
    rw [stWord_regState _ hw, getD_map_range hw]
    have c : (constU32 ((partsT ms gen D).work.next + w) (genesisHash.getD w 0)).holds ρ :=
      h.gleaf _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
    rw [const_word c (genesisHash_lt w hw)]
    unfold genesisState toState; interval_cases w <;> rfl
  have := pathOk_of (Tst := tState ρ ms gen D) hp (sealT_C h) (sealT_pw h) hD (regState_ends h hmem)
  rw [hleaf] at this
  exact this

/-- **Child path `p`**, with its registers. -/
theorem sealT_cpathC {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) (hD : D ≤ 60) {p : ℕ}
    (hp : p < (childIdx ms).length) :
    PathOk ρ (cN ms gen D p) (cE ms gen D p) D (regState ρ (cLeaf ms gen D p).res) (tState ρ ms gen D)
      ((cpathsT ms gen D).getD p noPath).res := by
  have hcall : Holds ρ ((cpathsT ms gen D).flatMap (·.ops)) := fun o ho => h.paths o (by
    rw [partsT_paths, List.flatMap_cons]; exact List.mem_append_right _ ho)
  have hmem : (cpathsT ms gen D).getD p noPath ∈ (partsT ms gen D).paths := by
    rw [partsT_paths, List.getD_eq_getElem _ _ (by rw [cpathsT, chainOuts_length]; exact hp)]
    exact List.mem_cons_of_mem _ (List.getElem_mem _)
  have hT := regState_ends h hmem
  have hin : (cpathsT ms gen D).getD p noPath ∈ cpathsT ms gen D := by
    rw [List.getD_eq_getElem _ _ (by rw [cpathsT, chainOuts_length]; exact hp)]; exact List.getElem_mem _
  have hops : Holds ρ ((cpathsT ms gen D).getD p noPath).ops := fun o ho => hcall o (List.mem_flatMap.mpr ⟨_, hin, ho⟩)
  rw [cpath_getD hp] at hT hops ⊢
  simp only [cpathF, holds_append] at hT hops ⊢
  exact pathOk_of hops.2 (sealT_C h) (sealT_pw h) hD hT

/-- Child path `p`'s leaf (the packed limbs) holds. -/
theorem cLeaf_holds {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) {p : ℕ} (hp : p < (childIdx ms).length) :
    Holds ρ (cLeaf ms gen D p).ops := by
  have hcall : Holds ρ ((cpathsT ms gen D).flatMap (·.ops)) := fun o ho => h.paths o (by
    rw [partsT_paths, List.flatMap_cons]; exact List.mem_append_right _ ho)
  have hin : (cpathsT ms gen D).getD p noPath ∈ cpathsT ms gen D := by
    rw [List.getD_eq_getElem _ _ (by rw [cpathsT, chainOuts_length]; exact hp)]; exact List.getElem_mem _
  have hops : Holds ρ ((cpathsT ms gen D).getD p noPath).ops := fun o ho => hcall o (List.mem_flatMap.mpr ⟨_, hin, ho⟩)
  rw [cpath_getD hp] at hops
  simp only [cpathF, holds_append] at hops
  exact hops.1

/-! ### The composition -/

/-- The verifier's sides (`chain_seal.pathPubs`): genesis, leaf 0's among `nH`; a child at
`(pos, k)`, leaf `pos`'s with the first `k` dropped. -/
def gSides (nH : ℕ) : List Bool := mmrSides nH 0
def cSides (nH pos k : ℕ) : List Bool := (mmrSides nH pos).drop k

/-- **What the verifier fixes about the paths**: the length and side words in the output message
(the seal's digest is the verifier's), and the native checks on each child's position `pos q` and
level `lvl q` (`epoch_root.openHead`: aligned sizes, `BeyondChain`; `pathPubs`: the dropped sides are
`false`). -/
structure PathPubsOk (ρ : ℕ → Q) (ms : List ℕ) (gen : Bool) (D nH : ℕ) (pos lvl : ℕ → ℕ) : Prop where
  n0 : 0 < nH
  gD : (gSides nH).length ≤ D
  glen : (ρ (gpathT ms gen D).res.len).a = ((gSides nH).length : F)
  glo : (ρ (gpathT ms gen D).res.sLo).a = (packLo D (gSides nH) : F)
  ghi : (ρ (gpathT ms gen D).res.sHi).a = (packHi D (gSides nH) : F)
  cD : ∀ q < (childIdx ms).length, (cSides nH (pos q) (lvl q)).length ≤ D
  clen : ∀ q < (childIdx ms).length,
    (ρ ((cpathsT ms gen D).getD q noPath).res.len).a = ((cSides nH (pos q) (lvl q)).length : F)
  clo : ∀ q < (childIdx ms).length,
    (ρ ((cpathsT ms gen D).getD q noPath).res.sLo).a = (packLo D (cSides nH (pos q) (lvl q)) : F)
  chi : ∀ q < (childIdx ms).length,
    (ρ ((cpathsT ms gen D).getD q noPath).res.sHi).a = (packHi D (cSides nH (pos q) (lvl q)) : F)
  cfalse : ∀ q < (childIdx ms).length, (mmrSides nH (pos q)).take (lvl q) = List.replicate (lvl q) false
  calign : ∀ q < (childIdx ms).length, 2 ^ lvl q ∣ pos q
  cbound : ∀ q < (childIdx ms).length, pos q + 2 ^ lvl q ≤ nH

/-- The node-hash inputs the paths compare, against the MMR over leaves `L`. -/
noncomputable def tPairs (ρ : ℕ → Q) (ms : List ℕ) (gen : Bool) (D nH : ℕ) (pos lvl : ℕ → ℕ)
    (L : List Spec.Sha256.State) : List ((Spec.Sha256.State × Spec.Sha256.State) × (Spec.Sha256.State × Spec.Sha256.State)) :=
  pathPairsRev (mmr L) 0 genesisState (stepsOf ρ (gN ms gen D) (gE ms gen D) D (gSides nH).length).reverse ++
    (List.range (childIdx ms).length).flatMap fun q =>
      subPairs (mmr L) (regState ρ (cLeaf ms gen D q).res)
        (stepsOf ρ (cN ms gen D q) (cE ms gen D q) D (cSides nH (pos q) (lvl q)).length).reverse

/-- **SEAL-T's header facts.** The seal's circuit facts, the header root's public inputs proven and
their tree the MMR, and the verifier's path data give: a valid header chain of `H` headers from
genesis whose block hashes are `T`'s leaves; and when `H = nH`, block 0's hash is Bitcoin's genesis
hash and every epoch child's block-hash root (its packed limbs) is the perfect tree's root over block
hashes `pos q … pos q + 2^(lvl q) − 1`; or two of `tPairs` collide. -/
theorem sealT_headerC {ms : List ℕ} {gen : Bool} {D nH : ℕ} {pos lvl : ℕ → ℕ} (h : THolds ms gen D ρ) (hD : D ≤ 60)
    (hv : HeaderTree.PubValidM (hpub ρ ms gen D)) (pp : PathPubsOk ρ ms gen D nH pos lvl) :
    ∃ H hs, Spec.Bitcoin.SegmentValid H hs
      ⟨HeaderChain.pubState (hpub ρ ms gen D) 0, 0, HeaderChain.leN (HeaderChain.pubWord (hpub ρ ms gen D) 34),
        HeaderChain.leN (HeaderChain.pubWord (hpub ρ ms gen D) 44), HeaderChain.leN (HeaderChain.pubWord (hpub ρ ms gen D) 36), [], 0⟩
      (HeaderChain.decodeOut (hpub ρ ms gen D)) ∧
      HeaderChain.pubState (hpub ρ ms gen D) 0 = HeaderChain.pubState (fun _ => 0) 0 ∧
      (H = nH →
        (Spec.Bitcoin.sha256d (hs 0) = genesisState ∧
          ∀ q < (childIdx ms).length,
            regState ρ (cLeaf ms gen D q).res = BlockTree.rootFrom (fun j => Spec.Bitcoin.sha256d (hs j)) (lvl q) (pos q)) ∨
        CollidesIn (tPairs ρ ms gen D nH pos lvl ((List.range H).map fun j => Spec.Bitcoin.sha256d (hs j)))) := by
  obtain ⟨H, hs, hseg, hg0, -, hmr0⟩ := HeaderTree.chain_from_genesis_M hv (sealT_genesis h)
  refine ⟨H, hs, hseg, hg0, fun hH => ?_⟩
  set L := (List.range H).map fun j => Spec.Bitcoin.sha256d (hs j) with hL
  have hmr : pubT (hpub ρ ms gen D) = limbsOf (mmr L).root := hmr0
  have hTs : tState ρ ms gen D = (mmr L).root := tState_eq h hmr
  have hLl : L.length = nH := by rw [hL, List.length_map, List.length_range, hH]
  have hLne : L ≠ [] := by intro e; rw [e] at hLl; simp at hLl; exact absurd hLl.symm (Nat.ne_of_gt pp.n0)
  by_cases col : CollidesIn (tPairs ρ ms gen D nH pos lvl L)
  · exact Or.inr col
  left
  constructor
  · -- genesis
    obtain ⟨hsd, hrt⟩ := pathOk_steps (sealT_gpathC h hD) hD (gSides nH) pp.gD pp.glen pp.glo pp.ghi
    have hs' : (stepsOf ρ (gN ms gen D) (gE ms gen D) D (gSides nH).length).map Step.left = (mmr L).sides 0 := by
      rw [hsd, gSides, Spec.Mmr.mmr_sides_eq, hLl]
    rcases Spec.Mmr.mmr_inclusionC L hLne 0 genesisState _ (by rw [hLl]; exact pp.n0) hs' (by rw [← hrt, hTs]) with e | c
    · rw [hL, List.getElem?_map, List.getElem?_range (by have := pp.n0; omega)] at e
      simpa using e
    · exact absurd ⟨c.choose, List.mem_append_left _ c.choose_spec.1, c.choose_spec.2⟩ col
  · intro q hq
    obtain ⟨hsd, hrt⟩ := pathOk_steps (sealT_cpathC h hD hq) hD _ (pp.cD q hq) (pp.clen q hq) (pp.clo q hq) (pp.chi q hq)
    have hs' : (mmr L).sides (pos q) = List.replicate (lvl q) false ++
        (stepsOf ρ (cN ms gen D q) (cE ms gen D q) D (cSides nH (pos q) (lvl q)).length).map Step.left := by
      rw [hsd, cSides, Spec.Mmr.mmr_sides_eq, hLl, ← pp.cfalse q hq, List.take_append_drop]
    rcases Spec.Mmr.mmr_subC L hLne (lvl q) (pos q) (pp.calign q hq) (by rw [hLl]; exact pp.cbound q hq) _ _ hs'
        (by rw [← hrt, hTs]) with e | c
    · rw [← e, hL, map_range_slice _ (by have := pp.cbound q hq; omega)]
      exact rootFrom_bal (fun j => Spec.Bitcoin.sha256d (hs j)) (lvl q) (pos q)
    · exact absurd ⟨c.choose, List.mem_append_right _ (List.mem_flatMap.mpr ⟨q, List.mem_range.mpr hq, c.choose_spec.1⟩),
        c.choose_spec.2⟩ col

end StarkedAir.Circuit.ChainSeal
