/-
**SEAL-T, composed (SEAL-T-LEAN, D-052).** One theorem for `verify-seal` on a SEAL-T seal: a proof
accepted under the pinned seal identity with the digest the verifier recomputes (`sealMsgT`: the key
over the join's, the set trees' and the header tree's identities, the range, the start and end set
digests, `acc`, the end facts `W`, the tip, its height `nH − 1`, the chainwork, every path's sides and
length from the positions alone) gives, under the trust records of the epoch chain (`TrustEW`), the
set trees and the header tree (`TrustW`), the header tree's MMR shape (`MmrT`, trusted HC-HASHTREE),
the seal's own circuit (`THolds` for `sealW d`) and the verifier's native position checks
(`PathNative`):

- everything `seal_soundW` concludes (the chain of epoch openings valid, each epoch's sets proven
  passes with the balance, the end facts), and
- a valid header chain of `nH` headers from genesis (`SegmentValid` from the genesis input state)
  whose tip and chainwork words are the ones in the message, whose block 0 is Bitcoin's genesis
  block, and in which every epoch child's block-hash root (the words of its limbs in `rest`'s
  preimage `x`) is the root of the perfect tree over the block hashes at its position;

or a named Blake2s collision (`sealPairsT`) or a named node-hash collision of the paths (`tPairs`).
-/
import StarkedAir.Circuit.ChainSealTPaths
import StarkedAir.Circuit.ChainSealCompose

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q Spec.Blake2s
open StarkedAir.Circuit.BlockRec (H H_length wordsOf_eq wordsOf_length blake2s_length)
open StarkedAir.Circuit.RecCR (Collides CollidesAt H_eqC)
open StarkedAir.Circuit.EpochChain (Chain Ep)
open StarkedAir.Spec.HeaderTree (stWord)
open StarkedAir.Spec.Mmr (CollidesIn)
open StarkedAir.HeaderTree (PubValidT)
open StarkedAir.Circuit.EpochRoot (chainOuts chainOuts_length lastNext)

/-! ### The verifier's side -/

/-- The verifier's header data: the header tree's witness functions and shape (from the plan), the
header count, the tip and chainwork words it read, and each epoch child's position and level. -/
structure HCtx where
  leafH : ℕ → List Word
  nodeH : List Word
  nw : List Word → ℕ → Q
  lw : ℕ → List Word → ℕ → F
  th : BlockRec.Tree
  nH : ℕ
  tipW : List Word
  workW : List Word
  pos : ℕ → ℕ
  lvl : ℕ → ℕ

/-- What `verify-seal` checks natively about the positions (`chain_seal.pathPubs`: `PathTooLong`,
`BadPath`; `epoch_root.openHead`: aligned sizes, `BeyondChain`; D-052: fewer than `2^31` headers). -/
structure PathNative (ms : List ℕ) (D : ℕ) (Y : HCtx) : Prop where
  n0 : 0 < Y.nH
  nlt : Y.nH ≤ 2 ^ 31
  gD : (gSides Y.nH).length ≤ D
  cD : ∀ q < (childIdx ms).length, (cSides Y.nH (Y.pos q) (Y.lvl q)).length ≤ D
  cfalse : ∀ q < (childIdx ms).length, (Spec.Mmr.mmrSides Y.nH (Y.pos q)).take (Y.lvl q) = List.replicate (Y.lvl q) false
  calign : ∀ q < (childIdx ms).length, 2 ^ Y.lvl q ∣ Y.pos q
  cbound : ∀ q < (childIdx ms).length, Y.pos q + 2 ^ Y.lvl q ≤ Y.nH

/-- A path's three message words (`chain_seal.packSides`). -/
def pathTriple (D : ℕ) (ss : List Bool) : List Word :=
  [BitVec.ofNat 32 (packLo D ss), BitVec.ofNat 32 (packHi D ss), BitVec.ofNat 32 ss.length]

/-- Every path's words: genesis, then the children in chain order. -/
def pathWords (D : ℕ) (Y : HCtx) (k : ℕ) : List Word :=
  pathTriple D (gSides Y.nH) ++ (List.range k).flatMap fun q => pathTriple D (cSides Y.nH (Y.pos q) (Y.lvl q))

section
variable (X : Ctx) (ms : List ℕ) (gen : Bool) (c : Chain Ep) (ts : ℕ → BlockRec.Tree) (W : List Word) (D : ℕ) (Y : HCtx)

/-- The key message the verifier expects: `sealKeyMsg`, then the header tree's identity. -/
noncomputable def sealKeyMsgT : List Word :=
  sealKeyMsg X ms gen c ts ++ Y.th.hash Y.leafH Y.nodeH ++ Y.th.key Y.leafH Y.nodeH

/-- **The SEAL-T output message the verifier expects.** -/
noncomputable def sealMsgT : List Word :=
  H (sealKeyMsgT X ms gen c ts Y) ++ [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++ c.first.o.prev ++
    c.last.o.fin ++ c.acc X.leafH X.nodeH ++ W ++ Y.tipW ++ [BitVec.ofNat 32 (Y.nH - 1)] ++ Y.workW ++
    pathWords D Y (childIdx ms).length

/-- The seal's assignment for that digest. -/
noncomputable def sealRhoT : ℕ → Q := X.sealW (H (sealMsgT X ms gen c ts W D Y))

/-- The key message's registers. -/
def keyRegsT : List ℕ := keyRegs (parts ms gen) ++ (partsT ms gen D).hc.res.chash ++ (partsT ms gen D).hc.res.key

/-- The Blake2s message pairs the theorem's checks compare. -/
noncomputable def sealPairsT : List (List Word × List Word) :=
  let ρ := sealRhoT X ms gen c ts W D Y
  (wordsOf ρ (partsT ms gen D).msg, sealMsgT X ms gen c ts W D Y) :: (wordsOf ρ (keyRegsT ms gen D), sealKeyMsgT X ms gen c ts Y) ::
    (coreSealPairs X ρ ms gen c ts ++ RecCR.pairsH Y.leafH Y.nodeH Y.nw Y.lw Y.th (hpub ρ ms gen D))

end

/-! ### The program's layout -/

theorem chainSealT_ops' (ms : List ℕ) (gen : Bool) (D : ℕ) : (chainSealT ms gen D).ops =
    sealOps ms gen ++ ((partsT ms gen D).hc.ops ++ [.const (partsT ms gen D).k65535 65535 0 0 0] ++ (partsT ms gen D).pws ++
      (partsT ms gen D).gen ++ (partsT ms gen D).T.ops ++ (partsT ms gen D).tip.ops ++ (partsT ms gen D).hgt.ops ++
      (partsT ms gen D).work.ops ++ (partsT ms gen D).gleaf ++ (partsT ms gen D).paths.flatMap (·.ops) ++
      (partsT ms gen D).ends ++ (partsT ms gen D).key.ops ++ (partsT ms gen D).dg.ops) := by
  simp only [chainSealT, sealOps, List.append_assoc]
  rfl

theorem mem_chainSealT_hc {ms : List ℕ} {gen : Bool} {D : ℕ} {o : Op} (h : o ∈ (partsT ms gen D).hc.ops) :
    o ∈ (chainSealT ms gen D).ops := by
  rw [chainSealT_ops']
  refine List.mem_append_right _ ?_
  iterate 12 apply List.mem_append_left
  exact h

theorem partsT_hc (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (partsT ms gen D).hc = hdrChild (parts ms gen).checks.next (eState ms gen (nSets ms.length gen)) (nSets ms.length gen + 1) := rfl

set_option maxHeartbeats 1000000 in
theorem partsT_key (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (partsT ms gen D).key = blake2s (lastNext (cpathsT ms gen D) (gpathT ms gen D).next) (keyRegsT ms gen D)
      (4 * (keyRegsT ms gen D).length) := by
  rfl

set_option maxHeartbeats 1000000 in
theorem partsT_msg (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (partsT ms gen D).msg = (partsT ms gen D).key.res ++ [(partsT ms gen D).key.next, (partsT ms gen D).key.next + 1] ++
      (parts ms gen).J.res.first ++ (parts ms gen).J.res.last ++ (parts ms gen).J.res.tail ++
      [(openO (parts ms gen) (nSets ms.length gen - 1)).res.cntW] ++ (openO (parts ms gen) (nSets ms.length gen - 1)).res.amtW ++
      [(openO (parts ms gen) (nSets ms.length gen - 1)).res.maxhW] ++ (openO (parts ms gen) (nSets ms.length gen - 1)).res.mroot ++
      (openO (parts ms gen) (nSets ms.length gen - 1)).res.shaDg ++ shaStartRegs (parts ms gen) gen ++
      (partsT ms gen D).tip.res ++ (partsT ms gen D).hgt.res ++ (partsT ms gen D).work.res ++
      (List.range (partsT ms gen D).paths.length).flatMap (fun p =>
        [(partsT ms gen D).key.next + 2 + 3 * p, (partsT ms gen D).key.next + 2 + 3 * p + 1,
          (partsT ms gen D).key.next + 2 + 3 * p + 2]) := by
  rfl

/-- The message in blocks: key, range, `parts.msg.drop 10`, tip, height, work, paths. -/
theorem partsT_msg' (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (partsT ms gen D).msg = (partsT ms gen D).key.res ++ [(partsT ms gen D).key.next, (partsT ms gen D).key.next + 1] ++
      ((parts ms gen).msg.drop 10 ++ ((partsT ms gen D).tip.res ++ ((partsT ms gen D).hgt.res ++ ((partsT ms gen D).work.res ++
      (List.range (partsT ms gen D).paths.length).flatMap (fun p =>
        [(partsT ms gen D).key.next + 2 + 3 * p, (partsT ms gen D).key.next + 2 + 3 * p + 1,
          (partsT ms gen D).key.next + 2 + 3 * p + 2]))))) := by
  rw [partsT_msg, parts_msg_drop]
  simp only [List.append_assoc]

theorem partsT_paths_length (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (partsT ms gen D).paths.length = (childIdx ms).length + 1 := by
  rw [partsT_paths, List.length_cons, cpathsT, chainOuts_length]

theorem hdr_key_length (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).hc.res.key.length = 8 := by
  rw [partsT_hc]; simp [hdrChild, BlockRec.guessHash_length]

theorem hdr_chash_length (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).hc.res.chash.length = 8 := by
  rw [partsT_hc]; simp [hdrChild]


theorem partsT_tip (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).tip =
    packN (partsT ms gen D).T.next ((List.range 16).map (fun j => (partsT ms gen D).hc.res.pubs (16 + j))) 8 (parts ms gen).C.res := rfl
theorem partsT_hgt (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).hgt =
    packN (partsT ms gen D).tip.next [(partsT ms gen D).hc.res.pubs 38, (partsT ms gen D).hc.res.pubs 39] 1 (parts ms gen).C.res := rfl
theorem partsT_work (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).work =
    packN (partsT ms gen D).hgt.next ((List.range 10).map (fun j => (partsT ms gen D).hc.res.pubs (98 + j))) 5 (parts ms gen).C.res := rfl

theorem packN_res_length (n : ℕ) (limbs : List ℕ) (k : ℕ) (C : Consts) : (packN n limbs k C).res.length = k := by
  simp [packN]

theorem partsT_key_length (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).key.res.length = 8 := by
  rw [partsT_key]; exact blake2s_length _ _ _

set_option maxHeartbeats 1000000 in
theorem partsT_dg (ms : List ℕ) (gen : Bool) (D : ℕ) : (chainSealT ms gen D).results =
    (blake2s ((partsT ms gen D).key.next + 2 + 3 * (partsT ms gen D).paths.length) (partsT ms gen D).msg
      (4 * (partsT ms gen D).msg.length)).res := rfl

theorem partsT_msg_length {ms : List ℕ} {gen : Bool} {D : ℕ} (hn : 2 ≤ ms.length) :
    (partsT ms gen D).msg.length = 80 + 3 * (childIdx ms).length := by
  rw [partsT_msg', partsT_tip, partsT_hgt, partsT_work]
  simp only [List.length_append, List.length_drop, msg_length hn, partsT_key_length, packN_res_length,
    List.length_cons, List.length_nil, List.length_flatMap, List.map_const', List.length_range, List.sum_replicate,
    partsT_paths_length, smul_eq_mul]
  omega

/-- A `packN`'s words. -/
theorem packN_words {ρ : ℕ → Q} {n k : ℕ} {limbs : List ℕ} {C : Consts} (h : Holds ρ (packN n limbs k C).ops)
    (hC : ConstsOk ρ C) (hl : ∀ j < 2 * k, IsBase (ρ (limbs.getD j 0))) :
    wordsOf ρ (packN n limbs k C).res =
      (List.range k).map fun w => word ⟨(ρ (limbs.getD (2 * w) 0)).a, (ρ (limbs.getD (2 * w + 1) 0)).a, 0, 0⟩ := by
  apply List.ext_getElem (by simp [wordsOf, packN_res_length])
  intro w h1 h2
  have hw : w < k := by simpa using h2
  simp only [wordsOf, List.getElem_map, List.getElem_range, Function.comp]
  rw [← List.getD_eq_getElem _ 0 (by rw [packN_res_length]; exact hw), packN_sound h hC hl w hw]

theorem getD_take_drop (l : List ℕ) {a j m : ℕ} (hj : j < m) : ((l.drop a).take m).getD j 0 = l.getD (a + j) 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hj, ite_true, List.getElem?_drop]

/-! ### Small facts -/

/-- A field element whose `u32` word is that of a small number is that number. -/
theorem eq_of_ofNat {x : F} {k : ℕ} (hk : k < 2 ^ 32) (h : BitVec.ofNat 32 x.val = BitVec.ofNat 32 k) : x = (k : F) := by
  have e := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at e
  have hx : x.val < 2 ^ 32 := lt_trans (ZMod.val_lt x) (by unfold P; norm_num)
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hk] at e
  rw [← e, ZMod.natCast_zmod_val]

theorem packLo_lt (D : ℕ) (ss : List Bool) : packLo D ss < 2 ^ 32 :=
  lt_of_lt_of_le (bits_lt _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))

theorem packHi_lt {D : ℕ} (hD : D ≤ 60) (ss : List Bool) : packHi D ss < 2 ^ 32 :=
  lt_of_lt_of_le (bits_lt _ _) (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- Lists of triples agree triple by triple. -/
theorem flatMap_triples {f g : ℕ → List Word} (hf : ∀ p, (f p).length = 3) (hg : ∀ p, (g p).length = 3) :
    ∀ m, (List.range m).flatMap f = (List.range m).flatMap g → ∀ p < m, f p = g p
  | 0, _, p, hp => absurd hp (Nat.not_lt_zero _)
  | m + 1, he, p, hp => by
    rw [List.range_succ, List.flatMap_append, List.flatMap_append] at he
    have hl : ((List.range m).flatMap f).length = ((List.range m).flatMap g).length := by
      rw [List.length_flatMap, List.length_flatMap]; simp [hf, hg]
    obtain ⟨e1, e2⟩ := List.append_inj he hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp | rfl
    · exact flatMap_triples hf hg m e1 p hp
    · simpa using e2

theorem childIdx_get {ms : List ℕ} {q : ℕ} (hq : q < (childIdx ms).length) :
    ((childIdx ms).getD q (0, 0)).1 < ms.length ∧ ((childIdx ms).getD q (0, 0)).2 < ms.getD ((childIdx ms).getD q (0, 0)).1 0 := by
  have hm : (childIdx ms).getD q (0, 0) ∈ childIdx ms := by
    rw [List.getD_eq_getElem _ _ hq]; exact List.getElem_mem _
  generalize (childIdx ms).getD q (0, 0) = z at hm ⊢
  simp only [childIdx, List.mem_flatMap, List.mem_map, List.mem_range] at hm
  obtain ⟨i, hi, cc, hc, e⟩ := hm
  rw [← e]; exact ⟨hi, hc⟩

/-! ### The theorem -/

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}

set_option maxHeartbeats 8000000 in
/-- **The SEAL-T seal is sound, up to a named collision (SEAL-T-LEAN).** -/
theorem sealT_soundW (X : Ctx) (Y : HCtx) {ok : (ℕ → F) → Prop} {sealH : List Word} {ms : List ℕ} {gen : Bool} {D : ℕ}
    (hD : D ≤ 60)
    (T : EpochChain.TrustEW Acc SatC VGates X.leafH X.nodeH X.rootH X.joinH (RecCR.LeafAt ok) X.nw X.lw X.rootW X.joinW)
    (TS : RecCR.TrustW Acc SatC VGates X.leafS X.nodeS SetTree.setNodeProgram (SetPass.LeafAtS SetPass.SegOk) X.nwS X.lwS)
    (TH : RecCR.TrustW Acc SatC VGates Y.leafH Y.nodeH nodeProgram RecCR.LeafAtH Y.nw Y.lw)
    (HS : ∀ p, SatC (Y.th.hash Y.leafH Y.nodeH) (HeaderRec.pubDigest (Y.th.key Y.leafH Y.nodeH) p) → MmrT p)
    (TC : ∀ d, SatC sealH d → THolds ms gen D (X.sealW d) ∧
      wordsOf (X.sealW d) (chainSealT ms gen D).results = d ∧ BlockRec.HookGates VGates (X.sealW d) (chainSealT ms gen D).ops)
    (hl : ∀ L, (X.leafH L).length = 8) (hn : ∀ a v, (X.nodeH a v).length = 8)
    (hr : ∀ M p s, (X.rootH M p s).length = 8) (hj : ∀ v, (X.joinH v).length = 8)
    (hlS : ∀ L, (X.leafS L).length = 8) (hnS : X.nodeS.length = 8)
    (hlH : ∀ L, (Y.leafH L).length = 8) (hnH : Y.nodeH.length = 8)
    (c : Chain Ep) (hok : (c.map Ep.sh).Ok) (hw : c.All (fun e => e.o.Fits))
    (hgen : c.gen = false → c.first.o.prev = List.replicate 8 0)
    (hlen : c.epochs.length = ms.length) (hcg : c.gen = !gen) (hms : ∀ i < ms.length, ms.getD i 0 ≤ 64)
    (hBk : 4 * (keyRegsT ms gen D).length < 2 ^ 32) (hBm : 4 * (80 + 3 * (childIdx ms).length) < 2 ^ 32)
    (ts : ℕ → BlockRec.Tree) (W : List Word) (hW : W.length = 29)
    (hN : PathNative ms D Y) (htip : Y.tipW.length = 8) (hwork : Y.workW.length = 5)
    (hacc : Acc sealH (H (sealMsgT X ms gen c ts W D Y))) :
    (∃ (x : ℕ → ℕ → F) (cE cB : ℕ → ℕ) (SE SB : ℕ → Spec.SetFile.St Spec.QM31.QM) (rE rB : ℕ → Spec.Sha256.State),
      c.Valid X.leafH X.nodeH X.rootH SatC ∧
      (∀ i < ms.length, EpochOk ts gen i (epAt c i) (ms.getD i 0) (x i) (cE i) (cB i) (SE i) (SB i) (rE i) (rB i)) ∧
      EndOk W (cE (ms.length - 1)) (SE (ms.length - 1)) (rE (ms.length - 1))
        (wordsOf (sealRhoT X ms gen c ts W D Y) (shaStartRegs (parts ms gen) gen)) ∧
      (gen = true → wordsOf (sealRhoT X ms gen c ts W D Y) (shaStartRegs (parts ms gen) gen) = List.replicate 8 0) ∧
      (gen = false → ∃ v : ℕ → F, SetPass.EncSha v 0 (SB 0).sha ∧
        wordsOf (sealRhoT X ms gen c ts W D Y) (shaStartRegs (parts ms gen) gen) = shaVec v) ∧
      ∃ hs, Spec.Bitcoin.SegmentValid Y.nH hs
          ⟨HeaderChain.pubState (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) 0, 0,
            HeaderChain.leN (HeaderChain.pubWord (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) 34),
            HeaderChain.leN (HeaderChain.pubWord (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) 44),
            HeaderChain.leN (HeaderChain.pubWord (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) 36), [], 0⟩
          (HeaderChain.decodeOut (hpub (sealRhoT X ms gen c ts W D Y) ms gen D)) ∧
        HeaderChain.pubState (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) 0 = HeaderChain.pubState (fun _ => 0) 0 ∧
        Y.tipW = (List.range 8).map (fun w => HeaderChain.pubWord (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) (16 + 2 * w)) ∧
        Y.workW = (List.range 5).map (fun w => HeaderChain.pubWord (hpub (sealRhoT X ms gen c ts W D Y) ms gen D) (98 + 2 * w)) ∧
        ((Spec.Bitcoin.sha256d (hs 0) = genesisState ∧
          ∀ q < (childIdx ms).length, ∀ w < 8,
            word ⟨x ((childIdx ms).getD q (0, 0)).1 (17 + 16 * ((childIdx ms).getD q (0, 0)).2 + 2 * w),
              x ((childIdx ms).getD q (0, 0)).1 (17 + 16 * ((childIdx ms).getD q (0, 0)).2 + 2 * w + 1), 0, 0⟩ =
            stWord (BlockTree.rootFrom (fun j => Spec.Bitcoin.sha256d (hs j)) (Y.lvl q) (Y.pos q)) w) ∨
         CollidesIn (tPairs (sealRhoT X ms gen c ts W D Y) ms gen D Y.nH Y.pos Y.lvl
           ((List.range Y.nH).map fun j => Spec.Bitcoin.sha256d (hs j))))) ∨
    Collides (sealPairsT X ms gen c ts W D Y) := by
  set d := H (sealMsgT X ms gen c ts W D Y) with hd
  obtain ⟨hT, hres, hg⟩ := TC d (T.stwoSound _ _ hacc)
  have hρdef : sealRhoT X ms gen c ts W D Y = X.sealW d := rfl
  rw [hρdef]
  set ρ := X.sealW d with hρρ
  set P := parts ms gen with hP
  set Q := partsT ms gen D with hQ
  set S := nSets ms.length gen with hS
  by_cases col : Collides (sealPairsT X ms gen c ts W D Y)
  · exact Or.inr col
  left
  have hsp : sealPairsT X ms gen c ts W D Y = (wordsOf ρ Q.msg, sealMsgT X ms gen c ts W D Y) ::
      (wordsOf ρ (keyRegsT ms gen D), sealKeyMsgT X ms gen c ts Y) ::
      (coreSealPairs X ρ ms gen c ts ++ RecCR.pairsH Y.leafH Y.nodeH Y.nw Y.lw Y.th (hpub ρ ms gen D)) := rfl
  have n2 : 2 ≤ ms.length := hlen ▸ epochs_two c
  have hk : (childIdx ms).length + 1 = Q.paths.length := (partsT_paths_length ms gen D).symm
  -- the output message
  have hml : 4 * Q.msg.length < 2 ^ 32 := by rw [partsT_msg_length n2]; exact hBm
  obtain ⟨hlo, hhi, hpath, hdig⟩ := sealT_digest hT hml
  have hdw : wordsOf ρ (chainSealT ms gen D).results = H (wordsOf ρ Q.msg) := by
    have hrl : (chainSealT ms gen D).results.length = 8 := by rw [partsT_dg]; exact blake2s_length _ _ _
    rw [wordsOf_eq hrl hdig, H, wordsOf_length]
  rw [hdw] at hres
  have hm : wordsOf ρ Q.msg = sealMsgT X ms gen c ts W D Y := by
    rcases H_eqC _ _ hres with e | cc
    · exact e
    · exact absurd ⟨_, by rw [hsp]; exact List.mem_cons_self, cc⟩ col
  have hfirst8 : c.first.o.prev.length = 8 := hw.first.1.2.1
  have hlast8 : c.last.o.fin.length = 8 := hw.last.1.1
  obtain ⟨eKey, eAB, hrest, etip, ehgt, ework, epaths⟩ :
      wordsOf ρ Q.key.res = H (sealKeyMsgT X ms gen c ts Y) ∧
      [word (ρ Q.key.next), word (ρ (Q.key.next + 1))] = [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ∧
      wordsOf ρ (P.msg.drop 10) = (sealMsg X ms gen c ts W).drop 10 ∧
      wordsOf ρ Q.tip.res = Y.tipW ∧ wordsOf ρ Q.hgt.res = [BitVec.ofNat 32 (Y.nH - 1)] ∧ wordsOf ρ Q.work.res = Y.workW ∧
      wordsOf ρ ((List.range Q.paths.length).flatMap (fun p => [Q.key.next + 2 + 3 * p, Q.key.next + 2 + 3 * p + 1,
        Q.key.next + 2 + 3 * p + 2])) = pathWords D Y (childIdx ms).length := by
    have e := hm
    have hR : sealMsgT X ms gen c ts W D Y = H (sealKeyMsgT X ms gen c ts Y) ++ [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++
        ((sealMsg X ms gen c ts W).drop 10 ++ (Y.tipW ++ ([BitVec.ofNat 32 (Y.nH - 1)] ++ (Y.workW ++
          pathWords D Y (childIdx ms).length)))) := by
      rw [sealMsg_drop]; simp only [sealMsgT, List.append_assoc]
    rw [partsT_msg', hR] at e
    simp only [wordsOf, List.map_append, List.map_cons, List.map_nil, Function.comp_apply] at e
    simp only [List.append_assoc] at e
    obtain ⟨k1, e⟩ := List.append_inj e (by simp [partsT_key_length, H_length])
    obtain ⟨k2, e⟩ := List.append_inj e (by simp)
    obtain ⟨k3, e⟩ := List.append_inj e (by
      simp only [List.length_map, List.length_drop, msg_length n2, sealMsg_drop, List.length_append, hfirst8, hlast8,
        EpochChain.Chain.acc_length, hW])
    obtain ⟨k4, e⟩ := List.append_inj e (by rw [List.length_map, partsT_tip, packN_res_length, htip])
    obtain ⟨k5, e⟩ := List.append_inj e (by rw [List.length_map, partsT_hgt, packN_res_length]; rfl)
    obtain ⟨k6, e⟩ := List.append_inj e (by rw [List.length_map, partsT_work, packN_res_length, hwork])
    exact ⟨k1, by simpa using k2, by simpa [wordsOf] using k3, k4, k5, k6, by simpa [wordsOf, List.map_flatMap] using e⟩
  -- the key message
  have hkey : wordsOf ρ Q.key.res = H (wordsOf ρ (keyRegsT ms gen D)) := by
    have hkw := sealT_key hT hBk
    rw [wordsOf_eq (partsT_key_length ms gen D) hkw, H, wordsOf_length]; rfl
  rw [hkey] at eKey
  have hkeT : wordsOf ρ (keyRegsT ms gen D) = sealKeyMsgT X ms gen c ts Y := by
    rcases H_eqC _ _ eKey with e | cc
    · exact e
    · exact absurd ⟨_, by rw [hsp]; exact List.mem_cons_of_mem _ List.mem_cons_self, cc⟩ col
  obtain ⟨hke, ehash, ekey⟩ : wordsOf ρ (keyRegs P) = sealKeyMsg X ms gen c ts ∧
      wordsOf ρ Q.hc.res.chash = Y.th.hash Y.leafH Y.nodeH ∧ wordsOf ρ Q.hc.res.key = Y.th.key Y.leafH Y.nodeH := by
    have e := hkeT
    simp only [keyRegsT, sealKeyMsgT, wordsOf, List.map_append] at e
    obtain ⟨e1, e3⟩ := List.append_inj' e (by rw [List.length_map, hdr_key_length, BlockRec.Tree.key_length])
    obtain ⟨e1, e2⟩ := List.append_inj' e1 (by rw [List.length_map, hdr_chash_length, tree_hash_length _ _ hlH hnH])
    exact ⟨e1, e2, e3⟩
  have hab : BitVec.ofNat 32 (ρ P.J.res.lo).a.val = BitVec.ofNat 32 c.first.o.lo ∧
      BitVec.ofNat 32 (ρ P.J.res.hi).a.val = BitVec.ofNat 32 c.last.o.hi := by
    rw [← hlo, ← hhi]; simpa using eAB
  have hp9 : Holds ρ (sealOps ms gen) := hT.sealOk
  have hg9 : BlockRec.HookGates VGates ρ (sealOps ms gen) := fun i a o ho => hg i a o (by
    rw [chainSealT_ops']; exact List.mem_append_left _ ho)
  -- the shared core
  rcases seal_core X T TS hl hn hr hj hlS hnS c hok hw hgen hlen hcg hms ts W hW hp9 hg9 hke hab hrest with r | cc
  swap
  · exact absurd (cc.mono fun x hx => by
      rw [hsp]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _ hx))) col
  obtain ⟨x, cE, cB, SE, SB, rE, rB, hV, hE, hEnd, hG1, hG2, hxl⟩ := r
  refine ⟨x, cE, cB, SE, SB, rE, rB, hV, hE, hEnd, hG1, hG2, ?_⟩
  -- the header root: hook S + 1
  have hhc : Holds ρ (hdrChild P.checks.next (eState ms gen S) (S + 1)).ops := by rw [← partsT_hc]; exact hT.hc
  obtain ⟨hroot, hrl, hrm⟩ := hdrChild_hook P.checks.next (eState ms gen S) (S + 1)
  have hmem : Op.hook (S + 1) (hroot ++ (hdrChild P.checks.next (eState ms gen S) (S + 1)).res.digest)
      (hdrChild P.checks.next (eState ms gen S) (S + 1)).res.chash ∈ (chainSealT ms gen D).ops := by
    apply mem_chainSealT_hc
    have e := partsT_hc ms gen D
    rw [e]; exact hrm
  have sH := T.recVerifies ρ _ _ _ (hg _ _ _ hmem)
  rw [List.drop_left' hrl, hdrChild_digest hhc] at sH
  rw [← partsT_hc] at sH
  rw [ehash, ekey] at sH
  have sat : SatC (Y.th.hash Y.leafH Y.nodeH) (HeaderRec.pubDigest (Y.th.key Y.leafH Y.nodeH) (hpub ρ ms gen D)) := sH
  have hv : PubValidT (hpub ρ ms gen D) := by
    rcases RecCR.htree_soundW TH hlH hnH Y.th _ sat with v | cc
    · exact v
    · exact absurd (cc.mono fun x hx => by
        rw [hsp]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _ hx))) col
  have hshape := HS _ sat
  -- the paths' words
  have hP0 : Q.paths.getD 0 noPath = gpathT ms gen D := by rw [hQ, partsT_paths]; rfl
  have hPq : ∀ q, Q.paths.getD (q + 1) noPath = (cpathsT ms gen D).getD q noPath := fun q => by rw [hQ, partsT_paths]; rfl
  have htr := flatMap_triples (f := fun p => [BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.sLo).a.val,
      BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.sHi).a.val, BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.len).a.val])
    (g := fun p => if p = 0 then pathTriple D (gSides Y.nH) else pathTriple D (cSides Y.nH (Y.pos (p - 1)) (Y.lvl (p - 1))))
    (fun _ => rfl) (fun p => by split <;> rfl) Q.paths.length (by
      have l1 : wordsOf ρ ((List.range Q.paths.length).flatMap (fun p => [Q.key.next + 2 + 3 * p, Q.key.next + 2 + 3 * p + 1,
          Q.key.next + 2 + 3 * p + 2])) = (List.range Q.paths.length).flatMap (fun p =>
            [BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.sLo).a.val,
              BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.sHi).a.val, BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.len).a.val]) := by
        simp only [wordsOf, List.map_flatMap, List.map_cons, List.map_nil, Function.comp_apply]
        refine List.flatMap_congr (fun p hp => ?_)
        obtain ⟨a1, a2, a3⟩ := hpath p (List.mem_range.mp hp)
        rw [a1, a2, a3]; rfl
      rw [← l1, epaths, pathWords, ← hk, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
      simp)
  have tri : ∀ p < (childIdx ms).length + 1, ∀ ss : List Bool, ss.length ≤ D →
      [BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.sLo).a.val, BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.sHi).a.val,
        BitVec.ofNat 32 (ρ (Q.paths.getD p noPath).res.len).a.val] = pathTriple D ss →
      (ρ (Q.paths.getD p noPath).res.len).a = (ss.length : F) ∧ (ρ (Q.paths.getD p noPath).res.sLo).a = (packLo D ss : F) ∧
        (ρ (Q.paths.getD p noPath).res.sHi).a = (packHi D ss : F) := by
    intro p _ ss hss e
    simp only [pathTriple, List.cons.injEq, and_true] at e
    exact ⟨eq_of_ofNat (by omega) e.2.2, eq_of_ofNat (packLo_lt D ss) e.1, eq_of_ofNat (packHi_lt hD ss) e.2.1⟩
  have pp : PathPubsOk ρ ms gen D Y.nH Y.pos Y.lvl := by
    have g0 := tri 0 (by omega) _ hN.gD (by have := htr 0 (by omega); simpa using this)
    rw [hP0] at g0
    have gq : ∀ q < (childIdx ms).length, _ := fun q hq =>
      tri (q + 1) (by omega) _ (hN.cD q hq) (by have := htr (q + 1) (by omega); simpa using this)
    refine ⟨hN.n0, hN.gD, g0.1, g0.2.1, g0.2.2, hN.cD, fun q hq => ?_, fun q hq => ?_, fun q hq => ?_,
      hN.cfalse, hN.calign, hN.cbound⟩
    · have := (gq q hq).1; rwa [hPq] at this
    · have := (gq q hq).2.1; rwa [hPq] at this
    · have := (gq q hq).2.2; rwa [hPq] at this
  -- the header chain
  obtain ⟨Hh, hs, hseg, hg0, himp⟩ := sealT_headerC hT hD hv hshape pp
  -- its length is the verifier's count (the height word)
  have hbase : ∀ k < N_PUB, IsBase (ρ (Q.hc.res.pubs k)) := by
    rw [partsT_hc]; exact hdrChild_base hhc
  have hgw : wordsOf ρ Q.hgt.res = [HeaderChain.pubWord (hpub ρ ms gen D) 38] := by
    rw [partsT_hgt, packN_words (by rw [← partsT_hgt]; exact hT.hgt) (sealT_C hT) (fun j hj => by
      interval_cases j
      · exact hbase 38 (by unfold N_PUB; omega)
      · exact hbase 39 (by unfold N_PUB; omega))]
    rfl
  have hHn : Hh = Y.nH := by
    rw [hgw] at ehgt
    have e1 := List.head_eq_of_cons_eq ehgt
    have hh := hseg.2.2.2.2.2.2.1
    simp only [HeaderChain.decodeOut, Nat.zero_add] at hh
    rw [e1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hN.nlt; omega)] at hh
    have := hseg.1; have := hN.n0; omega
  subst hHn
  have hpw : ∀ (b k : ℕ), (∀ j < 2 * k, IsBase (ρ (Q.hc.res.pubs (b + j)))) →
      ∀ (n : ℕ) (C : Consts), Holds ρ (packN n ((List.range (2 * k)).map (fun j => Q.hc.res.pubs (b + j))) k C).ops →
      ConstsOk ρ C → wordsOf ρ (packN n ((List.range (2 * k)).map (fun j => Q.hc.res.pubs (b + j))) k C).res =
        (List.range k).map (fun w => HeaderChain.pubWord (hpub ρ ms gen D) (b + 2 * w)) := by
    intro b k hb n C h hC
    rw [packN_words h hC (fun j hj => by rw [getD_map_range hj]; exact hb j hj)]
    refine List.map_congr_left (fun w hw => ?_)
    have hw' := List.mem_range.mp hw
    rw [getD_map_range (by omega), getD_map_range (by omega)]
    show _ = BitVec.ofNat 32 (_ + 65536 * _)
    rw [show b + (2 * w + 1) = b + 2 * w + 1 by omega]
    rfl
  refine ⟨hs, hseg, hg0, ?_, ?_, ?_⟩
  · rw [← etip, partsT_tip]
    exact hpw 16 8 (fun j hj => hbase _ (by unfold N_PUB; omega)) _ _ (by rw [← partsT_tip]; exact hT.tip) (sealT_C hT)
  · rw [← ework, partsT_work]
    exact hpw 98 5 (fun j hj => hbase _ (by unfold N_PUB; omega)) _ _ (by rw [← partsT_work]; exact hT.work) (sealT_C hT)
  -- the paths
  rcases himp rfl with ⟨hgen0, hch⟩ | cc
  · left
    refine ⟨hgen0, fun q hq w hw' => ?_⟩
    obtain ⟨hi, hcc⟩ := childIdx_get hq
    set i := ((childIdx ms).getD q (0, 0)).1 with hi'
    set cq := ((childIdx ms).getD q (0, 0)).2 with hcq
    obtain ⟨rr, hrr, hhr⟩ := chainOuts_getD_holds hi ⟨[], ⟨[], 0, [], []⟩, 0⟩ (sealOps_parts hp9).2.2.2.1
    change restO P i = _ at hrr
    obtain ⟨rbase, -⟩ := restOpen_sound hhr (hms i hi)
    have hhr' : (restO P i).res.hr = (List.range (16 * ms.getD i 0)).map (rr + 17 + ·) := by rw [hrr]; rfl
    have hlimb : ∀ j < 16, (childLimbs P i cq).getD j 0 = rr + 17 + (16 * cq + j) := fun j hj => by
      rw [childLimbs, getD_take_drop _ hj]
      change (restO P i).res.hr.getD _ 0 = _
      rw [hhr', getD_map_range (by have : cq + 1 ≤ ms.getD i 0 := hcc; omega)]
    have hbl : ∀ j < 2 * 8, IsBase (ρ ((childLimbs P i cq).getD j 0)) := fun j hj => by
      rw [hlimb j hj, Nat.add_assoc]; exact rbase _ (by have : cq + 1 ≤ ms.getD i 0 := hcc; omega)
    have e : stWord (regState ρ (cLeaf ms gen D q).res) w = _ := congrArg (fun R => stWord R w) (hch q hq)
    rw [← e, stWord_regState _ hw', cLeaf, packN_sound (cLeaf_holds hT hq) (sealT_C hT) hbl w hw']
    have hcc' : cq + 1 ≤ ms.getD i 0 := hcc
    have x0 := hxl i hi (16 * cq + 2 * w) (by omega)
    have x1 := hxl i hi (16 * cq + 2 * w + 1) (by omega)
    rw [hhr', getD_map_range (by omega)] at x0
    rw [hhr', getD_map_range (by omega)] at x1
    rw [hlimb _ (by omega), hlimb _ (by omega)]
    have x0' : x i (17 + 16 * cq + 2 * w) = (ρ (rr + 17 + (16 * cq + 2 * w))).a := by
      rw [show 17 + 16 * cq + 2 * w = 17 + (16 * cq + 2 * w) by omega]; exact x0
    have x1' : x i (17 + 16 * cq + 2 * w + 1) = (ρ (rr + 17 + (16 * cq + (2 * w + 1)))).a := by
      rw [show 17 + 16 * cq + 2 * w + 1 = 17 + (16 * cq + 2 * w + 1) by omega,
        show 16 * cq + (2 * w + 1) = 16 * cq + 2 * w + 1 by omega]; exact x1
    rw [x0', x1']
  · exact Or.inr cc

end

end StarkedAir.Circuit.ChainSeal
