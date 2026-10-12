/-
**The 16-component block system (D-043 part 3, option A).** `blockSys` is `hashSys` (`Link.lean`) with the
ancestry component (`Anc.lean`) appended. The ancestry has no lookups, so a satisfied `blockSys` is a
satisfied `hashSys` (every block theorem applies unchanged) plus a satisfied ancestry trace
(`blockSys_sat`).

`block_mtp`: below the CSV height the previous MTP's public limbs (inputs 3, 7) are 0; at and above it,
they are the median time past of 11 headers that hash-chain, in order, to a header whose SHA256d is the
block's (`HashPub.hash_pub`). Under SHA256d collision resistance those are the chain's 11 headers before
the block, so the MTP is Core's `GetMedianTimePast` of the previous block.
-/
import StarkedAir.Block.HashPub
import StarkedAir.Block.BlockSetup
import StarkedAir.Block.AncSound

namespace StarkedAir.Block

open StarkedAir

/-- The block system with the ancestry component (16 components; the prover's order). -/
def blockSys : System := ⟨16, fun i => if i < 15 then hashSys.comp i else Anc.anc⟩

theorem blockSys_comp {i : ℕ} (hi : i < 15) : blockSys.comp i = hashSys.comp i := by
  simp [blockSys, hi]

theorem sites_fst {sys : System} {inst : ℕ → Inst} {s : Site} (hs : s ∈ sites sys inst) : s.1 < sys.m := by
  unfold sites at hs
  obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨r, -, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hs
  exact List.mem_range.mp hi

theorem blockSys_sites (inst : ℕ → Inst) : sites blockSys inst = sites hashSys inst := by
  have h15 : (blockSys.comp 15).lookups = [] := by simp [blockSys, Anc.anc]
  unfold sites
  rw [show blockSys.m = 15 + 1 from rfl, List.range_succ, List.flatMap_append, List.flatMap_singleton, h15]
  simp only [List.length_nil, List.range_zero, List.map_nil]
  rw [show List.flatMap (fun _ => ([] : List Site)) (List.range (2 ^ (inst 15).logSize)) = [] by simp,
    List.append_nil, show hashSys.m = 15 from rfl]
  apply List.flatMap_congr
  intro i hi
  rw [blockSys_comp (List.mem_range.mp hi)]

theorem blockSys_total (inst : ℕ → Inst) (pub : ℕ → F) (R : ℕ) (v : List F) :
    total blockSys inst pub R v = total hashSys inst pub R v := by
  have e : ∀ s ∈ sites hashSys inst, siteRel blockSys s = siteRel hashSys s ∧
      siteVals blockSys inst pub s = siteVals hashSys inst pub s ∧
      siteMult blockSys inst pub s = siteMult hashSys inst pub s := by
    intro s hs
    have hc : blockSys.comp s.1 = hashSys.comp s.1 := blockSys_comp (sites_fst hs)
    unfold siteRel siteVals siteMult siteEval siteLookup
    rw [hc]
    exact ⟨rfl, rfl, rfl⟩
  unfold total
  rw [blockSys_sites, List.filter_congr (fun s hs => by rw [(e s hs).1, (e s hs).2.1])]
  congr 1
  apply List.map_congr_left
  intro s hs
  exact (e s (List.mem_filter.mp hs).1).2.2

/-- **A satisfied 16-component block system** is a satisfied `hashSys` and a satisfied ancestry. -/
theorem blockSys_sat {inst : ℕ → Inst} {pub : ℕ → F} (h : blockSys.SatisfiedExt inst pub []) :
    hashSys.SatisfiedExt inst pub [] ∧ Anc.anc.air.Satisfied (inst 15).logSize pub (inst 15).main := by
  obtain ⟨hair, hbal⟩ := h
  refine ⟨⟨fun i hi => ?_, fun R v => ?_⟩, ?_⟩
  · have := hair i (by show i < 16; exact Nat.lt_succ_of_lt hi)
    rwa [blockSys_comp hi] at this
  · rw [← blockSys_total]; exact hbal R v
  · have := hair 15 (by show 15 < 16; norm_num)
    simpa [blockSys] using this

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 16, (inst i).logSize = L) (hsat : blockSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

theorem hL15 : ∀ i < 15, (inst i).logSize = L := fun i hi => hL i (by omega)

/-- **The previous MTP.** -/
theorem block_mtp (hL8 : 8 ≤ L) :
    (pub Anc.PUB_CSV = 0 ∧ pub Anc.PUB_MLO = 0 ∧ pub Anc.PUB_MHI = 0) ∨
    (pub Anc.PUB_CSV = 1 ∧ ∃ (b : Spec.Block.Blk) (hw : ℕ → ℕ → Spec.Sha256.Word),
      Spec.Block.parseBlock (Rb inst pub) = some b ∧
      Spec.Block.stateBytes (Spec.Bitcoin.sha256d (hw Anc.NANC)) = Spec.Block.sha256d b.header ∧
      (∀ j, 1 ≤ j → j ≤ Anc.NANC → Spec.Bitcoin.prevHash (hw j) = Spec.Bitcoin.sha256d (hw (j - 1))) ∧
      (pub Anc.PUB_MLO).val < 65536 ∧ (pub Anc.PUB_MHI).val < 65536 ∧
      Anc.mtpOf pub = Spec.Bitcoin.medianTimePast
        ((List.range Anc.NANC).map (fun k => Spec.Bitcoin.timeOf (hw k))).reverse) := by
  obtain ⟨hh, ha⟩ := blockSys_sat hsat
  rw [hL 15 (by norm_num)] at ha
  rcases Anc.anc_sound ha hL8 with h0 | ⟨h1, -, hhash, hlink, hout, hlim, hmed⟩
  · exact Or.inl h0
  right
  obtain ⟨b, hp, S, hS, hpub⟩ := hash_pub (hL15 hL hsat hL24) hh hL24
  have hSw : ∀ w < 8, Spec.Bitcoin.stateWord S w = Spec.Bitcoin.stateWord (HeaderChain.hashAt (inst 15).main Anc.NANC) w := by
    intro w hw
    apply HeaderChain.half16_inj <;>
    · apply natCast_inj_of_lt (lt_trans (Sha256.half16_lt _ _) (by norm_num [P]))
        (lt_trans (Sha256.half16_lt _ _) (by norm_num [P]))
      first
      | (have e1 := hpub (2 * w) (by omega); have e2 := hout w hw 0 (by norm_num)
         simp only [show 2 * w / 2 = w by omega, show 2 * w % 2 = 0 by omega, Ctx.PUB_HASH, Anc.PUB_HASH,
           Nat.add_zero] at e1 e2
         rw [← e1, e2])
      | (have e1 := hpub (2 * w + 1) (by omega); have e2 := hout w hw 1 (by norm_num)
         simp only [show (2 * w + 1) / 2 = w by omega, show (2 * w + 1) % 2 = 1 by omega, Ctx.PUB_HASH, Anc.PUB_HASH,
           ← Nat.add_assoc] at e1 e2
         rw [← e1, e2])
  have hSeq : S = HeaderChain.hashAt (inst 15).main Anc.NANC := by
    have hw := hSw
    generalize HeaderChain.hashAt (inst 15).main Anc.NANC = T at hw ⊢
    rcases S with ⟨a0, a1, a2, a3, a4, a5, a6, a7⟩
    rcases T with ⟨b0, b1, b2, b3, b4, b5, b6, b7⟩
    have e0 := hw 0 (by norm_num); have e1 := hw 1 (by norm_num); have e2 := hw 2 (by norm_num)
    have e3 := hw 3 (by norm_num); have e4 := hw 4 (by norm_num); have e5 := hw 5 (by norm_num)
    have e6 := hw 6 (by norm_num); have e7 := hw 7 (by norm_num)
    simp only [Spec.Bitcoin.stateWord] at e0 e1 e2 e3 e4 e5 e6 e7
    rw [e0, e1, e2, e3, e4, e5, e6, e7]
  refine ⟨h1, b, fun j => HeaderChain.headerWord (inst 15).main j, hp, ?_, fun j hj1 hj => ?_, hlim.1, hlim.2, hmed⟩
  · rw [hhash _ le_rfl, ← hSeq, hS]
  · rw [hlink j hj1 hj, hhash _ (by omega)]

end System

end StarkedAir.Block
