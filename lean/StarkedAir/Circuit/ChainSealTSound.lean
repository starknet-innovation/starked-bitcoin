/-
**The SEAL-T gadgets' soundness** (`Circuit/ChainSealT.lean`, D-052), in the style of
`ChainSealSound.lean`: what a satisfying assignment `ρ` forces.

- `pathStep_sound`: one path step, with a boolean side bit and a boolean active bit, is the MMR spec's
  `Step.up` (`Spec.Mmr`: `hnode` of the sibling and the current value in the side's order) when
  active, the current value when not;
- `pathSteps_sound`, `foldSteps_prefix`, `pathOps_sound`: a path of `D ≤ 60` steps with length `L ≤ D`
  computes `Spec.Mmr.pathRoot` of its leaf over its first `L` steps (guessed siblings, boolean sides);
  `bitsWord_sound`: the side bits packed into two words;
- `packN_sound`, `hdrChild_digest`, `hdrChild_hook`, `genesisOps_sound`: words from limbs, the header
  root child's digest and hook, the genesis checks;
- the program (`chainSealT`): its parts hold separately (`sealT_parts`), every path ends at `T`
  (`sealT_ends`), `T` is the header root's limbs 108–123 (`sealT_T`), the genesis checks hold
  (`sealT_genesis`), the key and the output digest (`sealT_key`, `sealT_digest`).
-/
import StarkedAir.Circuit.ChainSealT
import StarkedAir.Circuit.ChainSealSound
import StarkedAir.Spec.Mmr
import StarkedAir.Circuit.ChainSealSet

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q Spec.Blake2s
open StarkedAir.HeaderTree (compress_congr compress_congr_m)
open StarkedAir.Spec.HeaderTree (hnode stWord toState)
open StarkedAir.Circuit.EpochRoot (isU32_pack isBase_lit chainOuts chainOuts_length)

variable {ρ : ℕ → Q}

/-! ### Booleans as QM31 values -/

/-- The QM31 value of a bit. -/
def bitQ (s : Bool) : Q := lit (if s then 1 else 0) 0 0 0

theorem bitQ_mul (s : Bool) (x : Q) : bitQ s * x = if s then x else ⟨0, 0, 0, 0⟩ := by
  cases s <;> ext <;> simp [bitQ, mul_def, cmul, lit]

/-- `cur + b (sib − cur)` and `sib − b (sib − cur)` select. -/
theorem sel_left (s : Bool) (cur sib : Q) : cur + bitQ s * (sib - cur) = if s then sib else cur := by
  rw [bitQ_mul]; cases s <;> ext <;> simp

theorem sel_right (s : Bool) (cur sib : Q) : sib - bitQ s * (sib - cur) = if s then cur else sib := by
  rw [bitQ_mul]; cases s <;> ext <;> simp

/-! ### States of eight u32 registers -/

/-- The state whose words are the registers' words. -/
def regState (ρ : ℕ → Q) (regs : List ℕ) : Spec.Sha256.State := toState fun w => word (ρ (regs.getD w 0))

theorem stWord_regState (regs : List ℕ) {w : ℕ} (hw : w < 8) : stWord (regState ρ regs) w = word (ρ (regs.getD w 0)) := by
  unfold regState toState; interval_cases w <;> rfl

theorem stWord_hnode' (a b : Spec.Sha256.State) {w : ℕ} (hw : w < 8) :
    stWord (hnode a b) w = compress h0 (fun k => if k < 8 then stWord a k else stWord b (k - 8)) 64 true w := by
  unfold hnode toState
  interval_cases w <;> rfl

/-! ### One step -/

/-- **One path step**: with side bit `sb` and active bit `sa`, on u32 current and sibling words, the
result is `Step.up ⟨sib, sb⟩ cur` when active, `cur` when not; a u32 wire either way. -/
theorem pathStep_sound {n : ℕ} {cur sib : List ℕ} {b a : ℕ} {sb sa : Bool} (h : Holds ρ (pathStep n cur sib b a).ops)
    (hb : ρ b = bitQ sb) (ha : ρ a = bitQ sa) :
    ∀ w < 8, word (ρ ((pathStep n cur sib b a).res.getD w 0)) =
        if sa then stWord (Spec.Mmr.Step.up ⟨regState ρ sib, sb⟩ (regState ρ cur)) w else word (ρ (cur.getD w 0)) := by
  dsimp only [pathStep] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨hsel, hblake⟩, hmux⟩ := h
  set msg := (List.range 8).map (fun w => n + 4 * w + 2) ++ (List.range 8).map (fun w => n + 4 * w + 3) with hmsg
  set H := blake2s (n + 32) msg 64 with hH
  -- the selections
  have selw : ∀ w < 8, ρ (n + 4 * w + 2) = (if sb then ρ (sib.getD w 0) else ρ (cur.getD w 0)) ∧
      ρ (n + 4 * w + 3) = (if sb then ρ (cur.getD w 0) else ρ (sib.getD w 0)) := by
    intro w hw
    have g := fun (o : Op) (ho : o ∈ _) => hsel o (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw, ho⟩)
    have d := g (.sub (n + 4 * w) (sib.getD w 0) (cur.getD w 0)) (by simp)
    have e := g (.mul (n + 4 * w + 1) b (n + 4 * w)) (by simp)
    have l := g (.add (n + 4 * w + 2) (cur.getD w 0) (n + 4 * w + 1)) (by simp)
    have r := g (.sub (n + 4 * w + 3) (sib.getD w 0) (n + 4 * w + 1)) (by simp)
    simp only [Op.holds] at d e l r
    rw [e, hb, d] at l r
    exact ⟨by rw [l, sel_left], by rw [r, sel_right]⟩
  -- the message words: the selected states' words
  have hm : ∀ q < 16, word (ρ (msg.getD q (n + 32))) =
      if q < 8 then stWord (if sb then regState ρ sib else regState ρ cur) q
      else stWord (if sb then regState ρ cur else regState ρ sib) (q - 8) := by
    intro q hq
    rw [hmsg, List.getD_eq_getElem _ _ (by simpa using hq)]
    by_cases h8 : q < 8
    · rw [List.getElem_append_left (by simpa using h8)]
      simp only [List.getElem_map, List.getElem_range, if_pos h8]
      rw [(selw q h8).1]
      cases sb <;> simp [stWord_regState _ h8]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range, if_neg h8]
      rw [(selw (q - 8) (by omega)).2]
      cases sb <;> simp [stWord_regState _ (show q - 8 < 8 by omega)]
  -- the compression is `hnode` of the selected states
  have hw := blake2s_sound hblake (by norm_num)
  have hpk := blake2s_res_pack hblake
  have hword : ∀ w < 8, word (ρ (H.res.getD w 0)) =
      stWord (Spec.Mmr.Step.up ⟨regState ρ sib, sb⟩ (regState ρ cur)) w := by
    intro w hw8
    have up : Spec.Mmr.Step.up ⟨regState ρ sib, sb⟩ (regState ρ cur) =
        hnode (if sb then regState ρ sib else regState ρ cur) (if sb then regState ρ cur else regState ρ sib) := by
      cases sb <;> rfl
    rw [hw w hw8, up, show nBlocks 64 = 0 + 1 from rfl, hashW_succ hw8, stWord_hnode' _ _ hw8]
    rw [compress_congr _ _ _ (fun i hi => hashW_zero hi) hw8]
    exact compress_congr_m _ _ _ (fun k hk => by simpa using hm k hk) w
  -- the mux
  intro w hw8
  have g := fun (o : Op) (ho : o ∈ _) => hmux o (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw8, ho⟩)
  have s := g (.sub (H.next + 3 * w) (H.res.getD w 0) (cur.getD w 0)) (by simp)
  have m := g (.mul (H.next + 3 * w + 1) a (H.next + 3 * w)) (by simp)
  have ad := g (.add (H.next + 3 * w + 2) (cur.getD w 0) (H.next + 3 * w + 1)) (by simp)
  simp only [Op.holds] at s m ad
  have hres : ((List.range 8).map (fun w => H.next + 3 * w + 2)).getD w 0 = H.next + 3 * w + 2 := by
    rw [List.getD_eq_getElem _ _ (by simpa using hw8)]; simp
  rw [hres, ad, m, ha, s, sel_left]
  cases sa
  · rfl
  · rw [if_pos rfl, if_pos rfl]; exact hword w hw8

/-! ### Paths -/

/-- A boolean register: base, `x (x − 1) = 0`. -/
theorem bitQ_of {x : Q} (hx : IsBase x) (h : x.a * (x.a - 1) = 0) : x = bitQ (decide (x.a = 1)) := by
  obtain ⟨hb, hc, hd⟩ := hx
  rcases mul_eq_zero.mp h with h0 | h1
  · have : ¬ x.a = 1 := by rw [h0]; exact zero_ne_one
    ext <;> simp [bitQ, lit, h0, hb, hc, hd, this]
  · have : x.a = 1 := sub_eq_zero.mp h1
    ext <;> simp [bitQ, lit, this, hb, hc, hd]

theorem state_ext {X Y : Spec.Sha256.State} (h : ∀ w < 8, stWord X w = stWord Y w) : X = Y := by
  obtain ⟨a, b, c, d, e, f, g, k⟩ := X
  obtain ⟨a', b', c', d', e', f', g', k'⟩ := Y
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num)
  have h3 := h 3 (by norm_num); have h4 := h 4 (by norm_num); have h5 := h 5 (by norm_num)
  have h6 := h 6 (by norm_num); have h7 := h 7 (by norm_num)
  simp only [stWord] at h0 h1 h2 h3 h4 h5 h6 h7
  simp [h0, h1, h2, h3, h4, h5, h6, h7]

/-- The steps `s, s + 1, …` (`k` of them) of a path, each taken when active. -/
def foldSteps (sib : ℕ → Spec.Sha256.State) (sb sa : ℕ → Bool) : ℕ → ℕ → Spec.Sha256.State → Spec.Sha256.State
  | _, 0, x => x
  | s, k + 1, x => foldSteps sib sb sa (s + 1) k (if sa s then Spec.Mmr.Step.up ⟨sib s, sb s⟩ x else x)

/-- **Chained steps.** -/
theorem pathSteps_sound {sibF : ℕ → List ℕ} {b a : ℕ → ℕ} {sb sa : ℕ → Bool} :
    ∀ (s k r : ℕ) (cur : List ℕ), Holds ρ (pathSteps sibF b a s k r cur).1 →
      (∀ j < k, ρ (b (s + j)) = bitQ (sb (s + j))) → (∀ j < k, ρ (a (s + j)) = bitQ (sa (s + j))) →
        regState ρ (pathSteps sibF b a s k r cur).2.1 =
          foldSteps (fun j => regState ρ (sibF j)) sb sa s k (regState ρ cur)
  | s, 0, r, cur, _, _, _ => rfl
  | s, k + 1, r, cur, h, hb, ha => by
    simp only [pathSteps] at h ⊢
    rw [holds_append] at h
    have st := pathStep_sound h.1 (by simpa using hb 0 (by omega)) (by simpa using ha 0 (by omega))
    have ih := pathSteps_sound (s + 1) k (pathStep r cur (sibF s) (b s) (a s)).next
      (pathStep r cur (sibF s) (b s) (a s)).res h.2
      (fun j hj => by rw [show s + 1 + j = s + (j + 1) by omega]; exact hb (j + 1) (by omega))
      (fun j hj => by rw [show s + 1 + j = s + (j + 1) by omega]; exact ha (j + 1) (by omega))
    rw [ih, foldSteps]
    congr 1
    apply state_ext
    intro w hw
    rw [stWord_regState _ hw, st w hw]
    split_ifs
    · rfl
    · rw [stWord_regState _ hw]

theorem foldSteps_off {sib : ℕ → Spec.Sha256.State} {sb : ℕ → Bool} {L : ℕ} :
    ∀ (s k : ℕ) (x : Spec.Sha256.State), L ≤ s → foldSteps sib sb (fun j => decide (j < L)) s k x = x
  | _, 0, _, _ => rfl
  | s, k + 1, x, h => by
    rw [foldSteps, if_neg (by simp; omega)]
    exact foldSteps_off (s + 1) k x (by omega)

/-- **The active prefix is the MMR path**: `L` active steps from `s` are `pathRoot`'s. -/
theorem foldSteps_prefix {sib : ℕ → Spec.Sha256.State} {sb : ℕ → Bool} {L : ℕ} :
    ∀ (s k : ℕ) (x : Spec.Sha256.State), s ≤ L → L ≤ s + k →
      foldSteps sib sb (fun j => decide (j < L)) s k x =
        Spec.Mmr.pathRoot x ((List.range (L - s)).map fun j => ⟨sib (s + j), sb (s + j)⟩)
  | s, 0, x, h1, h2 => by
    rw [show L - s = 0 by omega]; rfl
  | s, k + 1, x, h1, h2 => by
    rw [foldSteps]
    by_cases hs : s < L
    · rw [if_pos (by simpa using hs), foldSteps_prefix (s + 1) k _ (by omega) (by omega),
        show L - s = (L - (s + 1)) + 1 by omega, List.range_succ_eq_map]
      simp only [List.map_cons, List.map_map, Spec.Mmr.pathRoot, List.foldl_cons, Nat.add_zero]
      congr 1
      apply List.map_congr_left
      intro j _
      simp [Function.comp_def, Nat.add_assoc, Nat.add_comm 1 j]
    · rw [if_neg (by simpa using hs), foldSteps_off (s + 1) k x (by omega), show L - s = 0 by omega]
      rfl

/-- **The bits packed into a word**: `Σ b_{lo+j} 2^j` over `k ≤ 30` bits. -/
theorem bitsWord_sound {n lo k : ℕ} {b pw : ℕ → ℕ} {sb : ℕ → Bool} {C : Consts}
    (h : Holds ρ (bitsWord n b pw lo k C).ops) (hC : ConstsOk ρ C)
    (hpw : ∀ j < k, ρ (pw j) = lit (2 ^ j) 0 0 0) (hb : ∀ j < k, ρ (b (lo + j)) = bitQ (sb (lo + j))) :
    IsBase (ρ (bitsWord n b pw lo k C).res) ∧
      (ρ (bitsWord n b pw lo k C).res).a = (((Finset.range k).sum fun j => if sb (lo + j) then 2 ^ j else 0 : ℕ) : F) := by
  dsimp only [bitsWord] at h ⊢
  have part : ∀ j < k, IsBase (ρ (n + 2 * j + 1)) ∧
      (ρ (n + 2 * j + 1)).a = (((Finset.range (j + 1)).sum fun i => if sb (lo + i) then 2 ^ i else 0 : ℕ) : F) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have g := fun (o : Op) (ho : o ∈ _) => h o (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hj, ho⟩)
      have m := g (.mul (n + 2 * 0) (b (lo + 0)) (pw 0)) (by simp)
      have ad := g (.add (n + 2 * 0 + 1) C.zero (n + 2 * 0)) (by simp)
      simp only [Op.holds] at m ad
      rw [ad, m, hC.zero, hb 0 hj, hpw 0 hj]
      cases hs : sb (lo + 0) <;> simp only [Nat.add_zero] at hs <;> refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp [bitQ, lit, mul_def, cmul, hs]
    | succ j ih =>
      intro hj
      obtain ⟨b0, v0⟩ := ih (by omega)
      have g := fun (o : Op) (ho : o ∈ _) => h o (List.mem_flatMap.mpr ⟨j + 1, List.mem_range.mpr hj, ho⟩)
      have m := g (.mul (n + 2 * (j + 1)) (b (lo + (j + 1))) (pw (j + 1))) (by simp)
      have ad := g (.add (n + 2 * (j + 1) + 1) (n + 2 * (j + 1) - 1) (n + 2 * (j + 1))) (by simp)
      simp only [Op.holds] at m ad
      rw [show n + 2 * (j + 1) - 1 = n + 2 * j + 1 by omega] at ad
      rw [ad, m, hb (j + 1) hj, hpw (j + 1) hj, Finset.sum_range_succ]
      obtain ⟨c1, c2, c3⟩ := b0
      cases hs : sb (lo + (j + 1)) <;> refine ⟨⟨?_, ?_, ?_⟩, ?_⟩ <;> simp [bitQ, lit, mul_def, cmul, c1, c2, c3, v0, hs]
  rcases k with _ | k
  · simp [hC.zero, lit]; exact isBase_lit 0
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, if_false]
    rw [show n + 2 * (k + 1) - 1 = n + 2 * k + 1 by omega]
    exact part k (by omega)

/-- **An inclusion path of `D ≤ 60` steps is sound.** For some length `L < 65` (the length register's
value), when `L ≤ D` the result is the MMR spec's `pathRoot` of the leaf
over the first `L` steps, each with its guessed sibling (`sibS`) and side bit (`side`); the two packed
words are the side bits `0 … 29` and `30 … D − 1`. -/
theorem pathOps_sound {n e D : ℕ} {leaf : List ℕ} {C : Consts} {pw : ℕ → ℕ}
    (h : Holds ρ (pathOps n e leaf D C pw).ops) (hC : ConstsOk ρ C) (hpw : ∀ j < 30, ρ (pw j) = lit (2 ^ j) 0 0 0)
    (hD : D ≤ 60) :
    let side : ℕ → Bool := fun s => decide ((ρ (n + 40 * D + 4 * s)).a = 1)
    let sibS : ℕ → Spec.Sha256.State := fun s =>
      regState ρ ((((List.range D).map fun s => guessHash (n + 40 * s) (e + 8 * s)).getD s ⟨[], [], 0⟩).res)
    ∃ L : ℕ, L < 65 ∧ (ρ (pathOps n e leaf D C pw).res.len).a = (L : F) ∧
      (L ≤ D → regState ρ (pathOps n e leaf D C pw).res.res =
        Spec.Mmr.pathRoot (regState ρ leaf) ((List.range L).map fun s => ⟨sibS s, side s⟩)) ∧
      (ρ (pathOps n e leaf D C pw).res.sLo).a =
        (((Finset.range (min D 30)).sum fun j => if side j then 2 ^ j else 0 : ℕ) : F) ∧
      (ρ (pathOps n e leaf D C pw).res.sHi).a =
        (((Finset.range (D - 30)).sum fun j => if side (30 + j) then 2 ^ j else 0 : ℕ) : F) := by
  intro side sibS
  dsimp only [pathOps] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, hbits⟩, -⟩, hoh⟩, hlt⟩, hst⟩, hlo⟩, hhi⟩ := h
  set nb := n + 40 * D
  set nl := nb + 4 * D
  -- the side bits are booleans
  have hb : ∀ s < D, ρ (nb + 4 * s) = bitQ (side s) := by
    intro s hs
    have g := fun (o : Op) (ho : o ∈ _) => hbits o (List.mem_flatMap.mpr ⟨s, List.mem_range.mpr hs, ho⟩)
    have tg := g _ List.mem_cons_self
    have s1 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have m2 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have eq := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    simp only [Op.holds] at tg s1 m2 eq
    have b2 : IsBase (ρ (nb + 4 * s + 1)) := by rw [s1, hC.one]; exact EpochRoot.isBase_sub tg (isBase_lit 1)
    have := congrArg Q.a (m2.symm.trans (eq.trans hC.zero))
    rw [EpochRoot.mul_a tg b2, s1, sub_a, hC.one] at this
    exact bitQ_of tg (by simpa [lit] using this)
  -- the length and the active mask
  obtain ⟨L, hL, hLx, hbitsL⟩ := oneHot65_sound hoh hC
  have hohr : ∀ j < 65, ((List.range 65).map (nl + 1 + ·)).getD j 0 = nl + 1 + j := fun j hj => getD_map_range hj
  have hltm := ltMask_sound hlt hC hL (fun j hj => by
    show IsBase (ρ (((List.range 65).map (nl + 1 + ·)).getD j 0)) ∧
      (ρ (((List.range 65).map (nl + 1 + ·)).getD j 0)).a = _
    rw [hohr j hj]; exact hbitsL j hj)
  have ha : ∀ s < D, ρ ((ltMask (oneHot65 (nl + 1) nl C).next (oneHot65 (nl + 1) nl C).res C).res.getD s 0) =
      bitQ (decide (s < L)) := by
    intro s hs
    have e : ((List.range 64).map ((oneHot65 (nl + 1) nl C).next + ·)).getD s 0 = (oneHot65 (nl + 1) nl C).next + s :=
      getD_map_range (by omega)
    show ρ (((List.range 64).map ((oneHot65 (nl + 1) nl C).next + ·)).getD s 0) = _
    rw [e]
    obtain ⟨hbase, hv⟩ := hltm s (by omega)
    rw [bitQ_of hbase (by rw [hv]; split_ifs <;> simp)]
    congr 1
    rw [hv]; by_cases hsL : s < L <;> simp [hsL]
  -- the steps
  have ps := pathSteps_sound (sb := side) (sa := fun s => decide (s < L)) 0 D _ leaf hst
    (fun j hj => by simpa using hb j hj) (fun j hj => by simpa using ha j hj)
  refine ⟨L, hL, hLx, fun hLD => ?_, ?_, ?_⟩
  · rw [ps, foldSteps_prefix 0 D _ (by omega) (by omega)]
    simp only [Nat.sub_zero, Nat.zero_add]
    rfl
  · have := (bitsWord_sound hlo hC (fun j hj => hpw j (by omega)) (fun j hj => by
      simpa using hb j (by omega))).2
    simpa using this
  · exact (bitsWord_sound hhi hC (fun j hj => hpw j (by omega)) (fun j hj => hb (30 + j) (by omega))).2

/-! ### Words, the header root child, the genesis checks -/

theorem packN_res_getD (n k : ℕ) (limbs : List ℕ) (C : Consts) {w : ℕ} (hw : w < k) :
    (packN n limbs k C).res.getD w 0 = n + 2 * w + 1 := by
  dsimp only [packN]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

/-- `k` u32 wires from `2k` base limbs. -/
theorem packN_sound {n k : ℕ} {limbs : List ℕ} {C : Consts} (h : Holds ρ (packN n limbs k C).ops) (hC : ConstsOk ρ C)
    (hl : ∀ j < 2 * k, IsBase (ρ (limbs.getD j 0))) :
    ∀ w < k, ρ ((packN n limbs k C).res.getD w 0) = ⟨(ρ (limbs.getD (2 * w) 0)).a, (ρ (limbs.getD (2 * w + 1) 0)).a, 0, 0⟩ := by
  intro w hw
  rw [packN_res_getD n k limbs C hw]
  dsimp only [packN] at h
  have g : ∀ o ∈ [Op.mul (n + 2 * w) (limbs.getD (2 * w + 1) 0) C.e1, .add (n + 2 * w + 1) (limbs.getD (2 * w) 0) (n + 2 * w)],
      o.holds ρ := fun o ho => h o (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw, ho⟩)
  have m := g _ List.mem_cons_self
  have a := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [Op.holds] at m a
  rw [a, m, hC.e1, lohi (hl _ (by omega)) (hl _ (by omega))]

theorem hdrChild_key_length (n e hook : ℕ) : (hdrChild n e hook).res.key.length = 8 := by simp [hdrChild, guessHash]
theorem hdrChild_chash_length (n e hook : ℕ) : (hdrChild n e hook).res.chash.length = 8 := by simp [hdrChild]

/-- The header root child's public inputs are base values. -/
theorem hdrChild_base {n e hook : ℕ} (h : Holds ρ (hdrChild n e hook).ops) : ∀ k < N_PUB, IsBase (ρ (n + k)) := by
  intro k hk
  dsimp only [hdrChild] at h
  simp only [holds_append] at h
  have := h.1.1.1.1 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  simpa [Op.holds] using this

/-- The header root's 124 public inputs as words. -/
def hvals (v : ℕ → F) : List Word := (List.range N_PUB).map fun i => BitVec.ofNat 32 (v i).val

/-- **The header root child's digest** is `Blake2s(key ‖ public inputs)` (`leaf.pubsDigest`). -/
theorem hdrChild_digest {n e hook : ℕ} (h : Holds ρ (hdrChild n e hook).ops) :
    wordsOf ρ (hdrChild n e hook).res.digest =
      BlockRec.H (wordsOf ρ (hdrChild n e hook).res.key ++ hvals (fun k => (ρ (n + k)).a)) := by
  dsimp only [hdrChild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨-, -⟩, hdg⟩, -⟩, -⟩ := h
  rw [BlockRec.wordsOf_eq (SetTree.pubsDigest_length _ _ _) (pubsDigest_sound hdg (by simp [BlockRec.guessHash_length, N_PUB]))]
  simp only [BlockRec.H, wordsOf, hvals, List.length_append, List.length_map, List.length_range,
    BlockRec.guessHash_length, List.map_map]
  rfl

theorem hdrChild_hook (n e hook : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook hook (root ++ (hdrChild n e hook).res.digest) (hdrChild n e hook).res.chash ∈ (hdrChild n e hook).ops :=
  ⟨_, BlockRec.guessHash_length _ _, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

theorem genesisChecks_vals : ∀ c ∈ HeaderTree.genesisChecks, c.2 = 0 ∨ c.2 = 65535 := by decide

/-- **The genesis checks hold** on the public inputs `p` (`HeaderTree.genesis_checks_sound`'s hypothesis). -/
theorem genesisOps_sound {p : ℕ → ℕ} {C : Consts} {k : ℕ} (h : Holds ρ (genesisOps p C k)) (hC : ConstsOk ρ C)
    (hk : ρ k = lit 65535 0 0 0) : ∀ c ∈ HeaderTree.genesisChecks, ((ρ (p c.1)).a).val = c.2 := by
  intro c hc
  have e := h _ (List.mem_map.mpr ⟨c, hc, rfl⟩)
  simp only [Op.holds] at e
  rcases genesisChecks_vals c hc with h0 | h1
  · rw [e, if_pos h0, hC.zero, h0]; rfl
  · rw [e, if_neg (by omega), hk, h1]
    exact val_cast (by unfold P; norm_num)

/-! ### The program -/

theorem chainSealT_ops (ms : List ℕ) (gen : Bool) (D : ℕ) : (chainSealT ms gen D).ops =
    let Q := partsT ms gen D
    let P := Q.P
    P.J.ops ++ P.sets.flatMap (·.ops) ++ P.roots.flatMap (·.ops) ++ P.rests.flatMap (·.ops) ++ P.C.ops ++
      P.chals.flatMap (·.ops) ++ P.opens.flatMap (·.ops) ++ P.accs.flatMap (·.ops) ++ P.checks.ops ++
      Q.hc.ops ++ [.const Q.k65535 65535 0 0 0] ++ Q.pws ++ Q.gen ++ Q.T.ops ++ Q.tip.ops ++ Q.hgt.ops ++ Q.work.ops ++
      Q.gleaf ++ Q.paths.flatMap (·.ops) ++ Q.ends ++ Q.key.ops ++ Q.dg.ops := rfl

theorem partsT_P (ms : List ℕ) (gen : Bool) (D : ℕ) : (partsT ms gen D).P = parts ms gen := rfl

/-- The parts of `chainSealT` hold separately. -/
structure THolds (ms : List ℕ) (gen : Bool) (D : ℕ) (ρ : ℕ → Q) : Prop where
  sealOk : Holds ρ ((parts ms gen).J.ops ++ (parts ms gen).sets.flatMap (·.ops) ++ (parts ms gen).roots.flatMap (·.ops) ++
    (parts ms gen).rests.flatMap (·.ops) ++ (parts ms gen).C.ops ++ (parts ms gen).chals.flatMap (·.ops) ++
    (parts ms gen).opens.flatMap (·.ops) ++ (parts ms gen).accs.flatMap (·.ops) ++ (parts ms gen).checks.ops)
  hc : Holds ρ (partsT ms gen D).hc.ops
  k65535 : ρ (partsT ms gen D).k65535 = lit 65535 0 0 0
  pws : Holds ρ (partsT ms gen D).pws
  genOk : Holds ρ (partsT ms gen D).gen
  tW : Holds ρ (partsT ms gen D).T.ops
  tip : Holds ρ (partsT ms gen D).tip.ops
  hgt : Holds ρ (partsT ms gen D).hgt.ops
  work : Holds ρ (partsT ms gen D).work.ops
  gleaf : Holds ρ (partsT ms gen D).gleaf
  paths : Holds ρ ((partsT ms gen D).paths.flatMap (·.ops))
  ends : Holds ρ (partsT ms gen D).ends
  keyOk : Holds ρ (partsT ms gen D).key.ops
  dg : Holds ρ (partsT ms gen D).dg.ops

theorem sealT_parts {ms : List ℕ} {gen : Bool} {D : ℕ} (h : Holds ρ (chainSealT ms gen D).ops) : THolds ms gen D ρ := by
  rw [chainSealT_ops] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩,
    h17⟩, h18⟩, h19⟩, h20⟩, h21⟩, h22⟩ := h
  have k := h11 _ List.mem_cons_self
  simp only [Op.holds] at k
  refine ⟨?_, h10, k, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22⟩
  simp only [holds_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩

/-- The seal's own parts hold: every `ChainSealSound` theorem about `parts ms gen` applies. -/
theorem sealT_C {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) : ConstsOk ρ (parts ms gen).C.res := by
  have := h.sealOk
  simp only [holds_append] at this
  obtain ⟨⟨⟨⟨⟨-, hC⟩, -⟩, -⟩, -⟩, -⟩ := this
  exact consts_sound hC

/-- The constants `2^j`. -/
theorem sealT_pw {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) :
    ∀ j < 30, ρ ((partsT ms gen D).pw j) = lit (2 ^ j) 0 0 0 := by
  intro j hj
  have := h.pws _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Op.holds] at this
  exact this

/-- **The genesis checks hold** on the header root's public inputs. -/
theorem sealT_genesis {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) :
    ∀ c ∈ HeaderTree.genesisChecks, ((ρ ((partsT ms gen D).hc.res.pubs c.1)).a).val = c.2 :=
  genesisOps_sound h.genOk (sealT_C h) h.k65535

/-- **`T` is the header root's limbs 108–123**, as u32 wires. -/
theorem sealT_T {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) :
    ∀ w < 8, ρ ((partsT ms gen D).T.res.getD w 0) =
      ⟨(ρ ((partsT ms gen D).hc.res.pubs (108 + 2 * w))).a, (ρ ((partsT ms gen D).hc.res.pubs (108 + 2 * w + 1))).a, 0, 0⟩ := by
  have hb := hdrChild_base h.hc
  have g : ∀ j < 16, ((List.range 16).map (fun j => (partsT ms gen D).hc.res.pubs (108 + j))).getD j 0 =
      (partsT ms gen D).hc.res.pubs (108 + j) := fun j hj => getD_map_range hj
  intro w hw
  have := packN_sound (limbs := (List.range 16).map (fun j => (partsT ms gen D).hc.res.pubs (108 + j)))
    (C := (parts ms gen).C.res) h.tW (sealT_C h)
    (fun j hj => by rw [g j (by omega)]; exact hb _ (by unfold N_PUB; omega)) w hw
  rw [g (2 * w) (by omega), g (2 * w + 1) (by omega)] at this
  rw [← Nat.add_assoc] at this
  exact this

/-- **Every path ends at `T`.** -/
theorem sealT_ends {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) :
    ∀ pa ∈ (partsT ms gen D).paths, ∀ w < 8, ρ (pa.res.res.getD w 0) = ρ ((partsT ms gen D).T.res.getD w 0) := by
  intro pa hpa w hw
  have := h.ends _ (List.mem_flatMap.mpr ⟨pa, hpa, List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩⟩)
  simp only [Op.holds] at this
  exact this

/-- The genesis block hash as a state. -/
def genesisState : Spec.Sha256.State := toState fun w => BitVec.ofNat 32 (genesisHash.getD w 0)

theorem genesisHash_lt : ∀ w < 8, genesisHash.getD w 0 < 2 ^ 32 := by decide

/-- A path's statement: for some length `L < 65` in its length register, when `L ≤ D`, `T` is the path
root of `leaf` over its first `L` steps (guessed siblings, side bits), and the packed side words. -/
def PathOk (ρ : ℕ → Q) (n e D : ℕ) (leaf : Spec.Sha256.State) (Tst : Spec.Sha256.State) (pr : PathRegs) : Prop :=
  ∃ L : ℕ, L < 65 ∧ (ρ pr.len).a = (L : F) ∧
    (L ≤ D → Tst = Spec.Mmr.pathRoot leaf ((List.range L).map fun s =>
      ⟨regState ρ ((((List.range D).map fun s => guessHash (n + 40 * s) (e + 8 * s)).getD s ⟨[], [], 0⟩).res),
       decide ((ρ (n + 40 * D + 4 * s)).a = 1)⟩)) ∧
    (ρ pr.sLo).a = (((Finset.range (min D 30)).sum fun j =>
      if decide ((ρ (n + 40 * D + 4 * j)).a = 1) then 2 ^ j else 0 : ℕ) : F) ∧
    (ρ pr.sHi).a = (((Finset.range (D - 30)).sum fun j =>
      if decide ((ρ (n + 40 * D + 4 * (30 + j))).a = 1) then 2 ^ j else 0 : ℕ) : F)

theorem pathOk_of {n e D : ℕ} {leaf : List ℕ} {C : Consts} {pw : ℕ → ℕ} {Tst : Spec.Sha256.State}
    (h : Holds ρ (pathOps n e leaf D C pw).ops) (hC : ConstsOk ρ C) (hpw : ∀ j < 30, ρ (pw j) = lit (2 ^ j) 0 0 0)
    (hD : D ≤ 60) (hT : regState ρ (pathOps n e leaf D C pw).res.res = Tst) :
    PathOk ρ n e D (regState ρ leaf) Tst (pathOps n e leaf D C pw).res := by
  obtain ⟨L, hL, hLx, hp, hlo, hhi⟩ := pathOps_sound h hC hpw hD
  exact ⟨L, hL, hLx, fun hLD => by rw [← hT]; exact hp hLD, hlo, hhi⟩

/-- `T` as a state: the words of the packed limbs. -/
noncomputable def tState (ρ : ℕ → Q) (ms : List ℕ) (gen : Bool) (D : ℕ) : Spec.Sha256.State :=
  regState ρ (partsT ms gen D).T.res

theorem regState_ends {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) {pa : Out PathRegs}
    (hpa : pa ∈ (partsT ms gen D).paths) : regState ρ pa.res.res = tState ρ ms gen D := by
  apply state_ext
  intro w hw
  rw [stWord_regState _ hw, tState, stWord_regState _ hw, sealT_ends h pa hpa w hw]

/-- The genesis path and the children's paths, as `partsT` builds them. -/
def gpathT (ms : List ℕ) (gen : Bool) (D : ℕ) : Out PathRegs :=
  pathOps ((partsT ms gen D).work.next + 8) (eState ms gen (nSets ms.length gen) + N_PUB + 16)
    ((List.range 8).map ((partsT ms gen D).work.next + ·)) D (parts ms gen).C.res (partsT ms gen D).pw

def cpathsT (ms : List ℕ) (gen : Bool) (D : ℕ) : List (Out PathRegs) :=
  chainOuts (fun p r =>
      let ic := (childIdx ms).getD p (0, 0)
      let lw := packN r (childLimbs (parts ms gen) ic.1 ic.2) 8 (parts ms gen).C.res
      let pa := pathOps lw.next (eState ms gen (nSets ms.length gen) + N_PUB + 16 + pathExt D * (p + 1)) lw.res D
        (parts ms gen).C.res (partsT ms gen D).pw
      (⟨lw.ops ++ pa.ops, pa.res, pa.next⟩ : Out PathRegs)) (gpathT ms gen D).next (childIdx ms).length

theorem partsT_paths (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (partsT ms gen D).paths = gpathT ms gen D :: cpathsT ms gen D := rfl

/-- **The genesis block hash reaches `T`.** -/
theorem sealT_gpath {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) (hD : D ≤ 60) :
    ∃ n e, PathOk ρ n e D genesisState (tState ρ ms gen D) (gpathT ms gen D).res := by
  have hp : Holds ρ (gpathT ms gen D).ops := fun o ho => h.paths o (by
    rw [partsT_paths, List.flatMap_cons]; exact List.mem_append_left _ ho)
  have hmem : gpathT ms gen D ∈ (partsT ms gen D).paths := by rw [partsT_paths]; exact List.mem_cons_self
  -- the leaf: eight constant words
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
  exact ⟨_, _, this⟩

/-- **Each epoch child's block-hash root reaches `T`**: path `p + 1` starts from the packed words of
child `(childIdx ms)[p]`'s limbs. -/
theorem sealT_cpath {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ) (hD : D ≤ 60) {p : ℕ}
    (hp : p < (childIdx ms).length) :
    ∃ n e r, Holds ρ (packN r (childLimbs (parts ms gen) ((childIdx ms).getD p (0, 0)).1 ((childIdx ms).getD p (0, 0)).2) 8
        (parts ms gen).C.res).ops ∧
      PathOk ρ n e D (regState ρ (packN r (childLimbs (parts ms gen) ((childIdx ms).getD p (0, 0)).1
        ((childIdx ms).getD p (0, 0)).2) 8 (parts ms gen).C.res).res) (tState ρ ms gen D)
        ((cpathsT ms gen D)[p]'(by rw [cpathsT, chainOuts_length]; exact hp)).res := by
  have hcall : Holds ρ ((cpathsT ms gen D).flatMap (·.ops)) := fun o ho => h.paths o (by
    rw [partsT_paths, List.flatMap_cons]; exact List.mem_append_right _ ho)
  obtain ⟨r, hr, hh⟩ := EpochRoot.chainOuts_holds hp hcall
  simp only [holds_append] at hh
  have hmem : (cpathsT ms gen D)[p]'(by rw [cpathsT, chainOuts_length]; exact hp) ∈ (partsT ms gen D).paths := by
    rw [partsT_paths]; exact List.mem_cons_of_mem _ (List.getElem_mem _)
  have hr' : (cpathsT ms gen D)[p]'(by rw [cpathsT, chainOuts_length]; exact hp) = _ := hr
  have hT := regState_ends h hmem
  rw [hr'] at hT
  have po := pathOk_of hh.2 (sealT_C h) (sealT_pw h) hD hT
  rw [hr']
  exact ⟨_, _, r, hh.1, po⟩

/-- **The key**: Blake2s over every child's circuit hash and key (the join, the set roots, the header
chain root). -/
theorem sealT_key {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ)
    (hB : 4 * ((parts ms gen).J.res.chash ++ (parts ms gen).J.res.key ++
      (parts ms gen).sets.flatMap (fun c => c.res.chash ++ c.res.key) ++
      (partsT ms gen D).hc.res.chash ++ (partsT ms gen D).hc.res.key).length < 2 ^ 32) :
    let msg := (parts ms gen).J.res.chash ++ (parts ms gen).J.res.key ++
      (parts ms gen).sets.flatMap (fun c => c.res.chash ++ c.res.key) ++
      (partsT ms gen D).hc.res.chash ++ (partsT ms gen D).hc.res.key
    ∀ i < 8, word (ρ ((partsT ms gen D).key.res.getD i 0)) = blake2sWords (wordsOf ρ msg) (4 * msg.length) i :=
  fun i hi => blake2s_words h.keyOk hB i hi

theorem chainSealT_results (ms : List ℕ) (gen : Bool) (D : ℕ) :
    (chainSealT ms gen D).results = (partsT ms gen D).dg.res := rfl

/-- **The output digest**: Blake2s of the message's words (`partsT.msg`); the range words are
`m31_to_u32` of the join's `a` and `b`, each path's three words of its side words and length. -/
theorem sealT_digest {ms : List ℕ} {gen : Bool} {D : ℕ} (h : THolds ms gen D ρ)
    (hB : 4 * (partsT ms gen D).msg.length < 2 ^ 32) :
    let Q := partsT ms gen D
    word (ρ Q.key.next) = BitVec.ofNat 32 (ρ (parts ms gen).J.res.lo).a.val ∧
    word (ρ (Q.key.next + 1)) = BitVec.ofNat 32 (ρ (parts ms gen).J.res.hi).a.val ∧
    (∀ p < Q.paths.length, let pa := (Q.paths.getD p ⟨[], ⟨[], 0, 0, 0⟩, 0⟩).res
      word (ρ (Q.key.next + 2 + 3 * p)) = BitVec.ofNat 32 (ρ pa.sLo).a.val ∧
      word (ρ (Q.key.next + 2 + 3 * p + 1)) = BitVec.ofNat 32 (ρ pa.sHi).a.val ∧
      word (ρ (Q.key.next + 2 + 3 * p + 2)) = BitVec.ofNat 32 (ρ pa.len).a.val) ∧
    ∀ i < 8, word (ρ ((chainSealT ms gen D).results.getD i 0)) = blake2sWords (wordsOf ρ Q.msg) (4 * Q.msg.length) i := by
  intro Q
  have hd := h.dg
  have e : Q.dg.ops = [Op.m2u Q.key.next (parts ms gen).J.res.lo, .m2u (Q.key.next + 1) (parts ms gen).J.res.hi] ++
      ((List.range Q.paths.length).flatMap fun p =>
        let pa := (Q.paths.getD p ⟨[], ⟨[], 0, 0, 0⟩, 0⟩).res
        [Op.m2u (Q.key.next + 2 + 3 * p) pa.sLo, .m2u (Q.key.next + 2 + 3 * p + 1) pa.sHi,
         .m2u (Q.key.next + 2 + 3 * p + 2) pa.len]) ++
      (blake2s (Q.key.next + 2 + 3 * Q.paths.length) Q.msg (4 * Q.msg.length)).ops := rfl
  rw [e, holds_append, holds_append] at hd
  obtain ⟨⟨hm, hp⟩, hb⟩ := hd
  refine ⟨EpochRoot.m2u_word (hm _ List.mem_cons_self),
    EpochRoot.m2u_word (hm _ (List.mem_cons_of_mem _ List.mem_cons_self)), fun p hp' => ?_, fun i hi => ?_⟩
  · have g := fun (o : Op) (ho : o ∈ _) => hp o (List.mem_flatMap.mpr ⟨p, List.mem_range.mpr hp', ho⟩)
    exact ⟨EpochRoot.m2u_word (g _ List.mem_cons_self), EpochRoot.m2u_word (g _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      EpochRoot.m2u_word (g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
  · rw [chainSealT_results]
    exact blake2s_words hb hB i hi

-- The mainnet SEAL-T key message (80 + 16 words) and output message (176 words).
#guard ((parts [16, 16] false).J.res.chash ++ (parts [16, 16] false).J.res.key ++
  (parts [16, 16] false).sets.flatMap (fun c => c.res.chash ++ c.res.key) ++
  (partsT [16, 16] false 32).hc.res.chash ++ (partsT [16, 16] false 32).hc.res.key).length = 96

end StarkedAir.Circuit.ChainSeal
