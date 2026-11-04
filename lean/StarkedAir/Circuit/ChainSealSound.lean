/-
**The chain seal's soundness** (`Circuit/ChainSeal.lean`), gadget by gadget, in the style of
`EpochJoinSound` and `EpochRootSound`. Every theorem is about a satisfying register assignment `ρ`
(`Holds ρ ops`): what the gates force.

Children and openings:
- `setChild_digest`, `setChild_hook`: a set root child's digest is `pubsDigest(key, limbs)` (`sd`) and its
  hook is called with (its preprocessed root, that digest), outputting its circuit hash;
- `rootOpen_out`, `rootOpen_zeros`: an epoch root's opening digests to Blake2s of
  `key ‖ fin ‖ prev? ‖ from ‖ to ‖ rest`; from genesis its `prev` is 8 zero words;
- `restOpen_sound`: `rest` is Blake2s of the opened values (base registers) as words;
- `accChain_sound`: each `acc` is Blake2s of the previous one (`out₀` for the first) and the next output.

The set opening's gadgets:
- `consts_sound` (`ConstsOk`), `qm_sound`, `coords_sound`, `chal_sound`: the 112 challenge limbs are
  `γ`, `z` and the coordinates of `α^0 … α^25` (`qpow`);
- `byteOps_sound`, `count_sound`: bytes and the count from its bytes (below `2^30`);
- `packW_sound`, `packEq_sound`, `packBytes_sound`: 16-bit limbs and bytes packed into u32 wires;
- `oneHot65_sound`, `ltMask_sound`, `mask_sound`: the pending-length one-hot and the byte mask;
- `counter_sound`: the final Blake2s counter `64 nb + plen` as two u32 words;
- `compressFinal_sound`: one Blake2s compression from a chaining value with the last flag (RFC 7693 `F`).
-/
import StarkedAir.Circuit.ChainSeal
import StarkedAir.Circuit.EpochJoinSound
import StarkedAir.Circuit.SetTreeSound

namespace StarkedAir.Circuit.ChainSeal

open StarkedAir StarkedAir.Circuit Q Spec.Blake2s
open StarkedAir.Circuit.EpochRoot (restOut_sound chainOuts_holds chainOuts_length lastNext isBase_lit isBase_add
  isBase_sub isBase_mul mul_a one_hot m2u_word)
open StarkedAir.Circuit.EpochJoin (Child msg_words)
open StarkedAir.Circuit.BlockNode (lt30)
open StarkedAir.Circuit.SetTree (sd pubsDigest_sd)

variable {ρ : ℕ → Q}

/-! ### Small algebra -/

theorem mul_e1 {x : Q} (hx : IsBase x) : x * lit 0 1 0 0 = ⟨0, x.a, 0, 0⟩ := by
  obtain ⟨b, c, d⟩ := hx; ext <;> simp [mul_def, cmul, lit, b, c, d]
theorem mul_e2 {x : Q} (hx : IsBase x) : x * lit 0 0 1 0 = ⟨0, 0, x.a, 0⟩ := by
  obtain ⟨b, c, d⟩ := hx; ext <;> simp [mul_def, cmul, lit, b, c, d]
theorem mul_e3 {x : Q} (hx : IsBase x) : x * lit 0 0 0 1 = ⟨0, 0, 0, x.a⟩ := by
  obtain ⟨b, c, d⟩ := hx; ext <;> simp [mul_def, cmul, lit, b, c, d]

theorem base_a {x : Q} (hx : IsBase x) : x = ⟨x.a, 0, 0, 0⟩ := by
  obtain ⟨b, c, d⟩ := hx; ext <;> simp [b, c, d]

/-- A base value times a small literal, as a natural. -/
theorem val_mul_lit {x : F} {m : ℕ} (hmP : m < P) (hm : x.val * m < P) : (x * (m : F)).val = x.val * m := by
  rw [ZMod.val_mul_of_lt (by rw [val_cast hmP]; exact hm), val_cast hmP]

theorem val_add_small {x y : F} (h : x.val + y.val < P) : (x + y).val = x.val + y.val := ZMod.val_add_of_lt h

/-- `P` as a numeral, for `omega`. -/
theorem lt_P {a : ℕ} (h : a < 2147483647) : a < P := h

/-! ### Children -/

theorem setChild_key_length (n e hook : ℕ) : (setChild n e hook).res.key.length = 8 := by simp [setChild, guessHash]
theorem setChild_chash_length (n e hook : ℕ) : (setChild n e hook).res.chash.length = 8 := by simp [setChild]

/-- A set root child's summary limbs are base values. -/
theorem setChild_base {n e hook : ℕ} (h : Holds ρ (setChild n e hook).ops) : ∀ k < NS, IsBase (ρ (n + k)) := by
  intro k hk
  dsimp only [setChild] at h
  simp only [holds_append] at h
  have := h.1.1.1.1 _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  simpa [Op.holds] using this

/-- A set root child's digest is `pubsDigest(key, limbs)`. -/
theorem setChild_digest {n e hook : ℕ} (h : Holds ρ (setChild n e hook).ops) :
    wordsOf ρ (setChild n e hook).res.digest = sd (wordsOf ρ (setChild n e hook).res.key) (fun k => (ρ (n + k)).a) := by
  dsimp only [setChild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨-, -⟩, hdg⟩, -⟩, -⟩ := h
  exact pubsDigest_sd (f := (n + ·)) (BlockRec.guessHash_length _ _) hdg

theorem setChild_hook (n e hook : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook hook (root ++ (setChild n e hook).res.digest) (setChild n e hook).res.chash ∈ (setChild n e hook).ops :=
  ⟨_, BlockRec.guessHash_length _ _, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

/-- An epoch root's opening as words: `key ‖ fin ‖ prev (prevV) ‖ from ‖ to ‖ rest`. -/
def openWords (ρ : ℕ → Q) (R : RootRegs) (prevV : Bool) : List Word :=
  wordsOf ρ R.key ++ wordsOf ρ R.fin ++ (if prevV then wordsOf ρ R.prev else []) ++
    [BitVec.ofNat 32 (ρ R.lo).a.val, BitVec.ofNat 32 (ρ R.hi).a.val] ++ wordsOf ρ R.rest

theorem rootOpen_lengths (n e : ℕ) (prevV : Bool) :
    (rootOpen n e prevV).res.key.length = 8 ∧ (rootOpen n e prevV).res.fin.length = 8 ∧
    (rootOpen n e prevV).res.prev.length = 8 ∧ (rootOpen n e prevV).res.rest.length = 8 ∧
    (rootOpen n e prevV).res.out.length = 8 := by
  cases prevV <;> simp [rootOpen, BlockRec.guessHash_length, BlockRec.blake2s_length]

/-- The opening's range registers are base values. -/
theorem rootOpen_base {n e : ℕ} {prevV : Bool} (h : Holds ρ (rootOpen n e prevV).ops) :
    IsBase (ρ (rootOpen n e prevV).res.lo) ∧ IsBase (ρ (rootOpen n e prevV).res.hi) := by
  dsimp only [rootOpen] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hq⟩, -⟩, -⟩, -⟩ := h
  have a := hq _ List.mem_cons_self
  have b := hq _ (List.mem_cons_of_mem _ List.mem_cons_self)
  exact ⟨by simpa [Op.holds] using a, by simpa [Op.holds] using b⟩

/-- **An epoch root's opening digests to Blake2s of its words.** -/
theorem rootOpen_out {n e : ℕ} {prevV : Bool} (h : Holds ρ (rootOpen n e prevV).ops) :
    ∀ j < 8, word (ρ ((rootOpen n e prevV).res.out.getD j 0)) =
      blake2sWords (openWords ρ (rootOpen n e prevV).res prevV) (4 * (8 + 8 + (if prevV then 8 else 0) + 2 + 8)) j := by
  intro j hj
  dsimp only [rootOpen] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hq⟩, -⟩, -⟩, ho⟩ := h
  have hb := blake2s_words ho (by cases prevV <;> simp [BlockRec.guessHash_length]) j hj
  rw [hb, msg_words (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))]
  congr 1
  · cases prevV <;> rfl
  · cases prevV <;> simp [BlockRec.guessHash_length]

/-- A root from genesis opens no previous set: its `prev` is 8 zero words. -/
theorem rootOpen_zeros {n e : ℕ} (h : Holds ρ (rootOpen n e false).ops) :
    wordsOf ρ (rootOpen n e false).res.prev = List.replicate 8 0 := by
  dsimp only [rootOpen] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hz⟩, -⟩ := h
  simp only [Bool.false_eq_true, ite_false] at hz ⊢
  rw [show List.replicate 8 (0 : Word) = (List.range 8).map (fun _ => 0) by simp, wordsOf, List.map_map]
  refine List.map_congr_left (fun w hw => ?_)
  have := const_word (hz _ (List.mem_map.mpr ⟨w, hw, rfl⟩)) (by norm_num)
  simpa using this

/-- **`rest` opened**: the guessed values are base, and `rest`'s words are Blake2s of them as words. -/
theorem restOpen_sound {n e m : ℕ} {rest : List ℕ} (h : Holds ρ (restOpen n e m rest).ops) (hm : m ≤ 64) :
    (∀ j < 17 + 16 * m, IsBase (ρ (n + j))) ∧
    ∀ w < 8, word (ρ (rest.getD w 0)) =
      blake2sWords ((List.range (17 + 16 * m)).map (fun j => BitVec.ofNat 32 (ρ (n + j)).a.val)) (4 * (17 + 16 * m)) w := by
  dsimp only [restOpen] at h
  simp only [holds_append] at h
  obtain ⟨⟨hg, hro⟩, he⟩ := h
  refine ⟨fun j hj => ?_, fun w hw => ?_⟩
  · have := hg _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    simpa [Op.holds] using this
  · have rs := restOut_sound hro (by simp; omega) w hw
    have e := he _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
    simp only [Op.holds] at e
    rw [← e, rs]
    simp only [List.length_map, List.length_range, List.map_map]
    rfl

/-! ### `acc` -/

theorem accChain_length (rout : ℕ → List ℕ) (r : ℕ) : ∀ k, (accChain rout r k).length = k
  | 0 => rfl
  | k + 1 => by simp [accChain, accChain_length rout r k]

/-- The `k`-th hash's left message: `out₀`, then the previous hash's result. -/
def accLeft (rout : ℕ → List ℕ) (r : ℕ) (k : ℕ) : List ℕ :=
  match (accChain rout r k).getLast? with | some o => o.res | none => rout 0

theorem accChain_get (rout : ℕ → List ℕ) (r : ℕ) : ∀ K k (hk : k < K),
    (accChain rout r K)[k]'(by rw [accChain_length]; exact hk) =
      blake2s (lastNext (accChain rout r k) r) (accLeft rout r k ++ rout (k + 1)) 64
  | 0, _, hk => absurd hk (Nat.not_lt_zero _)
  | K + 1, k, hk => by
    by_cases hkK : k < K
    · have := accChain_get rout r K k hkK
      simp only [accChain]
      rw [List.getElem_append_left (by rw [accChain_length]; exact hkK)]
      exact this
    · have hkK' : k = K := by omega
      subst hkK'
      simp only [accChain]
      rw [List.getElem_append_right (by rw [accChain_length])]
      simp only [accChain_length, Nat.sub_self, List.getElem_singleton]
      rfl

theorem accLeft_succ (rout : ℕ → List ℕ) (r : ℕ) (k : ℕ) :
    accLeft rout r (k + 1) = ((accChain rout r (k + 1))[k]'(by rw [accChain_length]; omega)).res := by
  unfold accLeft
  simp only [accChain]
  rw [List.getLast?_append, List.getLast?_singleton, Option.some_or]
  rw [List.getElem_append_right (by rw [accChain_length])]
  simp [accChain_length]

/-- **Each `acc` is Blake2s of its left message and the next output.** -/
theorem accChain_sound {rout : ℕ → List ℕ} {r K : ℕ} (h : Holds ρ ((accChain rout r K).flatMap (·.ops))) :
    ∀ k (hk : k < K), ∀ i < 8,
      word (ρ (((accChain rout r K)[k]'(by rw [accChain_length]; exact hk)).res.getD i 0)) =
        blake2sWords (wordsOf ρ (accLeft rout r k) ++ wordsOf ρ (rout (k + 1))) 64 i := by
  intro k hk i hi
  rw [accChain_get rout r K k hk]
  have hops : Holds ρ (blake2s (lastNext (accChain rout r k) r) (accLeft rout r k ++ rout (k + 1)) 64).ops :=
    fun o ho => h o (List.mem_flatMap.mpr ⟨_, List.getElem_mem _, by rw [accChain_get rout r K k hk]; exact ho⟩)
  rw [blake2s_words hops (by norm_num) i hi]
  simp [wordsOf]

/-! ### Constants -/

/-- The constant registers hold their values. -/
structure ConstsOk (ρ : ℕ → Q) (C : Consts) : Prop where
  zero : ρ C.zero = lit 0 0 0 0
  one : ρ C.one = lit 1 0 0 0
  e1 : ρ C.e1 = lit 0 1 0 0
  e2 : ρ C.e2 = lit 0 0 1 0
  e3 : ρ C.e3 = lit 0 0 0 1
  c64 : ρ C.c64 = lit 64 0 0 0
  c256 : ρ C.c256 = lit 256 0 0 0
  c1024 : ρ C.c1024 = lit 1024 0 0 0
  c4096 : ρ C.c4096 = lit 4096 0 0 0
  c65536 : ρ C.c65536 = lit 65536 0 0 0
  c16M : ρ C.c16M = lit 16777216 0 0 0
  four : ρ C.four = lit 4 0 0 0
  small : ∀ k < 65, ρ (C.small k) = lit k 0 0 0
  b2iv : ∀ j < 16, ρ (C.b2iv.getD j 0) = lit ((b2ivWords.flatMap halves).getD j 0) 0 0 0
  shaiv : ∀ j < 16, ρ (C.shaiv.getD j 0) = lit ((shaIvWords.flatMap halves).getD j 0) 0 0 0

theorem consts_sound {n : ℕ} (h : Holds ρ (consts n).ops) : ConstsOk ρ (consts n).res := by
  dsimp only [consts] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨hf, hs⟩, hb⟩, hsh⟩ := h
  have f := fun (o : Op) (ho : o ∈ _) => hf o ho
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [Op.holds] using f (Op.const n 0 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 1) 1 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 2) 0 1 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 3) 0 0 1 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 4) 0 0 0 1) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 5) 64 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 6) 256 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 7) 1024 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 8) 4096 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 9) 65536 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 10) 16777216 0 0 0) (by simp)
  · simpa [Op.holds] using f (Op.const (n + 11) 4 0 0 0) (by simp)
  · intro k hk
    have := hs _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
    simpa [Op.holds] using this
  · intro j hj
    have := hb _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    simp only [Op.holds] at this
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simpa using this
  · intro j hj
    have := hsh _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
    simp only [Op.holds] at this
    rw [List.getD_eq_getElem _ _ (by simpa using hj)]
    simpa using this

/-! ### The challenge -/

/-- A QM31 from its four coordinates as base values. -/
theorem qm_sound {n : ℕ} {l : List ℕ} {C : Consts} (h : Holds ρ (qm n l C).ops) (hC : ConstsOk ρ C)
    (hl : ∀ j < 4, IsBase (ρ (l.getD j 0))) :
    ρ (qm n l C).res = ⟨(ρ (l.getD 0 0)).a, (ρ (l.getD 1 0)).a, (ρ (l.getD 2 0)).a, (ρ (l.getD 3 0)).a⟩ := by
  dsimp only [qm] at h ⊢
  have g := fun (o : Op) (ho : o ∈ _) => h o ho
  have m1 := g (Op.mul n (l.getD 1 0) C.e1) (by simp)
  have m2 := g (Op.mul (n + 1) (l.getD 2 0) C.e2) (by simp)
  have m3 := g (Op.mul (n + 2) (l.getD 3 0) C.e3) (by simp)
  have a3 := g (Op.add (n + 3) (l.getD 0 0) n) (by simp)
  have a4 := g (Op.add (n + 4) (n + 3) (n + 1)) (by simp)
  have a5 := g (Op.add (n + 5) (n + 4) (n + 2)) (by simp)
  simp only [Op.holds] at m1 m2 m3 a3 a4 a5
  rw [a5, a4, a3, m1, m2, m3, hC.e1, hC.e2, hC.e3, mul_e1 (hl 1 (by norm_num)), mul_e2 (hl 2 (by norm_num)),
    mul_e3 (hl 3 (by norm_num)), base_a (hl 0 (by norm_num))]
  ext <;> simp

/-- The coordinates of a register, recombined. -/
theorem coords_sound {n x : ℕ} {C : Consts} (h : Holds ρ (coords n x C).ops) (hC : ConstsOk ρ C) :
    (∀ j < 4, IsBase (ρ (n + j))) ∧ ρ x = ⟨(ρ n).a, (ρ (n + 1)).a, (ρ (n + 2)).a, (ρ (n + 3)).a⟩ := by
  dsimp only [coords] at h
  rw [holds_append] at h
  obtain ⟨hg, hr⟩ := h
  have hb : ∀ j < 4, IsBase (ρ (n + j)) := fun j hj => by
    have := hg _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩); simpa [Op.holds] using this
  refine ⟨hb, ?_⟩
  have g := fun (o : Op) (ho : o ∈ _) => hr o ho
  have m4 := g (Op.mul (n + 4) (n + 1) C.e1) (by simp)
  have m5 := g (Op.mul (n + 5) (n + 2) C.e2) (by simp)
  have m6 := g (Op.mul (n + 6) (n + 3) C.e3) (by simp)
  have a7 := g (Op.add (n + 7) n (n + 4)) (by simp)
  have a8 := g (Op.add (n + 8) (n + 7) (n + 5)) (by simp)
  have a9 := g (Op.add (n + 9) (n + 8) (n + 6)) (by simp)
  have e := g (Op.eq (n + 9) x) (by simp)
  simp only [Op.holds] at m4 m5 m6 a7 a8 a9 e
  have hb0 : IsBase (ρ n) := by simpa using hb 0 (by norm_num)
  rw [← e, a9, a8, a7, m4, m5, m6, hC.e1, hC.e2, hC.e3, mul_e1 (hb 1 (by norm_num)), mul_e2 (hb 2 (by norm_num)),
    mul_e3 (hb 3 (by norm_num)), base_a hb0]
  ext <;> simp

/-- `α^w` as the gadget computes it: `α^0 = 1`, `α^(w+1) = α^w · α`. -/
def qpow (α : Q) : ℕ → Q
  | 0 => lit 1 0 0 0
  | w + 1 => qpow α w * α

theorem chal_res_getD {n : ℕ} {ch : List ℕ} {C : Consts} (hc : 8 ≤ ch.length) {i : ℕ} (hi : i < 104) :
    (chal n ch C).res.getD (8 + i) 0 = n + 32 + 10 * (i / 4) + i % 4 := by
  dsimp only [chal]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [List.length_take]; try omega)]
  simp [List.length_take, hc, hi]

theorem chal_res_take {n : ℕ} {ch : List ℕ} {C : Consts} {i : ℕ} (hi : i < 8) (hc : 8 ≤ ch.length) :
    (chal n ch C).res.getD i 0 = ch.getD i 0 := by
  dsimp only [chal]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [List.length_take]; try omega), List.getElem?_take,
    if_pos hi, List.getD_eq_getElem?_getD]

/-- **The challenge expansion is sound.** With `α` the QM31 of limbs 8–11: limb `8 + 4w + j` is base and
the four limbs of block `w` are the coordinates of `α^w`. -/
theorem chal_sound {n : ℕ} {ch : List ℕ} {C : Consts} (h : Holds ρ (chal n ch C).ops) (hC : ConstsOk ρ C)
    (hch : ∀ j < 12, IsBase (ρ (ch.getD j 0))) (hc : 8 ≤ ch.length) :
    ∀ w < 26, (∀ j < 4, IsBase (ρ ((chal n ch C).res.getD (8 + 4 * w + j) 0))) ∧
      (⟨(ρ ((chal n ch C).res.getD (8 + 4 * w) 0)).a, (ρ ((chal n ch C).res.getD (8 + 4 * w + 1) 0)).a,
        (ρ ((chal n ch C).res.getD (8 + 4 * w + 2) 0)).a, (ρ ((chal n ch C).res.getD (8 + 4 * w + 3) 0)).a⟩ : Q) =
        qpow ⟨(ρ (ch.getD 8 0)).a, (ρ (ch.getD 9 0)).a, (ρ (ch.getD 10 0)).a, (ρ (ch.getD 11 0)).a⟩ w := by
  have hops := h
  dsimp only [chal] at hops
  simp only [holds_append] at hops
  obtain ⟨⟨hal, hp⟩, hcs⟩ := hops
  -- α.
  have hdrop : ∀ j, (ch.drop 8).getD j 0 = ch.getD (8 + j) 0 := fun j => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
  have ha := qm_sound hal hC (fun j hj => by rw [hdrop]; exact hch (8 + j) (by omega))
  simp only [hdrop, Nat.add_zero, Nat.reduceAdd] at ha
  set α : Q := ⟨(ρ (ch.getD 8 0)).a, (ρ (ch.getD 9 0)).a, (ρ (ch.getD 10 0)).a, (ρ (ch.getD 11 0)).a⟩ with hα
  -- The powers.
  have hpow : ∀ w < 26, ρ (n + 6 + w) = qpow α w := by
    intro w
    induction w with
    | zero =>
      intro _
      have := hp _ List.mem_cons_self
      simpa [Op.holds, ONE, qpow] using this
    | succ w ih =>
      intro hw
      have := hp _ (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, List.mem_range.mpr (by omega), rfl⟩))
      simp only [Op.holds] at this
      rw [this, ih (by omega), ha, qpow]
  intro w hw
  have hcw : Holds ρ (coords (n + 32 + 10 * w) (n + 6 + w) C).ops := fun o ho =>
    hcs o (List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩, ho⟩)
  obtain ⟨hb, hx⟩ := coords_sound hcw hC
  have idx : ∀ j < 4, (chal n ch C).res.getD (8 + 4 * w + j) 0 = n + 32 + 10 * w + j := fun j hj => by
    rw [show 8 + 4 * w + j = 8 + (4 * w + j) by omega, chal_res_getD hc (by omega)]
    congr 1 <;> omega
  have idx0 : (chal n ch C).res.getD (8 + 4 * w) 0 = n + 32 + 10 * w := by simpa using idx 0 (by norm_num)
  refine ⟨fun j hj => by rw [idx j hj]; exact hb j hj, ?_⟩
  rw [idx0, idx 1 (by norm_num), idx 2 (by norm_num), idx 3 (by norm_num), ← hpow w hw, hx]

/-! ### Bytes and the count -/

/-- `byteOps`: for a u16 `x` and the literal `m`, `x · m` is a u16. -/
theorem byteOps_sound {n x c m : ℕ} (h : Holds ρ (byteOps n x c)) (hx : IsBase (ρ x)) (hx16 : (ρ x).a.val < 65536)
    (hc : ρ c = lit m 0 0 0) (hm : m ≤ 4096) : (ρ x).a.val * m < 65536 := by
  have h1 := h _ List.mem_cons_self
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [Op.holds] at h1 h2 h3
  rw [h1, hc, BlockNode.mul_base _ _ hx (isBase_lit m)] at h3
  have ha := congrArg Q.a h3
  simp only [lit] at ha
  have hp : (ρ x).a.val * m < P := lt_P (by
    calc (ρ x).a.val * m ≤ 65535 * 4096 := Nat.mul_le_mul (by omega) hm
      _ < 2147483647 := by norm_num)
  rw [ha, val_mul_lit (lt_P (by omega)) hp] at h2
  exact h2.2

theorem bytes_sound {n c : ℕ} {xs : List ℕ} (h : Holds ρ (bytes n c xs).ops) (hc : ρ c = lit 256 0 0 0)
    (hx : ∀ k < xs.length, IsBase (ρ (xs.getD k 0)) ∧ (ρ (xs.getD k 0)).a.val < 65536) :
    ∀ k < xs.length, (ρ (xs.getD k 0)).a.val < 256 := by
  intro k hk
  dsimp only [bytes] at h
  have hb : Holds ρ (byteOps (n + 2 * k) (xs.getD k 0) c) := fun o ho =>
    h o (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ho⟩)
  have := byteOps_sound hb (hx k hk).1 (hx k hk).2 hc (by norm_num)
  omega

/-- **The count** from its bytes: base, the integer `c₀ + 256 c₁ + 2^16 c₂ + 2^24 c₃`, with `c₃ < 64`. -/
theorem count_sound {n : ℕ} {cnt : List ℕ} {C : Consts} (h : Holds ρ (count n cnt C).ops) (hC : ConstsOk ρ C)
    (hb : ∀ j < 4, IsBase (ρ (cnt.getD j 0)) ∧ (ρ (cnt.getD j 0)).a.val < 256) :
    IsBase (ρ (count n cnt C).res) ∧
    (ρ (count n cnt C).res).a.val = (ρ (cnt.getD 0 0)).a.val + 256 * (ρ (cnt.getD 1 0)).a.val +
      65536 * (ρ (cnt.getD 2 0)).a.val + 16777216 * (ρ (cnt.getD 3 0)).a.val ∧
    (ρ (cnt.getD 3 0)).a.val < 64 := by
  dsimp only [count] at h ⊢
  rw [holds_append] at h
  obtain ⟨ha, hl⟩ := h
  have g := fun (o : Op) (ho : o ∈ _) => ha o ho
  have m0 := g (Op.mul n (cnt.getD 1 0) C.c256) (by simp)
  have a1 := g (Op.add (n + 1) (cnt.getD 0 0) n) (by simp)
  have m2 := g (Op.mul (n + 2) (cnt.getD 2 0) C.c65536) (by simp)
  have a3 := g (Op.add (n + 3) (n + 1) (n + 2)) (by simp)
  have m4 := g (Op.mul (n + 4) (cnt.getD 3 0) C.c16M) (by simp)
  have a5 := g (Op.add (n + 5) (n + 3) (n + 4)) (by simp)
  simp only [Op.holds] at m0 a1 m2 a3 m4 a5
  have b0 := hb 0 (by norm_num)
  have b1 := hb 1 (by norm_num)
  have b2 := hb 2 (by norm_num)
  have b3 := hb 3 (by norm_num)
  have c3 : (ρ (cnt.getD 3 0)).a.val < 64 := by
    have := byteOps_sound hl b3.1 (by omega) hC.c1024 (by norm_num); omega
  rw [hC.c256, BlockNode.mul_base _ _ b1.1 (isBase_lit _)] at m0
  rw [hC.c65536, BlockNode.mul_base _ _ b2.1 (isBase_lit _)] at m2
  rw [hC.c16M, BlockNode.mul_base _ _ b3.1 (isBase_lit _)] at m4
  rw [m0] at a1
  rw [m2] at a3
  rw [m4] at a5
  have i1 : IsBase (ρ (n + 1)) := by rw [a1]; exact isBase_add b0.1 ⟨rfl, rfl, rfl⟩
  have i3 : IsBase (ρ (n + 3)) := by rw [a3]; exact isBase_add i1 ⟨rfl, rfl, rfl⟩
  have i5 : IsBase (ρ (n + 5)) := by rw [a5]; exact isBase_add i3 ⟨rfl, rfl, rfl⟩
  refine ⟨i5, ?_, c3⟩
  have v1 : (ρ (n + 1)).a.val = (ρ (cnt.getD 0 0)).a.val + 256 * (ρ (cnt.getD 1 0)).a.val := by
    rw [a1, add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]
    ring
  have v3 : (ρ (n + 3)).a.val = (ρ (cnt.getD 0 0)).a.val + 256 * (ρ (cnt.getD 1 0)).a.val + 65536 * (ρ (cnt.getD 2 0)).a.val := by
    rw [a3, add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega)), v1]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega)), v1]
    ring
  rw [a5, add_a]
  simp only [lit]
  rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega)), v3]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega)), v3]
  ring

/-! ### Packing -/

theorem packW_res_getD (n : ℕ) (limbs : List ℕ) (C : Consts) {w : ℕ} (hw : w < 8) :
    (packW n limbs C).res.getD w 0 = n + 2 * w + 1 := by
  dsimp only [packW]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

/-- Eight u32 wires from 16 base limbs. -/
theorem packW_sound {n : ℕ} {limbs : List ℕ} {C : Consts} (h : Holds ρ (packW n limbs C).ops) (hC : ConstsOk ρ C)
    (hl : ∀ j < 16, IsBase (ρ (limbs.getD j 0))) :
    ∀ w < 8, ρ ((packW n limbs C).res.getD w 0) = ⟨(ρ (limbs.getD (2 * w) 0)).a, (ρ (limbs.getD (2 * w + 1) 0)).a, 0, 0⟩ := by
  intro w hw
  rw [packW_res_getD n limbs C hw]
  dsimp only [packW] at h
  have g : ∀ o ∈ [Op.mul (n + 2 * w) (limbs.getD (2 * w + 1) 0) C.e1, .add (n + 2 * w + 1) (limbs.getD (2 * w) 0) (n + 2 * w)],
      o.holds ρ := fun o ho => h o (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw, ho⟩)
  have m := g _ List.mem_cons_self
  have a := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [Op.holds] at m a
  rw [a, m, hC.e1, lohi (hl _ (by omega)) (hl _ (by omega))]

/-- Eight packed limb pairs equal eight u32 wires. -/
theorem packEq_sound {n : ℕ} {limbs : ℕ → ℕ} {words : List ℕ} {C : Consts} (h : Holds ρ (packEq n limbs words C))
    (hC : ConstsOk ρ C) (hl : ∀ j < 16, IsBase (ρ (limbs j))) :
    ∀ w < 8, ρ (words.getD w 0) = ⟨(ρ (limbs (2 * w))).a, (ρ (limbs (2 * w + 1))).a, 0, 0⟩ := by
  intro w hw
  dsimp only [packEq] at h
  have g : ∀ o ∈ [Op.mul (n + 2 * w) (limbs (2 * w + 1)) C.e1, .add (n + 2 * w + 1) (limbs (2 * w)) (n + 2 * w),
      .eq (n + 2 * w + 1) (words.getD w 0)], o.holds ρ := fun o ho => h o (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw, ho⟩)
  have m := g _ List.mem_cons_self
  have a := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have e := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [Op.holds] at m a e
  rw [← e, a, m, hC.e1, lohi (hl _ (by omega)) (hl _ (by omega))]

theorem packBytes_res_getD (n nw : ℕ) (bs : List ℕ) (C : Consts) {w : ℕ} (hw : w < nw) :
    (packBytes n bs nw C).res.getD w 0 = n + 6 * w + 5 := by
  dsimp only [packBytes]
  rw [List.getD_eq_getElem _ _ (by simpa using hw)]
  simp

/-- **Bytes packed into u32 wires**: `b₀ + 256 b₁ + 2^16 b₂ + 2^24 b₃`, little-endian. -/
theorem packBytes_sound {n nw : ℕ} {bs : List ℕ} {C : Consts} (h : Holds ρ (packBytes n bs nw C).ops) (hC : ConstsOk ρ C)
    (hb : ∀ j < 4 * nw, IsBase (ρ (bs.getD j 0)) ∧ (ρ (bs.getD j 0)).a.val < 256) :
    ∀ w < nw, IsU32 (ρ ((packBytes n bs nw C).res.getD w 0)) ∧
      word (ρ ((packBytes n bs nw C).res.getD w 0)) =
        BitVec.ofNat 32 ((ρ (bs.getD (4 * w) 0)).a.val + 256 * (ρ (bs.getD (4 * w + 1) 0)).a.val +
          65536 * ((ρ (bs.getD (4 * w + 2) 0)).a.val + 256 * (ρ (bs.getD (4 * w + 3) 0)).a.val)) := by
  intro w hw
  rw [packBytes_res_getD n nw bs C hw]
  dsimp only [packBytes] at h
  set r := n + 6 * w
  have g : ∀ o ∈ [Op.mul r (bs.getD (4 * w + 1) 0) C.c256, .add (r + 1) (bs.getD (4 * w) 0) r,
      .mul (r + 2) (bs.getD (4 * w + 3) 0) C.c256, .add (r + 3) (bs.getD (4 * w + 2) 0) (r + 2),
      .mul (r + 4) (r + 3) C.e1, .add (r + 5) (r + 1) (r + 4)], o.holds ρ :=
    fun o ho => h o (List.mem_flatMap.mpr ⟨w, List.mem_range.mpr hw, ho⟩)
  have m0 := g _ List.mem_cons_self
  have a1 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have m2 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have a3 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  have m4 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
  have a5 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
  simp only [Op.holds] at m0 a1 m2 a3 m4 a5
  have b0 := hb (4 * w) (by omega)
  have b1 := hb (4 * w + 1) (by omega)
  have b2 := hb (4 * w + 2) (by omega)
  have b3 := hb (4 * w + 3) (by omega)
  rw [hC.c256, BlockNode.mul_base _ _ b1.1 (isBase_lit _)] at m0
  rw [hC.c256, BlockNode.mul_base _ _ b3.1 (isBase_lit _)] at m2
  have i1 : IsBase (ρ (r + 1)) := by rw [a1, m0]; exact isBase_add b0.1 ⟨rfl, rfl, rfl⟩
  have i3 : IsBase (ρ (r + 3)) := by rw [a3, m2]; exact isBase_add b2.1 ⟨rfl, rfl, rfl⟩
  have v1 : (ρ (r + 1)).a.val = (ρ (bs.getD (4 * w) 0)).a.val + 256 * (ρ (bs.getD (4 * w + 1) 0)).a.val := by
    rw [a1, m0, add_a]; simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; ring
  have v3 : (ρ (r + 3)).a.val = (ρ (bs.getD (4 * w + 2) 0)).a.val + 256 * (ρ (bs.getD (4 * w + 3) 0)).a.val := by
    rw [a3, m2, add_a]; simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; ring
  have e5 : ρ (r + 5) = ⟨(ρ (r + 1)).a, (ρ (r + 3)).a, 0, 0⟩ := by rw [a5, m4, hC.e1, lohi i1 i3]
  refine ⟨?_, ?_⟩
  · rw [e5]
    show (ρ (r + 1)).a.val < 65536 ∧ (ρ (r + 3)).a.val < 65536 ∧ (0 : F) = 0 ∧ (0 : F) = 0
    exact ⟨by omega, by omega, rfl, rfl⟩
  · rw [e5, word_mk, v1, v3]

/-! ### The pending-length one-hot and the mask -/

/-- **`oneHot65` is sound**: `x` is some `k ≤ 64` and bit `j` is `[j = k]`. -/
theorem oneHot65_sound {n x : ℕ} {C : Consts} (h : Holds ρ (oneHot65 n x C).ops) (hC : ConstsOk ρ C) :
    ∃ k : ℕ, k < 65 ∧ (ρ x).a = ((k : ℕ) : F) ∧ ∀ j < 65, IsBase (ρ (n + j)) ∧ (ρ (n + j)).a = if j = k then 1 else 0 := by
  dsimp only [oneHot65] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨hb, hs⟩, hw⟩, hl⟩ := h
  set bo := n + 65
  set s := bo + 130
  set w := s + 65
  set B : ℕ → F := fun j => (ρ (n + j)).a with hBdef
  have bit : ∀ j < 65, IsBase (ρ (n + j)) ∧ B j * (B j - 1) = 0 := by
    intro j hj
    have g := fun (o : Op) (ho : o ∈ _) => hb o (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ho⟩)
    have tg := g _ List.mem_cons_self
    have s1 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have m2 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have e := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    simp only [Op.holds] at tg s1 m2 e
    refine ⟨tg, ?_⟩
    have b2 : IsBase (ρ (bo + 2 * j)) := by rw [s1, hC.one]; exact isBase_sub tg (isBase_lit 1)
    have := congrArg Q.a (m2.symm.trans (e.trans hC.zero))
    rw [mul_a tg b2, s1, sub_a, hC.one] at this
    simpa [lit, B] using this
  have sums : ∀ j < 65, (ρ (s + j)).a = ∑ i ∈ Finset.range (j + 1), B i := by
    intro j
    induction j with
    | zero =>
      intro hj
      have a0 := hs _ (List.mem_map.mpr ⟨0, List.mem_range.mpr hj, rfl⟩)
      simp only [Op.holds, if_true] at a0
      rw [a0, add_a, hC.zero]; simp [lit, B]
    | succ j ih =>
      intro hj
      have a1 := hs _ (List.mem_map.mpr ⟨j + 1, List.mem_range.mpr hj, rfl⟩)
      simp only [Op.holds, Nat.add_one_ne_zero, if_false] at a1
      rw [show s + (j + 1) - 1 = s + j by omega] at a1
      rw [a1, add_a, ih (by omega), Finset.sum_range_succ _ (j + 1)]
  have wsum : ∀ j < 65, (ρ (w + 2 * j + 1)).a = ∑ i ∈ Finset.range (j + 1), B i * (i : F) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have g := fun (o : Op) (ho : o ∈ _) => hw o (List.mem_flatMap.mpr ⟨0, List.mem_range.mpr hj, ho⟩)
      have m0 := g _ List.mem_cons_self
      have a0 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [Op.holds, if_true, Nat.mul_zero, Nat.add_zero] at m0 a0
      have b0 : IsBase (ρ n) := by simpa using (bit 0 hj).1
      rw [a0, add_a, m0, hC.zero, mul_a b0 (by rw [hC.small 0 hj]; exact isBase_lit 0), hC.small 0 hj]
      simp [lit, B]
    | succ j ih =>
      intro hj
      have g := fun (o : Op) (ho : o ∈ _) => hw o (List.mem_flatMap.mpr ⟨j + 1, List.mem_range.mpr hj, ho⟩)
      have m1 := g _ List.mem_cons_self
      have a1 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [Op.holds, Nat.add_one_ne_zero, if_false] at m1 a1
      rw [show w + 2 * (j + 1) - 1 = w + 2 * j + 1 by omega] at a1
      rw [a1, add_a, ih (by omega), m1, mul_a (bit (j + 1) hj).1 (by rw [hC.small (j + 1) hj]; exact isBase_lit _),
        hC.small (j + 1) hj, Finset.sum_range_succ _ (j + 1)]
      rfl
  have eS := hl _ List.mem_cons_self
  have eX := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [Op.holds] at eS eX
  have sumB : ∑ i ∈ Finset.range 65, B i = 1 := by
    rw [← sums 64 (by norm_num), eS, hC.one]; simp [lit]
  have sumX : (ρ x).a = ∑ i ∈ Finset.range 65, B i * (i : F) := by
    rw [← wsum 64 (by norm_num), ← eX]
  have bv : ∀ i < 65, B i = (((B i).val : ℕ) : F) ∧ (B i).val ≤ 1 := fun i hi =>
    ⟨(ZMod.natCast_zmod_val _).symm, val_le_one_of_bool (bit i hi).2⟩
  have sumN : ∑ i ∈ Finset.range 65, (B i).val = 1 := by
    have hc : ((∑ i ∈ Finset.range 65, (B i).val : ℕ) : F) = 1 := by
      rw [Nat.cast_sum, ← sumB]
      exact Finset.sum_congr rfl (fun i hi => ((bv i (Finset.mem_range.mp hi)).1).symm)
    have hle : ∑ i ∈ Finset.range 65, (B i).val ≤ 65 := by
      calc ∑ i ∈ Finset.range 65, (B i).val ≤ ∑ _i ∈ Finset.range 65, 1 :=
            Finset.sum_le_sum (fun i hi => (bv i (Finset.mem_range.mp hi)).2)
        _ = 65 := by simp
    exact natCast_inj_of_lt (lt_of_le_of_lt hle (by unfold P; norm_num)) (by unfold P; norm_num) (by rw [hc]; simp)
  obtain ⟨k, hk, hone⟩ := one_hot (fun i => (B i).val) (fun i hi => (bv i hi).2) sumN
  have hBk : ∀ i < 65, B i = if i = k then 1 else 0 := fun i hi => by
    rw [(bv i hi).1, hone i hi]; split_ifs <;> simp
  refine ⟨k, hk, ?_, fun j hj => ⟨(bit j hj).1, hBk j hj⟩⟩
  rw [sumX, Finset.sum_congr rfl (fun i hi => by rw [hBk i (Finset.mem_range.mp hi)])]
  simp [Finset.sum_ite_eq', Finset.mem_range.mpr hk]

/-- **`ltMask` is sound**: `lt_j = [j < k]` from the one-hot of `k`. -/
theorem ltMask_sound {n : ℕ} {bits : List ℕ} {C : Consts} {k : ℕ} (h : Holds ρ (ltMask n bits C).ops) (hC : ConstsOk ρ C)
    (hk : k < 65) (hb : ∀ j < 65, IsBase (ρ (bits.getD j 0)) ∧ (ρ (bits.getD j 0)).a = if j = k then 1 else 0) :
    ∀ j < 64, IsBase (ρ (n + j)) ∧ (ρ (n + j)).a = if j < k then 1 else 0 := by
  dsimp only [ltMask] at h
  have g : ∀ j < 64, (Op.add (n + j) (if j = 63 then C.zero else n + j + 1) (bits.getD (j + 1) 0)).holds ρ := fun j hj =>
    h _ (List.mem_map.mpr ⟨j, List.mem_reverse.mpr (List.mem_range.mpr hj), rfl⟩)
  -- Downward from `j = 63`.
  have step : ∀ d < 64, IsBase (ρ (n + (63 - d))) ∧ (ρ (n + (63 - d))).a = if 63 - d < k then 1 else 0 := by
    intro d
    induction d with
    | zero =>
      intro _
      have a := g 63 (by norm_num)
      simp only [Op.holds, if_true] at a
      have b64 := hb 64 (by norm_num)
      refine ⟨by rw [a, hC.zero]; exact isBase_add (isBase_lit 0) b64.1, ?_⟩
      rw [a, add_a, hC.zero, b64.2]
      simp only [lit]
      by_cases hk64 : 64 = k
      · subst hk64; simp
      · have : ¬ 63 < k := by omega
        simp [hk64, this]
    | succ d ih =>
      intro hd
      have ih' := ih (by omega)
      have a := g (63 - (d + 1)) (by omega)
      have hne : 63 - (d + 1) ≠ 63 := by omega
      simp only [Op.holds, hne, if_false] at a
      have bj := hb (63 - (d + 1) + 1) (by omega)
      rw [show 63 - (d + 1) + 1 = 63 - d by omega] at a bj
      rw [show n + (63 - (d + 1)) + 1 = n + (63 - d) by omega] at a
      refine ⟨by rw [a]; exact isBase_add ih'.1 bj.1, ?_⟩
      rw [a, add_a, ih'.2, bj.2]
      by_cases h1 : 63 - d < k
      · have h2 : 63 - (d + 1) < k := by omega
        have h3 : 63 - d ≠ k := by omega
        rw [if_pos h1, if_neg h3, if_pos h2]; norm_num
      · by_cases h4 : 63 - d = k
        · have h5 : 63 - (d + 1) < k := by omega
          rw [if_neg h1, if_pos h4, if_pos h5]; norm_num
        · have h5 : ¬ 63 - (d + 1) < k := by omega
          rw [if_neg h1, if_neg h4, if_neg h5]; norm_num
  intro j hj
  have := step (63 - j) (by omega)
  rw [show 63 - (63 - j) = j by omega] at this
  exact this

/-- **`mask` is sound**: `m_j = pend_j · lt_j`, so `pend_j` below the length and `0` past it. -/
theorem mask_sound {n : ℕ} {pend lt : List ℕ} {k : ℕ} (h : Holds ρ (mask n pend lt).ops)
    (hp : ∀ j < 64, IsBase (ρ (pend.getD j 0)))
    (hl : ∀ j < 64, IsBase (ρ (lt.getD j 0)) ∧ (ρ (lt.getD j 0)).a = if j < k then 1 else 0) :
    ∀ j < 64, IsBase (ρ ((mask n pend lt).res.getD j 0)) ∧
      (ρ ((mask n pend lt).res.getD j 0)).a = if j < k then (ρ (pend.getD j 0)).a else 0 := by
  intro j hj
  dsimp only [mask] at h ⊢
  rw [List.getD_eq_getElem _ _ (by simpa using hj)]
  simp only [List.getElem_map, List.getElem_range]
  have m := h _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Op.holds] at m
  refine ⟨by rw [m]; exact isBase_mul (hp j hj) (hl j hj).1, ?_⟩
  rw [m, mul_a (hp j hj) (hl j hj).1, (hl j hj).2]
  split_ifs <;> simp

/-! ### The counter -/

/-- **`counter` is sound**: for `nb` and `plen ≤ 64`, `t = 64 nb + plen` and the two wires are the u32
words `t mod 2^32` and `t / 2^32`; `nb` is below `2^30 + 2^10`. -/
theorem counter_sound {n nb plen : ℕ} {C : Consts} (h : Holds ρ (counter n nb plen C).ops) (hC : ConstsOk ρ C)
    (hpl64 : (ρ plen).a.val ≤ 64) :
    (ρ nb).a.val < 2 ^ 30 + 2 ^ 10 ∧
    IsU32 (ρ (counter n nb plen C).res.1) ∧ IsU32 (ρ (counter n nb plen C).res.2) ∧
    word (ρ (counter n nb plen C).res.1) = BitVec.ofNat 32 (64 * (ρ nb).a.val + (ρ plen).a.val) ∧
    word (ρ (counter n nb plen C).res.2) = BitVec.ofNat 32 ((64 * (ρ nb).a.val + (ρ plen).a.val) / 2 ^ 32) := by
  dsimp only [counter] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨hg1, hb1⟩, hg2⟩, hb2⟩, hmid⟩, hb3⟩, hend⟩ := h
  have gr := hg1 _ List.mem_cons_self
  have gq := hg1 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have gq0 := hg2 _ List.mem_cons_self
  have gq1 := hg2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [Op.holds] at gr gq gq0 gq1
  have m := fun (o : Op) (ho : o ∈ _) => hmid o ho
  have m8 := m (Op.mul (n + 8) (n + 5) C.c65536) (by simp)
  have a9 := m (Op.add (n + 9) (n + 4) (n + 8)) (by simp)
  have e9 := m (Op.eq (n + 9) (n + 1)) (by simp)
  have m10 := m (Op.mul (n + 10) (n + 1) C.c1024) (by simp)
  have a11 := m (Op.add (n + 11) (n + 10) n) (by simp)
  have e11 := m (Op.eq (n + 11) nb) (by simp)
  have m12 := m (Op.mul (n + 12) n C.c64) (by simp)
  have a13 := m (Op.add (n + 13) (n + 12) plen) (by simp)
  have g14 := m (Op.guessU16 (n + 14) (.modC (.reg (n + 13)) 65536)) (by simp)
  have g15 := m (Op.guessM31 (n + 15) (.divC (.reg (n + 13)) 65536)) (by simp)
  have s16 := m (Op.sub (n + 16) (n + 15) C.one) (by simp)
  have m17 := m (Op.mul (n + 17) (n + 15) (n + 16)) (by simp)
  have e17 := m (Op.eq (n + 17) C.zero) (by simp)
  have m18 := m (Op.mul (n + 18) (n + 15) C.c65536) (by simp)
  have a19 := m (Op.add (n + 19) (n + 14) (n + 18)) (by simp)
  have e19 := m (Op.eq (n + 19) (n + 13)) (by simp)
  have a20 := m (Op.add (n + 20) (n + 1) (n + 15)) (by simp)
  have g21 := m (Op.guessU16 (n + 21) (.modC (.reg (n + 20)) 65536)) (by simp)
  have g22 := m (Op.guessU16 (n + 22) (.divC (.reg (n + 20)) 65536)) (by simp)
  simp only [Op.holds] at m8 a9 e9 m10 a11 e11 m12 a13 g14 g15 s16 m17 e17 m18 a19 e19 a20 g21 g22
  have en := fun (o : Op) (ho : o ∈ _) => hend o ho
  have m25 := en (Op.mul (n + 25) (n + 22) C.c65536) (by simp)
  have a26 := en (Op.add (n + 26) (n + 21) (n + 25)) (by simp)
  have e26 := en (Op.eq (n + 26) (n + 20)) (by simp)
  have m27 := en (Op.mul (n + 27) (n + 21) C.e1) (by simp)
  have a28 := en (Op.add (n + 28) (n + 14) (n + 27)) (by simp)
  simp only [Op.holds] at m25 a26 e26 m27 a28
  -- Ranges: r < 2^10, q1 < 16, t1 < 16.
  have hr : (ρ n).a.val < 1024 := by
    have := byteOps_sound hb1 gr.1 gr.2 hC.c64 (by norm_num); omega
  have hq1 : (ρ (n + 5)).a.val < 16 := by
    have := byteOps_sound hb2 gq1.1 gq1.2 hC.c4096 (by norm_num); omega
  have ht1 : (ρ (n + 22)).a.val < 16 := by
    have := byteOps_sound hb3 g22.1 g22.2 hC.c4096 (by norm_num); omega
  -- q = q0 + 65536 q1 (exact).
  have vq : (ρ (n + 1)).a.val = (ρ (n + 4)).a.val + 65536 * (ρ (n + 5)).a.val := by
    rw [← e9, a9, m8, hC.c65536, BlockNode.mul_base _ _ gq1.1 (isBase_lit _), add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]
    ring
  have hq : (ρ (n + 1)).a.val < 2 ^ 20 := by omega
  -- nb = 1024 q + r (exact).
  have vnb : (ρ nb).a.val = 1024 * (ρ (n + 1)).a.val + (ρ n).a.val := by
    rw [← e11, a11, m10, hC.c1024, BlockNode.mul_base _ _ gq (isBase_lit _), add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]
    ring
  -- 64 r + plen = a + 65536 c, c boolean (exact).
  have hc : (ρ (n + 15)).a.val ≤ 1 := by
    have b16 : IsBase (ρ (n + 16)) := by rw [s16, hC.one]; exact isBase_sub g15 (isBase_lit 1)
    have := congrArg Q.a (m17.symm.trans (e17.trans hC.zero))
    rw [mul_a g15 b16, s16, sub_a, hC.one] at this
    exact val_le_one_of_bool (by simpa [lit] using this)
  have v13 : (ρ (n + 13)).a.val = 64 * (ρ n).a.val + (ρ plen).a.val := by
    rw [a13, m12, hC.c64, BlockNode.mul_base _ _ gr.1 (isBase_lit _), add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]
    ring
  have v19 : (ρ (n + 13)).a.val = (ρ (n + 14)).a.val + 65536 * (ρ (n + 15)).a.val := by
    rw [← e19, a19, m18, hC.c65536, BlockNode.mul_base _ _ g15 (isBase_lit _), add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]
    ring
  -- q + c = b + 65536 t1 (exact).
  have v20 : (ρ (n + 20)).a.val = (ρ (n + 1)).a.val + (ρ (n + 15)).a.val := by
    rw [a20, add_a, val_add_small (lt_P (by omega))]
  have v26 : (ρ (n + 20)).a.val = (ρ (n + 21)).a.val + 65536 * (ρ (n + 22)).a.val := by
    rw [← e26, a26, m25, hC.c65536, BlockNode.mul_base _ _ g22.1 (isBase_lit _), add_a]
    simp only [lit]
    rw [val_add_small (lt_P (by rw [val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]; omega)), val_mul_lit (lt_P (by norm_num)) (lt_P (by omega))]
    ring
  -- The arithmetic.
  set T := 64 * (ρ nb).a.val + (ρ plen).a.val with hT
  have hTe : T = (ρ (n + 14)).a.val + 65536 * (ρ (n + 21)).a.val + 2 ^ 32 * (ρ (n + 22)).a.val := by
    rw [hT, vnb]; omega
  have e28 : ρ (n + 28) = ⟨(ρ (n + 14)).a, (ρ (n + 21)).a, 0, 0⟩ := by rw [a28, m27, hC.e1, lohi g14.1 g21.1]
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  · rw [e28]; exact ⟨g14.2, g21.2, rfl, rfl⟩
  · exact ⟨g22.2, by rw [g22.1.1]; simp, g22.1.2.1, g22.1.2.2⟩
  · rw [e28, word_mk]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [hTe]
    omega
  · rw [base_a g22.1, word_mk]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    rw [hTe]
    have : ((ρ (n + 14)).a.val + 65536 * (ρ (n + 21)).a.val + 2 ^ 32 * (ρ (n + 22)).a.val) / 2 ^ 32 = (ρ (n + 22)).a.val := by
      rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega)]
      try omega
    rw [this]
    simp only [ZMod.val_zero, Nat.mul_zero, Nat.add_zero]

/-! ### The final compression -/

/-- **`compressFinal` computes `F(h, m, t, true)`** from chaining words `H`, message words `M` and counter
wires holding `t mod 2^32` and `t / 2^32`. -/
theorem compressFinal_sound {n : ℕ} {h m : List ℕ} {t0 t1 : ℕ} {H M : ℕ → Word} {t : ℕ}
    (hops : Holds ρ (compressFinal n h m t0 t1).ops)
    (hH : ∀ i < 8, word (ρ (h.getD i 0)) = H i)
    (hM : ∀ j, word (ρ (m.getD j n)) = M j)
    (ht0w : word (ρ t0) = BitVec.ofNat 32 t) (ht1w : word (ρ t1) = BitVec.ofNat 32 (t / 2 ^ 32)) :
    ∀ i < 8, word (ρ ((compressFinal n h m t0 t1).res.getD i 0)) = compress H M t true i := by
  intro i hi
  dsimp only [compressFinal] at hops ⊢
  simp only [holds_append] at hops
  obtain ⟨⟨hc, hgs⟩, hx⟩ := hops
  set base := n + 3
  set st0 : ℕ → ℕ := fun j => if j < 8 then h.getD j 0 else base + (j - 8) with hst0
  set g0 := n + 11
  set msg : ℕ → ℕ := fun j => m.getD j n with hmsg
  have c := fun (o : Op) (ho : o ∈ _) => hc o ho
  have z0 := c (constU32 n 0) (by simp)
  have c1 := c (constU32 (n + 1) (IVn.getD 4 0)) (by simp)
  have c2 := c (constU32 (n + 2) (IVn.getD 5 0)) (by simp)
  have b0 := c (constU32 base (IVn.getD 0 0)) (by simp)
  have b1 := c (constU32 (base + 1) (IVn.getD 1 0)) (by simp)
  have b2 := c (constU32 (base + 2) (IVn.getD 2 0)) (by simp)
  have b3 := c (constU32 (base + 3) (IVn.getD 3 0)) (by simp)
  have x4 := c (Op.xor3 (base + 4) (n + 1) t0 n) (by simp)
  have x5 := c (Op.xor3 (base + 5) (n + 2) t1 n) (by simp)
  have b6 := c (constU32 (base + 6) (Nat.xor (IVn.getD 6 0) 0xFFFFFFFF)) (by simp)
  have b7 := c (constU32 (base + 7) (IVn.getD 7 0)) (by simp)
  have ivlt : ∀ i < 8, IVn.getD i 0 < 2 ^ 32 := by decide
  have wz : word (ρ n) = 0 := by rw [const_word z0 (by norm_num)]; rfl
  have w1 : word (ρ (n + 1)) = IV 4 := by rw [const_word c1 (ivlt 4 (by norm_num))]; rfl
  have w2 : word (ρ (n + 2)) = IV 5 := by rw [const_word c2 (ivlt 5 (by norm_num))]; rfl
  simp only [Op.holds] at x4 x5
  -- The initial working vector.
  have hv0 : vW ρ st0 = initV H t true := by
    apply List.ext_getElem (by simp [vW, initV])
    intro j hj _
    simp only [vW, List.length_map, List.length_range] at hj
    simp only [vW, initV, List.getElem_map, List.getElem_range]
    by_cases hj8 : j < 8
    · simp only [hst0, if_pos hj8]; exact hH j hj8
    · simp only [hst0, if_neg hj8]
      obtain ⟨q, hq, rfl⟩ : ∃ q, q < 8 ∧ j = q + 8 := ⟨j - 8, by omega, by omega⟩
      simp only [Nat.add_sub_cancel]
      interval_cases q
      · rw [const_word b0 (ivlt 0 (by norm_num))]; simp [IV]
      · rw [const_word b1 (ivlt 1 (by norm_num))]; simp [IV]
      · rw [const_word b2 (ivlt 2 (by norm_num))]; simp [IV]
      · rw [const_word b3 (ivlt 3 (by norm_num))]; simp [IV]
      · rw [x4.2.2.2, word_pack, w1, ht0w, wz]; simp
      · rw [x5.2.2.2, word_pack, w2, ht1w, wz]; simp
      · rw [const_word b6 (by decide)]
        simp only [show ¬ (6 + 8 = 12) by decide, show ¬ (6 + 8 = 13) by decide, show 6 + 8 = 14 by decide, if_false, if_true]
        decide
      · rw [const_word b7 (ivlt 7 (by norm_num))]; simp [IV]
  have hsteps := steps_regs (ρ := ρ) (st0 := st0) (g0 := g0) (msg := msg) 80
    (fun q hq => hgs _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩))
  rw [hv0] at hsteps
  have hxi := hx _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simp only [Op.holds] at hxi
  obtain ⟨-, -, -, hxo⟩ := hxi
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  have hM' : (fun j => word (ρ (msg j))) = M := funext hM
  rw [hxo, word_pack, hH i hi, compress, ← hM', ← hsteps, vW_getD (by omega), vW_getD (by omega)]

/-! ### The program -/

theorem chainSeal_ops (ms : List ℕ) (gen : Bool) : (chainSeal ms gen).ops =
    let P := parts ms gen
    P.J.ops ++ P.sets.flatMap (·.ops) ++ P.roots.flatMap (·.ops) ++ P.rests.flatMap (·.ops) ++ P.C.ops ++
      P.chals.flatMap (·.ops) ++ P.opens.flatMap (·.ops) ++ P.accs.flatMap (·.ops) ++ P.checks.ops ++ P.key.ops ++ P.dg.ops := rfl

theorem chainSeal_results (ms : List ℕ) (gen : Bool) : (chainSeal ms gen).results = (parts ms gen).dg.res := rfl

/-- **The program's parts hold separately.** -/
theorem seal_parts {ms : List ℕ} {gen : Bool} (h : Holds ρ (chainSeal ms gen).ops) :
    let P := parts ms gen
    Holds ρ P.J.ops ∧ Holds ρ (P.sets.flatMap (·.ops)) ∧ Holds ρ (P.roots.flatMap (·.ops)) ∧
    Holds ρ (P.rests.flatMap (·.ops)) ∧ Holds ρ P.C.ops ∧ Holds ρ (P.chals.flatMap (·.ops)) ∧
    Holds ρ (P.opens.flatMap (·.ops)) ∧ Holds ρ (P.accs.flatMap (·.ops)) ∧ Holds ρ P.checks.ops ∧
    Holds ρ P.key.ops ∧ Holds ρ P.dg.ops := by
  rw [chainSeal_ops] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hJ, hS⟩, hR⟩, hT⟩, hC⟩, hCh⟩, hO⟩, hA⟩, hK⟩, hKey⟩, hD⟩ := h
  exact ⟨hJ, hS, hR, hT, hC, hCh, hO, hA, hK, hKey, hD⟩

/-- **The key**: Blake2s over every child's circuit hash and key (the join's, then each set root's). -/
theorem seal_key {ms : List ℕ} {gen : Bool} (h : Holds ρ (chainSeal ms gen).ops)
    (hB : 4 * ((parts ms gen).J.res.chash ++ (parts ms gen).J.res.key ++
      (parts ms gen).sets.flatMap (fun c => c.res.chash ++ c.res.key)).length < 2 ^ 32) :
    let P := parts ms gen
    let msg := P.J.res.chash ++ P.J.res.key ++ P.sets.flatMap (fun c => c.res.chash ++ c.res.key)
    ∀ i < 8, word (ρ (P.key.res.getD i 0)) = blake2sWords (wordsOf ρ msg) (4 * msg.length) i := by
  intro P msg i hi
  have hk : Holds ρ (blake2s P.checks.next msg (4 * msg.length)).ops := (seal_parts h).2.2.2.2.2.2.2.2.2.1
  exact blake2s_words hk hB i hi

/-- **The output digest**: Blake2s of the message's words (`parts.msg`: the key, the range words, the
start and end sets, `acc`, the end set's count, amount, height and Merkle root, the SHA-256 state
digests); the range words are `m31_to_u32` of the join's `a` and `b`. -/
theorem seal_digest {ms : List ℕ} {gen : Bool} (h : Holds ρ (chainSeal ms gen).ops)
    (hB : 4 * (parts ms gen).msg.length < 2 ^ 32) :
    let P := parts ms gen
    word (ρ (P.key.next)) = BitVec.ofNat 32 (ρ P.J.res.lo).a.val ∧
    word (ρ (P.key.next + 1)) = BitVec.ofNat 32 (ρ P.J.res.hi).a.val ∧
    ∀ i < 8, word (ρ ((chainSeal ms gen).results.getD i 0)) = blake2sWords (wordsOf ρ P.msg) (4 * P.msg.length) i := by
  intro P
  have hd : Holds ρ P.dg.ops := (seal_parts h).2.2.2.2.2.2.2.2.2.2
  have e : P.dg.ops = [Op.m2u P.key.next P.J.res.lo, .m2u (P.key.next + 1) P.J.res.hi] ++
      (blake2s (P.key.next + 2) P.msg (4 * P.msg.length)).ops := rfl
  rw [e, holds_append] at hd
  obtain ⟨hm, hb⟩ := hd
  refine ⟨m2u_word (hm _ List.mem_cons_self), m2u_word (hm _ (List.mem_cons_of_mem _ List.mem_cons_self)), fun i hi => ?_⟩
  rw [chainSeal_results]
  exact blake2s_words hb hB i hi

-- The two exported seals' messages are 63 words (252 bytes); the key messages 80 and 96 words.
#guard (parts [16, 16] false).msg.length = 63
#guard (parts [1, 2, 3] true).msg.length = 63
#guard ((parts [16, 16] false).J.res.chash ++ (parts [16, 16] false).J.res.key ++
  (parts [16, 16] false).sets.flatMap (fun c => c.res.chash ++ c.res.key)).length = 80
#guard ((parts [1, 2, 3] true).J.res.chash ++ (parts [1, 2, 3] true).J.res.key ++
  (parts [1, 2, 3] true).sets.flatMap (fun c => c.res.chash ++ c.res.key)).length = 96

/-! ### The checks -/

def rootAt (roots : List RootRegs) (i : ℕ) : RootRegs := roots.getD i ⟨[], [], [], 0, 0, [], []⟩
def restAt (rests : List RestRegs) (i : ℕ) : RestRegs := rests.getD i ⟨[], 0, [], []⟩
def openAt (opens : List SetRegs) (j : ℕ) : SetRegs := opens.getD j ⟨⟨0, [], 0, [], [], [], [], []⟩, 0, 0, [], 0, [], [], []⟩

/-- **The join's opening is the epochs'**: its range is epoch 0's `from` and the last's `to`, its start
set epoch 0's `prev`, its end set the last's `fin`, its `acc` the last hash. -/
theorem checks_join {ms : List ℕ} {gen : Bool} {J : Child} {roots : List RootRegs} {rests : List RestRegs}
    {opens : List SetRegs} {accs : List (List ℕ)} {C : Consts} {n : ℕ}
    (h : Holds ρ (checksOps ms gen J roots rests opens accs C n).ops) :
    ρ J.lo = ρ (rootAt roots 0).lo ∧ ρ J.hi = ρ (rootAt roots (ms.length - 1)).hi ∧
    (∀ w < 8, ρ (J.first.getD w 0) = ρ ((rootAt roots 0).prev.getD w 0)) ∧
    (∀ w < 8, ρ (J.last.getD w 0) = ρ ((rootAt roots (ms.length - 1)).fin.getD w 0)) ∧
    (∀ w < 8, ρ (J.tail.getD w 0) = ρ ((accs.getD (ms.length - 2) []).getD w 0)) := by
  dsimp only [checksOps] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, -⟩, -⟩, -⟩ := h
  refine ⟨?_, ?_, fun w hw => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · simpa [Op.holds, rootAt] using h0 _ List.mem_cons_self
  · simpa [Op.holds, rootAt] using h0 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · simpa [Op.holds, rootAt] using h1 _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
  · simpa [Op.holds, rootAt] using h2 _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
  · simpa [Op.holds] using h3 _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)

/-- **Consecutive epochs link**: the next starts at the previous end + 1, with the previous end set. -/
theorem checks_links {ms : List ℕ} {gen : Bool} {J : Child} {roots : List RootRegs} {rests : List RestRegs}
    {opens : List SetRegs} {accs : List (List ℕ)} {C : Consts} {n : ℕ}
    (h : Holds ρ (checksOps ms gen J roots rests opens accs C n).ops) (hC : ConstsOk ρ C) :
    ∀ i < ms.length - 1, ρ (rootAt roots (i + 1)).lo = ρ (rootAt roots i).hi + lit 1 0 0 0 ∧
      ∀ w < 8, ρ ((rootAt roots i).fin.getD w 0) = ρ ((rootAt roots (i + 1)).prev.getD w 0) := by
  dsimp only [checksOps] at h
  simp only [holds_append] at h
  obtain ⟨⟨⟨-, hl⟩, -⟩, -⟩ := h
  intro i hi
  have g := fun (o : Op) (ho : o ∈ _) => hl o (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, ho⟩)
  have a := g _ (List.mem_append_left _ List.mem_cons_self)
  have e := g _ (List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [Op.holds] at a e
  refine ⟨by rw [rootAt, rootAt, ← e, a, hC.one], fun w hw => ?_⟩
  simpa [Op.holds, rootAt] using g _ (List.mem_append_right _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩))

/-- **From genesis, the join's start set is zero words.** -/
theorem checks_genesis {ms : List ℕ} {J : Child} {roots : List RootRegs} {rests : List RestRegs}
    {opens : List SetRegs} {accs : List (List ℕ)} {C : Consts} {n : ℕ}
    (h : Holds ρ (checksOps ms true J roots rests opens accs C n).ops) (hC : ConstsOk ρ C) :
    ∀ w < 8, ρ (J.first.getD w 0) = lit 0 0 0 0 := by
  dsimp only [checksOps] at h
  simp only [holds_append, if_true] at h
  obtain ⟨⟨-, hg⟩, -⟩ := h
  intro w hw
  have := hg _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
  simp only [Op.holds] at this
  rw [this, hC.zero]

/-- **Per epoch**: its end set finishes to `fin` and its start set to `prev`; the balance
`s + sum(start) = sum(end)` (`s = sum(end)` from genesis); the counts and the start height in range. -/
theorem checks_epoch {ms : List ℕ} {gen : Bool} {J : Child} {roots : List RootRegs} {rests : List RestRegs}
    {opens : List SetRegs} {accs : List (List ℕ)} {C : Consts} {n : ℕ}
    (h : Holds ρ (checksOps ms gen J roots rests opens accs C n).ops) (hC : ConstsOk ρ C) {i : ℕ} (hi : i < ms.length) :
    let E := openAt opens (endIdx gen i)
    let B := openAt opens (startIdx gen i)
    let R := rootAt roots i
    let T := restAt rests i
    (∀ w < 8, ρ (E.fin.getD w 0) = ρ (R.fin.getD w 0)) ∧
    (hasStart gen i = true →
      (∀ w < 8, ρ (B.fin.getD w 0) = ρ (R.prev.getD w 0)) ∧
      (∀ k < 4, ρ (E.st.sum.getD k 0) = ρ (T.s.getD k 0) + ρ (B.st.sum.getD k 0)) ∧
      (IsBase (ρ T.nin + ρ E.n + ρ B.n) ∧ (ρ T.nin + ρ E.n + ρ B.n).a.val < 2 ^ 30) ∧
      (IsBase (ρ R.lo - ρ B.st.maxh - lit 1 0 0 0) ∧ (ρ R.lo - ρ B.st.maxh - lit 1 0 0 0).a.val < 2 ^ 30)) ∧
    (hasStart gen i = false →
      (∀ k < 4, ρ (T.s.getD k 0) = ρ (E.st.sum.getD k 0)) ∧
      (IsBase (ρ T.nin + ρ E.n) ∧ (ρ T.nin + ρ E.n).a.val < 2 ^ 30)) := by
  intro E B R T
  dsimp only [checksOps] at h
  simp only [holds_append] at h
  obtain ⟨-, hp⟩ := h
  have hpi := fun (o : Op) (ho : o ∈ _) => hp o (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, ho⟩)
  by_cases hs : hasStart gen i = true
  · simp only [hs, if_true] at hpi
    refine ⟨fun w hw => ?_, fun _ => ⟨fun w hw => ?_, fun k hk => ?_, ?_, ?_⟩, fun hf => absurd hs (by simp [hf])⟩
    · have e := hpi (Op.eq (E.fin.getD w 0) (R.fin.getD w 0)) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
      exact e
    · have e := hpi (Op.eq (B.fin.getD w 0) (R.prev.getD w 0)) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        apply List.mem_append_left
        exact List.mem_append_right _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩))
      exact e
    · have a := hpi (Op.add (n + ms.length + 60 * i + k) (T.s.getD k 0) (B.st.sum.getD k 0)) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_self⟩))
      have e := hpi (Op.eq (n + ms.length + 60 * i + k) (E.st.sum.getD k 0)) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.mem_cons_of_mem _ List.mem_cons_self⟩))
      simp only [Op.holds] at a e
      rw [← e, a]
    · have a4 := hpi (Op.add (n + ms.length + 60 * i + 4) T.nin E.n) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_right _ List.mem_cons_self)
      have a5 := hpi (Op.add (n + ms.length + 60 * i + 5) (n + ms.length + 60 * i + 4) B.n) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have l := BlockNode.lt30_sound (fun o ho => hpi o (by
        apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_right _ ho))
      simp only [Op.holds] at a4 a5
      rw [a5, a4] at l
      exact l
    · have s17 := hpi (Op.sub (n + ms.length + 60 * i + 17) R.lo B.st.maxh) (by
        apply List.mem_append_left
        exact List.mem_append_right _ List.mem_cons_self)
      have s18 := hpi (Op.sub (n + ms.length + 60 * i + 18) (n + ms.length + 60 * i + 17) C.one) (by
        apply List.mem_append_left
        exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
      have l := BlockNode.lt30_sound (fun o ho => hpi o (List.mem_append_right _ ho))
      simp only [Op.holds] at s17 s18
      rw [s18, s17, hC.one] at l
      exact l
  · have hs' : hasStart gen i = false := by simpa using hs
    simp only [hs', Bool.false_eq_true, if_false] at hpi
    refine ⟨fun w hw => ?_, fun ht => absurd ht (by simp [hs']), fun _ => ⟨fun k hk => ?_, ?_⟩⟩
    · have e := hpi (Op.eq (E.fin.getD w 0) (R.fin.getD w 0)) (by
        apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
      exact e
    · have e := hpi (Op.eq (T.s.getD k 0) (E.st.sum.getD k 0)) (by
        apply List.mem_append_left; apply List.mem_append_left
        exact List.mem_append_right _ (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩))
      exact e
    · have a4 := hpi (Op.add (n + ms.length + 60 * i + 4) T.nin E.n) (by
        apply List.mem_append_left
        exact List.mem_append_right _ List.mem_cons_self)
      have l := BlockNode.lt30_sound (fun o ho => hpi o (List.mem_append_right _ ho))
      simp only [Op.holds] at a4
      rw [a4] at l
      exact l

end StarkedAir.Circuit.ChainSeal
