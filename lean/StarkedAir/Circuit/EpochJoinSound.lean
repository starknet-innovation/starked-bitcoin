/-
**The epoch join's soundness** (`Circuit/EpochJoin.lean`), in the style of `EpochRootSound`.

- `rootChild_out`, `joinChild_out`: a child's output digest is Blake2s of its opening as guessed (an epoch
  root's `key ‖ fin ‖ prev? ‖ from ‖ to ‖ rest`, a join's `key ‖ start ‖ end ‖ a ‖ b ‖ acc`), the range
  words being the base values of `from`/`to` (`a`/`b`) through `m31_to_u32`;
- `rootChild_hook`, `joinChild_hook`: the child's verifier hook is called with (its preprocessed root,
  that digest) and outputs its circuit hash;
- `rootChild_zeros`: a root from genesis opens no previous set; its `first` is 8 zero words;
- `join_links`: the right's previous set is the left's end set, the right starts at the left's end + 1,
  the right's end is below `2^30`;
- `join_sound`: all of it, plus the output: `acc`, `key` and the output digest over
  `key ‖ start ‖ end ‖ a ‖ b ‖ acc` (`outWords`), for each variant.
-/
import StarkedAir.Circuit.EpochJoin
import StarkedAir.Circuit.EpochRootSound

namespace StarkedAir.Circuit.EpochJoin

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Circuit.EpochRoot (m2u_word lt30_holds val_add_lt30)

variable {ρ : ℕ → Q}

/-! ### The program, by parts -/

/-- The left child: an epoch root (`base`) or a join (`step`). -/
def left : Variant → Out Child
  | .base lp => rootChild 0 0 lp
  | .step => joinChild 0 0

/-- The right child: an epoch root from a previous set. -/
def right (v : Variant) : Out Child := rootChild 1 (left v).next true

/-- The links (as `epochJoin` builds them, from register `(right v).next`). -/
def links (v : Variant) : List Op :=
  let l := (left v).res
  let r := (right v).res
  let n := (right v).next
  (List.range 8).map (fun w => Op.eq (r.first.getD w 0) (l.last.getD w 0)) ++
    [ONE n, .add (n + 1) l.hi n, .eq r.lo (n + 1)] ++ BlockNode.lt30 (n + 2) r.hi

/-- The output range's words. -/
def ab (v : Variant) : List Op :=
  [.m2u ((right v).next + 11) (left v).res.lo, .m2u ((right v).next + 12) (right v).res.hi]

/-- `acc`'s message registers: `out_left ‖ out_right` (`base`), `acc_left ‖ out_right` (`step`). -/
def accIn (v : Variant) : List ℕ :=
  (match v with | .base _ => (left v).res.out | .step => (left v).res.tail) ++ (right v).res.out

def accOut (v : Variant) : Out (List ℕ) := blake2s ((right v).next + 13) (accIn v) 64

/-- The key's message registers: `chash_left ‖ key_left ‖ chash_right ‖ key_right`. -/
def keyIn (v : Variant) : List ℕ :=
  (left v).res.chash ++ (left v).res.key ++ (right v).res.chash ++ (right v).res.key

def keyOut (v : Variant) : Out (List ℕ) := blake2s (accOut v).next (keyIn v) 128

/-- The output message's registers: `key ‖ start ‖ end ‖ a ‖ b ‖ acc`. -/
def outMsg (v : Variant) : List ℕ :=
  (keyOut v).res ++ (left v).res.first ++ (right v).res.last ++ [(right v).next + 11, (right v).next + 12] ++
    (accOut v).res

def dgOut (v : Variant) : Out (List ℕ) := blake2s (keyOut v).next (outMsg v) (4 * (outMsg v).length)

theorem epochJoin_ops (v : Variant) : (epochJoin v).ops =
    (left v).ops ++ (right v).ops ++ links v ++ ab v ++ (accOut v).ops ++ (keyOut v).ops ++ (dgOut v).ops := by
  cases v <;> rfl

theorem epochJoin_results (v : Variant) : (epochJoin v).results = (dgOut v).res := by
  cases v <;> rfl

/-! ### The semantic messages -/

/-- An epoch root's opening (`EpochRoot.digestOut`'s outer message): `key ‖ fin ‖ prev (prevV) ‖ from ‖
to ‖ rest`, `from`/`to` as their base values. -/
def rootWords (ρ : ℕ → Q) (c : Child) (prevV : Bool) : List Spec.Blake2s.Word :=
  wordsOf ρ c.key ++ wordsOf ρ c.last ++ (if prevV then wordsOf ρ c.first else []) ++
    [BitVec.ofNat 32 (ρ c.lo).a.val, BitVec.ofNat 32 (ρ c.hi).a.val] ++ wordsOf ρ c.tail

/-- A join's opening (this program's output message): `key ‖ start ‖ end ‖ a ‖ b ‖ acc`. -/
def joinWords (ρ : ℕ → Q) (c : Child) : List Spec.Blake2s.Word :=
  wordsOf ρ c.key ++ wordsOf ρ c.first ++ wordsOf ρ c.last ++
    [BitVec.ofNat 32 (ρ c.lo).a.val, BitVec.ofNat 32 (ρ c.hi).a.val] ++ wordsOf ρ c.tail

/-- The left child's opening, by variant. -/
def leftWords (ρ : ℕ → Q) : Variant → Child → List Spec.Blake2s.Word
  | .base lp, c => rootWords ρ c lp
  | .step, c => joinWords ρ c

/-- `acc`'s message: `out_left ‖ out_right` (`base`), `acc_left ‖ out_right` (`step`). -/
def accWords (ρ : ℕ → Q) (v : Variant) : List Spec.Blake2s.Word :=
  (match v with | .base _ => wordsOf ρ (left v).res.out | .step => wordsOf ρ (left v).res.tail) ++
    wordsOf ρ (right v).res.out

/-- The key's message: `chash_left ‖ key_left ‖ chash_right ‖ key_right`. -/
def keyWords (ρ : ℕ → Q) (v : Variant) : List Spec.Blake2s.Word :=
  wordsOf ρ (left v).res.chash ++ wordsOf ρ (left v).res.key ++ wordsOf ρ (right v).res.chash ++
    wordsOf ρ (right v).res.key

/-- **The output message**, semantically: `key ‖ start ‖ end ‖ a ‖ b ‖ acc` with `key = Blake2s(keyWords)`,
`start` the left's first set, `end` the right's last set, `a` the left's `from`/`a`, `b` the right's `to`,
`acc = Blake2s(accWords)`. -/
def outWords (ρ : ℕ → Q) (v : Variant) : List Spec.Blake2s.Word :=
  (List.range 8).map (blake2sWords (keyWords ρ v) 128) ++ wordsOf ρ (left v).res.first ++
    wordsOf ρ (right v).res.last ++
    [BitVec.ofNat 32 (ρ (left v).res.lo).a.val, BitVec.ofNat 32 (ρ (right v).res.hi).a.val] ++
    (List.range 8).map (blake2sWords (accWords ρ v) 64)

/-! ### Generic pieces -/

/-- A message `k ‖ f ‖ p ‖ [x, y] ‖ rs` whose `x`, `y` are `m31_to_u32` of `a`, `b`. -/
theorem msg_words {k f p rs : List ℕ} {x y a b : ℕ} (hx : (Op.m2u x a).holds ρ) (hy : (Op.m2u y b).holds ρ) :
    (k ++ f ++ p ++ [x, y] ++ rs).map (word ∘ ρ) =
      wordsOf ρ k ++ wordsOf ρ f ++ wordsOf ρ p ++ [BitVec.ofNat 32 (ρ a).a.val, BitVec.ofNat 32 (ρ b).a.val] ++
        wordsOf ρ rs := by
  simp only [List.map_append, List.map_cons, List.map_nil, Function.comp_apply, m2u_word hx, m2u_word hy, wordsOf]

/-! ### The children -/

theorem rootChild_lengths (i n : ℕ) (prevV : Bool) :
    (rootChild i n prevV).res.key.length = 8 ∧ (rootChild i n prevV).res.first.length = 8 ∧
    (rootChild i n prevV).res.last.length = 8 ∧ (rootChild i n prevV).res.tail.length = 8 ∧
    (rootChild i n prevV).res.out.length = 8 ∧ (rootChild i n prevV).res.chash.length = 8 := by
  cases prevV <;> simp [rootChild, guessHash, blake2s]

theorem joinChild_lengths (i n : ℕ) :
    (joinChild i n).res.key.length = 8 ∧ (joinChild i n).res.first.length = 8 ∧
    (joinChild i n).res.last.length = 8 ∧ (joinChild i n).res.tail.length = 8 ∧
    (joinChild i n).res.out.length = 8 ∧ (joinChild i n).res.chash.length = 8 := by
  simp [joinChild, guessHash, blake2s]

/-- **An epoch root child's output digest** is Blake2s of its opening (`rootWords`). -/
theorem rootChild_out {i n : ℕ} {prevV : Bool} (h : Holds ρ (rootChild i n prevV).ops) :
    ∀ j < 8, word (ρ ((rootChild i n prevV).res.out.getD j 0)) =
      blake2sWords (rootWords ρ (rootChild i n prevV).res prevV) (4 * (8 + 8 + (if prevV then 8 else 0) + 2 + 8)) j := by
  intro j hj
  dsimp only [rootChild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hq⟩, -⟩, -⟩, ho⟩, -⟩, -⟩ := h
  have hb := blake2s_words ho (by cases prevV <;> simp [BlockRec.guessHash_length]) j hj
  rw [hb, msg_words (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))]
  congr 1
  · cases prevV <;> rfl
  · cases prevV <;> simp [BlockRec.guessHash_length]

/-- **A join child's output digest** is Blake2s of its opening (`joinWords`). -/
theorem joinChild_out {i n : ℕ} (h : Holds ρ (joinChild i n).ops) :
    ∀ j < 8, word (ρ ((joinChild i n).res.out.getD j 0)) = blake2sWords (joinWords ρ (joinChild i n).res) (4 * 34) j := by
  intro j hj
  dsimp only [joinChild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, hq⟩, -⟩, ho⟩, -⟩, -⟩ := h
  have hb := blake2s_words ho (by simp [BlockRec.guessHash_length]) j hj
  rw [hb, msg_words (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    (hq _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))]
  congr 1

/-- An epoch root child's hook: args (its preprocessed root ‖ its output digest), outputs its circuit hash. -/
theorem rootChild_hook (i n : ℕ) (prevV : Bool) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (rootChild i n prevV).res.out) (rootChild i n prevV).res.chash ∈ (rootChild i n prevV).ops :=
  ⟨_, BlockRec.guessHash_length _ _, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

theorem joinChild_hook (i n : ℕ) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook i (root ++ (joinChild i n).res.out) (joinChild i n).res.chash ∈ (joinChild i n).ops :=
  ⟨_, BlockRec.guessHash_length _ _, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩

/-- A root from genesis opens no previous set: its `first` is 8 zero words. -/
theorem rootChild_zeros {i n : ℕ} (h : Holds ρ (rootChild i n false).ops) :
    wordsOf ρ (rootChild i n false).res.first = List.replicate 8 0 := by
  dsimp only [rootChild] at h ⊢
  simp only [holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, hz⟩, -⟩, -⟩, -⟩ := h
  simp only [Bool.false_eq_true, ite_false] at hz ⊢
  rw [show List.replicate 8 (0 : Spec.Blake2s.Word) = (List.range 8).map (fun _ => 0) by simp, wordsOf, List.map_map]
  refine List.map_congr_left (fun w hw => ?_)
  have := const_word (hz _ (List.mem_map.mpr ⟨w, hw, rfl⟩)) (by norm_num)
  simpa using this

/-! ### The join -/

theorem left_lengths (v : Variant) :
    (left v).res.key.length = 8 ∧ (left v).res.first.length = 8 ∧ (left v).res.last.length = 8 ∧
    (left v).res.tail.length = 8 ∧ (left v).res.out.length = 8 ∧ (left v).res.chash.length = 8 := by
  cases v with
  | base lp => exact rootChild_lengths 0 0 lp
  | step => exact joinChild_lengths 0 0

theorem rootWords_length {c : Child} {prevV : Bool} (hk : c.key.length = 8) (hf : c.first.length = 8)
    (hl : c.last.length = 8) (ht : c.tail.length = 8) :
    (rootWords ρ c prevV).length = 8 + 8 + (if prevV then 8 else 0) + 2 + 8 := by
  cases prevV <;> simp [rootWords, wordsOf, hk, hf, hl, ht]

theorem joinWords_length {c : Child} (hk : c.key.length = 8) (hf : c.first.length = 8)
    (hl : c.last.length = 8) (ht : c.tail.length = 8) : (joinWords ρ c).length = 34 := by
  simp [joinWords, wordsOf, hk, hf, hl, ht]

/-- The left child's output digest is Blake2s of its opening. -/
theorem left_out {v : Variant} (h : Holds ρ (left v).ops) :
    ∀ i < 8, word (ρ ((left v).res.out.getD i 0)) =
      blake2sWords (leftWords ρ v (left v).res) (4 * (leftWords ρ v (left v).res).length) i := by
  obtain ⟨hk, hf, hl, ht, -, -⟩ := left_lengths v
  cases v with
  | base lp =>
    intro i hi
    rw [show leftWords ρ (.base lp) (left (.base lp)).res = rootWords ρ (rootChild 0 0 lp).res lp from rfl,
      rootWords_length (c := (rootChild 0 0 lp).res) hk hf hl ht]
    exact rootChild_out h i hi
  | step =>
    intro i hi
    rw [show leftWords ρ .step (left .step).res = joinWords ρ (joinChild 0 0).res from rfl,
      joinWords_length (c := (joinChild 0 0).res) hk hf hl ht]
    exact joinChild_out h i hi

theorem left_hook (v : Variant) : ∃ root : List ℕ, root.length = 8 ∧
    Op.hook 0 (root ++ (left v).res.out) (left v).res.chash ∈ (left v).ops := by
  cases v with
  | base lp => exact rootChild_hook 0 0 lp
  | step => exact joinChild_hook 0 0

/-- **The links.** The right's previous set is the left's end set (register-wise), the right starts at
the left's end + 1, the right's end is a base value below `2^30`. -/
theorem join_links {v : Variant} (h : Holds ρ (links v)) :
    (∀ w < 8, ρ ((right v).res.first.getD w 0) = ρ ((left v).res.last.getD w 0)) ∧
    ρ (right v).res.lo = ρ (left v).res.hi + lit 1 0 0 0 ∧
    IsBase (ρ (right v).res.hi) ∧ (ρ (right v).res.hi).a.val < 2 ^ 30 := by
  unfold links at h
  rw [holds_append, holds_append] at h
  obtain ⟨⟨he, hc⟩, hl⟩ := h
  refine ⟨fun w hw => ?_, ?_, lt30_holds hl (fun _ h => h)⟩
  · have := he _ (List.mem_map.mpr ⟨w, List.mem_range.mpr hw, rfl⟩)
    simpa [Op.holds] using this
  · have h1 := hc _ List.mem_cons_self
    have h2 := hc _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have h3 := hc _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    simp only [Op.holds, ONE] at h1 h2 h3
    rw [h3, h2, h1]

theorem one_val : ((1 : ℕ) : F).val = 1 := by
  rw [ZMod.val_natCast]; unfold P; norm_num

theorem wordsOf_ext {a b : List ℕ} (ha : a.length = 8) (hb : b.length = 8)
    (h : ∀ w < 8, ρ (a.getD w 0) = ρ (b.getD w 0)) : wordsOf ρ a = wordsOf ρ b := by
  apply List.ext_getElem (by simp [wordsOf, ha, hb])
  intro w h1 h2
  have hw : w < 8 := by simpa [wordsOf, ha] using h1
  have e := h w hw
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at e
  simp [wordsOf, e]

/-- **The epoch join is sound.** For an assignment `ρ` holding the program's ops, with `l`, `r` the left
and right children's opened fields:
- the left's output digest is Blake2s of its opening (an epoch root's `key ‖ fin ‖ prev? ‖ from ‖ to ‖
  rest`, or a join's `key ‖ start ‖ end ‖ a ‖ b ‖ acc`: `leftWords`), and hook 0 is called with (a
  preprocessed root, that digest) and outputs `l.chash`;
- the right's (an epoch root from a previous set) likewise, at hook 1;
- the links: `r.prev = l.end` (word-wise), `r.from = l.b + 1` (in the field; as naturals once `l.b < 2^30`,
  which each child's own proof bounds), `r.to < 2^30`;
- a root from genesis on the left opens 8 zero words as its start;
- `acc = Blake2s(accWords)`, `key = Blake2s(keyWords)`, and the output is Blake2s of `outWords`:
  `key ‖ start (l.first) ‖ end (r.last) ‖ a (l.lo) ‖ b (r.hi) ‖ acc`. -/
theorem join_sound {v : Variant} (h : Holds ρ (epochJoin v).ops) :
    let l := (left v).res
    let r := (right v).res
    ((∀ i < 8, word (ρ (l.out.getD i 0)) = blake2sWords (leftWords ρ v l) (4 * (leftWords ρ v l).length) i) ∧
      ∃ root : List ℕ, root.length = 8 ∧ Op.hook 0 (root ++ l.out) l.chash ∈ (epochJoin v).ops) ∧
    ((∀ i < 8, word (ρ (r.out.getD i 0)) = blake2sWords (rootWords ρ r true) (4 * (8 + 8 + 8 + 2 + 8)) i) ∧
      ∃ root : List ℕ, root.length = 8 ∧ Op.hook 1 (root ++ r.out) r.chash ∈ (epochJoin v).ops) ∧
    (wordsOf ρ r.first = wordsOf ρ l.last ∧
      ρ r.lo = ρ l.hi + lit 1 0 0 0 ∧ ((ρ l.hi).a.val < 2 ^ 30 → (ρ r.lo).a.val = (ρ l.hi).a.val + 1) ∧
      IsBase (ρ r.hi) ∧ (ρ r.hi).a.val < 2 ^ 30) ∧
    (v = .base false → wordsOf ρ l.first = List.replicate 8 0) ∧
    (∀ i < 8, word (ρ ((accOut v).res.getD i 0)) = blake2sWords (accWords ρ v) 64 i) ∧
    (∀ i < 8, word (ρ ((keyOut v).res.getD i 0)) = blake2sWords (keyWords ρ v) 128 i) ∧
    (∀ i < 8, word (ρ ((epochJoin v).results.getD i 0)) = blake2sWords (outWords ρ v) (4 * 34) i) := by
  intro l r
  have h' := h
  rw [epochJoin_ops] at h'
  simp only [holds_append] at h'
  obtain ⟨⟨⟨⟨⟨⟨hL, hR⟩, hlk⟩, hab⟩, hacc⟩, hkey⟩, hdg⟩ := h'
  have memL : ∀ o ∈ (left v).ops, o ∈ (epochJoin v).ops := fun o ho => by
    rw [epochJoin_ops]; simp only [List.mem_append, ho, true_or]
  have memR : ∀ o ∈ (right v).ops, o ∈ (epochJoin v).ops := fun o ho => by
    rw [epochJoin_ops]; simp only [List.mem_append, ho, true_or, or_true]
  obtain ⟨-, lf, ll, -, -, -⟩ := left_lengths v
  obtain ⟨-, rf, rl, -, -, -⟩ := rootChild_lengths 1 (left v).next true
  have rf : (right v).res.first.length = 8 := rf
  have rl : (right v).res.last.length = 8 := rl
  obtain ⟨elink, elo, ehi, ehi30⟩ := join_links hlk
  -- the children
  refine ⟨⟨left_out hL, ?_⟩, ⟨rootChild_out hR, ?_⟩, ⟨wordsOf_ext rf ll elink, elo, fun hb => ?_, ehi, ehi30⟩, ?_, ?_⟩
  · obtain ⟨root, hr, hm⟩ := left_hook v
    exact ⟨root, hr, memL _ hm⟩
  · obtain ⟨root, hr, hm⟩ := rootChild_hook 1 (left v).next true
    exact ⟨root, hr, memR _ hm⟩
  · have e := congrArg Q.a elo
    rw [add_a] at e
    rw [e, val_add_lt30 hb (by show ((1 : ℕ) : F).val < 2 ^ 30; rw [one_val]; norm_num)]
    show _ + ((1 : ℕ) : F).val = _
    rw [one_val]
  · rintro rfl
    exact rootChild_zeros hL
  -- the output
  have hA : ∀ i < 8, word (ρ ((accOut v).res.getD i 0)) = blake2sWords (accWords ρ v) 64 i := by
    intro i hi
    rw [show accWords ρ v = (accIn v).map (word ∘ ρ) by cases v <;> simp [accIn, accWords, wordsOf]]
    exact blake2s_words hacc (by norm_num) i hi
  have hK : ∀ i < 8, word (ρ ((keyOut v).res.getD i 0)) = blake2sWords (keyWords ρ v) 128 i := by
    intro i hi
    rw [show keyWords ρ v = (keyIn v).map (word ∘ ρ) by simp [keyIn, keyWords, wordsOf]]
    exact blake2s_words hkey (by norm_num) i hi
  refine ⟨hA, hK, fun i hi => ?_⟩
  have hol : (outMsg v).length = 34 := by
    simp only [outMsg, keyOut, accOut, List.length_append, BlockRec.blake2s_length, lf, rl, List.length_cons, List.length_nil]
  rw [epochJoin_results]
  have hd := blake2s_words hdg (by rw [hol]; norm_num) i hi
  unfold dgOut
  rw [hd, hol]
  congr 1
  unfold outMsg outWords
  rw [msg_words (hab _ List.mem_cons_self) (hab _ (List.mem_cons_of_mem _ List.mem_cons_self)),
    BlockRec.wordsOf_eq (res := (keyOut v).res) (BlockRec.blake2s_length _ _ _) hK,
    BlockRec.wordsOf_eq (res := (accOut v).res) (BlockRec.blake2s_length _ _ _) hA]

end StarkedAir.Circuit.EpochJoin
