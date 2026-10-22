/-
**The chain of epochs, composed** (`Circuit/EpochJoin.lean`, `Circuit/EpochRoot.lean`).

The trust records, in the style of `BlockNodeK.TrustK`'s `nodeCircuit`: what a verifier may assume of a
proof whose circuit hash is pinned and whose output digest is `d`:
- `RootSat VGates M prevV d`: some assignment satisfies the epoch root program `epochRoot M prevV`, with
  its hook gates, and outputs `d`;
- `JoinSat VGates v d`: likewise for the join program `epochJoin v`;
- `TrustE`: `TrustK` (the block trees' named hypotheses) plus `rootCircuit` and `joinCircuit`: a satisfied
  circuit with a pinned epoch root identity `rootH M prevV s` (`s`: the circuit's variant, e.g. its node
  shape or lift) or join identity `joinH v` gives `RootSat` or `JoinSat` of its output.

The chain, as the verifier replays it (`Chain`): the first join is `base g e₀ e₁` (two epoch roots, the
first from a previous set when `g`, else from genesis), each later one `step c e` (the chain so far, then an
epoch root from a previous set). The verifier pins each epoch's shape (`EpS`: `M` children, the root's
variant, the children's trees, whose hashes and keys give the root's key `EpS.key`) and the join identities;
the expected key of a join is `Chain.key` (`H(hash‖key)` of both children, as `epochJoin` computes it).

- `root_range`: a root's own proof bounds its range: `from ≤ to < 2^30` (and the digest's rest is the
  verifier's), from the children's proven summaries (`root_children`) and the links (`links_sound`);
- `rootChild_ok`: an epoch root child of a join, its identity and key pinned, has a proven root
  (`RootOk`: the root circuit is satisfied with the recomputed digest, `from ≤ to < 2^30`);
- `join_open`: a join with a pinned identity and key: its children's identities and keys are the pinned ones;
- **`chain_sound`**: a join proof with a pinned identity, whose output digest is `H(Chain.key ++ rest)`,
  outputs the digest (`Chain.digest`) of a chain of epoch openings over the pinned shapes that is
  `Valid`: every epoch root is proven with its opening (`RootOk`), consecutive epochs link (the previous
  set digest is the last final set digest, `from = to + 1`), a genesis start opens zero words; the output
  is `key ‖ start ‖ end ‖ a ‖ b ‖ acc` with `start` the first epoch's previous set, `end` the last's final
  set, `a` the first's `from`, `b` the last's `to`, `acc` the running Blake2s over the epoch roots' output
  digests. Or Blake2s has a collision (as `rootK_epoch`; see `RecCR` on `Collision`).
- `Chain.Valid.range`, `.links`, `.roots`, `Chain.acc_fold`: the chain-level statement: `a ≤ b < 2^30`,
  each consecutive pair of epochs links (`List.IsChain Link`), every root proven, and `acc` is the left
  fold of Blake2s; `chain_cover` states it all at once;
- `chain_verify`: the verifier's own openings (from which it recomputed the digest) form a `Valid` chain
  (`acc_valid`: `acc` binds every epoch's opening).

The join's caveats: the left child's `b < 2^30` (for `from = b + 1` over the naturals) and `a`'s range come
from the left child's own proof: the epoch root's `root_range` (base) or, by induction, the chain so far
(step). Like `rootK_epoch`, the conclusions are `… ∨ Collision`, which `RecCR.collision_true` makes
vacuous; a per-instance restatement (`RecCR`'s `TrustKW` style) is not done here.
-/
import StarkedAir.Circuit.EpochJoinSound

namespace StarkedAir.Circuit.EpochChain

open StarkedAir StarkedAir.Circuit Q
local notation "Word" => Spec.Blake2s.Word
open StarkedAir.Circuit.BlockTree (SumOkP)
open StarkedAir.Circuit.BlockRec (H H_eq H_length Collision HookGates LeafOutP childSum wordsOf_eq wordsOf_length)
open StarkedAir.Circuit.BlockNodeK (TrustK TreeK keyOfK kid)
open StarkedAir.Circuit.EpochRoot (epochRoot parts digestWords root_children root_parts links_sound val_add_lt30)
open StarkedAir.Circuit.EpochJoin (Variant epochJoin rootChild joinChild left right rootWords joinWords outWords
  keyWords accWords rootChild_lengths rootChild_out rootWords_length)

/-! ### The trust records -/

/-- **An epoch root's output**: some assignment satisfies `epochRoot M prevV` with its hook gates and
outputs `d`. -/
def RootSat (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop) (M : ℕ) (prevV : Bool) (d : List Word) : Prop :=
  ∃ ρ : ℕ → Q, Holds ρ (epochRoot M prevV).ops ∧ wordsOf ρ (epochRoot M prevV).results = d ∧
    HookGates VGates ρ (epochRoot M prevV).ops

/-- **A join's output**: some assignment satisfies `epochJoin v` with its hook gates and outputs `d`. -/
def JoinSat (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop) (v : Variant) (d : List Word) : Prop :=
  ∃ ρ : ℕ → Q, Holds ρ (epochJoin v).ops ∧ wordsOf ρ (epochJoin v).results = d ∧ HookGates VGates ρ (epochJoin v).ops

/-- **The named hypotheses for a chain** (`TrustK`'s, plus): a satisfied circuit with an epoch root identity
`rootH M prevV s` (variant `s` of the root over `M` children) or a join identity `joinH v` runs that program
(circuit AIR soundness and the replay's faithfulness, as `TrustK.nodeCircuit`). -/
structure TrustE (Acc SatC : List Word → List Word → Prop) (VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop)
    (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (rootH : ℕ → Bool → ℕ → List Word)
    (joinH : Variant → List Word) (LeafOk : List Word → Prop) : Prop
    extends TrustK Acc SatC VGates leafH nodeH LeafOk where
  rootCircuit : ∀ M prevV s d, SatC (rootH M prevV s) d → RootSat VGates M prevV d
  joinCircuit : ∀ v d, SatC (joinH v) d → JoinSat VGates v d

/-! ### Chains -/

/-- An epoch's shape, as the verifier pins it: `M` children, the root circuit's variant `s`, the children's
trees `ts` (their hashes and keys give the root's key). -/
structure EpS where
  M : ℕ
  s : ℕ
  ts : ℕ → TreeK

/-- An epoch root's opening after its key: the final set digest, the previous set digest (zero words for
an epoch from genesis), `from`, `to`, and `rest`'s 8 words. -/
structure Open where
  fin : List Word
  prev : List Word
  lo : ℕ
  hi : ℕ
  rest : List Word

/-- An epoch: its shape and its opening. -/
structure Ep where
  sh : EpS
  o : Open

/-- A chain of joins: `base g e₀ e₁` (the first epoch from a previous set when `g`, else from genesis),
`step c e`. -/
inductive Chain (α : Type) where
  | base (g : Bool) (e0 e1 : α)
  | step (c : Chain α) (e : α)

namespace Chain
variable {α β : Type}

def map (f : α → β) : Chain α → Chain β
  | base g e0 e1 => base g (f e0) (f e1)
  | step c e => step (c.map f) (f e)

/-- The join variant at the chain's top. -/
def variant : Chain α → Variant
  | base g _ _ => .base g
  | step _ _ => .step

/-- Whether the first epoch starts from a previous set. -/
def gen : Chain α → Bool
  | base g _ _ => g
  | step c _ => c.gen

def first : Chain α → α
  | base _ e0 _ => e0
  | step c _ => c.first

def last : Chain α → α
  | base _ _ e1 => e1
  | step _ e => e

/-- The epochs, in order. -/
def epochs : Chain α → List α
  | base _ e0 e1 => [e0, e1]
  | step c e => c.epochs ++ [e]

@[simp] theorem variant_map (f : α → β) : ∀ c : Chain α, (c.map f).variant = c.variant
  | base _ _ _ => rfl
  | step _ _ => rfl

@[simp] theorem gen_map (f : α → β) : ∀ c : Chain α, (c.map f).gen = c.gen
  | base _ _ _ => rfl
  | step c _ => gen_map f c

@[simp] theorem first_map (f : α → β) : ∀ c : Chain α, (c.map f).first = f c.first
  | base _ _ _ => rfl
  | step c _ => first_map f c

@[simp] theorem last_map (f : α → β) : ∀ c : Chain α, (c.map f).last = f c.last
  | base _ _ _ => rfl
  | step _ _ => rfl

end Chain

section
variable (leafH : ℕ → List Word) (nodeH : ℕ → ℕ → List Word) (rootH : ℕ → Bool → ℕ → List Word)
  (joinH : Variant → List Word)

/-- An epoch root's key, as the verifier computes it from the children's trees. -/
def EpS.key (e : EpS) : List Word :=
  keyOfK e.M (fun i => (e.ts i).hash leafH nodeH) (fun i => (e.ts i).key leafH nodeH)

/-- The verifier's bounds on an epoch's shape (as `rootK_epoch` takes them). -/
def EpS.Ok (e : EpS) : Prop := 0 < e.M ∧ 68 + 64 * e.M < 2 ^ 32 ∧ ∀ i < e.M, (e.ts i).Ok

/-- An epoch root's output message after the key: `fin ‖ prev (prevV) ‖ from ‖ to ‖ rest`. -/
def rootRest (prevV : Bool) (o : Open) : List Word :=
  o.fin ++ (if prevV then o.prev else []) ++ [BitVec.ofNat 32 o.lo, BitVec.ofNat 32 o.hi] ++ o.rest

/-- An epoch root's output message (`EpochRoot.digestOut`'s outer one). -/
def rootMsg (K : List Word) (prevV : Bool) (o : Open) : List Word :=
  K ++ o.fin ++ (if prevV then o.prev else []) ++ [BitVec.ofNat 32 o.lo, BitVec.ofNat 32 o.hi] ++ o.rest

/-- An epoch root's output digest. -/
def Ep.out (e : Ep) (prevV : Bool) : List Word := H (rootMsg (e.sh.key leafH nodeH) prevV e.o)

/-- **The expected key** of a chain's top join (`epochJoin`'s `key`): `H(hash ‖ key)` of its two
children, the identities pinned. -/
def Chain.key : Chain EpS → List Word
  | .base g e0 e1 => H (rootH e0.M g e0.s ++ e0.key leafH nodeH ++ rootH e1.M true e1.s ++ e1.key leafH nodeH)
  | .step c e => H (joinH c.variant ++ c.key ++ rootH e.M true e.s ++ e.key leafH nodeH)

/-- **`acc`**: Blake2s over the epoch roots' output digests (`base`: `H(out₀ ‖ out₁)`; `step`: `H(acc ‖ out)`). -/
def Chain.acc : Chain Ep → List Word
  | .base g e0 e1 => H (e0.out leafH nodeH g ++ e1.out leafH nodeH true)
  | .step c e => H (c.acc ++ e.out leafH nodeH true)

/-- **A join's output message**: `key ‖ start ‖ end ‖ a ‖ b ‖ acc`. -/
def Chain.msg (c : Chain Ep) : List Word :=
  (c.map Ep.sh).key leafH nodeH rootH joinH ++ c.first.o.prev ++ c.last.o.fin ++
    [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++ c.acc leafH nodeH

def Chain.digest (c : Chain Ep) : List Word := H (c.msg leafH nodeH rootH joinH)

/-- A chain of shapes is within the verifier's bounds. -/
def Chain.Ok : Chain EpS → Prop
  | .base _ e0 e1 => e0.Ok ∧ e1.Ok
  | .step c e => c.Ok ∧ e.Ok

/-- An opening's digests are 8 words. -/
def Open.WF (o : Open) : Prop := o.fin.length = 8 ∧ o.prev.length = 8 ∧ o.rest.length = 8

variable (SatC : List Word → List Word → Prop)

/-- **A proven epoch root**: its circuit (pinned identity) is satisfied with the digest of its opening, and
its range is `from ≤ to < 2^30`. -/
def RootOk (e : Ep) (prevV : Bool) : Prop :=
  SatC (rootH e.sh.M prevV e.sh.s) (e.out leafH nodeH prevV) ∧ e.o.WF ∧ e.o.lo ≤ e.o.hi ∧ e.o.hi < 2 ^ 30

/-- **Consecutive epochs link**: the previous set digest is the last final one, `from` is the last `to + 1`. -/
def Link (e e' : Ep) : Prop := e'.o.prev = e.o.fin ∧ e'.o.lo = e.o.hi + 1

/-- **A valid chain**: every epoch root proven, consecutive ones linked, a genesis start zero words. -/
def Chain.Valid : Chain Ep → Prop
  | .base g e0 e1 => RootOk leafH nodeH rootH SatC e0 g ∧ (g = false → e0.o.prev = List.replicate 8 0) ∧
      RootOk leafH nodeH rootH SatC e1 true ∧ Link e0 e1
  | .step c e => c.Valid ∧ RootOk leafH nodeH rootH SatC e true ∧ Link c.last e

end

/-! ### An epoch root's range, from its own proof -/

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word}

theorem dpubs_length (M : ℕ) (prevV : Bool) : (parts M prevV).dpubs.length = 17 + 16 * M := by
  simp [parts, EpochRoot.sums, List.length_flatMap]
  ring

/-- **An epoch root bounds its range**: with its children proven (`root_children`), `from ≤ to < 2^30`
(`links_sound` gives `from < 2^30` and `to + 1 < 2^30` in the field; the last child's count is a power of
two, so `to + 1` does not wrap). The digest's rest is the verifier's. -/
theorem root_range {ok : (ℕ → F) → Prop} (T : TrustK Acc SatC VGates leafH nodeH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    {M : ℕ} {prevV : Bool} (hM0 : 0 < M) (hM : 68 + 64 * M < 2 ^ 32)
    (ts : ℕ → TreeK) (hok : ∀ i < M, (ts i).Ok) {ρ : ℕ → Q}
    (h : Holds ρ (epochRoot M prevV).ops) (hg : HookGates VGates ρ (epochRoot M prevV).ops) (rest : List Word)
    (hrest : 4 * (8 + rest.length) < 2 ^ 32)
    (hd : wordsOf ρ (epochRoot M prevV).results =
      H (keyOfK M (fun i => (ts i).hash leafH nodeH) (fun i => (ts i).key leafH nodeH) ++ rest)) :
    ((digestWords ρ M prevV).drop 8 = rest ∧
      (ρ (parts M prevV).inp.res.lo).a.val ≤ (ρ (parts M prevV).inp.res.hi).a.val ∧
      (ρ (parts M prevV).inp.res.hi).a.val < 2 ^ 30) ∨ Collision := by
  by_cases col : Collision
  · exact Or.inr col
  have hR : 4 * (parts M prevV).dpubs.length < 2 ^ 32 := by rw [dpubs_length]; omega
  obtain ⟨hkids, hrest'⟩ := (root_children T hl hn (by omega) hR ts hok h hg rest hrest hd).resolve_right col
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

/-! ### Openings, digests, lengths -/

/-- An epoch root child's opening, as a join guessed it. -/
def rootOpen (ρ : ℕ → Q) (c : EpochJoin.Child) : Open :=
  ⟨wordsOf ρ c.last, wordsOf ρ c.first, (ρ c.lo).a.val, (ρ c.hi).a.val, wordsOf ρ c.tail⟩

theorem rootWords_eq (ρ : ℕ → Q) (c : EpochJoin.Child) (p : Bool) :
    rootWords ρ c p = rootMsg (wordsOf ρ c.key) p (rootOpen ρ c) := rfl

theorem rootMsg_split (K : List Word) (p : Bool) (o : Open) : rootMsg K p o = K ++ rootRest p o := by
  simp [rootMsg, rootRest]

theorem rootRest_length {o : Open} (h : o.WF) (p : Bool) :
    (rootRest p o).length = 8 + (if p then 8 else 0) + 2 + 8 := by
  obtain ⟨h1, h2, h3⟩ := h
  cases p <;> simp [rootRest, h1, h2, h3]

theorem val_lt32 (x : F) : x.val < 2 ^ 32 := lt_trans (ZMod.val_lt x) (by unfold P; norm_num)

theorem ofNat_inj {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : BitVec.ofNat 32 a = BitVec.ofNat 32 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

theorem wordsOf_H {ρ : ℕ → Q} {res : List ℕ} (hl : res.length = 8) {m : List Word} {n : ℕ} (hn : n = 4 * m.length)
    (h : ∀ i < 8, word (ρ (res.getD i 0)) = blake2sWords m n i) : wordsOf ρ res = H m := by
  rw [wordsOf_eq hl h, H, hn]

/-- An epoch root's digest message after the key. -/
theorem digestWords_drop {ρ : ℕ → Q} {M : ℕ} {prevV : Bool} :
    (digestWords ρ M prevV).drop 8 =
      (parts M prevV).inp.res.fin.map (word ∘ ρ) ++
        (if prevV then (parts M prevV).inp.res.prev.map (word ∘ ρ) else []) ++
        [BitVec.ofNat 32 (ρ (parts M prevV).inp.res.lo).a.val, BitVec.ofNat 32 (ρ (parts M prevV).inp.res.hi).a.val] ++
        (List.range 8).map (blake2sWords (EpochRoot.restWords ρ M prevV) (4 * (parts M prevV).dpubs.length)) := by
  have hk8 : (parts M prevV).key.res.length = 8 := by show ((List.range 8).map _).length = 8; simp
  unfold digestWords
  simp only [List.append_assoc]
  rw [List.drop_left' (by rw [List.length_map, hk8])]

theorem keyWords_length {ρ : ℕ → Q} (v : Variant) : (keyWords ρ v).length = 32 := by
  obtain ⟨k, -, -, -, -, c⟩ := EpochJoin.left_lengths v
  obtain ⟨k', -, -, -, -, c'⟩ := rootChild_lengths 1 (left v).next true
  simp only [keyWords, List.length_append, wordsOf_length, k, c]
  rw [show (right v).res.chash.length = 8 from c', show (right v).res.key.length = 8 from k']

theorem accWords_length {ρ : ℕ → Q} (v : Variant) : (accWords ρ v).length = 16 := by
  obtain ⟨-, -, -, t, o, -⟩ := EpochJoin.left_lengths v
  obtain ⟨-, -, -, -, o', -⟩ := rootChild_lengths 1 (left v).next true
  have o' : (right v).res.out.length = 8 := o'
  cases v <;> simp [accWords, wordsOf_length, t, o, o']

/-- A join's output message, split as `Chain.msg`. -/
theorem outWords_eq {ρ : ℕ → Q} (v : Variant) :
    outWords ρ v = H (keyWords ρ v) ++ wordsOf ρ (left v).res.first ++ wordsOf ρ (right v).res.last ++
      [BitVec.ofNat 32 (ρ (left v).res.lo).a.val, BitVec.ofNat 32 (ρ (right v).res.hi).a.val] ++ H (accWords ρ v) := by
  rw [outWords, H, H, keyWords_length, accWords_length]

theorem outWords_length {ρ : ℕ → Q} (v : Variant) : (outWords ρ v).length = 34 := by
  obtain ⟨-, f, -, -, -, -⟩ := EpochJoin.left_lengths v
  obtain ⟨-, -, l, -, -, -⟩ := rootChild_lengths 1 (left v).next true
  have l : (right v).res.last.length = 8 := l
  simp [outWords_eq, H_length, wordsOf_length, f, l]

/-- **A join outputs the digest of its output message.** -/
theorem join_out {ρ : ℕ → Q} {v : Variant} (h : Holds ρ (epochJoin v).ops) :
    wordsOf ρ (epochJoin v).results = H (outWords ρ v) := by
  have hl : (epochJoin v).results.length = 8 := by
    rw [EpochJoin.epochJoin_results]; exact BlockRec.blake2s_length _ _ _
  exact wordsOf_H hl (by rw [outWords_length]) (EpochJoin.join_sound h).2.2.2.2.2.2

theorem joinWords_split (ρ : ℕ → Q) (c : EpochJoin.Child) :
    joinWords ρ c = wordsOf ρ c.key ++ (wordsOf ρ c.first ++ wordsOf ρ c.last ++
      [BitVec.ofNat 32 (ρ c.lo).a.val, BitVec.ofNat 32 (ρ c.hi).a.val] ++ wordsOf ρ c.tail) := by
  simp [joinWords, List.append_assoc]

section
variable {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {SatC : List Word → List Word → Prop}

theorem EpS.key_length (e : EpS) : (e.key leafH nodeH).length = 8 := H_length _

theorem Chain.acc_length (c : Chain Ep) : (c.acc leafH nodeH).length = 8 := by
  cases c <;> exact H_length _

theorem Chain.key_length (c : Chain EpS) : (c.key leafH nodeH rootH joinH).length = 8 := by
  cases c <;> exact H_length _

theorem Chain.msg_length (c : Chain Ep) (hf : c.first.o.prev.length = 8) (hl : c.last.o.fin.length = 8) :
    (c.msg leafH nodeH rootH joinH).length = 34 := by
  simp [Chain.msg, Chain.key_length, Chain.acc_length, hf, hl]

theorem Chain.Valid.first_ok : ∀ {c : Chain Ep}, c.Valid leafH nodeH rootH SatC → RootOk leafH nodeH rootH SatC c.first c.gen
  | .base _ _ _, h => h.1
  | .step c _, h => Chain.Valid.first_ok (c := c) h.1

theorem Chain.Valid.last_ok : ∀ {c : Chain Ep}, c.Valid leafH nodeH rootH SatC → RootOk leafH nodeH rootH SatC c.last true
  | .base _ _ _, h => h.2.2.1
  | .step _ _, h => h.2.1

end

/-! ### The children of a join -/

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word}

/-- **An epoch root child of a join is a proven root.** Its hook's gates hold, its identity is the pinned
`rootH M p s` and its key the verifier's (`EpS.key`): then the root circuit is satisfied with the digest of
the child's opening as the join guessed it (`rootOpen`), whose range is `from ≤ to < 2^30` (`root_range`,
the root's own proof). Or Blake2s has a collision. -/
theorem rootChild_ok {ok : (ℕ → F) → Prop} (T : TrustE Acc SatC VGates leafH nodeH rootH joinH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    {i n : ℕ} {p : Bool} {ρ : ℕ → Q} (hc : Holds ρ (rootChild i n p).ops) {root : List ℕ} (hroot : root.length = 8)
    (hv : VGates ρ i (root ++ (rootChild i n p).res.out) (rootChild i n p).res.chash)
    (e : EpS) (he : e.Ok) (hch : wordsOf ρ (rootChild i n p).res.chash = rootH e.M p e.s)
    (hk : wordsOf ρ (rootChild i n p).res.key = e.key leafH nodeH) :
    (RootOk leafH nodeH rootH SatC ⟨e, rootOpen ρ (rootChild i n p).res⟩ p ∧
      wordsOf ρ (rootChild i n p).res.out = Ep.out leafH nodeH ⟨e, rootOpen ρ (rootChild i n p).res⟩ p) ∨ Collision := by
  by_cases col : Collision
  · exact Or.inr col
  obtain ⟨hkl, hfl, hll, htl, hol, -⟩ := rootChild_lengths i n p
  have hout : wordsOf ρ (rootChild i n p).res.out = Ep.out leafH nodeH ⟨e, rootOpen ρ (rootChild i n p).res⟩ p := by
    rw [Ep.out, ← hk, ← rootWords_eq]
    exact wordsOf_H hol (by rw [rootWords_length hkl hfl hll htl]) (rootChild_out hc)
  have hwf : (rootOpen ρ (rootChild i n p).res).WF := by
    refine ⟨?_, ?_, ?_⟩ <;> simp [rootOpen, wordsOf_length, hll, hfl, htl]
  have s := T.recVerifies ρ _ _ _ hv
  rw [List.drop_left' hroot, hch, hout] at s
  obtain ⟨ρ', h', hres, hg'⟩ := T.rootCircuit _ _ _ _ s
  rw [Ep.out, rootMsg_split] at hres
  obtain ⟨hM0, hM, hok⟩ := he
  obtain ⟨hdrop, hle, hlt⟩ := (root_range T.toTrustK hl hn hM0 hM e.ts hok h' hg' _
    (by rw [rootRest_length hwf]; cases p <;> norm_num) hres).resolve_right col
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

/-- **A join with a pinned identity and key.** If a join circuit with identity `joinH v` outputs
`H(H(A ‖ B ‖ C ‖ D) ‖ rest)` (8-word `A … D`), it is satisfied by some `ρ` with its hook gates whose output
message is `H(A ‖ B ‖ C ‖ D) ‖ rest`, and its children's circuit hashes and keys are `A`, `B` (left) and
`C`, `D` (right). Or Blake2s has a collision. -/
theorem join_open {ok : (ℕ → F) → Prop} (T : TrustE Acc SatC VGates leafH nodeH rootH joinH (LeafOutP ok))
    {v : Variant} {d : List Word} (hs : SatC (joinH v) d) {A B C D rest : List Word} (hA : A.length = 8)
    (hB : B.length = 8) (hC : C.length = 8) (hD : D.length = 8) (hrest : 4 * (8 + rest.length) < 2 ^ 32)
    (hd : d = H (H (A ++ B ++ C ++ D) ++ rest)) :
    (∃ ρ : ℕ → Q, Holds ρ (epochJoin v).ops ∧ HookGates VGates ρ (epochJoin v).ops ∧ d = H (outWords ρ v) ∧
      wordsOf ρ (left v).res.chash = A ∧ wordsOf ρ (left v).res.key = B ∧
      wordsOf ρ (right v).res.chash = C ∧ wordsOf ρ (right v).res.key = D) ∨ Collision := by
  by_cases col : Collision
  · exact Or.inr col
  obtain ⟨ρ, h, hres, hg⟩ := T.joinCircuit v d hs
  have ho := join_out h
  rw [hres] at ho
  have e := (H_eq (by rw [outWords_length]; norm_num) (by rw [List.length_append, H_length]; exact hrest)
    (ho.symm.trans hd)).resolve_right col
  rw [outWords_eq] at e
  simp only [List.append_assoc] at e
  obtain ⟨ek, -⟩ := List.append_inj e (by rw [H_length, H_length])
  have ek' := (H_eq (by rw [keyWords_length]; norm_num) (by simp [hA, hB, hC, hD]) ek).resolve_right col
  obtain ⟨k, -, -, -, -, c⟩ := EpochJoin.left_lengths v
  obtain ⟨k', -, -, -, -, c'⟩ := rootChild_lengths 1 (left v).next true
  have k' : (right v).res.key.length = 8 := k'
  have c' : (right v).res.chash.length = 8 := c'
  unfold keyWords at ek'
  simp only [List.append_assoc] at ek'
  obtain ⟨e1, ek'⟩ := List.append_inj ek' (by simp [wordsOf_length, c, hA])
  obtain ⟨e2, ek'⟩ := List.append_inj ek' (by simp [wordsOf_length, k, hB])
  obtain ⟨e3, e4⟩ := List.append_inj ek' (by simp [wordsOf_length, c', hC])
  exact Or.inl ⟨ρ, h, hg, ho, e1, e2, e3, e4⟩

/-! ### The chain, composed -/

/-- **A chain of joins is sound.** Under `TrustE`, a satisfied join circuit with the pinned identity of a
chain's top join (`joinH c.variant`), whose output digest is `H(Chain.key c ‖ rest)` (the key the verifier
computes from the pinned identities and the epochs' trees), outputs the digest `Chain.digest c'` of a chain
`c'` of epoch openings over those shapes (`c'.map Ep.sh = c`) that is `Valid`: every epoch root is proven
over its opening with `from ≤ to < 2^30`, consecutive epochs link, a genesis start is zero words. Or
Blake2s has a collision. By induction over the step joins: the left child of a step is the chain so far
(its own `b < 2^30` and `a` come from its roots' own proofs, `root_range`). -/
theorem chain_sound {ok : (ℕ → F) → Prop} (T : TrustE Acc SatC VGates leafH nodeH rootH joinH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    (hr : ∀ M p s, (rootH M p s).length = 8) (hj : ∀ v, (joinH v).length = 8) :
    ∀ (c : Chain EpS), c.Ok → ∀ (d rest : List Word), 4 * (8 + rest.length) < 2 ^ 32 →
      SatC (joinH c.variant) d → d = H (c.key leafH nodeH rootH joinH ++ rest) →
      (∃ c' : Chain Ep, c'.map Ep.sh = c ∧ c'.Valid leafH nodeH rootH SatC ∧
        d = c'.digest leafH nodeH rootH joinH) ∨ Collision
  | .base g e0 e1, ⟨ok0, ok1⟩, d, rest, hrest, hs, hd => by
    by_cases col : Collision
    · exact Or.inr col
    obtain ⟨ρ, h, hg, hdo, ech0, ek0, ech1, ek1⟩ := (join_open T (v := .base g) hs (hr _ _ _) (EpS.key_length e0)
      (hr _ _ _) (EpS.key_length e1) hrest hd).resolve_right col
    have h' := h
    rw [EpochJoin.epochJoin_ops] at h'
    simp only [holds_append] at h'
    obtain ⟨⟨⟨⟨⟨⟨hL, hR⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := h'
    obtain ⟨⟨-, rl, hrl, hml⟩, ⟨-, rr, hrr, hmr⟩, ⟨elink, -, elo, -, -⟩, -, -, -, -⟩ := EpochJoin.join_sound h
    obtain ⟨ok0', hout0⟩ := (rootChild_ok T hl hn (i := 0) (n := 0) (p := g) hL hrl (hg _ _ _ hml) e0 ok0 ech0
      ek0).resolve_right col
    obtain ⟨ok1', hout1⟩ := (rootChild_ok T hl hn (i := 1) (n := (left (.base g)).next) (p := true) hR hrr
      (hg _ _ _ hmr) e1 ok1 ech1 ek1).resolve_right col
    refine Or.inl ⟨.base g ⟨e0, rootOpen ρ (left (.base g)).res⟩ ⟨e1, rootOpen ρ (right (.base g)).res⟩, rfl,
      ⟨ok0', fun hg0 => ?_, ok1', elink, elo ok0'.2.2.2⟩, ?_⟩
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
  | .step c0 e, ⟨okc, oke⟩, d, rest, hrest, hs, hd => by
    by_cases col : Collision
    · exact Or.inr col
    obtain ⟨ρ, h, hg, hdo, ech0, ek0, ech1, ek1⟩ := (join_open T (v := .step) hs (hj _) (Chain.key_length c0)
      (hr _ _ _) (EpS.key_length e) hrest hd).resolve_right col
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
    have hjl : (joinWords ρ (left .step).res).length = 34 := EpochJoin.joinWords_length lk lf ll lt
    have hlout : wordsOf ρ (left .step).res.out = H (joinWords ρ (left .step).res) :=
      wordsOf_H lo rfl hlo
    have s := T.recVerifies ρ _ _ _ (hg _ _ _ hml)
    rw [List.drop_left' hrl, ech0, hlout] at s
    have hjw := joinWords_split ρ (left .step).res
    rw [ek0] at hjw
    obtain ⟨c'', hmap, hval, hdig⟩ := (chain_sound T hl hn hr hj c0 okc _
      (wordsOf ρ (left .step).res.first ++ wordsOf ρ (left .step).res.last ++
        [BitVec.ofNat 32 (ρ (left .step).res.lo).a.val, BitVec.ofNat 32 (ρ (left .step).res.hi).a.val] ++
        wordsOf ρ (left .step).res.tail)
      (by simp [wordsOf_length, lf, ll, lt]) s (by rw [hjw])).resolve_right col
    -- Its opening is `c''`'s.
    obtain ⟨-, ⟨-, hfp, -⟩, -, -⟩ := Chain.Valid.first_ok hval
    obtain ⟨-, ⟨hlf, -, -⟩, -, hlh⟩ := Chain.Valid.last_ok hval
    have em := (H_eq (by rw [hjl]; norm_num) (by rw [Chain.msg_length _ hfp hlf]; norm_num) hdig).resolve_right col
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
    obtain ⟨okE, hout1⟩ := (rootChild_ok T hl hn (i := 1) (n := (left .step).next) (p := true) hR hrr
      (hg _ _ _ hmr) e oke ech1 ek1).resolve_right col
    refine Or.inl ⟨.step c'' ⟨e, rootOpen ρ (right .step).res⟩, ?_, ⟨hval, okE, elink.trans eL, ?_⟩, ?_⟩
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

end

/-! ### The chain-level statement -/

namespace Chain
variable {α : Type}

/-- Every epoch of a chain satisfies `P`. -/
def All (P : α → Prop) : Chain α → Prop
  | base _ e0 e1 => P e0 ∧ P e1
  | step c e => c.All P ∧ P e

theorem epochs_ne_nil : ∀ c : Chain α, c.epochs ≠ []
  | base _ _ _ => by simp [epochs]
  | step c _ => by simp [epochs]

theorem epochs_head : ∀ c : Chain α, c.epochs.head? = some c.first
  | base _ _ _ => rfl
  | step c _ => by
    rw [epochs, List.head?_append, epochs_head c]
    rfl

theorem epochs_getLast : ∀ c : Chain α, c.epochs.getLast? = some c.last
  | base _ _ _ => rfl
  | step c e => by simp [epochs, last]

theorem all_iff (P : α → Prop) : ∀ c : Chain α, c.All P ↔ ∀ e ∈ c.epochs, P e
  | base _ e0 e1 => by simp [All, epochs]
  | step c e => by simp [All, epochs, all_iff P c, or_imp, forall_and]

end Chain

section
variable {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {SatC : List Word → List Word → Prop}

/-- **A valid chain covers `a … b`**: `a ≤ b < 2^30` (each epoch `from ≤ to`, the next `from = to + 1`). -/
theorem Chain.Valid.range : ∀ {c : Chain Ep}, c.Valid leafH nodeH rootH SatC →
    c.first.o.lo ≤ c.last.o.hi ∧ c.last.o.hi < 2 ^ 30
  | .base _ _ _, ⟨⟨_, _, h0, _⟩, _, ⟨_, _, h1, h1'⟩, ⟨_, hl⟩⟩ => ⟨by simp only [Chain.first, Chain.last]; omega, h1'⟩
  | .step c _, ⟨hc, ⟨_, _, h1, h1'⟩, ⟨_, hl⟩⟩ => by
    have ih := Chain.Valid.range hc
    exact ⟨by simp only [Chain.first, Chain.last]; omega, h1'⟩

/-- **Consecutive epochs link** (the previous set digest is the last final one, `from = to + 1`). -/
theorem Chain.Valid.links : ∀ {c : Chain Ep}, c.Valid leafH nodeH rootH SatC → List.IsChain Link c.epochs
  | .base _ _ _, h => List.isChain_pair.mpr h.2.2.2
  | .step c e, h => by
    refine (Chain.Valid.links h.1).append (List.isChain_singleton e) (fun x hx y hy => ?_)
    rw [Chain.epochs_getLast] at hx
    simp only [Option.mem_def, Option.some.injEq, List.head?_cons] at hx hy
    subst hx hy
    exact h.2.2

/-- **Every epoch root is proven**: the first from its previous set (or genesis), the others from theirs. -/
theorem Chain.Valid.roots : ∀ {c : Chain Ep}, c.Valid leafH nodeH rootH SatC →
    RootOk leafH nodeH rootH SatC c.first c.gen ∧ ∀ e ∈ c.epochs.tail, RootOk leafH nodeH rootH SatC e true
  | .base _ _ _, h => ⟨h.1, by simp [Chain.epochs]; exact h.2.2.1⟩
  | .step c e, h => by
    obtain ⟨h0, ht⟩ := Chain.Valid.roots h.1
    refine ⟨h0, fun x hx => ?_⟩
    rw [Chain.epochs, List.tail_append_of_ne_nil (Chain.epochs_ne_nil c)] at hx
    rcases List.mem_append.mp hx with hx | hx
    · exact ht x hx
    · rw [List.mem_singleton.mp hx]; exact h.2.1

/-- **`acc` is the left fold of Blake2s** over the epoch roots' output digests: `H(out₀ ‖ out₁)`, then
`H(acc ‖ out)` per later epoch. -/
theorem Chain.acc_fold : ∀ c : Chain Ep, ∃ e0 e1 es, c.epochs = e0 :: e1 :: es ∧
    c.acc leafH nodeH = es.foldl (fun a e => H (a ++ e.out leafH nodeH true))
      (H (e0.out leafH nodeH c.gen ++ e1.out leafH nodeH true))
  | .base _ e0 e1 => ⟨e0, e1, [], rfl, rfl⟩
  | .step c e => by
    obtain ⟨e0, e1, es, he, ha⟩ := Chain.acc_fold c
    exact ⟨e0, e1, es ++ [e], by simp [Chain.epochs, he], by simp [Chain.acc, ha, List.foldl_append, Chain.gen]⟩

end

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word}

/-- **The chain, as one statement.** A join proof with the pinned identity of `c`'s top join, whose output
digest is `H(Chain.key c ‖ rest)`, proves a chain of epoch openings `c'` over `c`'s shapes (or Blake2s has a
collision):
- its output digest is `H(key ‖ start ‖ end ‖ a ‖ b ‖ acc)` (`Chain.digest`) with `start` the first epoch's
  previous set digest, zero words from genesis; `end` the last epoch's final set digest; `a` the first's
  `from`, `b` the last's `to`;
- every epoch root is proven over its opening (`RootOk`: the pinned root circuit satisfied with its
  digest, `from ≤ to < 2^30`);
- consecutive epochs link (`List.IsChain Link`), so the chain covers `a … b` contiguously, `a ≤ b < 2^30`;
- `acc` is the left fold of Blake2s over the epoch roots' output digests. -/
theorem chain_cover {ok : (ℕ → F) → Prop} (T : TrustE Acc SatC VGates leafH nodeH rootH joinH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    (hr : ∀ M p s, (rootH M p s).length = 8) (hj : ∀ v, (joinH v).length = 8)
    (c : Chain EpS) (hok : c.Ok) (d rest : List Word) (hrest : 4 * (8 + rest.length) < 2 ^ 32)
    (hs : SatC (joinH c.variant) d) (hd : d = H (c.key leafH nodeH rootH joinH ++ rest)) :
    (∃ c' : Chain Ep, c'.map Ep.sh = c ∧
      d = H (c.key leafH nodeH rootH joinH ++ c'.first.o.prev ++ c'.last.o.fin ++
        [BitVec.ofNat 32 c'.first.o.lo, BitVec.ofNat 32 c'.last.o.hi] ++ c'.acc leafH nodeH) ∧
      (c.gen = false → c'.first.o.prev = List.replicate 8 0) ∧
      RootOk leafH nodeH rootH SatC c'.first c.gen ∧ (∀ e ∈ c'.epochs.tail, RootOk leafH nodeH rootH SatC e true) ∧
      List.IsChain Link c'.epochs ∧ c'.first.o.lo ≤ c'.last.o.hi ∧ c'.last.o.hi < 2 ^ 30 ∧
      ∃ e0 e1 es, c'.epochs = e0 :: e1 :: es ∧
        c'.acc leafH nodeH = es.foldl (fun a e => H (a ++ e.out leafH nodeH true))
          (H (e0.out leafH nodeH c.gen ++ e1.out leafH nodeH true))) ∨ Collision := by
  rcases chain_sound T hl hn hr hj c hok d rest hrest hs hd with ⟨c', hmap, hval, hdig⟩ | col
  · refine Or.inl ⟨c', hmap, ?_, ?_, ?_, (Chain.Valid.roots hval).2, Chain.Valid.links hval, (Chain.Valid.range hval).1,
      (Chain.Valid.range hval).2, ?_⟩
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

/-- An opening fits its words: 8-word digests, `from` and `to` below `2^32`. -/
def Open.Fits (o : Open) : Prop := o.WF ∧ o.lo < 2 ^ 32 ∧ o.hi < 2 ^ 32

theorem Chain.All.first {α : Type} {P : α → Prop} : ∀ {c : Chain α}, c.All P → P c.first
  | .base _ _ _, h => h.1
  | .step c _, h => Chain.All.first (c := c) h.1

theorem Chain.All.last {α : Type} {P : α → Prop} : ∀ {c : Chain α}, c.All P → P c.last
  | .base _ _ _, h => h.2
  | .step _ _, h => h.2

section
variable {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word} {SatC : List Word → List Word → Prop}

theorem RootOk.fits {e : Ep} {p : Bool} (h : RootOk leafH nodeH rootH SatC e p) : e.o.Fits :=
  ⟨h.2.1, by have := h.2.2.1; have := h.2.2.2; omega, by have := h.2.2.2; omega⟩

theorem Chain.Valid.fits : ∀ {c : Chain Ep}, c.Valid leafH nodeH rootH SatC → c.All (fun e => e.o.Fits)
  | .base _ _ _, h => ⟨h.1.fits, h.2.2.1.fits⟩
  | .step _ _, h => ⟨Chain.Valid.fits h.1, h.2.1.fits⟩

theorem rootMsg_length {K : List Word} (hK : K.length = 8) {o : Open} (h : o.WF) (p : Bool) :
    (rootMsg K p o).length = 8 + (8 + (if p then 8 else 0) + 2 + 8) := by
  rw [rootMsg_split, List.length_append, rootRest_length h, hK]

/-- **One digest, one opening**: two epochs of one shape whose roots output one digest have one opening
(the previous set only when it is in the message), or Blake2s has a collision. -/
theorem out_inj {e e' : Ep} {p : Bool} (hs : e.sh = e'.sh) (hw : e.o.Fits) (hw' : e'.o.Fits)
    (h : e.out leafH nodeH p = e'.out leafH nodeH p) :
    (e.o.fin = e'.o.fin ∧ (p = true → e.o.prev = e'.o.prev) ∧ e.o.lo = e'.o.lo ∧ e.o.hi = e'.o.hi ∧
      e.o.rest = e'.o.rest) ∨ Collision := by
  by_cases col : Collision
  · exact Or.inr col
  have w := hw.1
  have w' := hw'.1
  obtain ⟨⟨f, pr, -⟩, lo, hi⟩ := hw
  obtain ⟨⟨f', pr', -⟩, lo', hi'⟩ := hw'
  have hK := EpS.key_length (leafH := leafH) (nodeH := nodeH) e.sh
  have hK' := EpS.key_length (leafH := leafH) (nodeH := nodeH) e'.sh
  have h' : H (rootMsg (e.sh.key leafH nodeH) p e.o) = H (rootMsg (e'.sh.key leafH nodeH) p e'.o) := h
  have e1 := (H_eq (by rw [rootMsg_length hK w]; cases p <;> norm_num)
    (by rw [rootMsg_length hK' w']; cases p <;> norm_num) h').resolve_right col
  unfold rootMsg at e1
  rw [hs] at e1
  obtain ⟨e1, er⟩ := List.append_inj e1 (by cases p <;> simp [f, pr, f', pr', hK'])
  obtain ⟨e1, exy⟩ := List.append_inj e1 (by cases p <;> simp [f, pr, f', pr', hK'])
  obtain ⟨e1, ep⟩ := List.append_inj e1 (by simp [f, f', hK'])
  obtain ⟨-, ef⟩ := List.append_inj e1 rfl
  simp only [List.cons.injEq, and_true] at exy
  refine Or.inl ⟨ef, fun hp => by subst hp; simpa using ep, ofNat_inj lo lo' exy.1, ofNat_inj hi hi' exy.2, er⟩

theorem rootOk_of {e e' : Ep} {p : Bool} (hs : e.sh = e'.sh) (hw : e.o.WF)
    (hout : e.out leafH nodeH p = e'.out leafH nodeH p) (hlo : e.o.lo = e'.o.lo) (hhi : e.o.hi = e'.o.hi)
    (h : RootOk leafH nodeH rootH SatC e' p) : RootOk leafH nodeH rootH SatC e p := by
  obtain ⟨s, -, h1, h2⟩ := h
  refine ⟨?_, hw, by rw [hlo, hhi]; exact h1, by rw [hhi]; exact h2⟩
  rw [hs, hout]; exact s

/-- **`acc` binds every epoch's opening**: a chain with the shapes and `acc` of a valid chain, its
openings fitting their words and a genesis start zero words, is valid (with the same last final set and
`to`), or Blake2s has a collision. -/
theorem acc_valid : ∀ (c c' : Chain Ep), c'.Valid leafH nodeH rootH SatC → c.map Ep.sh = c'.map Ep.sh →
    c.acc leafH nodeH = c'.acc leafH nodeH → c.All (fun e => e.o.Fits) → c'.All (fun e => e.o.Fits) →
    (c.gen = false → c.first.o.prev = List.replicate 8 0) →
    (c.Valid leafH nodeH rootH SatC ∧ c.last.o.fin = c'.last.o.fin ∧ c.last.o.hi = c'.last.o.hi) ∨ Collision
  | .base g e0 e1, .base g' e0' e1', hv, hm, ha, hw, hw', hgen => by
    by_cases col : Collision
    · exact Or.inr col
    simp only [Chain.map, Chain.base.injEq] at hm
    obtain ⟨rfl, h0, h1⟩ := hm
    have ha' : H (e0.out leafH nodeH g ++ e1.out leafH nodeH true) = H (e0'.out leafH nodeH g ++ e1'.out leafH nodeH true) := ha
    have e := (H_eq (by simp [Ep.out, H_length]) (by simp [Ep.out, H_length]) ha').resolve_right col
    obtain ⟨o0, o1⟩ := List.append_inj e (by simp [Ep.out, H_length])
    obtain ⟨f0, -, l0, hi0, -⟩ := (out_inj h0 hw.1 hw'.1 o0).resolve_right col
    obtain ⟨f1, p1, l1, hi1, -⟩ := (out_inj h1 hw.2 hw'.2 o1).resolve_right col
    obtain ⟨r0, -, r1, ⟨lp, ll⟩⟩ := hv
    refine Or.inl ⟨⟨rootOk_of h0 hw.1.1 o0 l0 hi0 r0, hgen, rootOk_of h1 hw.2.1 o1 l1 hi1 r1, ?_, ?_⟩, f1, hi1⟩
    · show e1.o.prev = e0.o.fin
      rw [p1 rfl, f0]; exact lp
    · show e1.o.lo = e0.o.hi + 1
      rw [l1, hi0]; exact ll
  | .step c e, .step c' e', hv, hm, ha, hw, hw', hgen => by
    by_cases col : Collision
    · exact Or.inr col
    simp only [Chain.map, Chain.step.injEq] at hm
    obtain ⟨hm, h1⟩ := hm
    have ha' : H (c.acc leafH nodeH ++ e.out leafH nodeH true) = H (c'.acc leafH nodeH ++ e'.out leafH nodeH true) := ha
    have eq := (H_eq (by simp [Ep.out, H_length, Chain.acc_length]) (by simp [Ep.out, H_length, Chain.acc_length])
      ha').resolve_right col
    obtain ⟨hac, o1⟩ := List.append_inj eq (by rw [Chain.acc_length, Chain.acc_length])
    obtain ⟨ihv, ihf, ihh⟩ := (acc_valid c c' hv.1 hm hac hw.1 hw'.1 hgen).resolve_right col
    obtain ⟨f1, p1, l1, hi1, -⟩ := (out_inj h1 hw.2 hw'.2 o1).resolve_right col
    obtain ⟨-, r1, ⟨lp, ll⟩⟩ := hv
    refine Or.inl ⟨⟨ihv, rootOk_of h1 hw.2.1 o1 l1 hi1 r1, ?_, ?_⟩, f1, hi1⟩
    · show e.o.prev = c.last.o.fin
      rw [p1 rfl, ihf]; exact lp
    · show e.o.lo = c.last.o.hi + 1
      rw [l1, ihh]; exact ll
  | .base _ _ _, .step _ _, _, hm, _, _, _, _ => by simp [Chain.map] at hm
  | .step _ _, .base _ _ _, _, hm, _, _, _, _ => by simp [Chain.map] at hm

end

section
variable {Acc SatC : List Word → List Word → Prop} {VGates : (ℕ → Q) → ℕ → List ℕ → List ℕ → Prop}
  {leafH : ℕ → List Word} {nodeH : ℕ → ℕ → List Word} {rootH : ℕ → Bool → ℕ → List Word}
  {joinH : Variant → List Word}

/-- **The chain verifier, composed.** The verifier holds a chain of epoch openings `c` (each epoch's public
part; the shapes pinned, within bounds), recomputes the join's output digest `Chain.digest c` (key from the
pinned identities, `start`, `end`, `a`, `b`, `acc`), and accepts the one join proof against the pinned join
identity with that digest (`SatC` by `stwoSound`). Then its chain is valid: every epoch root proven over
the verifier's own opening with `from ≤ to < 2^30`, consecutive epochs linked, so it covers `a … b`
contiguously (`Chain.Valid.range`, `.links`, `.roots`). Or Blake2s has a collision. -/
theorem chain_verify {ok : (ℕ → F) → Prop} (T : TrustE Acc SatC VGates leafH nodeH rootH joinH (LeafOutP ok))
    (hl : ∀ L, (leafH L).length = 8) (hn : ∀ a v, (nodeH a v).length = 8)
    (hr : ∀ M p s, (rootH M p s).length = 8) (hj : ∀ v, (joinH v).length = 8)
    (c : Chain Ep) (hok : (c.map Ep.sh).Ok) (hw : c.All (fun e => e.o.Fits))
    (hgen : c.gen = false → c.first.o.prev = List.replicate 8 0)
    (hs : SatC (joinH c.variant) (c.digest leafH nodeH rootH joinH)) :
    c.Valid leafH nodeH rootH SatC ∨ Collision := by
  by_cases col : Collision
  · exact Or.inr col
  have hf : c.first.o.prev.length = 8 := hw.first.1.2.1
  have hlf : c.last.o.fin.length = 8 := hw.last.1.1
  have hmsg : c.msg leafH nodeH rootH joinH = (c.map Ep.sh).key leafH nodeH rootH joinH ++
      (c.first.o.prev ++ c.last.o.fin ++ [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++
        c.acc leafH nodeH) := by
    simp [Chain.msg, List.append_assoc]
  obtain ⟨c', hmap, hval, hdig⟩ := (chain_sound T hl hn hr hj (c.map Ep.sh) hok _
    (c.first.o.prev ++ c.last.o.fin ++ [BitVec.ofNat 32 c.first.o.lo, BitVec.ofNat 32 c.last.o.hi] ++ c.acc leafH nodeH)
    (by simp [hf, hlf, Chain.acc_length]) (by rw [Chain.variant_map]; exact hs)
    (by rw [Chain.digest, hmsg])).resolve_right col
  have hw' := Chain.Valid.fits hval
  have em := (H_eq (by rw [Chain.msg_length _ hf hlf]; norm_num)
    (by rw [Chain.msg_length _ hw'.first.1.2.1 hw'.last.1.1]; norm_num) hdig).resolve_right col
  unfold Chain.msg at em
  obtain ⟨-, hacc⟩ := List.append_inj em (by simp [Chain.key_length, hf, hlf, hw'.first.1.2.1, hw'.last.1.1])
  exact Or.inl ((acc_valid c c' hval hmap.symm hacc hw hw' hgen).resolve_right col).1

end

end StarkedAir.Circuit.EpochChain
