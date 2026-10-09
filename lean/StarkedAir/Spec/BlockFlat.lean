/-
**The block rules as a conjunction (M3a.5a, D-035 stage 1).** `checkBlock` returns the first
failing rule's reason, following Core's check order. Proving `checkBlock = none` needs only that
every rule holds, in any order. This file proves that equivalence (`checkBlock_none_iff`) and the
simplifications the M3a.5 AIRs rely on:

* `checkTx_none_iff`: `CheckTransaction` passes iff the conditions of `TxOK` hold. The three
  per-output value checks become: every value non-negative and the total at most `MAX_MONEY`
  (`values_ok_iff`).
* `CtxFreeOK`, `CtxOK`: `CheckBlock` (minus PoW) and `ContextualCheckBlock` as conjunctions.
* `size_of_weight`: weight within the limit implies the stripped-size, transaction-count and
  per-transaction size limits.

Duplicate inputs (`nodupBy`) stay a separate conjunct: M3b's obligation (D-031).
-/
import StarkedAir.Spec.Block

namespace StarkedAir.Spec.Block

/-! ### Output values -/

/-- `CheckTransaction`'s per-output step (as in `checkTx`). -/
def valueStep (acc : Option String × ℤ) (o : TxOut) : Option String × ℤ :=
  match acc.1 with
  | some e => (some e, acc.2)
  | none =>
    if o.value < 0 then (some "bad-txns-vout-negative", 0)
    else if o.value > MAX_MONEY then (some "bad-txns-vout-toolarge", 0)
    else if acc.2 + o.value > MAX_MONEY then (some "bad-txns-txouttotal-toolarge", 0)
    else (none, acc.2 + o.value)

theorem fold_some (l : List TxOut) (e : String) (x : ℤ) : (l.foldl valueStep (some e, x)).1 = some e := by
  induction l generalizing x with
  | nil => rfl
  | cons o rest ih => simp only [List.foldl_cons, valueStep]; exact ih x

/-- With a running total `s ∈ [0, MAX_MONEY]`, the remaining outputs pass iff they are all
non-negative and the total stays within `MAX_MONEY`. -/
theorem fold_none : ∀ (l : List TxOut) (s : ℤ), 0 ≤ s → s ≤ MAX_MONEY →
    ((l.foldl valueStep (none, s)).1 = none ↔ (∀ o ∈ l, 0 ≤ o.value) ∧ s + (l.map (·.value)).sum ≤ MAX_MONEY)
  | [], s, _, h2 => by simp [h2]
  | o :: rest, s, h1, h2 => by
    have hsum : ∀ (l : List TxOut), (∀ o ∈ l, 0 ≤ o.value) → 0 ≤ (l.map (·.value)).sum := fun l hl =>
      List.sum_nonneg (by simpa using hl)
    simp only [List.foldl_cons, valueStep, List.mem_cons, forall_eq_or_imp, List.map_cons, List.sum_cons]
    by_cases hn : o.value < 0
    · simp only [hn, ite_true, fold_some, reduceCtorEq, false_iff, not_and]
      intro h; omega
    · by_cases hb : o.value > MAX_MONEY
      · simp only [hn, ite_false, hb, ite_true, fold_some, reduceCtorEq, false_iff, not_and]
        intro ⟨_, hr⟩ _; have := hsum rest hr; omega
      · by_cases ht : s + o.value > MAX_MONEY
        · simp only [hn, ite_false, hb, ht, ite_true, fold_some, reduceCtorEq, false_iff, not_and]
          intro ⟨_, hr⟩ _; have := hsum rest hr; omega
        · simp only [hn, ite_false, hb, ht]
          rw [fold_none rest (s + o.value) (by omega) (by omega)]
          constructor
          · rintro ⟨hr, hs⟩; exact ⟨⟨by omega, hr⟩, by omega⟩
          · rintro ⟨⟨_, hr⟩, hs⟩; exact ⟨hr, by omega⟩

/-- **Output values**: `CheckTransaction`'s value checks pass iff every value is non-negative and
the total is at most `MAX_MONEY` (each value and each prefix then is too). -/
theorem values_ok_iff (vout : List TxOut) :
    (vout.foldl valueStep (none, 0)).1 = none ↔ (∀ o ∈ vout, 0 ≤ o.value) ∧ (vout.map (·.value)).sum ≤ MAX_MONEY := by
  rw [fold_none vout 0 le_rfl (by decide)]; simp

/-! ### `CheckTransaction` -/

/-- `checkTx`, with the value step named. -/
def checkTx' (t : Tx) : Option String :=
  if t.vin.isEmpty then some "bad-txns-vin-empty"
  else if t.vout.isEmpty then some "bad-txns-vout-empty"
  else if (serNoWit t).length * 4 > MAX_BLOCK_WEIGHT then some "bad-txns-oversize"
  else
    let r := t.vout.foldl valueStep (none, 0)
    if r.1.isSome then r.1
    else if !nodupBy (t.vin.map (·.prevout)) then some "bad-txns-inputs-duplicate"
    else if t.isCoinbase then
      match t.vin with
      | [i] => if i.scriptSig.length < 2 ∨ i.scriptSig.length > 100 then some "bad-cb-length" else none
      | _ => none
    else if t.vin.any (·.prevout.isNull) then some "bad-txns-prevout-null"
    else none

theorem checkTx_eq : checkTx = checkTx' := rfl

/-- The coinbase's scriptSig length rule. -/
def CbLenOK (t : Tx) : Prop :=
  match t.vin with
  | [i] => 2 ≤ i.scriptSig.length ∧ i.scriptSig.length ≤ 100
  | _ => True

/-- **`CheckTransaction` as a conjunction.** -/
def TxOK (t : Tx) : Prop :=
  t.vin ≠ [] ∧ t.vout ≠ [] ∧ (serNoWit t).length * 4 ≤ MAX_BLOCK_WEIGHT ∧
  (∀ o ∈ t.vout, 0 ≤ o.value) ∧ (t.vout.map (·.value)).sum ≤ MAX_MONEY ∧
  nodupBy (t.vin.map (·.prevout)) = true ∧
  (if t.isCoinbase then CbLenOK t else ∀ i ∈ t.vin, i.prevout.isNull = false)

theorem checkTx_none_iff (t : Tx) : checkTx t = none ↔ TxOK t := by
  rw [checkTx_eq]
  unfold checkTx' TxOK
  have hv := values_ok_iff t.vout
  by_cases h1 : t.vin = []
  · simp [h1]
  by_cases h2 : t.vout = []
  · simp [h1, h2]
  by_cases h3 : (serNoWit t).length * 4 > MAX_BLOCK_WEIGHT
  · simp only [List.isEmpty_iff, h1, h2, h3, ite_false, ite_true, reduceCtorEq, false_iff]
    omega
  simp only [List.isEmpty_iff, h1, h2, h3, ite_false, ne_eq, not_false_eq_true, true_and]
  have h3' : (serNoWit t).length * 4 ≤ MAX_BLOCK_WEIGHT := by omega
  simp only [h3', true_and]
  cases hr : (t.vout.foldl valueStep (none, 0)).1 with
  | some e =>
    simp only [Option.isSome_some, ite_true, reduceCtorEq, false_iff]
    rw [hr] at hv
    intro ⟨ha, hb, _⟩
    exact absurd (hv.mpr ⟨ha, hb⟩) (by simp)
  | none =>
    rw [hr] at hv
    have hvals := hv.mp rfl
    simp only [Option.isSome_none, Bool.false_eq_true, ite_false, eq_true hvals.1, eq_true hvals.2, true_and]
    by_cases hd : nodupBy (t.vin.map (·.prevout)) = true
    · simp only [hd, Bool.not_true, Bool.false_eq_true, ite_false, true_and]
      by_cases hc : t.isCoinbase = true
      · simp only [hc, ite_true, CbLenOK]
        split
        · split <;> simp_all <;> omega
        · simp
      · simp only [hc, Bool.false_eq_true, ite_false]
        by_cases hn : t.vin.any (·.prevout.isNull) = true
        · simp only [hn, ite_true, reduceCtorEq, false_iff]
          intro hall
          obtain ⟨i, hi, h⟩ := List.any_eq_true.mp hn
          simp [hall i hi] at h
        · simp only [hn, Bool.false_eq_true, ite_false, true_iff]
          intro i hi
          simpa using List.any_eq_false.mp (by simpa using hn) i hi
    · simp [hd]

/-! ### `CheckBlock` (without proof of work) -/

/-- **`CheckBlock` as a conjunction** (the header's PoW is the header chain's). -/
def CtxFreeOK (b : Blk) : Prop :=
  merkleRoot (b.txs.map txid) = (headerMerkle b, false) ∧
  b.txs ≠ [] ∧ b.txs.length * 4 ≤ MAX_BLOCK_WEIGHT ∧ strippedSize b * 4 ≤ MAX_BLOCK_WEIGHT ∧
  (b.txs.headD ⟨0, [], [], 0⟩).isCoinbase = true ∧ (∀ t ∈ b.txs.drop 1, t.isCoinbase = false) ∧
  (∀ t ∈ b.txs, TxOK t) ∧ (b.txs.map legacySigOps).sum * 4 ≤ MAX_BLOCK_SIGOPS_COST

theorem checkBlockCtxFree_none_iff (b : Blk) : checkBlockCtxFree b = none ↔ CtxFreeOK b := by
  unfold checkBlockCtxFree CtxFreeOK
  rcases hm : merkleRoot (b.txs.map txid) with ⟨root, mutated⟩
  simp only [hm, Prod.mk.injEq]
  by_cases h1 : root = headerMerkle b
  · subst h1
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, true_and]
    cases mutated
    · simp only [Bool.false_eq_true, ite_false, true_and]
      by_cases h3 : b.txs.isEmpty = true ∨ b.txs.length * 4 > MAX_BLOCK_WEIGHT ∨ strippedSize b * 4 > MAX_BLOCK_WEIGHT
      · simp only [h3, ite_true, reduceCtorEq, false_iff]
        rintro ⟨hne, hl, hs, -⟩
        rcases h3 with h | h | h
        · exact hne (List.isEmpty_iff.mp h)
        · omega
        · omega
      · simp only [h3, ite_false]
        simp only [not_or, List.isEmpty_iff, not_lt] at h3
        obtain ⟨h3a, h3b, h3c⟩ := h3
        simp only [ne_eq, h3a, not_false_eq_true, h3b, h3c, true_and]
        by_cases h4 : (b.txs.headD ⟨0, [], [], 0⟩).isCoinbase = true
        · simp only [h4, Bool.not_true, Bool.false_eq_true, ite_false, true_and]
          by_cases h5 : (b.txs.drop 1).any Tx.isCoinbase = true
          · simp only [h5, ite_true, reduceCtorEq, false_iff, not_and]
            intro hall
            obtain ⟨t, ht, hc⟩ := List.any_eq_true.mp h5
            simp [hall t ht] at hc
          · simp only [h5, Bool.false_eq_true, ite_false]
            have h5' : ∀ t ∈ b.txs.drop 1, t.isCoinbase = false := by
              intro t ht; simpa using List.any_eq_false.mp (by simpa using h5) t ht
            simp only [eq_true h5', true_and]
            cases hf : (b.txs.map checkTx).filterMap id with
            | cons e rest =>
              simp only [reduceCtorEq, false_iff, not_and]
              intro hall
              have : e ∈ (b.txs.map checkTx).filterMap id := by rw [hf]; simp
              simp only [List.mem_filterMap, List.mem_map, id_eq] at this
              obtain ⟨_, ⟨t, ht, rfl⟩, he⟩ := this
              rw [(checkTx_none_iff t).mpr (hall t ht)] at he
              exact absurd he (by simp)
            | nil =>
              have hall : ∀ t ∈ b.txs, TxOK t := by
                intro t ht
                rw [← checkTx_none_iff]
                rw [List.filterMap_eq_nil_iff] at hf
                exact hf _ (List.mem_map_of_mem ht)
              simp only [eq_true hall, true_and]
              by_cases h6 : (b.txs.map legacySigOps).sum * 4 > MAX_BLOCK_SIGOPS_COST
              · simp only [h6, ite_true, reduceCtorEq, false_iff]; omega
              · simp only [h6, ite_false, true_iff]; omega
        · rw [Bool.not_eq_true] at h4
          simp only [h4, Bool.not_false, ite_true, reduceCtorEq, false_iff, Bool.false_eq_true, false_and,
            not_false_eq_true]
    · simp
  · simp [h1]

/-! ### `ContextualCheckBlock` -/

/-- The finality cutoff: the predecessor's MTP once CSV is active, else the block's time. -/
def cutoffOf (c : Ctx) (b : Blk) : ℕ := if c.height ≥ CSV_HEIGHT then c.prevMtp else b.time

def cbOf (b : Blk) : Tx := b.txs.headD ⟨0, [], [], 0⟩

def ssOf (b : Blk) : Bytes := ((cbOf b).vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).scriptSig

/-- The witness commitment output, if the commitment is required to be checked. -/
def commitOf (c : Ctx) (b : Blk) : Option ℕ := if c.height ≥ SEGWIT_HEIGHT then commitmentIndex (cbOf b) else none

/-- The commitment check at output `pos` (`none`: it passes). -/
def witCheck (b : Blk) (pos : ℕ) : Option String :=
  let cb := cbOf b
  let leaves := List.replicate 32 0 :: (b.txs.drop 1).map wtxid
  let stack := (cb.vin.headD ⟨⟨[], 0⟩, [], 0, []⟩).witness
  match stack with
  | [nonce] =>
    if nonce.length ≠ 32 then some "bad-witness-nonce-size"
    else if sha256d ((merkleRoot leaves).1 ++ nonce) ≠ (((cb.vout.getD pos ⟨0, []⟩).scriptPubKey.drop 6).take 32)
      then some "bad-witness-merkle-match" else none
  | _ => some "bad-witness-nonce-size"

/-- **`ContextualCheckBlock` as a conjunction.** -/
def CtxOK (c : Ctx) (b : Blk) : Prop :=
  (∀ t ∈ b.txs, isFinal t c.height (cutoffOf c b) = true) ∧
  (c.height ≥ BIP34_HEIGHT → (ssOf b).take (pushHeight c.height).length = pushHeight c.height) ∧
  (match commitOf c b with
    | some pos => witCheck b pos = none
    | none => ∀ t ∈ b.txs, t.hasWitness = false) ∧
  weight b ≤ MAX_BLOCK_WEIGHT

theorem checkBlockContextual_none_iff (c : Ctx) (b : Blk) : checkBlockContextual c b = none ↔ CtxOK c b := by
  unfold checkBlockContextual CtxOK
  -- Name the pieces as `CtxOK` does.
  show (if !b.txs.all (fun t => isFinal t c.height (cutoffOf c b)) then some "bad-txns-nonfinal"
    else if c.height ≥ BIP34_HEIGHT ∧ (ssOf b).take (pushHeight c.height).length ≠ pushHeight c.height then
      some "bad-cb-height"
    else match (commitOf c b).map (witCheck b) with
      | some (some e) => some e
      | _ =>
        if ((commitOf c b).map (witCheck b)).isNone ∧ b.txs.any Tx.hasWitness then some "unexpected-witness"
        else if weight b > MAX_BLOCK_WEIGHT then some "bad-blk-weight" else none) = none ↔ _
  by_cases h1 : (b.txs.all fun t => isFinal t c.height (cutoffOf c b)) = true
  · have h1' : ∀ t ∈ b.txs, isFinal t c.height (cutoffOf c b) = true := by simpa using h1
    simp only [h1, Bool.not_true, Bool.false_eq_true, ite_false, eq_true h1', true_and]
    by_cases h2 : c.height ≥ BIP34_HEIGHT ∧ (ssOf b).take (pushHeight c.height).length ≠ pushHeight c.height
    · rw [if_pos h2]
      simp only [reduceCtorEq, false_iff, not_and]
      intro h; exact absurd (h h2.1) h2.2
    · have h2' : c.height ≥ BIP34_HEIGHT → (ssOf b).take (pushHeight c.height).length = pushHeight c.height := by
        intro h; by_contra hc; exact h2 ⟨h, hc⟩
      rw [if_neg h2, and_iff_right h2']
      cases hc : commitOf c b with
      | none =>
        simp only [Option.map_none, Option.isNone_none, true_and]
        by_cases h3 : b.txs.any Tx.hasWitness = true
        · simp only [h3, ite_true, reduceCtorEq, false_iff, not_and]
          intro hall
          obtain ⟨t, ht, hw⟩ := List.any_eq_true.mp h3
          simp [hall t ht] at hw
        · have h3' : ∀ t ∈ b.txs, t.hasWitness = false := by
            intro t ht; simpa using List.any_eq_false.mp (by simpa using h3) t ht
          simp only [h3, Bool.false_eq_true, ite_false, eq_true h3', true_and]
          by_cases h4 : weight b > MAX_BLOCK_WEIGHT
          · rw [if_pos h4]; simp only [reduceCtorEq, false_iff]; omega
          · rw [if_neg h4]; simp only [true_iff]; omega
      | some pos =>
        simp only [Option.map_some]
        cases hwc : witCheck b pos with
        | some e => simp
        | none =>
          simp only [Option.isNone_some, Bool.false_eq_true, false_and, ite_false, true_and]
          by_cases h4 : weight b > MAX_BLOCK_WEIGHT
          · rw [if_pos h4]; simp only [reduceCtorEq, false_iff]; omega
          · rw [if_neg h4]; simp only [true_iff]; omega
  · simp only [Bool.not_eq_true] at h1
    simp only [h1, Bool.not_false, ite_true, reduceCtorEq, false_iff, not_and]
    intro h
    obtain ⟨t, ht, hf⟩ := List.all_eq_false.mp h1
    simp [h t ht] at hf

/-! ### The whole check -/

theorem orElse_none {α : Type} (x : Option α) (f : Unit → Option α) : x.orElse f = none ↔ x = none ∧ f () = none := by
  cases x <;> simp [Option.orElse]

/-- **`checkBlock` passes iff the block parses and every rule holds.** -/
theorem checkBlock_none_iff (c : Ctx) (raw : Bytes) :
    checkBlock c raw = none ↔ ∃ b, parseBlock raw = some b ∧ CtxFreeOK b ∧ CtxOK c b := by
  unfold checkBlock
  cases hp : parseBlock raw with
  | none => simp
  | some b =>
    simp only [orElse_none, checkBlockCtxFree_none_iff, checkBlockContextual_none_iff, Option.some.injEq]
    exact ⟨fun h => ⟨b, rfl, h⟩, fun ⟨_, hb, h⟩ => hb ▸ h⟩

/-! ### Simplifications for the AIR -/

theorem serNoWit_le_serWit (t : Tx) : (serNoWit t).length ≤ (serWit t).length := by
  unfold serWit
  split
  · simp only [serNoWit, List.length_append]; omega
  · exact le_rfl

theorem serNoWit_pos (t : Tx) : 1 ≤ (serNoWit t).length := by
  simp only [serNoWit, leBytes, List.length_append, List.length_map, List.length_range]; omega

/-- **Weight bounds the sizes.** A block within the weight limit is within the stripped-size,
transaction-count and per-transaction size limits. -/
theorem size_of_weight (b : Blk) (h : weight b ≤ MAX_BLOCK_WEIGHT) :
    strippedSize b * 4 ≤ MAX_BLOCK_WEIGHT ∧ b.txs.length * 4 ≤ MAX_BLOCK_WEIGHT ∧
      ∀ t ∈ b.txs, (serNoWit t).length * 4 ≤ MAX_BLOCK_WEIGHT := by
  have hst : strippedSize b ≤ totalSize b := by
    unfold strippedSize totalSize
    have : (b.txs.map fun t => (serNoWit t).length).sum ≤ (b.txs.map fun t => (serWit t).length).sum :=
      List.sum_le_sum (fun t _ => serNoWit_le_serWit t)
    omega
  have h4 : strippedSize b * 4 ≤ MAX_BLOCK_WEIGHT := by unfold weight at h; omega
  have hcount : b.txs.length ≤ strippedSize b := by
    unfold strippedSize
    have : b.txs.length ≤ (b.txs.map fun t => (serNoWit t).length).sum := by
      have := List.sum_le_sum (l := b.txs) (f := fun _ => 1) (g := fun t => (serNoWit t).length)
        (fun t _ => serNoWit_pos t)
      simpa using this
    omega
  refine ⟨h4, by omega, fun t ht => ?_⟩
  have : (serNoWit t).length ≤ strippedSize b := by
    unfold strippedSize
    have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun t => (serNoWit t).length) ht)
    omega
  omega

end StarkedAir.Spec.Block
