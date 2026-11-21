/-
**Core's coins view, transaction by transaction (M3b).** `connectTx` is Core's `CheckTxInputs` plus
`UpdateCoins` for one transaction of a block at height `h`:
- every input must find a coin, and a coinbase coin must be at least 100 blocks old;
- the inputs sum to at most `MAX_MONEY` and at least the outputs (the fee is the difference);
- spent coins are removed;
- the spendable outputs are added.

Genesis: Core never connects block 0, so its coinbase output is never created; the same holds here.

Two deviations, both stricter than Core (they can only reject more):
- the outputs of the two coinbases Core overwrote unspent (heights 91,722 and 91,812, BIP30) are never
  created. Core replaced them at 91,880 and 91,842, so the views agree from 91,880 on;
- adding an output over an existing coin fails. Core allows a coinbase overwrite after BIP34, which needs
  a SHA256d collision.

**`connect_of_run`**: a transaction's coin events are its inputs' *claimed* coins (the undo records, with
creation indices) and its outputs. If the multiset run on those events succeeds, and the checks hold on
the claimed coins, Core's connect succeeds from the untagged view, ends at the untagged view, and the fees
are the claimed ones. With `run_of_balance`, a balanced epoch therefore connects in Core's sense.

**With relative locks (BIP68, CONNECT-RULES step 2).** `connectTxL` is `connectTx` with one more check
per input, `heightLockOk`: the height-based half of Core's `SequenceLocks`. `connectL_of_run` is
`connect_of_run` for it, given `ClaimsLockOK` as well; `connectTxsL_connectTxs` says the stricter connect
implies the plain one. The time-based half is not in this model yet (step 4).
-/
import StarkedAir.Spec.UtxoMultiset
import StarkedAir.Spec.Block

namespace StarkedAir.Spec.Coins

open StarkedAir.Spec.Block StarkedAir.Spec.Utxo

/-- A coin: creation height, coinbase flag, amount, script. -/
structure Coin where
  height : ℕ
  coinbase : Bool
  value : ℤ
  script : Bytes
  deriving DecidableEq

def COINBASE_MATURITY : ℕ := 100

/-- `CScript::IsUnspendable`: `OP_RETURN` first, or longer than `MAX_SCRIPT_SIZE`. -/
def unspendable (o : TxOut) : Bool := o.scriptPubKey.head? == some 0x6a || decide (10000 < o.scriptPubKey.length)

/-- Coinbases whose outputs are never created: genesis (never connected) and the two Core overwrote
unspent (BIP30). -/
def bip30Lost (h : ℕ) : Bool := h == 0 || h == 91722 || h == 91812

abbrev CView := OutPoint → Option Coin

/-- A transaction in context: height, coinbase flag, txid, the transaction, and per input its claimed coin
and creation index (empty for the coinbase). -/
structure TxC where
  h : ℕ
  cb : Bool
  txid : Bytes
  t : Tx
  claims : List (Coin × ℕ)

/-- The outputs it creates. -/
def created (x : TxC) : List (OutPoint × Coin) :=
  if x.cb && bip30Lost x.h then [] else
  ((x.t.vout.zipIdx).filter fun p => !unspendable p.1).map fun p => (⟨x.txid, p.2⟩, ⟨x.h, x.cb, p.1.value, p.1.scriptPubKey⟩)

/-- Its coin events (`UtxoMultiset`). -/
def events (x : TxC) : Utxo.Tx OutPoint Coin :=
  ⟨if x.cb then [] else (x.t.vin.zip x.claims).map fun p => (p.1.prevout, p.2.1, p.2.2), created x⟩

/-- Core: spend the inputs, summing their amounts. -/
def spendIns (h : ℕ) : CView → List OutPoint → Option (CView × ℤ)
  | v, [] => some (v, 0)
  | v, p :: ps => match v p with
    | none => none
    | some c => if c.coinbase && decide (h < c.height + COINBASE_MATURITY) then none
      else (spendIns h (Function.update v p none) ps).map fun r => (r.1, r.2 + c.value)

/-- Core: add the outputs (no overwrite). -/
def addOuts : CView → List (OutPoint × Coin) → Option CView
  | v, [] => some v
  | v, (k, c) :: rest => match v k with
    | some _ => none
    | none => addOuts (Function.update v k (some c)) rest

def outSum (t : Tx) : ℤ := (t.vout.map (·.value)).sum

/-- **Core's connect of one transaction**, returning the new view and the fee. -/
def connectTx (v : CView) (x : TxC) : Option (CView × ℤ) :=
  if x.cb then (addOuts v (created x)).map fun w => (w, 0)
  else match spendIns x.h v (x.t.vin.map (·.prevout)) with
    | none => none
    | some (v1, vin) =>
      if vin < outSum x.t || MAX_MONEY < vin then none
      else (addOuts v1 (created x)).map fun w => (w, vin - outSum x.t)

def connectTxs : CView → List TxC → Option (CView × List ℤ)
  | v, [] => some (v, [])
  | v, x :: xs => match connectTx v x with
    | none => none
    | some (w, fee) => (connectTxs w xs).map fun r => (r.1, fee :: r.2)

/-- The checks on the claimed coins (the AIR's): maturity per input, and the amounts. -/
def claimSum (x : TxC) : ℤ := (x.claims.map (·.1.value)).sum

def ClaimsOK (x : TxC) : Prop :=
  x.cb ∨ (x.claims.length = x.t.vin.length ∧
    (∀ c ∈ x.claims, ¬ (c.1.coinbase ∧ x.h < c.1.height + COINBASE_MATURITY)) ∧
    outSum x.t ≤ claimSum x ∧ claimSum x ≤ MAX_MONEY)

def claimFee (x : TxC) : ℤ := if x.cb then 0 else claimSum x - outSum x.t

/-- The untagged view of a tagged one. -/
def untag (m : View OutPoint Coin) : CView := fun k => (m k).map Prod.fst

theorem untag_update_none (m : View OutPoint Coin) (k : OutPoint) :
    untag (Function.update m k none) = Function.update (untag m) k none := by
  funext j; by_cases h : j = k
  · subst h; simp [untag]
  · simp [untag, Function.update_of_ne h]

theorem untag_update_some (m : View OutPoint Coin) (k : OutPoint) (c : Coin) (i : ℕ) :
    untag (Function.update m k (some (c, i))) = Function.update (untag m) k (some c) := by
  funext j; by_cases h : j = k
  · subst h; simp [untag]
  · simp [untag, Function.update_of_ne h]

/-- Tagged spends that succeed are Core's spends of the claimed coins. -/
theorem spend_core (h : ℕ) : ∀ (ins : List (TxIn × (Coin × ℕ))) (m m' : View OutPoint Coin),
    (ins.map fun p => (p.1.prevout, p.2.1, p.2.2)).foldlM spendOne m = some m' →
    (∀ p ∈ ins, ¬ (p.2.1.coinbase ∧ h < p.2.1.height + COINBASE_MATURITY)) →
    spendIns h (untag m) (ins.map (·.1.prevout)) = some (untag m', (ins.map (·.2.1.value)).sum)
  | [], m, m', hrun, _ => by simp at hrun; subst hrun; simp [spendIns]
  | p :: ps, m, m', hrun, hmat => by
    simp only [List.map_cons, List.foldlM_cons] at hrun
    obtain ⟨m1, h1, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    simp only [spendOne] at h1
    split_ifs at h1 with hm
    simp only [Option.some.injEq] at h1; subst h1
    have hv : untag m p.1.prevout = some p.2.1 := by simp [untag, hm]
    have hnm := hmat p (by simp)
    simp only [List.map_cons, spendIns, hv]
    rw [if_neg (by simpa using hnm), ← untag_update_none, spend_core h ps _ m' hrest (fun q hq => hmat q (by simp [hq]))]
    simp [List.sum_cons, add_comm]

/-- Tagged adds that succeed are Core's adds. -/
theorem add_core (i : ℕ) : ∀ (outs : List (OutPoint × Coin)) (m m' : View OutPoint Coin),
    outs.foldlM (addOne i) m = some m' → addOuts (untag m) outs = some (untag m')
  | [], m, m', h => by simp at h; subst h; rfl
  | (k, c) :: rest, m, m', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨m1, h1, hrest⟩ := Option.bind_eq_some_iff.mp h
    simp only [addOne] at h1
    split_ifs at h1 with hm
    simp only [Option.some.injEq] at h1; subst h1
    have hv : untag m k = none := by simp [untag, hm]
    simp only [addOuts, hv]
    rw [← untag_update_some]
    exact add_core i rest _ m' hrest

/-- **A successful multiset run on the events is Core's connect.** -/
theorem connect_of_run : ∀ (xs : List TxC) (g : ℕ) (m m' : View OutPoint Coin),
    run g m (xs.map events) = some m' → (∀ x ∈ xs, ClaimsOK x) →
    connectTxs (untag m) xs = some (untag m', xs.map claimFee)
  | [], g, m, m', h, _ => by simp [run] at h; subst h; rfl
  | x :: xs, g, m, m', h, hok => by
    simp only [List.map_cons, run] at h
    obtain ⟨m1, h1, hrest⟩ := Option.bind_eq_some_iff.mp h
    have ih := connect_of_run xs (g + 1) m1 m' hrest (fun y hy => hok y (by simp [hy]))
    simp only [applyTx] at h1
    obtain ⟨m0, h0, hadd⟩ := Option.bind_eq_some_iff.mp h1
    have hcore_add := add_core g (created x) m0 m1 (by simpa [events] using hadd)
    simp only [connectTxs, List.map_cons]
    rcases hok x (by simp) with hcb | ⟨hlen, hmat, hlo, hhi⟩
    · -- the coinbase: no inputs
      have : m0 = m := by simpa [events, hcb] using h0.symm
      subst this
      simp [connectTx, hcb, hcore_add, ih, claimFee]
    · by_cases hcb : x.cb = true
      · have : m0 = m := by simpa [events, hcb] using h0.symm
        subst this
        simp [connectTx, hcb, hcore_add, ih, claimFee]
      · have hcb' : x.cb = false := by simpa using hcb
        have hz : (x.t.vin.zip x.claims).map (·.1.prevout) = x.t.vin.map (·.prevout) := by
          rw [show (fun p : TxIn × (Coin × ℕ) => p.1.prevout) = (fun i : TxIn => i.prevout) ∘ Prod.fst from rfl,
            ← List.map_map, List.map_fst_zip (by omega)]
        have hzs : ((x.t.vin.zip x.claims).map (·.2.1.value)).sum = claimSum x := by
          unfold claimSum
          rw [show (fun p : TxIn × (Coin × ℕ) => p.2.1.value) = (fun c : Coin × ℕ => c.1.value) ∘ Prod.snd from rfl,
            ← List.map_map, List.map_snd_zip (by omega)]
        have hsp := spend_core x.h (x.t.vin.zip x.claims) m m0 (by simpa [events, hcb'] using h0)
          (fun p hp => hmat p.2 (List.of_mem_zip hp).2)
        rw [hz, hzs] at hsp
        have hc : connectTx (untag m) x = some (untag m1, claimSum x - outSum x.t) := by
          simp only [connectTx, hcb', Bool.false_eq_true, if_false, hsp]
          rw [if_neg (by simp; omega), hcore_add]; rfl
        simp [hc, ih, claimFee, hcb']

/-! ### With height-based relative locks (BIP68) -/

/-- **BIP68, height-based** (`SequenceLocks`, the height half): once CSV is active, an input of a
transaction of version at least 2 whose sequence has bits 31 and 22 clear spends a coin at least
`sequence mod 2^16` blocks old. Inputs with a time-based lock (bit 22 set) pass here. -/
def heightLockOk (h version sequence coinHeight : ℕ) : Bool :=
  !(decide (CSV_HEIGHT ≤ h) && decide (2 ≤ version) && decide (sequence / 2 ^ 31 % 2 = 0) &&
      decide (sequence / 2 ^ 22 % 2 = 0)) ||
    decide (coinHeight + sequence % 2 ^ 16 ≤ h)

/-- **The time-based half of Core's `SequenceLocks`** (BIP68, CONNECT-RULES step 4), for one input: when
CSV is active, the version is at least 2, bit 31 of the sequence is clear and bit 22 is set, the median
time past of the block before the coin's (`coinMtp`) plus `512 ·` the sequence's low 16 bits is at most the
median time past of the block before the spending one (`prevMtp`). Core: `nMinTime = coinMtp +
(lock << 9) − 1` must be below the block's previous median time past. -/
def timeLockOk (h version sequence coinMtp prevMtp : ℕ) : Bool :=
  !(decide (CSV_HEIGHT ≤ h) && decide (2 ≤ version) && decide (sequence / 2 ^ 31 % 2 = 0) &&
      decide (sequence / 2 ^ 22 % 2 = 1)) ||
    decide (coinMtp + 512 * (sequence % 2 ^ 16) ≤ prevMtp)

/-- `spendIns` with each input's height lock checked against the coin it finds (`version` is the
transaction's; each input is its prevout and its sequence). -/
def spendInsL (h version : ℕ) : CView → List (OutPoint × ℕ) → Option (CView × ℤ)
  | v, [] => some (v, 0)
  | v, p :: ps => match v p.1 with
    | none => none
    | some c => if (c.coinbase && decide (h < c.height + COINBASE_MATURITY)) ||
          !heightLockOk h version p.2 c.height then none
      else (spendInsL h version (Function.update v p.1 none) ps).map fun r => (r.1, r.2 + c.value)

/-- **Core's connect of one transaction, with the height-based relative locks.** -/
def connectTxL (v : CView) (x : TxC) : Option (CView × ℤ) :=
  if x.cb then (addOuts v (created x)).map fun w => (w, 0)
  else match spendInsL x.h x.t.version v (x.t.vin.map fun i => (i.prevout, i.sequence)) with
    | none => none
    | some (v1, vin) =>
      if vin < outSum x.t || MAX_MONEY < vin then none
      else (addOuts v1 (created x)).map fun w => (w, vin - outSum x.t)

def connectTxsL : CView → List TxC → Option (CView × List ℤ)
  | v, [] => some (v, [])
  | v, x :: xs => match connectTxL v x with
    | none => none
    | some (w, fee) => (connectTxsL w xs).map fun r => (r.1, fee :: r.2)

/-- The lock check on the claimed coins (the AIR's): each input's height lock against its claim's height. -/
def ClaimsLockOK (x : TxC) : Prop :=
  x.cb ∨ ∀ p ∈ x.t.vin.zip x.claims, heightLockOk x.h x.t.version p.1.sequence p.2.1.height = true

/-- The stricter spend implies the plain one. -/
theorem spendInsL_spendIns (h version : ℕ) : ∀ (ins : List (OutPoint × ℕ)) (v : CView) (r : CView × ℤ),
    spendInsL h version v ins = some r → spendIns h v (ins.map Prod.fst) = some r
  | [], v, r, hr => by simpa [spendInsL, spendIns] using hr
  | p :: ps, v, r, hr => by
    simp only [spendInsL] at hr
    simp only [List.map_cons, spendIns]
    cases hv : v p.1 with
    | none => rw [hv] at hr; simp at hr
    | some c =>
      rw [hv] at hr
      simp only at hr ⊢
      split_ifs at hr with hc
      have hm : ¬ (c.coinbase && decide (h < c.height + COINBASE_MATURITY)) = true := by
        intro hm; exact hc (by rw [hm]; rfl)
      rw [if_neg hm]
      obtain ⟨r1, h1, rfl⟩ := Option.map_eq_some_iff.mp hr
      rw [spendInsL_spendIns h version ps _ r1 h1]; rfl

/-- **Connecting with the relative locks implies connecting without them**: the lock is one more reason
to reject. -/
theorem connectTxL_connectTx (v : CView) (x : TxC) (r : CView × ℤ) (h : connectTxL v x = some r) :
    connectTx v x = some r := by
  unfold connectTxL at h
  unfold connectTx
  split_ifs at h ⊢ with hcb
  · exact h
  · cases hs : spendInsL x.h x.t.version v (x.t.vin.map fun i => (i.prevout, i.sequence)) with
    | none => rw [hs] at h; simp at h
    | some r1 =>
      rw [hs] at h
      have := spendInsL_spendIns x.h x.t.version _ v r1 hs
      rw [List.map_map] at this
      rw [show (x.t.vin.map (·.prevout)) = x.t.vin.map (Prod.fst ∘ fun i : TxIn => (i.prevout, i.sequence)) from rfl,
        this]
      exact h

theorem connectTxsL_connectTxs : ∀ (xs : List TxC) (v : CView) (r : CView × List ℤ),
    connectTxsL v xs = some r → connectTxs v xs = some r
  | [], v, r, h => by simpa [connectTxsL, connectTxs] using h
  | x :: xs, v, r, h => by
    simp only [connectTxsL] at h
    simp only [connectTxs]
    cases hx : connectTxL v x with
    | none => rw [hx] at h; simp at h
    | some wf =>
      rw [hx] at h
      rw [connectTxL_connectTx v x wf hx]
      simp only at h ⊢
      obtain ⟨r1, h1, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [connectTxsL_connectTxs xs _ r1 h1]; rfl

/-- Tagged spends that succeed, with the claimed coins mature and their height locks met, are Core's
spends with the locks checked. -/
theorem spend_coreL (h version : ℕ) : ∀ (ins : List (TxIn × (Coin × ℕ))) (m m' : View OutPoint Coin),
    (ins.map fun p => (p.1.prevout, p.2.1, p.2.2)).foldlM spendOne m = some m' →
    (∀ p ∈ ins, ¬ (p.2.1.coinbase ∧ h < p.2.1.height + COINBASE_MATURITY)) →
    (∀ p ∈ ins, heightLockOk h version p.1.sequence p.2.1.height = true) →
    spendInsL h version (untag m) (ins.map fun p => (p.1.prevout, p.1.sequence)) =
      some (untag m', (ins.map (·.2.1.value)).sum)
  | [], m, m', hrun, _, _ => by simp at hrun; subst hrun; simp [spendInsL]
  | p :: ps, m, m', hrun, hmat, hlk => by
    simp only [List.map_cons, List.foldlM_cons] at hrun
    obtain ⟨m1, h1, hrest⟩ := Option.bind_eq_some_iff.mp hrun
    simp only [spendOne] at h1
    split_ifs at h1 with hm
    simp only [Option.some.injEq] at h1; subst h1
    have hv : untag m p.1.prevout = some p.2.1 := by simp [untag, hm]
    have hnm := hmat p (by simp)
    have hl := hlk p (by simp)
    simp only [List.map_cons, spendInsL, hv]
    rw [if_neg (by simpa [hl] using hnm), ← untag_update_none,
      spend_coreL h version ps _ m' hrest (fun q hq => hmat q (by simp [hq])) (fun q hq => hlk q (by simp [hq]))]
    simp [List.sum_cons, add_comm]

/-- **A successful multiset run on the events is Core's connect with the relative locks**, when the
claims pass the lock check too. -/
theorem connectL_of_run : ∀ (xs : List TxC) (g : ℕ) (m m' : View OutPoint Coin),
    run g m (xs.map events) = some m' → (∀ x ∈ xs, ClaimsOK x) → (∀ x ∈ xs, ClaimsLockOK x) →
    connectTxsL (untag m) xs = some (untag m', xs.map claimFee)
  | [], g, m, m', h, _, _ => by simp [run] at h; subst h; rfl
  | x :: xs, g, m, m', h, hok, hokL => by
    simp only [List.map_cons, run] at h
    obtain ⟨m1, h1, hrest⟩ := Option.bind_eq_some_iff.mp h
    have ih := connectL_of_run xs (g + 1) m1 m' hrest (fun y hy => hok y (by simp [hy]))
      (fun y hy => hokL y (by simp [hy]))
    simp only [applyTx] at h1
    obtain ⟨m0, h0, hadd⟩ := Option.bind_eq_some_iff.mp h1
    have hcore_add := add_core g (created x) m0 m1 (by simpa [events] using hadd)
    simp only [connectTxsL, List.map_cons]
    by_cases hcb : x.cb = true
    · have : m0 = m := by simpa [events, hcb] using h0.symm
      subst this
      simp [connectTxL, hcb, hcore_add, ih, claimFee]
    · have hcb' : x.cb = false := by simpa using hcb
      obtain ⟨hlen, hmat, hlo, hhi⟩ := (hok x (by simp)).resolve_left hcb
      have hlock := (hokL x (by simp)).resolve_left hcb
      have hz : (x.t.vin.zip x.claims).map (fun p => (p.1.prevout, p.1.sequence)) =
          x.t.vin.map fun i => (i.prevout, i.sequence) := by
        rw [show (fun p : TxIn × (Coin × ℕ) => (p.1.prevout, p.1.sequence)) =
            (fun i : TxIn => (i.prevout, i.sequence)) ∘ Prod.fst from rfl,
          ← List.map_map, List.map_fst_zip (by omega)]
      have hzs : ((x.t.vin.zip x.claims).map (·.2.1.value)).sum = claimSum x := by
        unfold claimSum
        rw [show (fun p : TxIn × (Coin × ℕ) => p.2.1.value) = (fun c : Coin × ℕ => c.1.value) ∘ Prod.snd from rfl,
          ← List.map_map, List.map_snd_zip (by omega)]
      have hsp := spend_coreL x.h x.t.version (x.t.vin.zip x.claims) m m0 (by simpa [events, hcb'] using h0)
        (fun p hp => hmat p.2 (List.of_mem_zip hp).2) hlock
      rw [hz, hzs] at hsp
      have hc : connectTxL (untag m) x = some (untag m1, claimSum x - outSum x.t) := by
        simp only [connectTxL, hcb', Bool.false_eq_true, if_false, hsp]
        rw [if_neg (by simp; omega), hcore_add]; rfl
      simp [hc, ih, claimFee, hcb']

end StarkedAir.Spec.Coins
