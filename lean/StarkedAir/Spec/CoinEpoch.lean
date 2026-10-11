/-
**An epoch's coin events, at the spec level (M3b, layer 5).** A block at height `h` creates, per
transaction `t` and live output `v` (spendable, and not a BIP30-lost coinbase output), the coin
`(⟨txid, v⟩, (2h + [t = 0], serTxOut))` with creation index `N h + t`, where `N h` counts the chain's
transactions before height `h` (so indices are the transactions' global positions, as `Utxo.run`
numbers them). Each non-coinbase input spends its claim: the record's `(code, serTxOut)` and the claimed
creating transaction `ctx`, with index `N (code / 2) + ctx`.

Coin values are `(code, serTxOut)` pairs here, the coin component's tuple fields; Core's `Coin`s are
recovered once the balance shows every claim is a created coin.
-/
import StarkedAir.Spec.UtxoBalance
import StarkedAir.Spec.Coins

namespace StarkedAir.Spec.CoinEpoch

open StarkedAir.Spec.Block StarkedAir.Spec.Utxo

/-- A coin value: `code = 2·height + coinbase` and `serTxOut`. -/
abbrev Val := ℕ × Bytes
abbrev CEv := Ev OutPoint Val

/-- An input's claim (an undo record and the claimed creating transaction). -/
structure Claim where
  code : ℕ
  ser : Bytes
  ctx : ℕ
  deriving DecidableEq, Inhabited

/-- A block's coin data: height, transactions, the BIP30-lost bit, one claim per non-coinbase input. -/
structure BlockC where
  h : ℕ
  txs : List Tx
  lost : Bool
  claims : List Claim

def codeOf (h t : ℕ) : ℕ := 2 * h + if t = 0 then 1 else 0

def live (lost : Bool) (t : ℕ) (o : TxOut) : Bool := !Spec.Coins.unspendable o && !(t == 0 && lost)

/-- The non-coinbase inputs of transactions `1 … t − 1`. -/
def insBefore (txs : List Tx) (t : ℕ) : ℕ :=
  ((List.range t).map fun t' => if 1 ≤ t' then ((txs[t']?.map (·.vin.length)).getD 0) else 0).sum

/-- A transaction's created coins. -/
def txOuts (B : BlockC) (t : ℕ) (tx : Tx) : List (OutPoint × Val) :=
  ((tx.vout.zipIdx).filter fun p => live B.lost t p.1).map fun p => (⟨txid tx, p.2⟩, (codeOf B.h t, serTxOut p.1))

/-- A transaction's spends: its inputs with their claims (none for the coinbase). -/
def txIns (N : ℕ → ℕ) (B : BlockC) (t : ℕ) (tx : Tx) : List CEv :=
  if t = 0 then [] else
  (tx.vin.zipIdx).map fun p =>
    let c := B.claims.getD (insBefore B.txs t + p.2) default
    (p.1.prevout, (c.code, c.ser), N (c.code / 2) + c.ctx)

/-- A block's transactions as multiset-argument transactions. -/
def blockTxs (N : ℕ → ℕ) (B : BlockC) : List (Utxo.Tx OutPoint Val) :=
  (B.txs.zipIdx).map fun p => ⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩

/-! ### Creation indices are positions -/

theorem created_append (g : ℕ) : ∀ (l1 l2 : List (Utxo.Tx OutPoint Val)),
    created g (l1 ++ l2) = created g l1 + created (g + l1.length) l2
  | [], l2 => by simp [created]
  | t :: l1, l2 => by
    simp only [List.cons_append, created, List.length_cons]
    rw [created_append (g + 1) l1 l2, ← add_assoc, show g + 1 + l1.length = g + (l1.length + 1) by omega]

/-- A created coin of a block's transaction list: its code and its index (`g + t`). -/
theorem mem_created_block (N : ℕ → ℕ) (B : BlockC) (g : ℕ) {e : CEv} (he : e ∈ created g (blockTxs N B)) :
    ∃ t < B.txs.length, e.2.2 = g + t ∧ e.2.1.1 = codeOf B.h t := by
  have gen : ∀ (l : List (Tx × ℕ)) (g : ℕ), (∀ p ∈ l, p.2 < B.txs.length) →
      e ∈ created g (l.map fun p => (⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩ : Utxo.Tx OutPoint Val)) →
      ∃ k < l.length, ∃ p ∈ l, e.2.2 = g + k ∧ e.2.1.1 = codeOf B.h p.2 ∧ l[k]? = some p := by
    intro l
    induction l with
    | nil => intro g _ h; simp [created] at h
    | cons p l ih =>
      intro g hl h
      simp only [List.map_cons, created, Multiset.mem_add] at h
      rcases h with h | h
      · simp only [outsT, Multiset.mem_coe] at h
        obtain ⟨o, ho, rfl⟩ := List.mem_map.mp h
        simp only [txOuts] at ho
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp ho
        exact ⟨0, by simp, p, by simp, by simp, rfl, by simp⟩
      · obtain ⟨k, hk, p', hp', h1, h2, h3⟩ := ih (g + 1) (fun q hq => hl q (by simp [hq])) h
        exact ⟨k + 1, by simp; omega, p', by simp [hp'], by omega, h2, by simpa using h3⟩
  obtain ⟨k, hk, p, hp, h1, h2, h3⟩ := gen B.txs.zipIdx g (fun p hp => by simpa using (List.mem_zipIdx hp).2.1) he
  have hk' : k < B.txs.length := by simpa using hk
  have hpk : p.2 = k := by
    rw [List.getElem?_zipIdx, Option.map_eq_some_iff] at h3
    obtain ⟨tx, -, rfl⟩ := h3; simp
  exact ⟨k, hk', h1, by rw [h2, hpk]⟩

/-! ### Ordering, from the balance -/

def allTxs (N : ℕ → ℕ) (blocks : List BlockC) : List (Utxo.Tx OutPoint Val) := blocks.flatMap (blockTxs N)

theorem blockTxs_length (N : ℕ → ℕ) (B : BlockC) : (blockTxs N B).length = B.txs.length := by simp [blockTxs]

theorem ordered_append : ∀ (g : ℕ) (l1 l2 : List (Utxo.Tx OutPoint Val)),
    Ordered g l1 → Ordered (g + l1.length) l2 → Ordered g (l1 ++ l2)
  | g, [], l2, _, h2 => by simpa using h2
  | g, t :: l1, l2, ⟨h1, h1'⟩, h2 => ⟨h1, ordered_append (g + 1) l1 l2 h1' (by simpa [Nat.add_assoc, Nat.add_comm 1] using h2)⟩

theorem mem_spent_append : ∀ (l1 l2 : List (Utxo.Tx OutPoint Val)), spent (l1 ++ l2) = spent l1 + spent l2
  | [], l2 => by simp [spent]
  | t :: l1, l2 => by simp only [List.cons_append, spent]; rw [mem_spent_append l1 l2, add_assoc]

/-- The created coins of the epoch: each from some block `i`'s transaction `t`, with index
`g + (earlier blocks' transactions) + t` and code `codeOf h t`. -/
theorem mem_created_all (N : ℕ → ℕ) : ∀ (blocks : List BlockC) (g : ℕ) {e : CEv}, e ∈ created g (allTxs N blocks) →
    ∃ i B t, blocks[i]? = some B ∧ t < B.txs.length ∧
      e.2.2 = g + ((blocks.take i).map (·.txs.length)).sum + t ∧ e.2.1.1 = codeOf B.h t
  | [], g, e, h => by simp [allTxs, created] at h
  | B :: bs, g, e, h => by
    simp only [allTxs, List.flatMap_cons, created_append, Multiset.mem_add] at h
    rcases h with h | h
    · obtain ⟨t, ht, h1, h2⟩ := mem_created_block N B g h
      exact ⟨0, B, t, rfl, ht, by simpa using h1, h2⟩
    · obtain ⟨i, B', t, hB, ht, h1, h2⟩ := mem_created_all N bs _ h
      refine ⟨i + 1, B', t, by simpa using hB, ht, ?_, h2⟩
      rw [h1, blockTxs_length]; simp [List.take_succ_cons]; ring

theorem codeOf_div (h t : ℕ) : codeOf h t / 2 = h := by unfold codeOf; split_ifs <;> omega

/-- A block's spends are among the epoch's. -/
theorem mem_spent_all (N : ℕ → ℕ) : ∀ (blocks : List BlockC) {i : ℕ} {B : BlockC} {t : ℕ} {tx : Tx} {e : CEv},
    blocks[i]? = some B → B.txs[t]? = some tx → e ∈ txIns N B t tx → e ∈ spent (allTxs N blocks)
  | [], i, _, _, _, _, h, _, _ => by simp at h
  | B0 :: bs, i, B, t, tx, e, hB, htx, he => by
    simp only [allTxs, List.flatMap_cons, mem_spent_append, Multiset.mem_add]
    cases i with
    | zero =>
      left
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hB; subst hB
      have gen : ∀ (l : List (Tx × ℕ)), (tx, t) ∈ l →
          e ∈ spent (l.map fun p => (⟨txIns N B0 p.2 p.1, txOuts B0 p.2 p.1⟩ : Utxo.Tx OutPoint Val)) := by
        intro l hl
        induction l with
        | nil => simp at hl
        | cons p l ih =>
          simp only [List.map_cons, spent, Multiset.mem_add, Multiset.mem_coe]
          rcases List.mem_cons.mp hl with h | h
          · left; rw [← h]; exact he
          · right; exact ih h
      exact gen _ (List.mem_zipIdx_iff_getElem?.mpr (by simpa using htx))
    | succ i => right; exact mem_spent_all N bs (by simpa using hB) htx he

/-- **Ordering from the balance.** Every claimed creation index is earlier than its spending
transaction: a claim equal to an initial coin is before the epoch; one equal to a created coin is that
coin's transaction, and the circuit's check `(code / 2, ctx) < (height, t)` orders the two. -/
theorem ordered_of_balance (N : ℕ → ℕ) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv)
    (hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum)
    (hinc : ∀ (i i' : ℕ) (B B' : BlockC), blocks[i]? = some B → blocks[i']? = some B' → (B.h < B'.h ↔ i < i'))
    (hlex : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Tx), B.txs[t]? = some tx → ∀ e ∈ txIns N B t tx,
      ∃ c : Claim, e = (e.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
        (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t)))
    (hinit : ∀ e ∈ init, e.2.2 < g0)
    (hbal : (init : Multiset CEv) + created g0 (allTxs N blocks) = spent (allTxs N blocks) + fin) :
    ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Tx), B.txs[t]? = some tx →
      ∀ e ∈ txIns N B t tx, e.2.2 < N B.h + t := by
  intro i B hB t tx htx e he
  have hsp := mem_spent_all N blocks hB htx he
  have hin : e ∈ (init : Multiset CEv) + created g0 (allTxs N blocks) := by
    rw [hbal]; exact Multiset.mem_add.mpr (Or.inl hsp)
  have hNB := hpos i B hB
  obtain ⟨c, hc, hl⟩ := hlex i B hB t tx htx e he
  rcases Multiset.mem_add.mp hin with h | h
  · have := hinit e (by simpa using h); omega
  · obtain ⟨i', B', t', hB', ht', hidx, hcode⟩ := mem_created_all N blocks g0 h
    have hNB' := hpos i' B' hB'
    rw [hc] at hidx hcode
    simp only at hidx hcode
    have hh' : c.code / 2 = B'.h := by rw [hcode, codeOf_div]
    rw [hh'] at hidx hl
    have hctx : c.ctx = t' := by omega
    rcases hl with hl | ⟨hl, hlt⟩
    · have hii : i' < i := (hinc i' i B' B hB' hB).mp hl
      -- the earlier block's transactions all come before block i
      have hpre : ((blocks.take i').map (·.txs.length)).sum + B'.txs.length ≤ ((blocks.take i).map (·.txs.length)).sum := by
        have hi'l : i' < blocks.length := (List.getElem?_eq_some_iff.mp hB').1
        have e1 : ((blocks.take (i' + 1)).map (·.txs.length)).sum = ((blocks.take i').map (·.txs.length)).sum + B'.txs.length := by
          rw [List.take_succ, List.map_append, List.sum_append, hB']; simp
        have e2 : ((blocks.take (i' + 1)).map (·.txs.length)).sum ≤ ((blocks.take i).map (·.txs.length)).sum := by
          have := List.take_prefix_take_left (l := blocks) (show i' + 1 ≤ i by omega)
          exact List.Sublist.sum_le_sum ((this.sublist).map _) (fun _ _ => Nat.zero_le _)
        omega
      rw [hc]; simp only; rw [hh']; omega
    · have hii : i' = i := by
        rcases Nat.lt_trichotomy i' i with h1 | h1 | h1
        · exact absurd ((hinc i' i B' B hB' hB).mpr h1) (by omega)
        · exact h1
        · exact absurd ((hinc i i' B B' hB hB').mpr h1) (by omega)
      subst hii
      rw [hB] at hB'; obtain rfl := Option.some.inj hB'
      rw [hc]; simp only; rw [hh']; omega

theorem ordered_block (N : ℕ → ℕ) (B : BlockC) (g : ℕ)
    (h : ∀ (t : ℕ) (tx : Tx), B.txs[t]? = some tx → ∀ e ∈ txIns N B t tx, e.2.2 < g + t) : Ordered g (blockTxs N B) := by
  have gen : ∀ (l : List (Tx × ℕ)) (g' : ℕ), (∀ k p, l[k]? = some p → B.txs[p.2]? = some p.1 ∧ p.2 = g' - g + k) → g ≤ g' →
      Ordered g' (l.map fun p => (⟨txIns N B p.2 p.1, txOuts B p.2 p.1⟩ : Utxo.Tx OutPoint Val)) := by
    intro l
    induction l with
    | nil => intro _ _ _; trivial
    | cons p l ih =>
      intro g' hl hg
      obtain ⟨hp1, hp2⟩ := hl 0 p rfl
      refine ⟨fun e he => ?_, ih (g' + 1) (fun k q hq => ?_) (by omega)⟩
      · have := h p.2 p.1 hp1 e he; omega
      · obtain ⟨a, b⟩ := hl (k + 1) q (by simpa using hq); exact ⟨a, by omega⟩
  apply gen B.txs.zipIdx g (fun k p hp => ?_) le_rfl
  rw [List.getElem?_zipIdx, Option.map_eq_some_iff] at hp
  obtain ⟨tx, htx, rfl⟩ := hp
  exact ⟨by simpa using htx, by simp⟩

/-- **The epoch is ordered.** -/
theorem ordered_all (N : ℕ → ℕ) (g0 : ℕ) : ∀ (blocks : List BlockC) (pre : ℕ),
    (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Tx), B.txs[t]? = some tx →
      ∀ e ∈ txIns N B t tx, e.2.2 < g0 + pre + ((blocks.take i).map (·.txs.length)).sum + t) →
    Ordered (g0 + pre) (allTxs N blocks)
  | [], _, _ => trivial
  | B :: bs, pre, h => by
    simp only [allTxs, List.flatMap_cons]
    apply ordered_append
    · exact ordered_block N B _ (fun t tx htx e he => by have := h 0 B rfl t tx htx e he; simpa using this)
    · rw [blockTxs_length, Nat.add_assoc]
      exact ordered_all N g0 bs (pre + B.txs.length) (fun i B' hB' t tx htx e he => by
        have := h (i + 1) B' (by simpa using hB') t tx htx e he
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this
        omega)

end StarkedAir.Spec.CoinEpoch
