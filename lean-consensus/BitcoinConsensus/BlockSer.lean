/-
**Serialization round trip (M3a.2 foundation).** For a well-formed block, Core's deserializer
(`parseBlock`, Spec/Block.lean) reads back exactly the block that `serBlock` wrote. The block
AIR proves that the raw bytes are the serialization of the fields the prover supplies; this file
carries that to "the raw bytes parse to those fields".
-/
import BitcoinConsensus.Block

namespace BitcoinConsensus.Block

/-! ### Parser steps -/

theorem bind_eq {α β : Type} (p : Parser α) (q : α → Parser β) {s s' : Bytes} {x : α}
    (h : p s = some (x, s')) : (p >>= q) s = q x s' := by
  show (StateT.bind p q) s = q x s'
  simp [StateT.bind, h]

theorem take_append (xs rest : Bytes) : take xs.length (xs ++ rest) = some (xs, rest) := by
  simp [take]

theorem take_append' (n : ℕ) (xs rest : Bytes) (h : xs.length = n) : take n (xs ++ rest) = some (xs, rest) := by
  subst h; exact take_append xs rest

theorem byte_cons (b : UInt8) (rest : Bytes) : byte (b :: rest) = some (b, rest) := rfl

/-! ### Little-endian integers -/

theorem leBytes_succ (k n : ℕ) : leBytes (k + 1) n = UInt8.ofNat n :: leBytes k (n / 256) := by
  simp only [leBytes, List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_eq_add_one]
    congr 1
    rw [Nat.div_div_eq_div_mul, show 8 * (i + 1) = 8 + 8 * i by ring, pow_add]
    norm_num

theorem leBytes_length (k n : ℕ) : (leBytes k n).length = k := by simp [leBytes]

theorem le_leBytes : ∀ k n, le (leBytes k n) = n % 256 ^ k
  | 0, n => by simp [leBytes, le, Nat.mod_one]
  | k + 1, n => by
    rw [leBytes_succ]
    show (UInt8.ofNat n).toNat + 256 * le (leBytes k (n / 256)) = _
    rw [le_leBytes k, show (UInt8.ofNat n).toNat = n % 256 from rfl, pow_succ', Nat.mod_mul]

theorem u32_append (n : ℕ) (rest : Bytes) : u32 (leBytes 4 n ++ rest) = some (n % 2 ^ 32, rest) := by
  unfold u32
  rw [bind_eq _ _ (take_append' 4 _ rest (leBytes_length 4 n))]
  simp only [le_leBytes]
  rfl

theorem MAX_SIZE_lt : MAX_SIZE < 0x100000000 := by unfold MAX_SIZE; norm_num

theorem compactSize_append (n : ℕ) (hn : n ≤ MAX_SIZE) (rest : Bytes) :
    compactSize (serCompact n ++ rest) = some (n, rest) := by
  have hM := MAX_SIZE_lt
  unfold compactSize serCompact
  by_cases h1 : n < 253
  · have hb : (UInt8.ofNat n) < 253 := by
      rw [UInt8.lt_iff_toNat_lt]; show n % 256 < 253; omega
    simp only [if_pos h1, List.singleton_append]
    simp [bind, StateT.bind, byte, hb, pure, StateT.pure, show (UInt8.ofNat n).toNat = n % 256 from rfl,
      Nat.mod_eq_of_lt (by omega : n < 256), show ¬ n > MAX_SIZE by omega]
  · by_cases h2 : n < 0x10000
    · simp only [if_neg h1, if_pos h2, List.cons_append]
      simp [bind, StateT.bind, byte, take, pure, leBytes_length, le_leBytes]
      rw [Nat.mod_eq_of_lt (show n < 65536 by omega), if_neg (by omega)]
      simp [StateT.bind, StateT.pure, show ¬ MAX_SIZE < n by omega]
    · simp only [if_neg h1, if_neg h2, if_pos (show n < 0x100000000 by omega), List.cons_append]
      simp [bind, StateT.bind, byte, take, pure, leBytes_length, le_leBytes]
      rw [Nat.mod_eq_of_lt (show n < 4294967296 by omega), if_neg (by omega)]
      simp [StateT.bind, StateT.pure, show ¬ MAX_SIZE < n by omega]

/-! ### Lists -/

theorem count_append {α : Type} (p : Parser α) (ser : α → Bytes) :
    ∀ (xs : List α), (∀ x ∈ xs, ∀ rest, p (ser x ++ rest) = some (x, rest)) →
      ∀ rest, count p xs.length (xs.flatMap ser ++ rest) = some (xs, rest)
  | [], _, rest => rfl
  | x :: xs, hp, rest => by
    show (do let y ← p; let ys ← count p xs.length; pure (y :: ys) : Parser (List α)) _ = _
    rw [List.flatMap_cons, List.append_assoc, bind_eq _ _ (hp x (List.mem_cons_self ..) _)]
    rw [bind_eq _ _ (count_append p ser xs (fun y hy => hp y (List.mem_cons_of_mem _ hy)) rest)]
    rfl

theorem vec_append {α : Type} (p : Parser α) (ser : α → Bytes) (xs : List α) (hlen : xs.length ≤ MAX_SIZE)
    (hp : ∀ x ∈ xs, ∀ rest, p (ser x ++ rest) = some (x, rest)) (rest : Bytes) :
    vec p (serCompact xs.length ++ xs.flatMap ser ++ rest) = some (xs, rest) := by
  unfold vec
  rw [List.append_assoc, bind_eq _ _ (compactSize_append _ hlen _)]
  exact count_append p ser xs hp rest

theorem varBytes_append (b : Bytes) (hb : b.length ≤ MAX_SIZE) (rest : Bytes) :
    varBytes (serVarBytes b ++ rest) = some (b, rest) := by
  unfold varBytes serVarBytes
  rw [List.append_assoc, bind_eq _ _ (compactSize_append _ hb _)]
  exact take_append b rest

/-! ### Transactions -/

def TxIn.WF (i : TxIn) : Prop :=
  i.prevout.hash.length = 32 ∧ i.prevout.n < 2 ^ 32 ∧ i.scriptSig.length ≤ MAX_SIZE ∧ i.sequence < 2 ^ 32 ∧
    i.witness.length ≤ MAX_SIZE ∧ ∀ w ∈ i.witness, w.length ≤ MAX_SIZE

def TxOut.WF (o : TxOut) : Prop :=
  -2 ^ 63 ≤ o.value ∧ o.value < 2 ^ 63 ∧ o.scriptPubKey.length ≤ MAX_SIZE

theorem txIn_append (i : TxIn) (h : i.WF) (rest : Bytes) :
    txIn (serTxIn i ++ rest) = some ({ i with witness := [] }, rest) := by
  obtain ⟨hh, hn, hs, hq, -, -⟩ := h
  unfold txIn serTxIn
  simp only [List.append_assoc]
  rw [bind_eq _ _ (take_append' 32 _ _ hh), bind_eq _ _ (u32_append _ _), bind_eq _ _ (varBytes_append _ hs _),
    bind_eq _ _ (u32_append _ _), Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hq]
  rfl

theorem txOut_append (o : TxOut) (h : o.WF) (rest : Bytes) : txOut (serTxOut o ++ rest) = some (o, rest) := by
  obtain ⟨hlo, hhi, hs⟩ := h
  unfold txOut serTxOut
  simp only [List.append_assoc]
  rw [bind_eq _ _ (take_append' 8 _ _ (leBytes_length 8 _)), le_leBytes, bind_eq _ _ (varBytes_append _ hs _)]
  show some (_, rest) = some (o, rest)
  congr
  have h64 : ((o.value % 2 ^ 64).toNat : ℤ) = o.value % 2 ^ 64 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num))
  have hlt : (o.value % 2 ^ 64).toNat < 256 ^ 8 := by
    have := Int.emod_lt_of_pos o.value (show (0 : ℤ) < 2 ^ 64 by norm_num)
    omega
  rw [Nat.mod_eq_of_lt hlt]
  split_ifs with hc
  · rw [h64]; push_cast at hc ⊢; omega
  · have hc' : (2 : ℤ) ^ 63 ≤ o.value % 2 ^ 64 := by rw [← h64]; exact_mod_cast not_lt.mp hc
    rw [h64]; omega

def Tx.WF (t : Tx) : Prop :=
  t.version < 2 ^ 32 ∧ t.lockTime < 2 ^ 32 ∧ t.vin ≠ [] ∧ t.vin.length ≤ MAX_SIZE ∧ t.vout.length ≤ MAX_SIZE ∧
    (∀ i ∈ t.vin, i.WF) ∧ ∀ o ∈ t.vout, o.WF

theorem no_witness {t : Tx} (h : t.hasWitness = false) : ∀ i ∈ t.vin, i.witness = [] := by
  intro i hi
  have := List.any_eq_false.mp h i hi
  simpa using this

theorem txIn_noWit {i : TxIn} (h : i.WF) (hw : i.witness = []) (rest : Bytes) :
    txIn (serTxIn i ++ rest) = some (i, rest) := by
  rw [txIn_append i h]; rw [← hw]

theorem tx_legacy (t : Tx) (h : t.WF) (hw : t.hasWitness = false) (rest : Bytes) :
    tx (serNoWit t ++ rest) = some (t, rest) := by
  obtain ⟨hv, hl, hne, hin, hout, hi, ho⟩ := h
  have hw' := no_witness hw
  unfold tx serNoWit
  simp only [List.append_assoc]
  rw [bind_eq _ _ (u32_append _ _), Nat.mod_eq_of_lt hv]
  rw [← List.append_assoc (serCompact _), bind_eq _ _ (vec_append txIn serTxIn t.vin hin
    (fun x hx r => txIn_noWit (hi x hx) (hw' x hx) r) _)]
  have hne' : t.vin.isEmpty = false := by simpa using hne
  simp only [hne', Bool.false_eq_true, if_false]
  rw [← List.append_assoc (serCompact _)]
  rw [bind_eq _ _ (vec_append txOut serTxOut t.vout hout (fun x hx r => txOut_append x (ho x hx) r) _)]
  show (StateT.bind (StateT.pure (0, t.vin, t.vout)) _) _ = _
  simp only [StateT.bind, StateT.pure, pure_bind]
  simp only [Nat.zero_mod, Nat.zero_div, zero_ne_one, if_false, ne_eq, not_true_eq_false]
  simp only [pure, StateT.pure, pure_bind]
  rw [bind_eq _ _ (u32_append _ _), Nat.mod_eq_of_lt hl]
  rfl

theorem zip_witness (vin : List TxIn) :
    ((vin.map fun i => { i with witness := [] }).zip (vin.map (·.witness))).map
      (fun (x : TxIn × List Bytes) => (TxIn.mk x.1.prevout x.1.scriptSig x.1.sequence x.2)) = vin := by
  induction vin with
  | nil => rfl
  | cons i vin ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- The witness section: per input, its stack as a vector of byte vectors. -/
def serWitStack (w : List Bytes) : Bytes := serCompact w.length ++ w.flatMap serVarBytes

theorem witStack_append (w : List Bytes) (hl : w.length ≤ MAX_SIZE) (hw : ∀ x ∈ w, x.length ≤ MAX_SIZE)
    (rest : Bytes) : vec varBytes (serWitStack w ++ rest) = some (w, rest) := by
  unfold serWitStack
  exact vec_append varBytes serVarBytes w hl (fun x hx r => varBytes_append x (hw x hx) r) rest

theorem vec_zero {α : Type} (p : Parser α) (rest : Bytes) : vec p (0 :: rest) = some ([], rest) := by
  have := vec_append p (fun _ => []) [] (by unfold MAX_SIZE; norm_num) (by simp) rest
  simpa [serCompact] using this

theorem tx_segwit (t : Tx) (h : t.WF) (hw : t.hasWitness = true) (rest : Bytes) :
    tx (serWit t ++ rest) = some (t, rest) := by
  obtain ⟨hv, hl, hne, hin, hout, hi, ho⟩ := h
  unfold tx serWit
  simp only [hw, if_true, List.append_assoc]
  rw [bind_eq _ _ (u32_append _ _), Nat.mod_eq_of_lt hv]
  -- The marker 0x00 reads as an empty input vector.
  simp only [List.cons_append, List.nil_append]
  rw [bind_eq _ _ (vec_zero txIn _)]
  simp only [List.isEmpty_nil, if_true]
  rw [bind_eq _ _ (byte_cons _ _)]
  simp only [show (1 : UInt8) ≠ 0 by decide, ne_eq, not_false_eq_true, if_true]
  -- The inputs, read without their witnesses.
  set vs := t.vin.map fun i => { i with witness := [] } with hvs
  have hstrip : t.vin.flatMap serTxIn = vs.flatMap serTxIn := by rw [hvs, List.flatMap_map]; rfl
  have hlen : t.vin.length = vs.length := by rw [hvs, List.length_map]
  rw [hstrip, hlen, ← List.append_assoc (serCompact _), bind_eq _ _ (vec_append txIn serTxIn vs (by rw [← hlen]; exact hin)
    (fun x hx r => by
      obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hx
      exact txIn_append i (hi i hi') r) _)]
  rw [← List.append_assoc (serCompact _)]
  rw [bind_eq _ _ (vec_append txOut serTxOut t.vout hout (fun x hx r => txOut_append x (ho x hx) r) _)]
  -- The witness section: one stack per input.
  have hwit : t.vin.flatMap (fun i => serCompact i.witness.length ++ i.witness.flatMap serVarBytes) =
      (t.vin.map (·.witness)).flatMap serWitStack := by rw [List.flatMap_map]; rfl
  have hlen2 : vs.length = (t.vin.map (·.witness)).length := by rw [hvs, List.length_map, List.length_map]
  simp only [pure_bind, show UInt8.toNat 1 = 1 from rfl, Nat.one_mod, if_true]
  rw [hwit, hlen2, bind_eq _ _ (count_append (vec varBytes) serWitStack _ (fun w hw r => by
      obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hw
      obtain ⟨-, -, -, -, h5, h6⟩ := hi i hi'
      exact witStack_append _ h5 h6 r) _)]
  have hz := zip_witness t.vin
  rw [← hvs] at hz
  simp only [hz]
  have hall : (t.vin.all fun x => x.witness.isEmpty) = false := by
    unfold Tx.hasWitness at hw
    rw [List.all_eq_false]
    obtain ⟨i, hi', hne⟩ := List.any_eq_true.mp hw
    exact ⟨i, hi', by simpa using hne⟩
  simp only [hall, Bool.false_eq_true, if_false, not_true_eq_false]
  rw [bind_eq _ _ (u32_append _ _), Nat.mod_eq_of_lt hl]
  rfl

theorem tx_append (t : Tx) (h : t.WF) (rest : Bytes) : tx (serWit t ++ rest) = some (t, rest) := by
  cases hw : t.hasWitness
  · have : serWit t = serNoWit t := by unfold serWit; simp [hw]
    rw [this]; exact tx_legacy t h hw rest
  · exact tx_segwit t h hw rest

/-! ### Blocks -/

def Blk.WF (b : Blk) : Prop := b.header.length = 80 ∧ b.txs.length ≤ MAX_SIZE ∧ ∀ t ∈ b.txs, t.WF

/-- **Round trip.** Core's deserializer reads a well-formed block's serialization back exactly. -/
theorem parseBlock_serBlock (b : Blk) (h : b.WF) : parseBlock (serBlock b) = some b := by
  obtain ⟨hh, hn, ht⟩ := h
  have e : serBlock b = b.header ++ (serCompact b.txs.length ++ b.txs.flatMap serWit ++ []) := by
    simp [serBlock, List.append_assoc]
  unfold parseBlock
  rw [e, bind_eq _ _ (take_append' 80 _ _ hh), bind_eq _ _ (vec_append tx serWit b.txs hn (fun t ht' r => tx_append t (ht t ht') r) [])]
  rfl

end BitcoinConsensus.Block
