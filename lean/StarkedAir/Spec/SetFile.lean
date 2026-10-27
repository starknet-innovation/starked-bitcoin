/-
**The coin-set file and the set pass (D-048; docs/design/set-pass.md, step 2).** A set file is the
4-byte count, then per coin `txid(32) ‖ vout(4) ‖ height(4) ‖ cb(1) ‖ txi(4) ‖ len(4) ‖ ser(len)`,
strictly sorted by outpoint (`set_file.zig`'s `Reader`). A record is a coin event
`(⟨txid, vout⟩, (2·height + cb, ser), txi)` (`CoinEpoch.CEv`).

- `parseSet`: the reader's parse and range checks; `parseSet_encSet` and `encSet_of_parseSet`: it
  accepts exactly the encodings of well-formed record lists, so a file's bytes (hence its Blake2s
  digest, under collision resistance) fix its records (`encSet_inj`).
- `facts`: what the pass proves about a file: count, amount, highest coin height, Blake2s digest of the
  file, Core's `hash_serialized` (SHA256d over the `TxOutSer` stream, reversed) and one fraction sum
  per challenge.
- The pass: a state, a per-record `step`, `begin` and `finish`. The hashes are streamed: the Blake2s
  and SHA-256 states hold the chaining value and the bytes not yet compressed (`b2Feed_rep`,
  `shaFeed_rep`), so a segment boundary may fall anywhere. `pass_sound`: `finish` accepts the fold
  over a record list exactly when the list is well formed, sorted and as long as declared, and then
  returns `facts`. `pass_segments`: folding segment by segment is folding the whole list, so any
  segmentation proves the same facts.
-/
import StarkedAir.Spec.BlockTokens
import StarkedAir.Spec.Blake2s
import StarkedAir.Spec.CoinEpoch

namespace StarkedAir.Spec.SetFile

open StarkedAir.Spec.Block StarkedAir.Spec.CoinEpoch

/-! ### The file -/

def txid (e : CEv) : Bytes := e.1.hash
def vout (e : CEv) : ℕ := e.1.n
def code (e : CEv) : ℕ := e.2.1.1
def ser (e : CEv) : Bytes := e.2.1.2
def txi (e : CEv) : ℕ := e.2.2

/-- A record as the file stores it. -/
def encRec (e : CEv) : Bytes :=
  txid e ++ leBytes 4 (vout e) ++ leBytes 4 (code e / 2) ++ [UInt8.ofNat (code e % 2)] ++ leBytes 4 (txi e) ++
    leBytes 4 (ser e).length ++ ser e

def encSet (es : List CEv) : Bytes := leBytes 4 es.length ++ es.flatMap encRec

/-- The reader's range checks (`CoinEpochSound.WFE`: the code below 2^32, the length below P), and the
8-byte amount the pass reads. -/
def RecOk (e : CEv) : Prop :=
  (txid e).length = 32 ∧ vout e < 2 ^ 32 ∧ code e < 2 ^ 32 ∧ txi e < 2 ^ 32 ∧ 8 ≤ (ser e).length ∧
    (ser e).length < 2 ^ 31 - 1

instance (e : CEv) : Decidable (RecOk e) := by unfold RecOk; infer_instance

/-- Lexicographic order on byte strings. -/
def lexLt : Bytes → Bytes → Bool
  | [], _ :: _ => true
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)
  | _, _ => false

/-- Outpoint order: txid bytes, then `vout`. -/
def keyLt (a b : CEv) : Bool := lexLt (txid a) (txid b) || (txid a == txid b && decide (vout a < vout b))

def Sorted (es : List CEv) : Prop := es.IsChain fun a b => keyLt a b = true

/-- Parses `k` records: the fixed 49-byte head, then `len` script bytes. -/
def parseRecs : ℕ → Bytes → Option (List CEv)
  | 0, b => if b = [] then some [] else none
  | k + 1, b =>
    let l := le ((b.drop 45).take 4)
    let cb := le ((b.drop 40).take 1)
    let h := le ((b.drop 36).take 4)
    if b.length < 49 + l ∨ 1 < cb ∨ 2 ^ 31 ≤ h ∨ 2 ^ 31 - 1 ≤ l ∨ l < 8 then none
    else
      let e : CEv := (⟨b.take 32, le ((b.drop 32).take 4)⟩, (2 * h + cb, (b.drop 49).take l), le ((b.drop 41).take 4))
      (parseRecs k (b.drop (49 + l))).map (e :: ·)

def parseSet (b : Bytes) : Option (List CEv) :=
  if b.length < 4 then none else parseRecs (le (b.take 4)) (b.drop 4)

/-! ### Encoding and parsing agree -/

theorem le_leBytes_lt {k n : ℕ} (h : n < 256 ^ k) : le (leBytes k n) = n := by
  rw [le_leBytes, Nat.mod_eq_of_lt h]

theorem encRec_length (e : CEv) (he : RecOk e) : (encRec e).length = 49 + (ser e).length := by
  obtain ⟨h1, -⟩ := he
  simp [encRec, leBytes_length, h1]; omega

/-- The record's fields at their offsets. -/
theorem encRec_fields (e : CEv) (he : RecOk e) (rest : Bytes) :
    let b := encRec e ++ rest
    b.take 32 = txid e ∧ le ((b.drop 32).take 4) = vout e ∧ le ((b.drop 36).take 4) = code e / 2 ∧
      le ((b.drop 40).take 1) = code e % 2 ∧ le ((b.drop 41).take 4) = txi e ∧
      le ((b.drop 45).take 4) = (ser e).length ∧ (b.drop 49).take (ser e).length = ser e ∧
      b.drop (49 + (ser e).length) = rest := by
  obtain ⟨h1, h2, h3, h4, -, h6⟩ := he
  intro b
  have l4 := leBytes_length 4
  have hb : b = txid e ++ (leBytes 4 (vout e) ++ (leBytes 4 (code e / 2) ++ ([UInt8.ofNat (code e % 2)] ++
      (leBytes 4 (txi e) ++ (leBytes 4 (ser e).length ++ (ser e ++ rest)))))) := by
    simp only [b, encRec, List.append_assoc]
  have d49' : (leBytes 4 (ser e).length ++ (ser e ++ rest)).drop 4 = ser e ++ rest := List.drop_left' (l4 _)
  have d45' : (leBytes 4 (txi e) ++ (leBytes 4 (ser e).length ++ (ser e ++ rest))).drop 4 =
      leBytes 4 (ser e).length ++ (ser e ++ rest) := List.drop_left' (l4 _)
  have d41' : ([UInt8.ofNat (code e % 2)] ++ (leBytes 4 (txi e) ++ (leBytes 4 (ser e).length ++ (ser e ++ rest)))).drop 1 =
      leBytes 4 (txi e) ++ (leBytes 4 (ser e).length ++ (ser e ++ rest)) := List.drop_left' rfl
  have d40' : (leBytes 4 (code e / 2) ++ ([UInt8.ofNat (code e % 2)] ++ (leBytes 4 (txi e) ++
      (leBytes 4 (ser e).length ++ (ser e ++ rest))))).drop 4 =
      [UInt8.ofNat (code e % 2)] ++ (leBytes 4 (txi e) ++ (leBytes 4 (ser e).length ++ (ser e ++ rest))) :=
    List.drop_left' (l4 _)
  have d36' : (leBytes 4 (vout e) ++ (leBytes 4 (code e / 2) ++ ([UInt8.ofNat (code e % 2)] ++ (leBytes 4 (txi e) ++
      (leBytes 4 (ser e).length ++ (ser e ++ rest)))))).drop 4 =
      leBytes 4 (code e / 2) ++ ([UInt8.ofNat (code e % 2)] ++ (leBytes 4 (txi e) ++
      (leBytes 4 (ser e).length ++ (ser e ++ rest)))) := List.drop_left' (l4 _)
  have d32 : b.drop 32 = leBytes 4 (vout e) ++ (leBytes 4 (code e / 2) ++ ([UInt8.ofNat (code e % 2)] ++
      (leBytes 4 (txi e) ++ (leBytes 4 (ser e).length ++ (ser e ++ rest))))) := by rw [hb]; exact List.drop_left' h1
  refine ⟨by rw [hb]; exact List.take_left' h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [d32, List.take_left' (l4 _), le_leBytes_lt (by norm_num; omega)]
  · rw [show (36 : ℕ) = 32 + 4 from rfl, ← List.drop_drop, d32, d36', List.take_left' (l4 _),
      le_leBytes_lt (by norm_num; omega)]
  · rw [show (40 : ℕ) = 32 + 4 + 4 from rfl, ← List.drop_drop, ← List.drop_drop, d32, d36', d40']
    simp [le]; omega
  · rw [show (41 : ℕ) = 32 + 4 + 4 + 1 from rfl, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, d32, d36', d40',
      d41', List.take_left' (l4 _), le_leBytes_lt (by norm_num; omega)]
  · rw [show (45 : ℕ) = 32 + 4 + 4 + 1 + 4 from rfl, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop,
      ← List.drop_drop, d32, d36', d40', d41', d45', List.take_left' (l4 _), le_leBytes_lt (by norm_num; omega)]
  · rw [show (49 : ℕ) = 32 + 4 + 4 + 1 + 4 + 4 from rfl, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop,
      ← List.drop_drop, ← List.drop_drop, d32, d36', d40', d41', d45', d49']
    exact List.take_left' (l₁ := ser e) rfl
  · rw [show (49 : ℕ) = 32 + 4 + 4 + 1 + 4 + 4 from rfl, ← List.drop_drop, ← List.drop_drop, ← List.drop_drop,
      ← List.drop_drop, ← List.drop_drop, ← List.drop_drop, d32, d36', d40', d41', d45', d49']
    exact List.drop_left' (l₁ := ser e) rfl

theorem code_split (e : CEv) : 2 * (code e / 2) + code e % 2 = code e := by omega

/-- **The reader parses an encoding back.** -/
theorem parseRecs_enc : ∀ (es : List CEv), (∀ e ∈ es, RecOk e) → parseRecs es.length (es.flatMap encRec) = some es
  | [], _ => by simp [parseRecs]
  | e :: es, hok => by
    have he := hok e List.mem_cons_self
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := encRec_fields e he (es.flatMap encRec)
    have hlen := encRec_length e he
    obtain ⟨-, -, h3, -, h5, h6⟩ := he
    rw [List.flatMap_cons, List.length_cons, parseRecs]
    simp only [f6, f4, f3]
    rw [if_neg (by simp only [List.length_append, hlen, not_or]; omega)]
    simp only [f1, f2, f5, f7, f8, code_split]
    rw [parseRecs_enc es (fun x hx => hok x (List.mem_cons_of_mem _ hx))]
    rfl

theorem parseSet_encSet (es : List CEv) (hok : ∀ e ∈ es, RecOk e) (hn : es.length < 2 ^ 32) :
    parseSet (encSet es) = some es := by
  have l4 := leBytes_length 4 es.length
  unfold parseSet encSet
  rw [if_neg (by simp [l4]), List.take_append_of_le_length (by rw [l4]), List.take_of_length_le (by rw [l4]),
    le_leBytes_lt (by norm_num; omega), List.drop_append_of_le_length (by rw [l4]),
    List.drop_of_length_le (by rw [l4]), List.nil_append]
  exact parseRecs_enc es hok

theorem le_take_lt (b : Bytes) (k : ℕ) : le (b.take k) < 256 ^ k := by
  have := le_lt (b.take k)
  exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by simp))

/-- **Everything the reader accepts is an encoding.** -/
theorem enc_of_parseRecs : ∀ (k : ℕ) (b : Bytes) (es : List CEv), parseRecs k b = some es →
    es.length = k ∧ (∀ e ∈ es, RecOk e) ∧ es.flatMap encRec = b
  | 0, b, es, h => by
    simp only [parseRecs] at h
    split_ifs at h with hb
    · cases h; subst hb; simp
  | k + 1, b, es, h => by
    simp only [parseRecs] at h
    split_ifs at h with hc
    simp only [not_or, not_lt, not_le] at hc
    obtain ⟨hl, hcb, hh, hl1, hl8⟩ := hc
    obtain ⟨es', hp, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨hk, hok, henc⟩ := enc_of_parseRecs k _ es' hp
    set l := le ((b.drop 45).take 4)
    set e : CEv := (⟨b.take 32, le ((b.drop 32).take 4)⟩, (2 * le ((b.drop 36).take 4) + le ((b.drop 40).take 1),
      (b.drop 49).take l), le ((b.drop 41).take 4))
    have hb49 : 49 ≤ b.length := by omega
    have hser : (ser e).length = l := by simp [ser, e]; omega
    have hok' : RecOk e := by
      refine ⟨by simp [txid, e]; omega, ?_, ?_, ?_, by omega, by omega⟩
      · have := le_take_lt (b.drop 32) 4; simp [vout, e]; omega
      · simp only [code, e]; omega
      · have := le_take_lt (b.drop 41) 4; simp [txi, e]; omega
    refine ⟨by simp [hk], ?_, ?_⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hok'
      · exact hok x hx
    · rw [List.flatMap_cons, henc]
      -- The head's bytes are the encoding of `e`'s fields.
      have hcode2 : code e / 2 = le ((b.drop 36).take 4) := by simp only [code, e]; omega
      have hcode1 : code e % 2 = le ((b.drop 40).take 1) := by simp only [code, e]; omega
      have w4 : ∀ j, j + 4 ≤ b.length → leBytes 4 (le ((b.drop j).take 4)) = (b.drop j).take 4 :=
        fun j hj => leBytes_le' (by simp; omega)
      have w1 : [UInt8.ofNat (le ((b.drop 40).take 1))] = (b.drop 40).take 1 := by
        have := leBytes_le' (b := (b.drop 40).take 1) (k := 1) (by simp; omega)
        simpa [leBytes] using this
      have w45 : leBytes 4 l = (b.drop 45).take 4 := w4 45 (by omega)
      simp only [encRec, hser, hcode2, hcode1]
      simp only [txid, vout, txi, ser, e, w4 32 (by omega), w4 36 (by omega), w4 41 (by omega), w45, w1]
      -- Reassemble `b` from its consecutive pieces.
      have split : ∀ (i n : ℕ) (c : Bytes), (c.drop i).take n ++ c.drop (i + n) = c.drop i := by
        intro i n c; rw [← List.drop_drop, List.take_append_drop]
      rw [List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc, List.append_assoc,
        List.append_assoc, split 49 l, split 45 4, split 41 4, split 40 1, split 36 4, split 32 4]
      exact List.take_append_drop 32 b

theorem encSet_of_parseSet {b : Bytes} {es : List CEv} (h : parseSet b = some es) :
    es.length < 2 ^ 32 ∧ (∀ e ∈ es, RecOk e) ∧ encSet es = b := by
  unfold parseSet at h
  split_ifs at h with hb
  obtain ⟨hk, hok, henc⟩ := enc_of_parseRecs _ _ _ h
  refine ⟨by rw [hk]; have := le_take_lt b 4; simpa using this, hok, ?_⟩
  unfold encSet
  rw [henc, hk, leBytes_le' (by simp; omega), List.take_append_drop]

/-- **The bytes fix the records.** -/
theorem encSet_inj {es es' : List CEv} (h : ∀ e ∈ es, RecOk e) (h' : ∀ e ∈ es', RecOk e)
    (hn : es.length < 2 ^ 32) (hn' : es'.length < 2 ^ 32) (he : encSet es = encSet es') : es = es' := by
  have := parseSet_encSet es h hn
  rw [he, parseSet_encSet es' h' hn'] at this
  exact (Option.some.inj this).symm

/-! ### What the pass proves -/

/-- Core's `TxOutSer` (`kernel/coinstats.cpp`): outpoint, `2·height + cb` as u32, the output. -/
def txOutSer (e : CEv) : Bytes := txid e ++ leBytes 4 (vout e) ++ leBytes 4 (code e) ++ ser e

def amountOf (e : CEv) : ℕ := le ((ser e).take 8)

/-- A set file's facts, with one fraction sum per challenge (`fr`: the coin fraction under each). -/
structure Facts (𝕂 : Type) where
  count : ℕ
  amount : ℕ
  maxHeight : ℕ
  digest : Bytes
  hash : Bytes
  sums : List 𝕂

variable {𝕂 : Type} [AddCommMonoid 𝕂]

def facts (fr : List (CEv → 𝕂)) (es : List CEv) : Facts 𝕂 where
  count := es.length
  amount := (es.map amountOf).sum
  maxHeight := (es.map fun e => code e / 2).foldl max 0
  digest := Blake2s.blake2s (encSet es)
  hash := (sha256d (es.flatMap txOutSer)).reverse
  sums := fr.map fun f => (es.map f).sum

/-! ### Streaming Blake2s -/

/-- One non-final compression of the next 64 bytes. -/
def b2Next (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) : ℕ → Blake2s.Word :=
  fun i => ((List.range 8).map (Blake2s.compress h (Blake2s.leWord (b.take 64)) (t + 64) false)).getD i 0

theorem hashBlocks_long (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) (hb : 64 < b.length) :
    Blake2s.hashBlocks h t b = Blake2s.hashBlocks (b2Next h t b) (t + 64) (b.drop 64) := by
  rcases b with _ | ⟨x, xs⟩
  · simp at hb
  · rw [Blake2s.hashBlocks, if_neg (by omega)]
    · rfl
    · simp

/-- The Blake2s state: chaining value, counter, the bytes not yet compressed (at most 64: the last
block is held back for the final compression). -/
structure B2 where
  h : ℕ → Blake2s.Word
  t : ℕ
  pend : Bytes

/-- Compresses while more than one block is pending. -/
def b2Absorb (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) : B2 :=
  if 64 < b.length then b2Absorb (b2Next h t b) (t + 64) (b.drop 64) else ⟨h, t, b⟩
termination_by b.length

theorem b2Absorb_pos {h : ℕ → Blake2s.Word} {t : ℕ} {b : Bytes} (hb : 64 < b.length) :
    b2Absorb h t b = b2Absorb (b2Next h t b) (t + 64) (b.drop 64) := by
  rw [b2Absorb, if_pos hb]

theorem b2Absorb_neg {h : ℕ → Blake2s.Word} {t : ℕ} {b : Bytes} (hb : ¬64 < b.length) : b2Absorb h t b = ⟨h, t, b⟩ := by
  rw [b2Absorb, if_neg hb]

theorem b2Absorb_eq (h : ℕ → Blake2s.Word) (t : ℕ) (b : Bytes) :
    ∀ r, Blake2s.hashBlocks h t (b ++ r) = Blake2s.hashBlocks (b2Absorb h t b).h (b2Absorb h t b).t ((b2Absorb h t b).pend ++ r) := by
  induction h, t, b using b2Absorb.induct with
  | case1 h t b hb ih =>
    intro r
    have hl : 64 < (b ++ r).length := by rw [List.length_append]; omega
    have e1 : b2Next h t (b ++ r) = b2Next h t b := by
      unfold b2Next; rw [List.take_append_of_le_length (by omega)]
    rw [b2Absorb_pos hb, hashBlocks_long _ _ _ hl, ← ih r, e1, List.drop_append_of_le_length (by omega)]
  | case2 h t b hb => intro r; rw [b2Absorb_neg hb]

def b2Init : B2 := ⟨Blake2s.h0, 0, []⟩

def b2Feed (s : B2) (x : Bytes) : B2 := b2Absorb s.h s.t (s.pend ++ x)

def b2Final (s : B2) : Bytes := Blake2s.digest (Blake2s.hashBlocks s.h s.t s.pend)

/-- `s` has absorbed `msg`. -/
def B2Rep (s : B2) (msg : Bytes) : Prop := ∀ r, Blake2s.hashBlocks Blake2s.h0 0 (msg ++ r) = Blake2s.hashBlocks s.h s.t (s.pend ++ r)

theorem b2Init_rep : B2Rep b2Init [] := fun _ => rfl

theorem b2Feed_rep {s : B2} {msg : Bytes} (h : B2Rep s msg) (x : Bytes) : B2Rep (b2Feed s x) (msg ++ x) := by
  intro r
  rw [List.append_assoc, h, ← List.append_assoc, b2Absorb_eq]
  rfl

theorem b2Final_rep {s : B2} {msg : Bytes} (h : B2Rep s msg) : b2Final s = Blake2s.blake2s msg := by
  have := h []
  simp only [List.append_nil] at this
  rw [b2Final, Blake2s.blake2s, this]

/-! ### Streaming SHA-256 -/

theorem compressAll_long (H : Sha256.State) (b : Bytes) (hb : 64 ≤ b.length) :
    compressAll H b = compressAll (Sha256.compress H (chunkWords (b.take 64))) (b.drop 64) := by
  rcases b with _ | ⟨x, xs⟩
  · simp at hb
  · rw [compressAll]

/-- The SHA-256 state: chaining value, the bytes not yet compressed (fewer than 64), the length so far. -/
structure Sha where
  H : Sha256.State
  pend : Bytes
  len : ℕ

/-- Compresses every whole pending block. -/
def shaAbsorb (H : Sha256.State) (b : Bytes) : Sha256.State × Bytes :=
  if 64 ≤ b.length then shaAbsorb (Sha256.compress H (chunkWords (b.take 64))) (b.drop 64) else (H, b)
termination_by b.length
decreasing_by simp; omega

theorem shaAbsorb_pos {H : Sha256.State} {b : Bytes} (hb : 64 ≤ b.length) :
    shaAbsorb H b = shaAbsorb (Sha256.compress H (chunkWords (b.take 64))) (b.drop 64) := by
  rw [shaAbsorb, if_pos hb]

theorem shaAbsorb_neg {H : Sha256.State} {b : Bytes} (hb : ¬64 ≤ b.length) : shaAbsorb H b = (H, b) := by
  rw [shaAbsorb, if_neg hb]

theorem shaAbsorb_eq (H : Sha256.State) (b : Bytes) :
    ∀ r, compressAll H (b ++ r) = compressAll (shaAbsorb H b).1 ((shaAbsorb H b).2 ++ r) := by
  induction H, b using shaAbsorb.induct with
  | case1 H b hb ih =>
    intro r
    have hl : 64 ≤ (b ++ r).length := by rw [List.length_append]; omega
    rw [shaAbsorb_pos hb, compressAll_long _ _ hl, ← ih r,
      List.take_append_of_le_length hb, List.drop_append_of_le_length hb]
  | case2 H b hb => intro r; rw [shaAbsorb_neg hb]

def shaInit : Sha := ⟨Sha256.IV, [], 0⟩

def shaFeed (s : Sha) (x : Bytes) : Sha :=
  let a := shaAbsorb s.H (s.pend ++ x)
  ⟨a.1, a.2, s.len + x.length⟩

/-- The padding after a message of `n` bytes. -/
def padTail (n : ℕ) : Bytes := [0x80] ++ List.replicate ((119 - n % 64) % 64) 0 ++ beBytes 8 (8 * n)

theorem pad_eq (m : Bytes) : pad m = m ++ padTail m.length := by simp [pad, padTail, List.append_assoc]

def shaFinal (s : Sha) : Bytes := stateBytes (compressAll s.H (s.pend ++ padTail s.len))

def ShaRep (s : Sha) (msg : Bytes) : Prop :=
  s.len = msg.length ∧ ∀ r, compressAll Sha256.IV (msg ++ r) = compressAll s.H (s.pend ++ r)

theorem shaInit_rep : ShaRep shaInit [] := ⟨rfl, fun _ => rfl⟩

theorem shaFeed_rep {s : Sha} {msg : Bytes} (h : ShaRep s msg) (x : Bytes) : ShaRep (shaFeed s x) (msg ++ x) := by
  refine ⟨by simp [shaFeed, h.1], fun r => ?_⟩
  rw [List.append_assoc, h.2, ← List.append_assoc, shaAbsorb_eq]
  rfl

theorem shaFinal_rep {s : Sha} {msg : Bytes} (h : ShaRep s msg) : shaFinal s = sha256 msg := by
  rw [shaFinal, sha256, pad_eq, h.2, h.1]

/-! ### The pass -/

/-- The carried state: the declared count and records so far, both hashes, the sums, the amount, the
highest height, the last outpoint (sortedness across segments) and whether every check held. -/
structure St (𝕂 : Type) where
  n : ℕ
  i : ℕ
  b2 : B2
  sha : Sha
  sums : List 𝕂
  amount : ℕ
  maxHeight : ℕ
  last : Option CEv
  ok : Bool

def begin (k : ℕ) (n : ℕ) : St 𝕂 :=
  ⟨n, 0, b2Feed b2Init (leBytes 4 n), shaInit, List.replicate k 0, 0, 0, none, decide (n < 2 ^ 32)⟩

def sortedAfter (last : Option CEv) (e : CEv) : Bool :=
  match last with
  | none => true
  | some p => keyLt p e

def step (fr : List (CEv → 𝕂)) (s : St 𝕂) (e : CEv) : St 𝕂 where
  n := s.n
  i := s.i + 1
  b2 := b2Feed s.b2 (encRec e)
  sha := shaFeed s.sha (txOutSer e)
  sums := List.zipWith (fun a f => a + f e) s.sums fr
  amount := s.amount + amountOf e
  maxHeight := max s.maxHeight (code e / 2)
  last := some e
  ok := s.ok && decide (RecOk e) && sortedAfter s.last e

def finish (s : St 𝕂) : Option (Facts 𝕂) :=
  if s.ok ∧ s.i = s.n then
    some ⟨s.i, s.amount, s.maxHeight, b2Final s.b2, (sha256 (shaFinal s.sha)).reverse, s.sums⟩
  else none

/-- **Segments compose.** Folding segment by segment is folding the whole record list. -/
theorem pass_segments (fr : List (CEv → 𝕂)) (s : St 𝕂) (segs : List (List CEv)) :
    segs.foldl (fun s seg => seg.foldl (step fr) s) s = segs.flatten.foldl (step fr) s := by
  induction segs generalizing s with
  | nil => rfl
  | cons seg segs ih => rw [List.foldl_cons, ih, List.flatten_cons, List.foldl_append]

/-- What the fold keeps, for a prefix `pre` of records already passed. -/
def Inv (fr : List (CEv → 𝕂)) (n : ℕ) (pre : List CEv) (s : St 𝕂) : Prop :=
  s.n = n ∧ s.i = pre.length ∧ B2Rep s.b2 (leBytes 4 n ++ pre.flatMap encRec) ∧ ShaRep s.sha (pre.flatMap txOutSer) ∧
    s.sums = fr.map (fun f => (pre.map f).sum) ∧ s.amount = (pre.map amountOf).sum ∧
    s.maxHeight = (pre.map fun e => code e / 2).foldl max 0 ∧ s.last = pre.getLast? ∧
    (s.ok = true ↔ n < 2 ^ 32 ∧ (∀ e ∈ pre, RecOk e) ∧ Sorted pre)

theorem foldl_max_append (l : List ℕ) (x a : ℕ) : (l ++ [x]).foldl max a = max (l.foldl max a) x := by simp

theorem sorted_append_one (pre : List CEv) (e : CEv) :
    Sorted (pre ++ [e]) ↔ Sorted pre ∧ sortedAfter pre.getLast? e = true := by
  unfold Sorted
  rw [List.isChain_append]
  cases h : pre.getLast? with
  | none => simp [sortedAfter, List.getLast?_eq_none_iff.mp h]
  | some p => simp [sortedAfter]

theorem zipWith_map_self (e : CEv) (g : (CEv → 𝕂) → 𝕂) :
    ∀ fr : List (CEv → 𝕂), List.zipWith (fun a f => a + f e) (fr.map g) fr = fr.map fun f => g f + f e
  | [] => rfl
  | f :: fr => by simp [zipWith_map_self e g fr]

theorem inv_step (fr : List (CEv → 𝕂)) (n : ℕ) (pre : List CEv) (s : St 𝕂) (h : Inv fr n pre s) (e : CEv) :
    Inv fr n (pre ++ [e]) (step fr s e) := by
  obtain ⟨hn, hi, hb, hs, hsum, ham, hmx, hl, hok⟩ := h
  refine ⟨hn, by simp [step, hi], ?_, ?_, ?_, ?_, ?_, by simp [step], ?_⟩
  · have := b2Feed_rep hb (encRec e)
    simpa [step, List.flatMap_append, List.append_assoc] using this
  · have := shaFeed_rep hs (txOutSer e)
    simpa [step, List.flatMap_append] using this
  · simp only [step, hsum, zipWith_map_self]
    simp [List.map_append, List.sum_append]
  · simp [step, ham, List.sum_append]
  · simp [step, hmx]
  · simp only [step, hl, Bool.and_eq_true, decide_eq_true_eq, hok, List.mem_append, List.mem_singleton,
      sorted_append_one]
    constructor
    · rintro ⟨⟨⟨h1, h2, h3⟩, h4⟩, h5⟩
      exact ⟨h1, fun x hx => hx.elim (h2 x) (fun hx => hx ▸ h4), h3, h5⟩
    · rintro ⟨h1, h2, h3, h5⟩
      exact ⟨⟨⟨h1, fun x hx => h2 x (Or.inl hx), h3⟩, h2 e (Or.inr rfl)⟩, h5⟩

theorem inv_fold (fr : List (CEv → 𝕂)) (n : ℕ) :
    ∀ (es pre : List CEv) (s : St 𝕂), Inv fr n pre s → Inv fr n (pre ++ es) (es.foldl (step fr) s)
  | [], pre, s, h => by simpa using h
  | e :: es, pre, s, h => by
    rw [List.foldl_cons, show pre ++ e :: es = (pre ++ [e]) ++ es by simp]
    exact inv_fold fr n es _ _ (inv_step fr n pre s h e)

theorem inv_begin (fr : List (CEv → 𝕂)) (n : ℕ) : Inv fr n [] (begin (𝕂 := 𝕂) fr.length n) := by
  refine ⟨rfl, rfl, ?_, shaInit_rep, ?_, rfl, rfl, rfl, ?_⟩
  · simpa [begin] using b2Feed_rep b2Init_rep (leBytes 4 n)
  · simp [begin, List.map_const']
  · simp [begin, Sorted]

/-- **The pass is sound and complete.** From `begin` with the declared count `n`, `finish` accepts
the fold over `es` exactly when `es` has `n` well-formed, strictly sorted records (`n < 2^32`), and
then returns the file's facts. With `pass_segments`, any segmentation gives the same. -/
theorem pass_sound (fr : List (CEv → 𝕂)) (n : ℕ) (es : List CEv) (F : Facts 𝕂) :
    finish (es.foldl (step fr) (begin fr.length n)) = some F ↔
      (n = es.length ∧ n < 2 ^ 32 ∧ (∀ e ∈ es, RecOk e) ∧ Sorted es) ∧ F = facts fr es := by
  obtain ⟨hn, hi, hb, hs, hsum, ham, hmx, -, hok⟩ := by simpa using inv_fold fr n es [] _ (inv_begin fr n)
  unfold finish
  constructor
  · intro h
    split_ifs at h with hc
    cases h
    obtain ⟨h1, h2⟩ := hc
    obtain ⟨hlt, hrec, hsort⟩ := hok.mp h1
    have hlen : n = es.length := by rw [← hn, ← h2, hi]
    refine ⟨⟨hlen, hlt, hrec, hsort⟩, ?_⟩
    simp only [facts, hi, ham, hmx, hsum, b2Final_rep hb, shaFinal_rep hs, sha256d, encSet, ← hlen]
  · rintro ⟨⟨hlen, hlt, hrec, hsort⟩, rfl⟩
    rw [if_pos ⟨hok.mpr ⟨hlt, hrec, hsort⟩, by rw [hi, hn, hlen]⟩]
    simp only [facts, hi, ham, hmx, hsum, b2Final_rep hb, shaFinal_rep hs, sha256d, encSet, ← hlen]

/-! ### A two-coin file, against Python's `hashlib` and `chainproof set-pass-model` -/

/-- Coins `(00 01 … 1f):1` at height 5, coinbase, 50 BTC; `(01 … 20):0` at height 6, 1,234 sat. -/
def ex2 : Bytes := [
  2, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 30, 31, 1, 0, 0, 0, 5, 0, 0, 0, 1, 7, 0, 0, 0, 10, 0, 0, 0, 0, 242, 5, 42, 1, 0, 0, 0, 1, 81, 1,
  2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30,
  31, 32, 0, 0, 0, 0, 6, 0, 0, 0, 0, 8, 0, 0, 0, 9, 0, 0, 0, 210, 4, 0, 0, 0, 0, 0, 0, 0]

#guard (parseSet ex2).map (fun es => (Blake2s.hex (facts (𝕂 := ℕ) [] es).digest, Blake2s.hex (facts (𝕂 := ℕ) [] es).hash)) =
  some ("073a759f588e2877fd827e4a1c495930268b59999eebb025e0aeb1c597529a05",
    "552bf9252379ea7f7271a758f92852cf6cc3e088fa6b1a9f977454c6d0a38463")

-- The pass over `ex2`'s records, one segment per record, the amount as a "fraction".
#guard ((parseSet ex2).bind fun es => match es with
    | [a, b] => finish ([[a], [b]].foldl (fun s seg => seg.foldl (step (𝕂 := ℕ) [amountOf]) s) (begin 1 2))
    | _ => none).map
      (fun F => (F.count, F.amount, F.maxHeight, Blake2s.hex F.digest, Blake2s.hex F.hash, F.sums)) ==
  some (2, 5000001234, 6, "073a759f588e2877fd827e4a1c495930268b59999eebb025e0aeb1c597529a05",
    "552bf9252379ea7f7271a758f92852cf6cc3e088fa6b1a9f977454c6d0a38463", [5000001234])

-- Out of order: the pass rejects the records swapped.
#guard ((parseSet ex2).bind fun es => match es with
    | [a, b] => finish ([b, a].foldl (step (𝕂 := ℕ) []) (begin 0 2))
    | _ => some ⟨0, 0, 0, [], [], []⟩).isNone

end StarkedAir.Spec.SetFile
