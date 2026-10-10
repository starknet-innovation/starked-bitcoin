/-
**A block's inputs and outputs, as tokens (M3b).** The coin component sees a block's input and output
tokens in order. For a block parsed from tokens (`toksBlock`), those tokens are, transaction by
transaction, the transaction's inputs then its outputs:

- `io_txT`: a transaction's tokens' input and output tokens are its inputs' and outputs' tokens;
- `io_txsT`, `io_toksBlock`: for the whole block, `ioOf ts = b.txs.flatMap ioTx`.

`ioTx t` lists, per input, the token `inp` carrying the prevout's hash and index bytes, and per output
the token `out` carrying the value bytes and the script.
-/
import StarkedAir.Spec.BlockTokens

namespace StarkedAir.Spec.Block

/-- Input and output tokens. -/
def Tok.isIo : Tok → Bool
  | .inp .. => true
  | .out .. => true
  | _ => false

def ioOf (ts : List Tok) : List Tok := ts.filter Tok.isIo

/-- A token's description of an input: the prevout matches, the script and sequence too. -/
def InTok (i : TxIn) : Tok → Prop
  | .inp h ix s q => h.length = 32 ∧ ix.length = 4 ∧ q.length = 4 ∧ i.prevout = ⟨h, le ix⟩ ∧ i.scriptSig = s ∧
      i.sequence = le q
  | _ => False

/-- A token's description of an output: its value bytes and script. -/
def OutTok (o : TxOut) : Tok → Prop
  | .out v s => v.length = 8 ∧ o.value = signed64 (le v) ∧ o.scriptPubKey = s
  | _ => False

/-- A list of tokens describes a transaction's inputs then outputs. -/
def IoTx (t : Tx) (l : List Tok) : Prop :=
  ∃ li lo, l = li ++ lo ∧ List.Forall₂ InTok t.vin li ∧ List.Forall₂ OutTok t.vout lo

theorem io_insT : ∀ (k : ℕ) (ts : List Tok) (ins : List TxIn) (rest : List Tok),
    insT k ts = some (ins, rest) →
    ∃ pre, ts = pre ++ rest ∧ ioOf pre = pre ∧ List.Forall₂ (fun i tk => InTok i tk ∧ i.witness = []) ins pre
  | 0, ts, ins, rest, h => by
    simp [insT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, List.Forall₂.nil⟩
  | k + 1, .inp hh ix s q :: ts, ins, rest, h => by
    simp only [insT] at h
    split_ifs at h with hc
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨pre, hpre, hio, hf⟩ := io_insT k ts r.1 r.2 (by rw [hr])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨.inp hh ix s q :: pre, by simp [hpre], by simp [ioOf, Tok.isIo] at hio ⊢; exact hio, ?_⟩
    exact List.Forall₂.cons ⟨⟨hc.1, hc.2.1, hc.2.2.2, rfl, rfl, rfl⟩, rfl⟩ hf
  | k + 1, .blk .. :: _, _, _, h => by simp [insT] at h
  | k + 1, .txh .. :: _, _, _, h => by simp [insT] at h
  | k + 1, .nout .. :: _, _, _, h => by simp [insT] at h
  | k + 1, .out .. :: _, _, _, h => by simp [insT] at h
  | k + 1, .wcnt .. :: _, _, _, h => by simp [insT] at h
  | k + 1, .witem .. :: _, _, _, h => by simp [insT] at h
  | k + 1, .lock .. :: _, _, _, h => by simp [insT] at h
  | k + 1, [], _, _, h => by simp [insT] at h

theorem io_outsT : ∀ (k : ℕ) (ts : List Tok) (outs : List TxOut) (rest : List Tok),
    outsT k ts = some (outs, rest) →
    ∃ pre, ts = pre ++ rest ∧ ioOf pre = pre ∧ List.Forall₂ OutTok outs pre
  | 0, ts, outs, rest, h => by
    simp [outsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, List.Forall₂.nil⟩
  | k + 1, .out v s :: ts, outs, rest, h => by
    simp only [outsT] at h
    split_ifs at h with hc
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨pre, hpre, hio, hf⟩ := io_outsT k ts r.1 r.2 (by rw [hr])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    refine ⟨.out v s :: pre, by simp [hpre], by simp [ioOf, Tok.isIo] at hio ⊢; exact hio, ?_⟩
    exact List.Forall₂.cons ⟨hc.1, rfl, rfl⟩ hf
  | k + 1, .blk .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, .txh .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, .nout .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, .inp .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, .wcnt .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, .witem .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, .lock .. :: _, _, _, h => by simp [outsT] at h
  | k + 1, [], _, _, h => by simp [outsT] at h

theorem io_itemsT : ∀ (k : ℕ) (ts : List Tok) (w : List Bytes) (rest : List Tok),
    itemsT k ts = some (w, rest) → ∃ pre, ts = pre ++ rest ∧ ioOf pre = []
  | 0, ts, w, rest, h => by simp [itemsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl⟩
  | k + 1, .witem it :: ts, w, rest, h => by
    simp only [itemsT] at h
    split_ifs at h
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨pre, hpre, hio⟩ := io_itemsT k ts r.1 r.2 (by rw [hr])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨.witem it :: pre, by simp [hpre], by simp [ioOf, Tok.isIo] at hio ⊢; exact hio⟩
  | k + 1, .blk .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .txh .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .nout .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .inp .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .out .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .wcnt .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .lock .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, [], _, _, h => by simp [itemsT] at h

theorem io_witsT : ∀ (k : ℕ) (ts : List Tok) (ws : List (List Bytes)) (rest : List Tok),
    witsT k ts = some (ws, rest) → ∃ pre, ts = pre ++ rest ∧ ioOf pre = []
  | 0, ts, ws, rest, h => by simp [witsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl⟩
  | k + 1, .wcnt c :: ts, ws, rest, h => by
    simp only [witsT] at h
    split_ifs at h
    cases hi : itemsT c ts with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨w, ts'⟩ := p
      simp only [hi] at h
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨pre1, hpre1, hio1⟩ := io_itemsT c ts w ts' hi
      obtain ⟨pre2, hpre2, hio2⟩ := io_witsT k ts' r.1 r.2 (by rw [hr])
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨.wcnt c :: (pre1 ++ pre2), by simp [hpre1, hpre2], ?_⟩
      simp only [ioOf, List.filter_cons, Tok.isIo, Bool.false_eq_true, if_false, List.filter_append] at hio1 hio2 ⊢
      rw [hio1, hio2]; rfl
  | k + 1, .blk .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, .txh .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, .nout .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, .inp .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, .out .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, .witem .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, .lock .. :: _, _, _, h => by simp [witsT] at h
  | k + 1, [], _, _, h => by simp [witsT] at h

theorem inTok_witness (i : TxIn) (w : List Bytes) (tk : Tok) : InTok { i with witness := w } tk ↔ InTok i tk := by
  cases tk <;> simp [InTok]

/-- Attaching witnesses keeps the inputs' tokens. -/
theorem forall₂_attach : ∀ (ins : List TxIn) (ws : List (List Bytes)) (l : List Tok), ins.length = ws.length →
    List.Forall₂ (fun i tk => InTok i tk ∧ i.witness = []) ins l → List.Forall₂ InTok (attach ins ws) l
  | [], [], [], _, _ => List.Forall₂.nil
  | i :: ins, w :: ws, tk :: l, hl, h => by
    cases h with
    | cons h1 h2 =>
      show List.Forall₂ InTok ({ i with witness := w } :: attach ins ws) (tk :: l)
      exact List.Forall₂.cons ((inTok_witness i w tk).mpr h1.1) (forall₂_attach ins ws l (by simpa using hl) h2)
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | [], [], _ :: _, _, h => by cases h
  | _ :: _, _ :: _, [], _, h => by cases h

/-- **A transaction's input and output tokens** describe its inputs then its outputs. -/
theorem io_txT {ts : List Tok} {t : Tx} {rest : List Tok} (h : txT ts = some (t, rest)) :
    ∃ pre, ts = pre ++ rest ∧ IoTx t (ioOf pre) := by
  match ts, h with
  | .txh v seg nIn :: ts, h =>
    simp only [txT] at h
    by_cases hc : v.length = 4 ∧ 1 ≤ nIn ∧ nIn ≤ MAX_SIZE
    swap; · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    cases hins : insT nIn ts with
    | none => simp [hins] at h
    | some r =>
      obtain ⟨ins, ts1⟩ := r
      obtain ⟨p1, hp1, hio1, hf1⟩ := io_insT nIn ts ins ts1 hins
      have il := (insT_sound nIn ts ins ts1 hins).1
      rw [hins] at h
      match ts1, h, hp1 with
      | .nout k :: ts1, h, hp1 =>
        simp only at h
        by_cases hk : k ≤ MAX_SIZE
        swap; · rw [if_neg hk] at h; simp at h
        rw [if_pos hk] at h
        cases houts : outsT k ts1 with
        | none => simp [houts] at h
        | some r =>
          obtain ⟨outs, ts2⟩ := r
          obtain ⟨p2, hp2, hio2, hf2⟩ := io_outsT k ts1 outs ts2 houts
          rw [houts] at h
          simp only at h
          have hw : ∃ ws ts3 p3, (if seg then witsT nIn ts2 else some (List.replicate nIn [], ts2)) = some (ws, ts3) ∧
              ws.length = nIn ∧ ts2 = p3 ++ ts3 ∧ ioOf p3 = [] := by
            cases seg with
            | false => exact ⟨_, _, [], rfl, by simp, by simp, rfl⟩
            | true =>
              cases hws : witsT nIn ts2 with
              | none => simp [hws] at h
              | some r =>
                obtain ⟨p3, hp3, hio3⟩ := io_witsT nIn ts2 r.1 r.2 hws
                exact ⟨r.1, r.2, p3, by simp, (witsT_sound nIn ts2 r.1 r.2 hws).1, hp3, hio3⟩
          obtain ⟨ws, ts3, p3, hwe, wl, hp3, hio3⟩ := hw
          rw [hwe] at h
          match ts3, h, hp3 with
          | .lock l :: rest', h, hp3 =>
            simp only at h
            by_cases hl : l.length = 4 ∧ (seg = true → (ws.any fun w => !w.isEmpty) = true)
            swap; · rw [if_neg hl] at h; simp at h
            rw [if_pos hl] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            refine ⟨.txh v seg nIn :: (p1 ++ (.nout k :: (p2 ++ (p3 ++ [.lock l])))), ?_, ?_⟩
            · rw [hp1, hp2, hp3]; simp
            · refine ⟨p1, p2, ?_, forall₂_attach ins ws p1 (by rw [il, wl]) hf1, hf2⟩
              simp only [ioOf, List.filter_cons, Tok.isIo, Bool.false_eq_true, if_false, List.filter_append,
                List.filter_nil] at hio1 hio2 hio3 ⊢
              rw [hio1, hio2, hio3]; simp
          | [], h, _ => simp at h
          | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .nout .. :: _, h, _
          | .out .. :: _, h, _ | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ => simp at h
      | [], h, _ => simp at h
      | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .out .. :: _, h, _
      | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ | .lock .. :: _, h, _ => simp at h
  | [], h => simp [txT] at h
  | .blk .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [txT] at h

theorem io_txsT : ∀ (k : ℕ) (ts : List Tok) (txs : List Tx) (rest : List Tok),
    txsT k ts = some (txs, rest) →
    ∃ pre, ts = pre ++ rest ∧ ∃ parts : List (List Tok), ioOf pre = parts.flatten ∧ List.Forall₂ IoTx txs parts
  | 0, ts, txs, rest, h => by
    simp [txsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, [], by simp [ioOf], List.Forall₂.nil⟩
  | k + 1, ts, txs, rest, h => by
    simp only [txsT] at h
    cases ht : txT ts with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, ts'⟩ := p
      simp only [ht] at h
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨p1, hp1, hio1⟩ := io_txT ht
      obtain ⟨p2, hp2, parts, hio2, hf2⟩ := io_txsT k ts' r.1 r.2 (by rw [hr])
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨p1 ++ p2, by rw [hp1, hp2, List.append_assoc], ioOf p1 :: parts, ?_, List.Forall₂.cons hio1 hf2⟩
      simp only [ioOf, List.filter_append] at hio2 ⊢
      rw [hio2]; simp

/-- **A block's input and output tokens** are, transaction by transaction, its inputs then outputs. -/
theorem io_toksBlock {ts : List Tok} {b : Blk} (h : toksBlock ts = some b) :
    ∃ parts : List (List Tok), ioOf ts = parts.flatten ∧ List.Forall₂ IoTx b.txs parts := by
  match ts, h with
  | .blk hd n :: ts, h =>
    simp only [toksBlock] at h
    split_ifs at h
    cases hx : txsT n ts with
    | none => simp [hx] at h
    | some p =>
      obtain ⟨txs, rest⟩ := p
      rw [hx] at h
      match rest, h with
      | [], h =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨pre, hpre, parts, hio, hf⟩ := io_txsT n ts txs [] hx
        refine ⟨parts, ?_, hf⟩
        simp only [List.append_nil] at hpre
        subst hpre
        simp [ioOf, Tok.isIo] at hio ⊢; exact hio
      | _ :: _, h => simp at h
  | [], h => simp [toksBlock] at h
  | .txh .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [toksBlock] at h

end StarkedAir.Spec.Block
