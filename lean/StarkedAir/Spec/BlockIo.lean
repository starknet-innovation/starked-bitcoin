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

def Tok.isLock : Tok → Bool
  | .lock .. => true
  | _ => false

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
    itemsT k ts = some (w, rest) → ∃ pre, ts = pre ++ rest ∧ ioOf pre = [] ∧ pre.filter Tok.isLock = []
  | 0, ts, w, rest, h => by simp [itemsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, rfl⟩
  | k + 1, .witem it :: ts, w, rest, h => by
    simp only [itemsT] at h
    split_ifs at h
    obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨pre, hpre, hio, hlk⟩ := io_itemsT k ts r.1 r.2 (by rw [hr])
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨.witem it :: pre, by simp [hpre], by simp [ioOf, Tok.isIo] at hio ⊢; exact hio,
      by simp [List.filter_cons, Tok.isLock, hlk]⟩
  | k + 1, .blk .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .txh .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .nout .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .inp .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .out .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .wcnt .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, .lock .. :: _, _, _, h => by simp [itemsT] at h
  | k + 1, [], _, _, h => by simp [itemsT] at h

theorem io_witsT : ∀ (k : ℕ) (ts : List Tok) (ws : List (List Bytes)) (rest : List Tok),
    witsT k ts = some (ws, rest) → ∃ pre, ts = pre ++ rest ∧ ioOf pre = [] ∧ pre.filter Tok.isLock = []
  | 0, ts, ws, rest, h => by simp [witsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, rfl⟩
  | k + 1, .wcnt c :: ts, ws, rest, h => by
    simp only [witsT] at h
    split_ifs at h
    cases hi : itemsT c ts with
    | none => simp [hi] at h
    | some p =>
      obtain ⟨w, ts'⟩ := p
      simp only [hi] at h
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨pre1, hpre1, hio1, hlk1⟩ := io_itemsT c ts w ts' hi
      obtain ⟨pre2, hpre2, hio2, hlk2⟩ := io_witsT k ts' r.1 r.2 (by rw [hr])
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨.wcnt c :: (pre1 ++ pre2), by simp [hpre1, hpre2], ?_, by simp [List.filter_cons, Tok.isLock, hlk1, hlk2]⟩
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

/-! ### Transaction indices -/

/-- Input and output tokens tagged with the number of lock-time tokens before them (from `c`). -/
def tagged : ℕ → List Tok → List (ℕ × Tok)
  | _, [] => []
  | c, tk :: ts => (if tk.isIo then [(c, tk)] else []) ++ tagged (if tk.isLock then c + 1 else c) ts

theorem tagged_append (c : ℕ) : ∀ (a b : List Tok),
    tagged c (a ++ b) = tagged c a ++ tagged (c + (a.filter Tok.isLock).length) b
  | [], b => by simp [tagged]
  | tk :: a, b => by
    by_cases hl : tk.isLock = true
    · simp only [List.cons_append, tagged, List.filter_cons, hl, if_true, List.length_cons]
      rw [tagged_append _ a b, List.append_assoc]
      congr 3; omega
    · simp only [List.cons_append, tagged, List.filter_cons, hl, Bool.false_eq_true, if_false]
      rw [tagged_append _ a b, List.append_assoc]

/-- Lock-free and io-free token lists. -/
theorem tagged_noio : ∀ (c : ℕ) (l : List Tok), ioOf l = [] → tagged c l = []
  | _, [], _ => rfl
  | c, tk :: l, h => by
    have h1 : tk.isIo = false := by
      by_contra hc; simp only [ioOf, List.filter_cons, Bool.not_eq_false] at h hc; simp [hc] at h
    have h2 : ioOf l = [] := by
      simp only [ioOf, List.filter_cons, h1, Bool.false_eq_true, if_false] at h; exact h
    simp only [tagged, h1, Bool.false_eq_true, if_false, List.nil_append]
    exact tagged_noio _ l h2

theorem tagged_io : ∀ (c : ℕ) (l : List Tok), ioOf l = l → tagged c l = l.map (c, ·)
  | _, [], _ => rfl
  | c, tk :: l, h => by
    have h1 : tk.isIo = true := by
      by_contra hc; simp only [ioOf, List.filter_cons] at h; simp [hc] at h
      have := List.length_filter_le Tok.isIo l; rw [h] at this; simp at this
    have h2 : ioOf l = l := by
      simp only [ioOf, List.filter_cons, h1, if_true, List.cons.injEq, true_and] at h; exact h
    have h3 : tk.isLock = false := by cases tk <;> simp_all [Tok.isIo, Tok.isLock]
    simp only [tagged, h1, h3, if_true, Bool.false_eq_true, if_false, List.map_cons, List.singleton_append]
    rw [tagged_io c l h2]

theorem lock_free_io : ∀ (l : List Tok), ioOf l = l → (l.filter Tok.isLock).length = 0
  | [], _ => rfl
  | tk :: l, h => by
    have h1 : tk.isIo = true := by
      by_contra hc; simp only [ioOf, List.filter_cons] at h; simp [hc] at h
      have := List.length_filter_le Tok.isIo l; rw [h] at this; simp at this
    have h2 : ioOf l = l := by
      simp only [ioOf, List.filter_cons, h1, if_true, List.cons.injEq, true_and] at h; exact h
    have h3 : tk.isLock = false := by cases tk <;> simp_all [Tok.isIo, Tok.isLock]
    simp [List.filter_cons, h3, lock_free_io l h2]

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
    ∃ pre, ts = pre ++ rest ∧ IoTx t (ioOf pre) ∧ (pre.filter Tok.isLock).length = 1 ∧
      ∀ c, tagged c pre = (ioOf pre).map (c, ·) := by
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
              ws.length = nIn ∧ ts2 = p3 ++ ts3 ∧ ioOf p3 = [] ∧ p3.filter Tok.isLock = [] := by
            cases seg with
            | false => exact ⟨_, _, [], rfl, by simp, by simp, rfl, rfl⟩
            | true =>
              cases hws : witsT nIn ts2 with
              | none => simp [hws] at h
              | some r =>
                obtain ⟨p3, hp3, hio3, hlk3⟩ := io_witsT nIn ts2 r.1 r.2 hws
                exact ⟨r.1, r.2, p3, by simp, (witsT_sound nIn ts2 r.1 r.2 hws).1, hp3, hio3, hlk3⟩
          obtain ⟨ws, ts3, p3, hwe, wl, hp3, hio3, hlk3⟩ := hw
          rw [hwe] at h
          match ts3, h, hp3 with
          | .lock l :: rest', h, hp3 =>
            simp only at h
            by_cases hl : l.length = 4 ∧ (seg = true → (ws.any fun w => !w.isEmpty) = true)
            swap; · rw [if_neg hl] at h; simp at h
            rw [if_pos hl] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hio : ioOf (.txh v seg nIn :: (p1 ++ (.nout k :: (p2 ++ (p3 ++ [.lock l]))))) = p1 ++ p2 := by
              have e1 := hio1; have e2 := hio2; have e3 := hio3
              simp only [ioOf, List.filter_cons, Tok.isIo, Bool.false_eq_true, if_false, List.filter_append,
                List.filter_nil] at e1 e2 e3 ⊢
              rw [e1, e2, e3]; simp
            have l1 := lock_free_io p1 hio1
            have l2 := lock_free_io p2 hio2
            refine ⟨.txh v seg nIn :: (p1 ++ (.nout k :: (p2 ++ (p3 ++ [.lock l])))), ?_, ?_, ?_, fun c => ?_⟩
            · rw [hp1, hp2, hp3]; simp
            · rw [hio]
              exact ⟨p1, p2, rfl, forall₂_attach ins ws p1 (by rw [il, wl]) hf1, hf2⟩
            · simp only [List.filter_cons, Tok.isLock, Bool.false_eq_true, if_false, List.filter_append, hlk3]
              rw [List.length_eq_zero_iff.mp l1, List.length_eq_zero_iff.mp l2]; simp
            · rw [hio]
              simp only [tagged, Tok.isIo, Tok.isLock, Bool.false_eq_true, if_false, List.nil_append]
              rw [tagged_append, tagged_io c p1 hio1, l1, Nat.add_zero]
              simp only [tagged, Tok.isIo, Tok.isLock, Bool.false_eq_true, if_false, List.nil_append]
              rw [tagged_append, tagged_io c p2 hio2, l2, Nat.add_zero, tagged_append, tagged_noio c p3 hio3, hlk3]
              simp [tagged, Tok.isIo, Tok.isLock]
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
      obtain ⟨p1, hp1, hio1, -, -⟩ := io_txT ht
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

/-- Parts tagged by their index from `c`. -/
def tagParts (c : ℕ) : List (List Tok) → List (ℕ × Tok)
  | [] => []
  | p :: ps => p.map (c, ·) ++ tagParts (c + 1) ps

theorem io_txsT_tag : ∀ (k : ℕ) (ts : List Tok) (txs : List Tx) (rest : List Tok),
    txsT k ts = some (txs, rest) →
    ∃ pre parts, ts = pre ++ rest ∧ List.Forall₂ IoTx txs parts ∧ (pre.filter Tok.isLock).length = k ∧
      ∀ c, tagged c pre = tagParts c parts
  | 0, ts, txs, rest, h => by
    simp [txsT] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], [], by simp, List.Forall₂.nil, rfl, fun c => rfl⟩
  | k + 1, ts, txs, rest, h => by
    simp only [txsT] at h
    cases ht : txT ts with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, ts'⟩ := p
      simp only [ht] at h
      obtain ⟨r, hr, he⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨p1, hp1, hio1, hl1, htg1⟩ := io_txT ht
      obtain ⟨p2, parts, hp2, hf2, hl2, htg2⟩ := io_txsT_tag k ts' r.1 r.2 (by rw [hr])
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      refine ⟨p1 ++ p2, ioOf p1 :: parts, by rw [hp1, hp2, List.append_assoc], List.Forall₂.cons hio1 hf2, ?_, fun c => ?_⟩
      · rw [List.filter_append, List.length_append, hl1, hl2]; omega
      · rw [tagged_append, htg1, hl1, htg2]; rfl

/-- **A block's tagged input and output tokens**: transaction `i`'s inputs then outputs, tagged `i`. -/
theorem io_toksBlock_tag {ts : List Tok} {b : Blk} (h : toksBlock ts = some b) :
    ∃ parts : List (List Tok), List.Forall₂ IoTx b.txs parts ∧ tagged 0 ts = tagParts 0 parts := by
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
        obtain ⟨pre, parts, hpre, hf, -, htg⟩ := io_txsT_tag n ts txs [] hx
        refine ⟨parts, hf, ?_⟩
        simp only [List.append_nil] at hpre
        subst hpre
        simp only [tagged, Tok.isIo, Tok.isLock, Bool.false_eq_true, if_false, List.nil_append]
        exact htg 0
      | _ :: _, h => simp at h
  | [], h => simp [toksBlock] at h
  | .txh .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [toksBlock] at h

/-- Tagging a mapped range: each io element, tagged with the lock count before it. -/
theorem tagged_range (f : ℕ → Tok) (c : ℕ) : ∀ m, tagged c ((List.range m).map f) =
    ((List.range m).filter fun r => (f r).isIo).map fun r => (c + (((List.range r).map f).filter Tok.isLock).length, f r)
  | 0 => by simp [tagged]
  | m + 1 => by
    rw [List.range_succ, List.map_append, tagged_append, tagged_range f c m, List.filter_append, List.map_append]
    congr 1
    simp only [List.map_singleton, tagged, List.filter_cons, List.filter_nil, List.nil_append, List.append_nil]
    split_ifs <;> simp

end StarkedAir.Spec.Block
