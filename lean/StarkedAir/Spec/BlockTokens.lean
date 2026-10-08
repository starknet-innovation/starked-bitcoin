/-
**Block tokens (M3a.2 `BLK-FIELDS`, grammar layer).** The fields AIR checks a block's bytes as a
sequence of tokens (one per row). `toksBlock` accepts a token list when it follows the
serialization grammar; `toksBlock_sound`: then the tokens' bytes are `serBlock b` of a well-formed
block `b` (so `parseBlock` reads `b` back, by `parseBlock_serBlock`).
-/
import StarkedAir.Spec.BlockSer

namespace StarkedAir.Spec.Block

/-- One token: a field group the AIR checks in one row. Fixed-size fields are kept as bytes. -/
inductive Tok where
  /-- Header (80 bytes) and the transaction count. -/
  | blk (header : Bytes) (nTx : ℕ)
  /-- Version (4 bytes), the segwit marker and flag if `seg`, the input count. -/
  | txh (version : Bytes) (seg : Bool) (nIn : ℕ)
  /-- Prevout hash (32), index (4), scriptSig, sequence (4). -/
  | inp (hash idx : Bytes) (script : Bytes) (seq : Bytes)
  | nout (k : ℕ)
  /-- Value (8 bytes) and scriptPubKey. -/
  | out (value : Bytes) (script : Bytes)
  | wcnt (k : ℕ)
  | witem (item : Bytes)
  | lock (lockTime : Bytes)

def Tok.bytes : Tok → Bytes
  | .blk h n => h ++ serCompact n
  | .txh v seg n => v ++ (if seg then [0, 1] else []) ++ serCompact n
  | .inp h i s q => h ++ i ++ serVarBytes s ++ q
  | .nout k => serCompact k
  | .out v s => v ++ serVarBytes s
  | .wcnt k => serCompact k
  | .witem it => serVarBytes it
  | .lock l => l

def toksBytes (ts : List Tok) : Bytes := ts.flatMap Tok.bytes

/-- The signed value of 8 little-endian bytes. -/
def signed64 (n : ℕ) : ℤ := if n < 2 ^ 63 then (n : ℤ) else (n : ℤ) - 2 ^ 64

/-! ### The token grammar -/

def insT : ℕ → List Tok → Option (List TxIn × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, .inp h i s q :: ts =>
    if h.length = 32 ∧ i.length = 4 ∧ s.length ≤ MAX_SIZE ∧ q.length = 4 then
      (insT k ts).map fun r => (⟨⟨h, le i⟩, s, le q, []⟩ :: r.1, r.2)
    else none
  | _, _ => none

def outsT : ℕ → List Tok → Option (List TxOut × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, .out v s :: ts =>
    if v.length = 8 ∧ s.length ≤ MAX_SIZE then
      (outsT k ts).map fun r => (⟨signed64 (le v), s⟩ :: r.1, r.2)
    else none
  | _, _ => none

def itemsT : ℕ → List Tok → Option (List Bytes × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, .witem it :: ts =>
    if it.length ≤ MAX_SIZE then (itemsT k ts).map fun r => (it :: r.1, r.2) else none
  | _, _ => none

def witsT : ℕ → List Tok → Option (List (List Bytes) × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, .wcnt c :: ts =>
    if c ≤ MAX_SIZE then
      match itemsT c ts with
      | some (w, ts') => (witsT k ts').map fun r => (w :: r.1, r.2)
      | none => none
    else none
  | _, _ => none

/-- One transaction's tokens. -/
def txT : List Tok → Option (Tx × List Tok)
  | .txh v seg nIn :: ts =>
    if v.length = 4 ∧ 1 ≤ nIn ∧ nIn ≤ MAX_SIZE then
      match insT nIn ts with
      | some (ins, .nout k :: ts1) =>
        if k ≤ MAX_SIZE then
          match outsT k ts1 with
          | some (outs, ts2) =>
            match (if seg then witsT nIn ts2 else some (List.replicate nIn [], ts2)) with
            | some (ws, .lock l :: ts3) =>
              if l.length = 4 ∧ (seg → ws.any (fun w => !w.isEmpty)) then
                some (⟨le v, (ins.zip ws).map (fun p => { p.1 with witness := p.2 }), outs, le l⟩, ts3)
              else none
            | _ => none
          | none => none
        else none
      | _ => none
    else none
  | _ => none

def txsT : ℕ → List Tok → Option (List Tx × List Tok)
  | 0, ts => some ([], ts)
  | k + 1, ts =>
    match txT ts with
    | some (t, ts') => (txsT k ts').map fun r => (t :: r.1, r.2)
    | none => none

/-- **The block grammar**: the header token, then `nTx ≥ 1` transactions, nothing after. -/
def toksBlock : List Tok → Option Blk
  | .blk h n :: ts =>
    if h.length = 80 ∧ 1 ≤ n ∧ n ≤ MAX_SIZE then
      match txsT n ts with
      | some (txs, []) => some ⟨h, txs⟩
      | _ => none
    else none
  | _ => none

/-! ### Soundness -/

theorem le_lt : ∀ b : Bytes, le b < 256 ^ b.length
  | [] => by simp [le]
  | x :: xs => by
    have ih := le_lt xs
    have hx : x.toNat < 256 := x.toNat_lt
    show x.toNat + 256 * le xs < 256 ^ (xs.length + 1)
    rw [pow_succ]
    generalize 256 ^ xs.length = N at *
    omega

theorem leBytes_le : ∀ b : Bytes, leBytes b.length (le b) = b
  | [] => by simp [leBytes]
  | x :: xs => by
    rw [List.length_cons, leBytes_succ]
    have hx := x.toNat_lt
    have e1 : (x.toNat + 256 * le xs) / 256 = le xs := by omega
    have e2 : UInt8.ofNat (x.toNat + 256 * le xs) = x := by
      apply UInt8.toNat_inj.mp; simp
    show UInt8.ofNat (x.toNat + 256 * le xs) :: leBytes xs.length ((x.toNat + 256 * le xs) / 256) = x :: xs
    rw [e1, e2, leBytes_le xs]

theorem leBytes_le' {b : Bytes} {k : ℕ} (h : b.length = k) : leBytes k (le b) = b := by
  subst h; exact leBytes_le b

theorem signed64_bytes {v : Bytes} (hv : v.length = 8) : leBytes 8 (signed64 (le v) % 2 ^ 64).toNat = v := by
  have hlt : le v < 2 ^ 64 := by have := le_lt v; rw [hv] at this; simpa using this
  have : (signed64 (le v) % 2 ^ 64).toNat = le v := by
    unfold signed64
    split_ifs <;> omega
  rw [this, leBytes_le' hv]

theorem signed64_wf (n : ℕ) (h : n < 2 ^ 64) : -2 ^ 63 ≤ signed64 n ∧ signed64 n < 2 ^ 63 := by
  unfold signed64; split_ifs <;> omega

theorem insT_sound : ∀ (k : ℕ) (ts : List Tok) (ins : List TxIn) (rest : List Tok),
    insT k ts = some (ins, rest) →
    ins.length = k ∧ (∀ i ∈ ins, i.WF ∧ i.witness = []) ∧
      toksBytes ts = ins.flatMap serTxIn ++ toksBytes rest
  | 0, ts, ins, rest, h => by
    simp [insT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, [], _, _, h => by simp [insT] at h
  | k + 1, t :: ts, ins, rest, h => by
    cases t with
    | inp hh i s q =>
      simp only [insT] at h
      split_ifs at h with hc
      obtain ⟨h1, h2, h3, h4⟩ := hc
      cases hr : insT k ts with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨ins', rest'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, hwf, hb⟩ := insT_sound k ts ins' rest' hr
        have hi4 : le i < 2 ^ 32 := by have := le_lt i; rw [h2] at this; simpa using this
        have hq4 : le q < 2 ^ 32 := by have := le_lt q; rw [h4] at this; simpa using this
        refine ⟨by simp [hl], ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨⟨h1, hi4, h3, hq4, by simp, by simp⟩, rfl⟩
          · exact hwf x hx
        · simp only [toksBytes, List.flatMap_cons] at hb ⊢
          rw [hb]
          simp [Tok.bytes, serTxIn, leBytes_le' h2, leBytes_le' h4]
    | _ => simp [insT] at h

theorem outsT_sound : ∀ (k : ℕ) (ts : List Tok) (outs : List TxOut) (rest : List Tok),
    outsT k ts = some (outs, rest) →
    outs.length = k ∧ (∀ o ∈ outs, o.WF) ∧ toksBytes ts = outs.flatMap serTxOut ++ toksBytes rest
  | 0, ts, outs, rest, h => by
    simp [outsT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, [], _, _, h => by simp [outsT] at h
  | k + 1, t :: ts, outs, rest, h => by
    cases t with
    | out v sc =>
      simp only [outsT] at h
      split_ifs at h with hc
      obtain ⟨h1, h2⟩ := hc
      cases hr : outsT k ts with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨outs', rest'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, hwf, hb⟩ := outsT_sound k ts outs' rest' hr
        have h64 : le v < 2 ^ 64 := by have := le_lt v; rw [h1] at this; simpa using this
        refine ⟨by simp [hl], ?_, ?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨(signed64_wf _ h64).1, (signed64_wf _ h64).2, h2⟩
          · exact hwf x hx
        · simp only [toksBytes, List.flatMap_cons] at hb ⊢
          rw [hb]
          have e := signed64_bytes h1
          norm_num at e
          simp [Tok.bytes, serTxOut, e]
    | _ => simp [outsT] at h

theorem itemsT_sound : ∀ (k : ℕ) (ts : List Tok) (w : List Bytes) (rest : List Tok),
    itemsT k ts = some (w, rest) →
    w.length = k ∧ (∀ x ∈ w, x.length ≤ MAX_SIZE) ∧ toksBytes ts = w.flatMap serVarBytes ++ toksBytes rest
  | 0, ts, w, rest, h => by
    simp [itemsT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, [], _, _, h => by simp [itemsT] at h
  | k + 1, t :: ts, w, rest, h => by
    cases t with
    | witem it =>
      simp only [itemsT] at h
      split_ifs at h with hc
      cases hr : itemsT k ts with
      | none => simp [hr] at h
      | some r =>
        obtain ⟨w', rest'⟩ := r
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hl, hwf, hb⟩ := itemsT_sound k ts w' rest' hr
        refine ⟨by simp [hl], fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hc
          · exact hwf x hx
        · simp only [toksBytes, List.flatMap_cons] at hb ⊢
          rw [hb]; simp [Tok.bytes]
    | _ => simp [itemsT] at h

/-- A witness stack's serialization. -/
def serStack (w : List Bytes) : Bytes := serCompact w.length ++ w.flatMap serVarBytes

theorem witsT_sound : ∀ (k : ℕ) (ts : List Tok) (ws : List (List Bytes)) (rest : List Tok),
    witsT k ts = some (ws, rest) →
    ws.length = k ∧ (∀ w ∈ ws, w.length ≤ MAX_SIZE ∧ ∀ x ∈ w, x.length ≤ MAX_SIZE) ∧
      toksBytes ts = ws.flatMap serStack ++ toksBytes rest
  | 0, ts, ws, rest, h => by
    simp [witsT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, [], _, _, h => by simp [witsT] at h
  | k + 1, t :: ts, ws, rest, h => by
    cases t with
    | wcnt c =>
      simp only [witsT] at h
      split_ifs at h with hc
      cases hi : itemsT c ts with
      | none => simp [hi] at h
      | some r =>
        obtain ⟨w, ts'⟩ := r
        simp only [hi] at h
        cases hr : witsT k ts' with
        | none => simp [hr] at h
        | some r2 =>
          obtain ⟨ws', rest'⟩ := r2
          simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨il, iwf, ib⟩ := itemsT_sound c ts w ts' hi
          obtain ⟨hl, hwf, hb⟩ := witsT_sound k ts' ws' rest' hr
          refine ⟨by simp [hl], fun x hx => ?_, ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact ⟨il ▸ hc, iwf⟩
            · exact hwf x hx
          · simp only [toksBytes, List.flatMap_cons] at ib hb ⊢
            rw [ib, hb]; simp [Tok.bytes, serStack, il]
    | _ => simp [witsT] at h

/-! ### Transactions -/

def attach (ins : List TxIn) (ws : List (List Bytes)) : List TxIn :=
  (ins.zip ws).map fun p => { p.1 with witness := p.2 }

theorem attach_props : ∀ (ins : List TxIn) (ws : List (List Bytes)), ins.length = ws.length →
    (attach ins ws).length = ins.length ∧
    (attach ins ws).flatMap serTxIn = ins.flatMap serTxIn ∧
    (attach ins ws).flatMap (fun i => serCompact i.witness.length ++ i.witness.flatMap serVarBytes) = ws.flatMap serStack ∧
    (attach ins ws).any (fun i => !i.witness.isEmpty) = ws.any (fun w => !w.isEmpty) ∧
    ∀ x ∈ attach ins ws, ∃ i ∈ ins, ∃ w ∈ ws, x = { i with witness := w }
  | [], [], _ => by simp [attach]
  | i :: ins, w :: ws, h => by
    obtain ⟨a1, a2, a3, a4, a5⟩ := attach_props ins ws (by simpa using h)
    simp only [attach, List.zip_cons_cons, List.map_cons] at a1 a2 a3 a4 a5 ⊢
    refine ⟨by simp [a1], ?_, ?_, ?_, ?_⟩
    · simp only [List.flatMap_cons, a2]; rfl
    · simp only [List.flatMap_cons, a3]; rfl
    · simp only [List.any_cons, a4]
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨i, List.mem_cons_self, w, List.mem_cons_self, rfl⟩
      · obtain ⟨i', hi', w', hw', e⟩ := a5 x hx
        exact ⟨i', List.mem_cons_of_mem _ hi', w', List.mem_cons_of_mem _ hw', e⟩
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem txT_sound {ts : List Tok} {t : Tx} {rest : List Tok} (h : txT ts = some (t, rest)) :
    t.WF ∧ toksBytes ts = serWit t ++ toksBytes rest := by
  match ts, h with
  | .txh v seg nIn :: ts, h =>
    simp only [txT] at h
    by_cases hc : v.length = 4 ∧ 1 ≤ nIn ∧ nIn ≤ MAX_SIZE
    swap; · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    obtain ⟨hv, h1, hmax⟩ := hc
    cases hins : insT nIn ts with
    | none => simp [hins] at h
    | some r =>
      obtain ⟨ins, ts1⟩ := r
      obtain ⟨il, iwf, ib⟩ := insT_sound nIn ts ins ts1 hins
      rw [hins] at h
      match ts1, h, ib with
      | .nout k :: ts1, h, ib =>
        simp only at h
        by_cases hk : k ≤ MAX_SIZE
        swap; · rw [if_neg hk] at h; simp at h
        rw [if_pos hk] at h
        cases houts : outsT k ts1 with
        | none => simp [houts] at h
        | some r =>
          obtain ⟨outs, ts2⟩ := r
          obtain ⟨ol, owf, ob⟩ := outsT_sound k ts1 outs ts2 houts
          rw [houts] at h
          simp only at h
          -- The witness section.
          have hw : ∃ ws ts3, (if seg then witsT nIn ts2 else some (List.replicate nIn [], ts2)) = some (ws, ts3) ∧
              ws.length = nIn ∧ (∀ w ∈ ws, w.length ≤ MAX_SIZE ∧ ∀ x ∈ w, x.length ≤ MAX_SIZE) ∧
              toksBytes ts2 = (if seg then ws.flatMap serStack else []) ++ toksBytes ts3 ∧
              (seg = false → ws = List.replicate nIn []) := by
            cases seg with
            | false => exact ⟨_, _, rfl, by simp, by simp, by simp, fun _ => rfl⟩
            | true =>
              cases hws : witsT nIn ts2 with
              | none => simp [hws] at h
              | some r =>
                obtain ⟨wl, wwf, wb⟩ := witsT_sound nIn ts2 r.1 r.2 hws
                exact ⟨r.1, r.2, by simp, wl, wwf, by simpa using wb, by simp⟩
          obtain ⟨ws, ts3, hwe, wl, wwf, wb, wnil⟩ := hw
          rw [hwe] at h
          match ts3, h, wb with
          | .lock l :: rest', h, wb =>
            simp only at h
            by_cases hl : l.length = 4 ∧ (seg = true → (ws.any fun w => !w.isEmpty) = true)
            swap; · rw [if_neg hl] at h; simp at h
            rw [if_pos hl] at h
            obtain ⟨hl4, hany⟩ := hl
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨a1, a2, a3, a4, a5⟩ := attach_props ins ws (by rw [il, wl])
            have hv4 : le v < 2 ^ 32 := by have := le_lt v; rw [hv] at this; simpa using this
            have hl4' : le l < 2 ^ 32 := by have := le_lt l; rw [hl4] at this; simpa using this
            refine ⟨⟨hv4, hl4', ?_, ?_, by rw [ol]; exact hk, ?_, owf⟩, ?_⟩
            · show attach ins ws ≠ []
              intro e
              have := a1.trans il
              rw [e] at this; simp at this; omega
            · show (attach ins ws).length ≤ MAX_SIZE; rw [a1, il]; exact hmax
            · intro x hx
              obtain ⟨i, hi, w, hw, rfl⟩ := a5 x hx
              obtain ⟨⟨q1, q2, q3, q4, -, -⟩, -⟩ := iwf i hi
              exact ⟨q1, q2, q3, q4, (wwf w hw).1, (wwf w hw).2⟩
            · show toksBytes (Tok.txh v seg nIn :: ts) = serWit ⟨le v, attach ins ws, outs, le l⟩ ++ toksBytes rest'
              simp only [toksBytes, List.flatMap_cons] at ib ob wb ⊢
              -- Assemble the bytes.
              have hhas : (Tx.hasWitness ⟨le v, attach ins ws, outs, le l⟩) = seg := by
                unfold Tx.hasWitness
                show (attach ins ws).any _ = seg
                rw [a4]
                cases seg with
                | true => exact hany rfl
                | false => rw [wnil rfl]; simp
              unfold serWit
              rw [hhas]
              cases seg with
              | true =>
                simp only [if_true] at wb ⊢
                rw [ib, ob, wb]
                simp [Tok.bytes, serWit, leBytes_le' hv, leBytes_le' hl4, a1, a2, a3, il, ol, List.append_assoc]
              | false =>
                simp only [if_false, Bool.false_eq_true, List.nil_append] at wb ⊢
                rw [ib, ob, wb]
                simp [Tok.bytes, serNoWit, leBytes_le' hv, leBytes_le' hl4, a1, a2, il, ol, List.append_assoc]
          | [], h, _ => simp at h
          | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .nout .. :: _, h, _
          | .out .. :: _, h, _ | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ => simp at h
      | [], h, _ => simp at h
      | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .out .. :: _, h, _
      | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ | .lock .. :: _, h, _ => simp at h
  | [], h => simp [txT] at h
  | .blk .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [txT] at h

theorem txsT_sound : ∀ (k : ℕ) (ts : List Tok) (txs : List Tx) (rest : List Tok),
    txsT k ts = some (txs, rest) →
    txs.length = k ∧ (∀ t ∈ txs, t.WF) ∧ toksBytes ts = txs.flatMap serWit ++ toksBytes rest
  | 0, ts, txs, rest, h => by
    simp [txsT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, ts, txs, rest, h => by
    simp only [txsT] at h
    cases ht : txT ts with
    | none => simp [ht] at h
    | some r =>
      obtain ⟨t, ts'⟩ := r
      rw [ht] at h
      cases hr : txsT k ts' with
      | none => simp [hr] at h
      | some r2 =>
        obtain ⟨txs', rest'⟩ := r2
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨twf, tb⟩ := txT_sound ht
        obtain ⟨hl, hwf, hb⟩ := txsT_sound k ts' txs' rest' hr
        refine ⟨by simp [hl], fun x hx => ?_, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact twf
          · exact hwf x hx
        · rw [tb, hb]; simp [List.append_assoc]

/-- **Grammar soundness.** Accepted tokens are the serialization of a well-formed block. -/
theorem toksBlock_sound {ts : List Tok} {b : Blk} (h : toksBlock ts = some b) :
    b.WF ∧ serBlock b = toksBytes ts := by
  match ts, h with
  | .blk hd n :: ts, h =>
    simp only [toksBlock] at h
    by_cases hc : hd.length = 80 ∧ 1 ≤ n ∧ n ≤ MAX_SIZE
    swap; · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    obtain ⟨h80, -, hmax⟩ := hc
    cases hr : txsT n ts with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨txs, rest⟩ := r
      rw [hr] at h
      match rest, h with
      | [], h =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hl, hwf, hb⟩ := txsT_sound n ts txs [] hr
        refine ⟨⟨h80, by rw [hl]; exact hmax, hwf⟩, ?_⟩
        simp only [serBlock, toksBytes, List.flatMap_cons, Tok.bytes, hl] at hb ⊢
        rw [hb]; simp [toksBytes, List.append_assoc]
      | _ :: _, h => simp at h
  | [], h => simp [toksBlock] at h
  | .txh .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [toksBlock] at h

/-- Hence Core's deserializer reads the tokens' bytes as that block. -/
theorem toksBlock_parse {ts : List Tok} {b : Blk} (h : toksBlock ts = some b) :
    parseBlock (toksBytes ts) = some b := by
  obtain ⟨wf, e⟩ := toksBlock_sound h
  rw [← e]; exact parseBlock_serBlock b wf

end StarkedAir.Spec.Block
