/-
**Sums over a block's tokens (M3a.5).** The legacy sigops of a block's scripts and the size of its witness
data, read token by token: each input and output token contributes its script's sigops; each segwit
transaction head contributes its marker and flag (2 bytes), each witness token its bytes.
-/
import StarkedAir.Spec.TxFields

namespace StarkedAir.Spec.Block

/-- A token's legacy sigops (its script's). -/
def tokSig : Tok → ℕ
  | .inp _ _ s _ => sigOps s
  | .out _ s => sigOps s
  | _ => 0

def sumSig (ts : List Tok) : ℕ := (ts.map tokSig).sum

theorem sumSig_append (a b : List Tok) : sumSig (a ++ b) = sumSig a + sumSig b := by simp [sumSig]

theorem sumSig_cons (x : Tok) (a : List Tok) : sumSig (x :: a) = tokSig x + sumSig a := by simp [sumSig]

theorem sumSig_wit {l : List Tok} (h : ∀ x ∈ l, x.isWit) : sumSig l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [sumSig_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have := h x (List.mem_cons_self ..)
    cases x <;> simp_all [Tok.isWit, tokSig]

theorem sum_map_ext {α β : Type} (l1 : List α) (l2 : List β) (f : α → ℕ) (g : β → ℕ) (hl : l1.length = l2.length)
    (h : ∀ i (h1 : i < l1.length) (h2 : i < l2.length), f l1[i] = g l2[i]) : (l1.map f).sum = (l2.map g).sum := by
  congr 1
  apply List.ext_getElem (by simp [hl])
  intro i h1 h2
  simp only [List.getElem_map]
  exact h i (by simpa using h1) (by simpa using h2)

/-- **A transaction's tokens carry its legacy sigops.** -/
theorem txT_sig {v : Bytes} {seg : Bool} {nIn : ℕ} {ts : List Tok} {t : Tx} {rest : List Tok}
    (h : txT (.txh v seg nIn :: ts) = some (t, rest)) : sumSig ts = legacySigOps t + sumSig rest := by
  obtain ⟨pin, k, pout, pw, l, hsplit, hpl, hpo, hvl, hol, -, -, -, hwit, hins, houts, -, -⟩ := txT_vals h
  rw [hsplit, sumSig_append, sumSig_cons, sumSig_append, sumSig_append, sumSig_cons, sumSig_wit hwit]
  have hi : sumSig pin = (t.vin.map fun i => sigOps i.scriptSig).sum :=
    sum_map_ext pin t.vin tokSig (fun i => sigOps i.scriptSig) (by rw [hpl, hvl]) (fun i h1 h2 => by
      obtain ⟨hh, n, s, q, e1, ⟨w, e2⟩, -⟩ := hins i (by omega)
      rw [List.getElem?_eq_getElem h1] at e1; rw [List.getElem?_eq_getElem h2] at e2
      rw [Option.some.inj e1, Option.some.inj e2]; rfl)
  have ho : sumSig pout = (t.vout.map fun o => sigOps o.scriptPubKey).sum :=
    sum_map_ext pout t.vout tokSig (fun o => sigOps o.scriptPubKey) (by rw [hpo, hol]) (fun i h1 h2 => by
      obtain ⟨val, s, e1, e2, -⟩ := houts i (by omega)
      rw [List.getElem?_eq_getElem h1] at e1; rw [List.getElem?_eq_getElem h2] at e2
      rw [Option.some.inj e1, Option.some.inj e2]; rfl)
  rw [hi, ho]
  simp [tokSig, legacySigOps]; ring

theorem txsT_sig : ∀ (k : ℕ) (ts : List Tok) (txs : List Tx) (rest : List Tok),
    txsT k ts = some (txs, rest) → sumSig ts = (txs.map legacySigOps).sum + sumSig rest
  | 0, ts, txs, rest, h => by simp [txsT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, ts, txs, rest, h => by
    simp only [txsT] at h
    cases ht : txT ts with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, ts'⟩ := p
      rw [ht] at h
      cases hr : txsT k ts' with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨txs', rest'⟩ := q
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        match ts, ht with
        | .txh v seg nIn :: ts0, ht =>
          rw [sumSig_cons, txT_sig ht, txsT_sig k ts' txs' rest' hr]
          simp [tokSig]; ring
        | [], ht => simp [txT] at ht
        | .blk .. :: _, ht | .inp .. :: _, ht | .nout .. :: _, ht | .out .. :: _, ht | .wcnt .. :: _, ht
        | .witem .. :: _, ht | .lock .. :: _, ht => simp [txT] at ht

/-- **A block's tokens carry its legacy sigops.** -/
theorem toksBlock_sig {ts : List Tok} {b : Blk} (h : toksBlock ts = some b) :
    sumSig ts = (b.txs.map legacySigOps).sum := by
  match ts, h with
  | .blk hd n :: ts, h =>
    simp only [toksBlock] at h
    by_cases hc : hd.length = 80 ∧ 1 ≤ n ∧ n ≤ MAX_SIZE
    swap; · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    cases hr : txsT n ts with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨txs, rest⟩ := r
      rw [hr] at h
      match rest, h with
      | [], h =>
        simp only [Option.some.injEq] at h
        subst h
        rw [sumSig_cons, txsT_sig n ts txs [] hr]; simp [tokSig, sumSig]
      | _ :: _, h => simp at h
  | [], h => simp [toksBlock] at h
  | .txh .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [toksBlock] at h

/-! ### Witness bytes -/

/-- A token's witness bytes: the marker and flag of a segwit head, each witness token's bytes. -/
def tokW : Tok → ℕ
  | .txh _ seg _ => if seg then 2 else 0
  | .wcnt k => (serCompact k).length
  | .witem it => (serVarBytes it).length
  | _ => 0

def sumW (ts : List Tok) : ℕ := (ts.map tokW).sum

theorem sumW_append (a b : List Tok) : sumW (a ++ b) = sumW a + sumW b := by simp [sumW]

theorem sumW_cons (x : Tok) (a : List Tok) : sumW (x :: a) = tokW x + sumW a := by simp [sumW]

theorem sumW_zero {l : List Tok} (h : ∀ x ∈ l, x.isInp ∨ x.isOut) : sumW l = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [sumW_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have := h x (List.mem_cons_self ..)
    cases x <;> simp_all [Tok.isInp, Tok.isOut, tokW]

theorem sumW_wit {l : List Tok} (h : ∀ x ∈ l, x.isWit) : sumW l = (toksBytes l).length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [sumW_cons, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    have := h x (List.mem_cons_self ..)
    cases x <;> simp_all [Tok.isWit, tokW, toksBytes, Tok.bytes]

/-- **A transaction's witness bytes.** Its tokens' witness bytes are the length difference of its two
serializations. -/
theorem txT_w {v : Bytes} {seg : Bool} {nIn : ℕ} {ts : List Tok} {t : Tx} {rest : List Tok}
    (h : txT (.txh v seg nIn :: ts) = some (t, rest)) :
    (serNoWit t).length ≤ (serWit t).length ∧
    tokW (.txh v seg nIn) + sumW ts = ((serWit t).length - (serNoWit t).length) + sumW rest := by
  obtain ⟨pin, k, pout, pw, l, hsplit, hinp, hout, hwit, -, -, -, hnw⟩ := txT_split h
  obtain ⟨-, hb⟩ := txT_sound h
  have hall : toksBytes (.txh v seg nIn :: ts) = v ++ (if seg then [0, 1] else []) ++ serCompact nIn ++ toksBytes pin ++
      serCompact k ++ toksBytes pout ++ toksBytes pw ++ l ++ toksBytes rest := by
    rw [hsplit]; simp [toksBytes, Tok.bytes, List.append_assoc]
  rw [hb] at hall
  have lw := congrArg List.length hall
  have ln := congrArg List.length hnw
  simp only [List.length_append] at lw ln
  have hseg : (if seg then [(0 : UInt8), 1] else []).length = if seg then 2 else 0 := by split_ifs <;> rfl
  rw [hseg] at lw
  refine ⟨by omega, ?_⟩
  rw [hsplit, sumW_append, sumW_cons, sumW_append, sumW_append, sumW_cons,
    sumW_zero (fun x hx => Or.inl (hinp x hx)), sumW_zero (fun x hx => Or.inr (hout x hx)), sumW_wit hwit]
  simp only [tokW]
  omega

theorem txsT_w : ∀ (k : ℕ) (ts : List Tok) (txs : List Tx) (rest : List Tok),
    txsT k ts = some (txs, rest) → (∀ t ∈ txs, (serNoWit t).length ≤ (serWit t).length) ∧
      sumW ts = (txs.map fun t => (serWit t).length - (serNoWit t).length).sum + sumW rest
  | 0, ts, txs, rest, h => by simp [txsT] at h; obtain ⟨rfl, rfl⟩ := h; simp
  | k + 1, ts, txs, rest, h => by
    simp only [txsT] at h
    cases ht : txT ts with
    | none => simp [ht] at h
    | some p =>
      obtain ⟨t, ts'⟩ := p
      rw [ht] at h
      cases hr : txsT k ts' with
      | none => simp [hr] at h
      | some q =>
        obtain ⟨txs', rest'⟩ := q
        simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨ihl, ihs⟩ := txsT_w k ts' txs' rest' hr
        match ts, ht with
        | .txh v seg nIn :: ts0, ht =>
          obtain ⟨hle, hw⟩ := txT_w ht
          refine ⟨fun x hx => ?_, ?_⟩
          · rcases List.mem_cons.mp hx with rfl | hx
            · exact hle
            · exact ihl x hx
          · rw [sumW_cons, hw, ihs]; simp; ring
        | [], ht => simp [txT] at ht
        | .blk .. :: _, ht | .inp .. :: _, ht | .nout .. :: _, ht | .out .. :: _, ht | .wcnt .. :: _, ht
        | .witem .. :: _, ht | .lock .. :: _, ht => simp [txT] at ht

/-- **A block's weight** is `4 · len − 3 · W`, with `W` its tokens' witness bytes. -/
theorem toksBlock_weight {ts : List Tok} {b : Blk} (h : toksBlock ts = some b) :
    sumW ts ≤ (toksBytes ts).length ∧ weight b = 4 * (toksBytes ts).length - 3 * sumW ts := by
  obtain ⟨-, hser⟩ := toksBlock_sound h
  match ts, h with
  | .blk hd n :: ts, h =>
    simp only [toksBlock] at h
    by_cases hc : hd.length = 80 ∧ 1 ≤ n ∧ n ≤ MAX_SIZE
    swap; · rw [if_neg hc] at h; simp at h
    rw [if_pos hc] at h
    cases hr : txsT n ts with
    | none => simp [hr] at h
    | some r =>
      obtain ⟨txs, rest⟩ := r
      rw [hr] at h
      match rest, h with
      | [], h =>
        simp only [Option.some.injEq] at h
        subst h
        obtain ⟨hle, hw⟩ := txsT_w n ts txs [] hr
        obtain ⟨hl, -, -⟩ := txsT_sound n ts txs [] hr
        rw [sumW_cons, hw]
        simp only [tokW, sumW, List.map_nil, List.sum_nil, add_zero, zero_add]
        rw [← hser]
        simp only [weight, strippedSize, totalSize, serBlock, List.length_append, List.length_flatMap, hc.1, hl]
        have key : ∀ l : List Tx, (∀ t ∈ l, (serNoWit t).length ≤ (serWit t).length) →
            (l.map fun t => (serNoWit t).length).sum + (l.map fun t => (serWit t).length - (serNoWit t).length).sum =
              (l.map fun t => (serWit t).length).sum := by
          intro l hl'
          induction l with
          | nil => simp
          | cons a l ih =>
            simp only [List.map_cons, List.sum_cons]
            have := hl' a (List.mem_cons_self ..)
            have := ih (fun t ht => hl' t (List.mem_cons_of_mem _ ht))
            omega
        have := key txs hle
        refine ⟨by omega, ?_⟩
        omega
      | _ :: _, h => simp at h
  | [], h => simp [toksBlock] at h
  | .txh .. :: _, h | .inp .. :: _, h | .nout .. :: _, h | .out .. :: _, h | .wcnt .. :: _, h
  | .witem .. :: _, h | .lock .. :: _, h => simp [toksBlock] at h

end StarkedAir.Spec.Block
