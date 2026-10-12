/-
**A transaction's fields in its tokens (M3a.5).** Where each input's prevout, scriptSig and sequence, each
output's value and script, the lock time and the witness flag of a parsed transaction come from: input
`i` is the `i`-th input token, output `o` the `o`-th output token. The M3a.5 checks read these tokens' bytes.
-/
import BitcoinConsensus.TxSplit

namespace BitcoinConsensus.Block

/-- Input `i` of the parse is input token `i`. -/
theorem insT_vals : ∀ (k : ℕ) (ts : List Tok) (ins : List TxIn) (rest : List Tok),
    insT k ts = some (ins, rest) → ∃ pre, ts = pre ++ rest ∧ pre.length = k ∧ ins.length = k ∧
      ∀ i < k, ∃ h n s q, pre[i]? = some (.inp h n s q) ∧ ins[i]? = some ⟨⟨h, le n⟩, s, le q, []⟩ ∧
        h.length = 32 ∧ n.length = 4 ∧ q.length = 4
  | 0, ts, ins, rest, h => by
    simp [insT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, rfl, fun i hi => absurd hi (by omega)⟩
  | k + 1, [], _, _, h => by simp [insT] at h
  | k + 1, t :: ts, ins, rest, h => by
    cases t with
    | inp hh i s q =>
      simp only [insT] at h
      by_cases hc : hh.length = 32 ∧ i.length = 4 ∧ s.length ≤ MAX_SIZE ∧ q.length = 4
      swap; · rw [if_neg hc] at h; simp at h
      rw [if_pos hc] at h
      cases hk : insT k ts with
      | none => simp [hk] at h
      | some r =>
        rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, hp, hl, hil, hv⟩ := insT_vals k ts r.1 r.2 (by rw [hk])
        refine ⟨.inp hh i s q :: pre, by simp [hp], by simp [hl], by simp [hil], fun j hj => ?_⟩
        rcases j with _ | j
        · exact ⟨hh, i, s, q, rfl, rfl, hc.1, hc.2.1, hc.2.2.2⟩
        · obtain ⟨a, b, c, d, e1, e2, l1, l2, l3⟩ := hv j (by omega)
          exact ⟨a, b, c, d, by simpa using e1, by simpa using e2, l1, l2, l3⟩
    | _ => simp [insT] at h

/-- Output `o` of the parse is output token `o`. -/
theorem outsT_vals : ∀ (k : ℕ) (ts : List Tok) (outs : List TxOut) (rest : List Tok),
    outsT k ts = some (outs, rest) → ∃ pre, ts = pre ++ rest ∧ pre.length = k ∧ outs.length = k ∧
      ∀ o < k, ∃ v s, pre[o]? = some (.out v s) ∧ outs[o]? = some ⟨signed64 (le v), s⟩ ∧ v.length = 8
  | 0, ts, outs, rest, h => by
    simp [outsT] at h; obtain ⟨rfl, rfl⟩ := h; exact ⟨[], by simp, rfl, rfl, fun i hi => absurd hi (by omega)⟩
  | k + 1, [], _, _, h => by simp [outsT] at h
  | k + 1, t :: ts, outs, rest, h => by
    cases t with
    | out v s =>
      simp only [outsT] at h
      by_cases hc : v.length = 8 ∧ s.length ≤ MAX_SIZE
      swap; · rw [if_neg hc] at h; simp at h
      rw [if_pos hc] at h
      cases hk : outsT k ts with
      | none => simp [hk] at h
      | some r =>
        rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨pre, hp, hl, hol, hv⟩ := outsT_vals k ts r.1 r.2 (by rw [hk])
        refine ⟨.out v s :: pre, by simp [hp], by simp [hl], by simp [hol], fun j hj => ?_⟩
        rcases j with _ | j
        · exact ⟨v, s, rfl, rfl, hc.1⟩
        · obtain ⟨a, b, e1, e2, l1⟩ := hv j (by omega)
          exact ⟨a, b, by simpa using e1, by simpa using e2, l1⟩
    | _ => simp [outsT] at h

theorem attach_get {ins : List TxIn} {ws : List (List Bytes)} (hl : ins.length = ws.length) {i : ℕ}
    (hi : i < ins.length) : ∃ w, (attach ins ws)[i]? = some { ins[i] with witness := w } ∧ ws[i]? = some w := by
  refine ⟨ws[i]'(by omega), ?_, by simp⟩
  simp [attach, List.getElem?_map, List.getElem?_zip_eq_some, hi, show i < ws.length by omega]

/-- **A transaction's fields.** For `txT (txh v seg nIn :: ts) = some (t, rest)`: the tokens split as in
`txT_split`, input `i` of `t` carries input token `i`'s prevout, scriptSig and sequence, output `o` carries
output token `o`'s value and script, the lock time is the lock-time token's, and without the segwit flag
every witness is empty, with it some witness is not. -/
theorem txT_vals {v : Bytes} {seg : Bool} {nIn : ℕ} {ts : List Tok} {t : Tx} {rest : List Tok}
    (h : txT (.txh v seg nIn :: ts) = some (t, rest)) :
    ∃ pin k pout pw l, ts = pin ++ .nout k :: (pout ++ (pw ++ .lock l :: rest)) ∧
      pin.length = nIn ∧ pout.length = k ∧ t.vin.length = nIn ∧ t.vout.length = k ∧ 1 ≤ nIn ∧
      t.lockTime = le l ∧ l.length = 4 ∧ (∀ x ∈ pw, x.isWit) ∧
      (∀ i < nIn, ∃ hh n s q, pin[i]? = some (.inp hh n s q) ∧
        (∃ w, t.vin[i]? = some ⟨⟨hh, le n⟩, s, le q, w⟩) ∧ hh.length = 32 ∧ n.length = 4 ∧ q.length = 4) ∧
      (∀ o < k, ∃ val s, pout[o]? = some (.out val s) ∧ t.vout[o]? = some ⟨signed64 (le val), s⟩ ∧ val.length = 8) ∧
      (seg = false → pw = [] ∧ t.hasWitness = false) ∧
      (seg = true → t.hasWitness = true ∧
        ∃ ws, witsT nIn (pw ++ .lock l :: rest) = some (ws, .lock l :: rest) ∧ t.vin.map (·.witness) = ws) := by
  simp only [txT] at h
  by_cases hc : v.length = 4 ∧ 1 ≤ nIn ∧ nIn ≤ MAX_SIZE
  swap; · rw [if_neg hc] at h; simp at h
  rw [if_pos hc] at h
  obtain ⟨hv, h1, -⟩ := hc
  cases hins : insT nIn ts with
  | none => simp [hins] at h
  | some r =>
    obtain ⟨ins, ts1⟩ := r
    obtain ⟨pin, hpin, hpl, hil, hiv⟩ := insT_vals nIn ts ins ts1 hins
    obtain ⟨-, -, hinp⟩ := insT_split nIn ts ins ts1 hins
    rw [hins] at h
    match ts1, h, hpin with
    | .nout k :: ts1, h, hpin =>
      simp only at h
      by_cases hk : k ≤ MAX_SIZE
      swap; · rw [if_neg hk] at h; simp at h
      rw [if_pos hk] at h
      cases houts : outsT k ts1 with
      | none => simp [houts] at h
      | some r =>
        obtain ⟨outs, ts2⟩ := r
        obtain ⟨pout, hpout, hol, houl, hov⟩ := outsT_vals k ts1 outs ts2 houts
        rw [houts] at h
        simp only at h
        have hw : ∃ ws ts3 pw, (if seg then witsT nIn ts2 else some (List.replicate nIn [], ts2)) = some (ws, ts3) ∧
            ws.length = nIn ∧ ts2 = pw ++ ts3 ∧ (∀ x ∈ pw, x.isWit) ∧ (seg = false → pw = [] ∧ ws = List.replicate nIn []) ∧
            (seg = true → witsT nIn ts2 = some (ws, ts3)) := by
          cases seg with
          | false => exact ⟨_, _, [], rfl, by simp, by simp, by simp, fun _ => ⟨rfl, rfl⟩, fun h => by simp at h⟩
          | true =>
            cases hws : witsT nIn ts2 with
            | none => simp [hws] at h
            | some r =>
              obtain ⟨wl, -, -⟩ := witsT_sound nIn ts2 r.1 r.2 hws
              obtain ⟨pw, hpw, hw⟩ := witsT_split nIn ts2 r.1 r.2 hws
              exact ⟨r.1, r.2, pw, by simp, wl, hpw, hw, by simp, fun _ => by simp [hws]⟩
        obtain ⟨ws, ts3, pw, hwe, wl, hpw, hwit, hnil, hpre⟩ := hw
        rw [hwe] at h
        match ts3, h, hpw with
        | .lock l :: rest', h, hpw =>
          simp only at h
          by_cases hl : l.length = 4 ∧ (seg = true → (ws.any fun w => !w.isEmpty) = true)
          swap; · rw [if_neg hl] at h; simp at h
          rw [if_pos hl] at h
          obtain ⟨hl4, hany⟩ := hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨a1, -, -, a4, -⟩ := attach_props ins ws (by rw [hil, wl])
          refine ⟨pin, k, pout, pw, l, by rw [hpin, hpout, hpw], hpl, hol,
            by show (attach ins ws).length = nIn; rw [a1, hil],
            houl, h1, rfl, hl4, hwit, fun i hi => ?_, hov, fun hs => ?_, fun hs => ?_⟩
          · obtain ⟨hh, n, s, q, e1, e2, l1, l2, l3⟩ := hiv i hi
            obtain ⟨w, ew, -⟩ := attach_get (by rw [hil, wl]) (show i < ins.length by omega)
            have : ins[i]'(by omega) = ⟨⟨hh, le n⟩, s, le q, []⟩ := by
              rw [List.getElem?_eq_getElem (by omega)] at e2; exact Option.some.inj e2
            refine ⟨hh, n, s, q, e1, ⟨w, ?_⟩, l1, l2, l3⟩
            show (attach ins ws)[i]? = _
            rw [ew, this]
          · obtain ⟨hp, hws⟩ := hnil hs
            refine ⟨hp, ?_⟩
            show (attach ins ws).any (fun i => !i.witness.isEmpty) = false
            rw [a4, hws]; simp
          · refine ⟨by show (attach ins ws).any (fun i => !i.witness.isEmpty) = true; rw [a4]; exact hany hs,
              ws, by rw [← hpw]; exact hpre hs, ?_⟩
            show (attach ins ws).map (·.witness) = ws
            apply List.ext_getElem
            · simp [attach, hil, wl]
            · intro j h1 h2
              simp [attach]
        | [], h, _ => simp at h
        | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .nout .. :: _, h, _
        | .out .. :: _, h, _ | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ => simp at h
    | [], h, _ => simp at h
    | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .out .. :: _, h, _
    | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ | .lock .. :: _, h, _ => simp at h

end BitcoinConsensus.Block
