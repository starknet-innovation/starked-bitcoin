/-
**Where a transaction's parts sit in its tokens (M3a.3).** A parsed transaction's tokens split into the
header token, the input/output tokens, the witness tokens and the lock time; `serNoWit` is the header
without marker and flag, the input/output bytes and the lock time.
-/
import StarkedAir.Spec.BlockTokens

namespace StarkedAir.Spec.Block

/-- Witness-section tokens. -/
def Tok.isWit : Tok → Bool
  | .wcnt _ => true
  | .witem _ => true
  | _ => false

theorem insT_split : ∀ (k : ℕ) (ts : List Tok) (ins : List TxIn) (rest : List Tok),
    insT k ts = some (ins, rest) → ∃ pre, ts = pre ++ rest
  | 0, ts, ins, rest, h => by simp [insT] at h; exact ⟨[], by simp [h.2]⟩
  | k + 1, [], _, _, h => by simp [insT] at h
  | k + 1, t :: ts, ins, rest, h => by
    cases t with
    | inp hh i s q =>
      simp only [insT] at h
      split_ifs at h
      cases hk : insT k ts with
      | none => simp [hk] at h
      | some r =>
        rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨pre, hp⟩ := insT_split k ts r.1 r.2 (by rw [hk])
        exact ⟨.inp hh i s q :: pre, by rw [hp, ← h.2]; rfl⟩
    | _ => simp [insT] at h

theorem outsT_split : ∀ (k : ℕ) (ts : List Tok) (outs : List TxOut) (rest : List Tok),
    outsT k ts = some (outs, rest) → ∃ pre, ts = pre ++ rest
  | 0, ts, outs, rest, h => by simp [outsT] at h; exact ⟨[], by simp [h.2]⟩
  | k + 1, [], _, _, h => by simp [outsT] at h
  | k + 1, t :: ts, outs, rest, h => by
    cases t with
    | out v s =>
      simp only [outsT] at h
      split_ifs at h
      cases hk : outsT k ts with
      | none => simp [hk] at h
      | some r =>
        rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨pre, hp⟩ := outsT_split k ts r.1 r.2 (by rw [hk])
        exact ⟨.out v s :: pre, by rw [hp, ← h.2]; rfl⟩
    | _ => simp [outsT] at h

theorem itemsT_split : ∀ (k : ℕ) (ts : List Tok) (w : List Bytes) (rest : List Tok),
    itemsT k ts = some (w, rest) → ∃ pre, ts = pre ++ rest ∧ ∀ t ∈ pre, t.isWit
  | 0, ts, w, rest, h => by simp [itemsT] at h; exact ⟨[], by simp [h.2]⟩
  | k + 1, [], _, _, h => by simp [itemsT] at h
  | k + 1, t :: ts, w, rest, h => by
    cases t with
    | witem it =>
      simp only [itemsT] at h
      split_ifs at h
      cases hk : itemsT k ts with
      | none => simp [hk] at h
      | some r =>
        rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨pre, hp, hw⟩ := itemsT_split k ts r.1 r.2 (by rw [hk])
        refine ⟨.witem it :: pre, by rw [hp, ← h.2]; rfl, ?_⟩
        intro t ht; rcases List.mem_cons.mp ht with rfl | ht
        · rfl
        · exact hw t ht
    | _ => simp [itemsT] at h

theorem witsT_split : ∀ (k : ℕ) (ts : List Tok) (ws : List (List Bytes)) (rest : List Tok),
    witsT k ts = some (ws, rest) → ∃ pre, ts = pre ++ rest ∧ ∀ t ∈ pre, t.isWit
  | 0, ts, ws, rest, h => by simp [witsT] at h; exact ⟨[], by simp [h.2]⟩
  | k + 1, [], _, _, h => by simp [witsT] at h
  | k + 1, t :: ts, ws, rest, h => by
    cases t with
    | wcnt c =>
      simp only [witsT] at h
      split_ifs at h
      cases hi : itemsT c ts with
      | none => simp [hi] at h
      | some r1 =>
        obtain ⟨w, ts'⟩ := r1
        rw [hi] at h; simp only at h
        cases hk : witsT k ts' with
        | none => simp [hk] at h
        | some r =>
          rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨p1, hp1, hw1⟩ := itemsT_split c ts w ts' hi
          obtain ⟨p2, hp2, hw2⟩ := witsT_split k ts' r.1 r.2 (by rw [hk])
          refine ⟨.wcnt c :: (p1 ++ p2), by rw [hp1, hp2, ← h.2]; simp, ?_⟩
          intro t ht
          rcases List.mem_cons.mp ht with rfl | ht
          · rfl
          · rcases List.mem_append.mp ht with ht | ht
            · exact hw1 t ht
            · exact hw2 t ht
    | _ => simp [witsT] at h

theorem toksBytes_append (a b : List Tok) : toksBytes (a ++ b) = toksBytes a ++ toksBytes b := by
  simp [toksBytes]

/-- **A transaction's token layout.** After the header token: input tokens, the output count, output
tokens, witness tokens (none without the segwit flag), the lock time. `serNoWit` skips the marker, the
flag and the witness tokens. -/
theorem txT_split {v : Bytes} {seg : Bool} {nIn : ℕ} {ts : List Tok} {t : Tx} {rest : List Tok}
    (h : txT (.txh v seg nIn :: ts) = some (t, rest)) :
    ∃ pin k pout pw l, ts = pin ++ .nout k :: (pout ++ (pw ++ .lock l :: rest)) ∧ (∀ x ∈ pw, x.isWit) ∧
      (seg = false → pw = []) ∧ v.length = 4 ∧ l.length = 4 ∧
      serNoWit t = v ++ serCompact nIn ++ toksBytes pin ++ serCompact k ++ toksBytes pout ++ l := by
  simp only [txT] at h
  by_cases hc : v.length = 4 ∧ 1 ≤ nIn ∧ nIn ≤ MAX_SIZE
  swap; · rw [if_neg hc] at h; simp at h
  rw [if_pos hc] at h
  obtain ⟨hv, -, -⟩ := hc
  cases hins : insT nIn ts with
  | none => simp [hins] at h
  | some r =>
    obtain ⟨ins, ts1⟩ := r
    obtain ⟨il, -, ib⟩ := insT_sound nIn ts ins ts1 hins
    obtain ⟨pin, hpin⟩ := insT_split nIn ts ins ts1 hins
    rw [hins] at h
    match ts1, h, ib, hpin with
    | .nout k :: ts1, h, ib, hpin =>
      simp only at h
      by_cases hk : k ≤ MAX_SIZE
      swap; · rw [if_neg hk] at h; simp at h
      rw [if_pos hk] at h
      cases houts : outsT k ts1 with
      | none => simp [houts] at h
      | some r =>
        obtain ⟨outs, ts2⟩ := r
        obtain ⟨ol, -, ob⟩ := outsT_sound k ts1 outs ts2 houts
        obtain ⟨pout, hpout⟩ := outsT_split k ts1 outs ts2 houts
        rw [houts] at h
        simp only at h
        have hw : ∃ ws ts3 pw, (if seg then witsT nIn ts2 else some (List.replicate nIn [], ts2)) = some (ws, ts3) ∧
            ws.length = nIn ∧ ts2 = pw ++ ts3 ∧ (∀ x ∈ pw, x.isWit) ∧ (seg = false → pw = []) := by
          cases seg with
          | false => exact ⟨_, _, [], rfl, by simp, by simp, by simp, fun _ => rfl⟩
          | true =>
            cases hws : witsT nIn ts2 with
            | none => simp [hws] at h
            | some r =>
              obtain ⟨wl, -, -⟩ := witsT_sound nIn ts2 r.1 r.2 hws
              obtain ⟨pw, hpw, hw⟩ := witsT_split nIn ts2 r.1 r.2 hws
              exact ⟨r.1, r.2, pw, by simp, wl, hpw, hw, by simp⟩
        obtain ⟨ws, ts3, pw, hwe, wl, hpw, hwit, hnil⟩ := hw
        rw [hwe] at h
        match ts3, h, hpw with
        | .lock l :: rest', h, hpw =>
          simp only at h
          by_cases hl : l.length = 4 ∧ (seg = true → (ws.any fun w => !w.isEmpty) = true)
          swap; · rw [if_neg hl] at h; simp at h
          rw [if_pos hl] at h
          obtain ⟨hl4, -⟩ := hl
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨a1, a2, -⟩ := attach_props ins ws (by rw [il, wl])
          refine ⟨pin, k, pout, pw, l, by rw [hpin, hpout, hpw], hwit, hnil, hv, hl4, ?_⟩
          have bi : toksBytes pin = ins.flatMap serTxIn := by
            rw [hpin, toksBytes_append] at ib; simpa using ib
          have bo : toksBytes pout = outs.flatMap serTxOut := by
            rw [hpout, toksBytes_append] at ob; simpa using ob
          have a2' : ((ins.zip ws).map (fun p : TxIn × List Bytes => { p.1 with witness := p.2 })).flatMap serTxIn =
              ins.flatMap serTxIn := a2
          simp [serNoWit, leBytes_le' hv, leBytes_le' hl4, a2', il, ol, wl, bi, bo, List.append_assoc]
        | [], h, _ => simp at h
        | .blk .. :: _, h, _ | .txh .. :: _, h, _ | .inp .. :: _, h, _ | .nout .. :: _, h, _
        | .out .. :: _, h, _ | .wcnt .. :: _, h, _ | .witem .. :: _, h, _ => simp at h
    | [], h, _, _ => simp at h
    | .blk .. :: _, h, _, _ | .txh .. :: _, h, _, _ | .inp .. :: _, h, _, _ | .out .. :: _, h, _, _
    | .wcnt .. :: _, h, _, _ | .witem .. :: _, h, _, _ | .lock .. :: _, h, _, _ => simp at h

end StarkedAir.Spec.Block
