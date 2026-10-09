/-
**Transaction byte ranges (M3a.3).** On a transaction's lock-time row the fields hold its byte ranges:
`TXA` (start), `WST` (witness section start), `START` (lock time). The wtxid message `[TXA, START + 4)`
serializes to `serWit`, and the txid message (split around marker/flag and witnesses for segwit) to
`serNoWit`.
-/
import StarkedAir.Block.TxIndex
import StarkedAir.Spec.TxSplit

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (eval_cst)

/-! ### Token kinds give row kinds -/

theorem tokk_wit {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} (h : (tokOf M R r).isWit = true) :
    M K_WCNT r = 1 ∨ M K_WITEM r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> simp [Spec.Block.Tok.isWit] at h
  · exact Or.inl h6
  · exact Or.inr h7

theorem tokk_out {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} (h : (tokOf M R r).isOut = true) :
    M K_OUT r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp [Spec.Block.Tok.isOut] at h
  exact h5

theorem tokk_nout {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r k : ℕ} (h : tokOf M R r = .nout k) :
    M K_NOUT r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 <;> simp at h
  exact h4

theorem tokk_lock {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {r : ℕ} {l : Spec.Block.Bytes} (h : tokOf M R r = .lock l) :
    M K_BLK r ≠ 1 ∧ M K_TXH r ≠ 1 ∧ M K_IN r ≠ 1 ∧ M K_NOUT r ≠ 1 ∧ M K_OUT r ≠ 1 ∧ M K_WCNT r ≠ 1 ∧
      M K_WITEM r ≠ 1 ∧ l = slice R (M START r).val 4 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 h3 h4 h5 h6 h7 <;> simp at h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h.symm⟩

/-! ### Tokens by row -/

theorem toksFrom_length {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r : ℕ} : (toksFrom M R m r).length = m - r := by
  simp [toksFrom]

theorem toksFrom_get {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r i : ℕ} (hi : i < m - r) :
    (toksFrom M R m r)[i]? = some (tokOf M R (r + i)) := by
  simp [toksFrom, hi]

theorem toksFrom_take {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r j : ℕ} (h : r + j ≤ m) :
    (toksFrom M R m r).take j = toksFrom M R (r + j) r := by
  unfold toksFrom
  rw [← List.map_take, List.take_range, show min j (m - r) = r + j - r by omega]

theorem get_app {α : Type} {A B : List α} {L : List α} (h : L = A ++ B) (j : ℕ) : L[A.length + j]? = B[j]? := by
  rw [h, List.getElem?_append_right (by omega)]; simp

section Layout

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

/-- **A transaction's rows.** From its header row `rh`: input/output rows up to `rw`, witness rows
`rw … r' − 1` (none without the segwit flag), the lock-time row `r'`. `serNoWit` is the header's
version and input count, the rows `rh + 1 … rw − 1`, and the lock time. -/
theorem tx_layout {rh : ℕ} (hr : rh < m) (ht : M K_TXH rh = 1) :
    ∃ tx r' rw v nIn l, Spec.Block.txT (toksFrom M R m rh) = some (tx, toksFrom M R m (r' + 1)) ∧
      rh + 1 < rw ∧ rw ≤ r' ∧ r' < m ∧ M K_LOCK r' = 1 ∧
      tokOf M R rh = .txh v (decide (M SEG rh = 1)) nIn ∧ tokOf M R r' = .lock l ∧
      (∀ j, rw ≤ j → j < r' → M K_WCNT j = 1 ∨ M K_WITEM j = 1) ∧
      (M K_NOUT (rw - 1) = 1 ∨ M K_OUT (rw - 1) = 1) ∧
      (M SEG rh ≠ 1 → rw = r') ∧ (∀ j, rh ≤ j → j < r' → ∀ l', tokOf M R j ≠ .lock l') ∧
      Spec.Block.serNoWit tx = v ++ Spec.Block.serCompact nIn ++ Spec.Block.toksBytes (toksFrom M R rw (rh + 1)) ++ l := by
  obtain ⟨tx, r', htx, hrr', hr'm, hl, -⟩ := tx_sim hsat R hcs hmn hpad hfit hr ht
  have hrn : rh < n := by omega
  have hblk : M K_BLK rh ≠ 1 := by
    rw [kind_unique hsat hrn (a := K_TXH) (b := K_BLK) (by simp [K_TXH]) (by simp [K_BLK]) (by simp [K_TXH, K_BLK]) ht]
    exact zero_ne_one
  have htok : tokOf M R rh = .txh (slice R (M START rh).val 4) (decide (M SEG rh = 1)) (M VAL rh).val := by
    simp [tokOf, hblk, ht]
  rw [toksFrom_cons hr, htok] at htx
  obtain ⟨pin, k, pout, pw, l, hsplit, hinp, hout, hwit, hnil, -, -, hnw⟩ := Spec.Block.txT_split htx
  have hlen := congrArg List.length hsplit
  simp only [toksFrom_length, List.length_append, List.length_cons] at hlen
  set rw := rh + 2 + pin.length + pout.length with hrw
  have hr' : r' = rw + pw.length := by omega
  have tk : ∀ i, i < m - (rh + 1) → (toksFrom M R m (rh + 1))[i]? = some (tokOf M R (rh + 1 + i)) :=
    fun i hi => toksFrom_get hi
  -- the output-count row
  have hnout : tokOf M R (rh + 1 + pin.length) = .nout k := by
    have := get_app hsplit 0
    rw [tk _ (by omega)] at this; simpa using this
  -- the lock-time row
  have hlock : tokOf M R r' = .lock l := by
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
        (pin ++ .nout k :: pout ++ pw) ++ (.lock l :: toksFrom M R m (r' + 1)) := by simp
    have := get_app (hsplit.trans e) 0
    rw [tk _ (by simp; omega)] at this
    simp only [List.length_append, List.length_cons] at this
    rw [show rh + 1 + (pin.length + (pout.length + 1) + pw.length + 0) = r' by omega] at this
    simpa using this
  refine ⟨tx, r', rw, _, _, l, ?_, by omega, by omega, hr'm, hl, htok, hlock, fun j h1 h2 => ?_, ?_, fun hs => ?_,
    fun j h1 h2 l' => ?_, ?_⟩
  · rw [toksFrom_cons hr, htok]; exact htx
  · -- witness rows
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
        (pin ++ .nout k :: pout) ++ (pw ++ .lock l :: toksFrom M R m (r' + 1)) := by simp
    have := get_app (hsplit.trans e) (j - rw)
    rw [tk _ (by simp; omega)] at this
    simp only [List.length_append, List.length_cons] at this
    rw [List.getElem?_append_left (by omega)] at this
    rw [show rh + 1 + (pin.length + (pout.length + 1) + (j - rw)) = j by omega] at this
    have hm : tokOf M R j ∈ pw := List.mem_of_getElem? this.symm
    exact tokk_wit (hwit _ hm)
  · -- the row before the witnesses: the output count or the last output
    rcases List.eq_nil_or_concat pout with h0 | ⟨pl, last, hpl⟩
    · left
      rw [h0] at hrw
      rw [show rw - 1 = rh + 1 + pin.length by simp at hrw; omega]
      exact tokk_nout hnout
    · right
      have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
          (pin ++ .nout k :: pl) ++ (last :: (pw ++ .lock l :: toksFrom M R m (r' + 1))) := by rw [hpl]; simp
      have := get_app (hsplit.trans e) 0
      rw [tk _ (by simp; rw [hpl] at hrw; simp at hrw; omega)] at this
      simp only [List.length_append, List.length_cons] at this
      rw [show rh + 1 + (pin.length + (pl.length + 1) + 0) = rw - 1 by rw [hpl] at hrw; simp at hrw; omega] at this
      simp at this
      exact tokk_out (by rw [this]; exact hout last (by rw [hpl]; simp))
  · have : pw = [] := hnil (by simpa using hs)
    rw [hr', this]; simp
  · -- rows before the lock time are not lock-time rows
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; rw [htok]; simp
    · have e2 : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l :: toksFrom M R m (r' + 1))) =
          (pin ++ .nout k :: pout ++ pw) ++ (.lock l :: toksFrom M R m (r' + 1)) := by simp
      have := hsplit.trans e2
      have g : (toksFrom M R m (rh + 1))[j - (rh + 1)]? = _ := congrArg (fun L => L[j - (rh + 1)]?) this
      rw [tk _ (by omega), List.getElem?_append_left (by simp; omega),
        show rh + 1 + (j - (rh + 1)) = j by omega] at g
      have hm : tokOf M R j ∈ pin ++ .nout k :: pout ++ pw := List.mem_of_getElem? g.symm
      intro hj; rw [hj] at hm
      simp only [List.mem_append, List.mem_cons] at hm
      rcases hm with ((h | h | h) | h)
      · have := hinp _ h; simp [Spec.Block.Tok.isInp] at this
      · cases h
      · have := hout _ h; simp [Spec.Block.Tok.isOut] at this
      · have := hwit _ h; simp [Spec.Block.Tok.isWit] at this
  · rw [hnw]
    have e : (toksFrom M R m (rh + 1)).take (pin.length + 1 + pout.length) = pin ++ .nout k :: pout := by
      rw [hsplit, List.take_append, List.take_of_length_le (by omega),
        show pin.length + 1 + pout.length - pin.length = pout.length + 1 by omega, List.take_succ_cons,
        List.take_left' rfl]
    rw [toksFrom_take (by omega), show rh + 1 + (pin.length + 1 + pout.length) = rw by omega] at e
    rw [e]
    simp [Spec.Block.toksBytes, Spec.Block.Tok.bytes, List.append_assoc]

omit hcs hmn hpad hfit in
theorem tok_lock_of {r : ℕ} (hr : r < n) (h : M K_LOCK r = 1) : ∃ l, tokOf M R r = .lock l := by
  have ka := kinds_at hsat hr (a := K_LOCK) (by simp [K_LOCK]) h
  have z : ∀ c, c < 9 → c ≠ K_LOCK → M c r ≠ 1 := fun c hc hne => by rw [ka c hc, if_neg hne]; exact zero_ne_one
  refine ⟨slice R (M START r).val 4, ?_⟩
  unfold tokOf
  rw [if_neg (z K_BLK (by simp [K_BLK]) (by simp [K_BLK, K_LOCK])), if_neg (z K_TXH (by simp [K_TXH]) (by simp [K_TXH, K_LOCK])),
    if_neg (z K_IN (by simp [K_IN]) (by simp [K_IN, K_LOCK])), if_neg (z K_NOUT (by simp [K_NOUT]) (by simp [K_NOUT, K_LOCK])),
    if_neg (z K_OUT (by simp [K_OUT]) (by simp [K_OUT, K_LOCK])), if_neg (z K_WCNT (by simp [K_WCNT]) (by simp [K_WCNT, K_LOCK])),
    if_neg (z K_WITEM (by simp [K_WITEM]) (by simp [K_WITEM, K_LOCK]))]

/-- **The tuple on the lock-time row**: `TXA` is the transaction's start and `WST` the start of row `rw`
(the witness section, or the lock time without witnesses). -/
theorem tx_cols {rh : ℕ} (hr : rh < m) (ht : M K_TXH rh = 1) :
    ∃ tx r' rw v nIn l, Spec.Block.txT (toksFrom M R m rh) = some (tx, toksFrom M R m (r' + 1)) ∧
      rh + 1 < rw ∧ rw ≤ r' ∧ r' < m ∧ M K_LOCK r' = 1 ∧
      tokOf M R rh = .txh v (decide (M SEG rh = 1)) nIn ∧ tokOf M R r' = .lock l ∧
      (M SEG rh ≠ 1 → rw = r') ∧
      Spec.Block.serNoWit tx = v ++ Spec.Block.serCompact nIn ++ Spec.Block.toksBytes (toksFrom M R rw (rh + 1)) ++ l ∧
      M TXA r' = M START rh ∧ M WST r' = M START rw ∧ M SEG r' = M SEG rh ∧
      (∀ j, rh < j → j ≤ r' → M K_TXH j = 0) ∧ (∀ j, rh ≤ j → j < r' → M K_LOCK j = 0) := by
  obtain ⟨tx, r', rw, v, nIn, l, htx, h1, h2, hr'm, hl, htok, hlock, hwit, hpre, hseg, hnl, hnw⟩ :=
    tx_layout hsat R hcs hmn hpad hfit hr ht
  have hrn : r' < n := by omega
  have rh0 : 0 < rh := by
    rcases Nat.eq_zero_or_pos rh with e | e
    · subst e
      have := kind_unique hsat (by omega : 0 < n) (a := K_BLK) (b := K_TXH) (by simp [K_BLK]) (by simp [K_TXH])
        (by simp [K_BLK, K_TXH]) (first_blk hsat (by omega))
      rw [ht] at this; exact absurd this one_ne_zero
    · exact e
  have nolock : ∀ j, rh ≤ j → j < r' → M K_LOCK j = 0 := by
    intro j a b
    rcases kind_bool hsat (c := K_LOCK) (by simp [kinds]) (by omega : j < n) with z | z
    · exact z
    · obtain ⟨l', e⟩ := tok_lock_of hsat R (by omega) z; exact absurd e (hnl j a b l')
  have notxh : ∀ j, rh < j → j ≤ r' → M K_TXH j = 0 := by
    intro j a b
    obtain ⟨t1, -⟩ := trans_all hsat (r := j - 1) (by omega)
    rw [show j - 1 + 1 = j by omega] at t1
    have hb : M K_BLK (j - 1) = 0 := by
      have := not_blk hsat (r := j - 2) (by omega); rwa [show j - 2 + 1 = j - 1 by omega] at this
    rw [t1, hb, nolock (j - 1) (by omega) (by omega)]; ring
  have c := fun (e : Expr) (h : e ∈ txC) {j : ℕ} (hj : j < n) => sat hsat (mem_txC h) hj
  -- TXA and SEG hold the header row's values
  have txa : ∀ i, i ≤ r' - rh → M TXA (rh + i) = M START rh ∧ M SEG (rh + i) = M SEG rh := by
    intro i hi
    induction i with
    | zero =>
      have := c (.mul (k K_TXH) (.sub (k TXA) (k START))) (by simp [txC]) (by omega : rh < n)
      simp only [Expr.eval, ev_k (show rh < n by omega), ht, one_mul, sub_eq_zero, add_zero] at this ⊢
      exact ⟨this, trivial⟩
    | succ i ih =>
      obtain ⟨a, b⟩ := ih (by omega)
      have hj : rh + i + 1 < n := by omega
      have h0 := notxh (rh + i + 1) (by omega) (by omega)
      have := c (.mul (oneMinus (k K_TXH)) (.mul notFirst (.sub (k TXA) (kp TXA)))) (by simp [txC]) hj
      simp only [Expr.eval, ev_notFirst hj, ev_k hj, ev_kp hj, oneMinus, one, eval_cst, Nat.cast_one, h0,
        sub_zero, one_mul, sub_eq_zero] at this
      rw [show rh + (i + 1) = rh + i + 1 by ring, this, a]
      refine ⟨rfl, ?_⟩
      rw [(counters hsat hj).2.2.2.2.2.2.2.1 h0, b]
  obtain ⟨hta, hsg⟩ := txa (r' - rh) le_rfl
  rw [show rh + (r' - rh) = r' by omega] at hta hsg
  -- WST: set at the first witness (or lock-time) row, then held
  have hp : rw - 1 + 1 < n := by omega
  obtain ⟨-, -, -, -, t5, -, t7, -⟩ := trans_all hsat hp
  rw [show rw - 1 + 1 = rw by omega] at t5 t7
  have hpn : rw - 1 < n := by omega
  have hesc : M ESC (rw - 1) = 0 := by
    rw [esc_eq hsat hpn]
    rcases hpre with h | h
    · rw [kind_unique hsat hpn (a := K_NOUT) (b := K_WCNT) (by simp [K_NOUT]) (by simp [K_WCNT]) (by simp [K_NOUT, K_WCNT]) h,
        kind_unique hsat hpn (a := K_NOUT) (b := K_WITEM) (by simp [K_NOUT]) (by simp [K_WITEM]) (by simp [K_NOUT, K_WITEM]) h]
      ring
    · rw [kind_unique hsat hpn (a := K_OUT) (b := K_WCNT) (by simp [K_OUT]) (by simp [K_WCNT]) (by simp [K_OUT, K_WCNT]) h,
        kind_unique hsat hpn (a := K_OUT) (b := K_WITEM) (by simp [K_OUT]) (by simp [K_WITEM]) (by simp [K_OUT, K_WITEM]) h]
      ring
  have hsum : M K_WCNT rw + M K_LOCK rw = 1 := by
    have hrw : rw < n := by omega
    rcases Nat.eq_or_lt_of_le h2 with e | e
    · rw [e, hl, kind_unique hsat hrn (a := K_LOCK) (b := K_WCNT) (by simp [K_LOCK]) (by simp [K_WCNT])
        (by simp [K_LOCK, K_WCNT]) hl]; ring
    · have hw : M K_WCNT rw = 1 := by
        rcases hwit rw le_rfl e with h | h
        · exact h
        · obtain ⟨-, -, -, -, -, t6, -, -⟩ := trans_all hsat hp
          rw [show rw - 1 + 1 = rw by omega] at t6
          rcases hpre with g | g
          · rw [t6, kind_unique hsat hpn (a := K_NOUT) (b := K_WCNT) (by simp [K_NOUT]) (by simp [K_WCNT])
              (by simp [K_NOUT, K_WCNT]) g, kind_unique hsat hpn (a := K_NOUT) (b := K_WITEM) (by simp [K_NOUT])
              (by simp [K_WITEM]) (by simp [K_NOUT, K_WITEM]) g] at h; simp at h
          · rw [t6, kind_unique hsat hpn (a := K_OUT) (b := K_WCNT) (by simp [K_OUT]) (by simp [K_WCNT])
              (by simp [K_OUT, K_WCNT]) g, kind_unique hsat hpn (a := K_OUT) (b := K_WITEM) (by simp [K_OUT])
              (by simp [K_WITEM]) (by simp [K_OUT, K_WITEM]) g] at h; simp at h
      rw [hw, kind_unique hsat hrw (a := K_WCNT) (b := K_LOCK) (by simp [K_WCNT]) (by simp [K_LOCK])
        (by simp [K_LOCK, K_WCNT]) hw]; ring
  have heoc : M EOC (rw - 1) = 1 := by
    rw [t5, t7, hesc] at hsum; linear_combination hsum
  have wst : ∀ i, i ≤ r' - rw → M WST (rw + i) = M START rw := by
    intro i hi
    induction i with
    | zero =>
      have hj : rw - 1 + 1 < n := hp
      have := c (.mul (kp EOC) (.sub (k WST) (k START))) (by simp [txC]) hj
      simp only [Expr.eval, ev_k hj, ev_kp hj, heoc, one_mul, sub_eq_zero] at this
      rw [show rw - 1 + 1 = rw by omega] at this; simpa using this
    | succ i ih =>
      have hj : rw + i + 1 < n := by omega
      have hrj : rw + i < n := by omega
      have he0 : M EOC (rw + i) = 0 := by
        rw [eoc_eq hsat hrj]
        rcases hwit (rw + i) (by omega) (by omega) with g | g
        · rw [kind_unique hsat hrj (a := K_WCNT) (b := K_NOUT) (by simp [K_WCNT]) (by simp [K_NOUT]) (by simp [K_WCNT, K_NOUT]) g,
            kind_unique hsat hrj (a := K_WCNT) (b := K_OUT) (by simp [K_WCNT]) (by simp [K_OUT]) (by simp [K_WCNT, K_OUT]) g]
          ring
        · rw [kind_unique hsat hrj (a := K_WITEM) (b := K_NOUT) (by simp [K_WITEM]) (by simp [K_NOUT]) (by simp [K_WITEM, K_NOUT]) g,
            kind_unique hsat hrj (a := K_WITEM) (b := K_OUT) (by simp [K_WITEM]) (by simp [K_OUT]) (by simp [K_WITEM, K_OUT]) g]
          ring
      have := c (.mul (oneMinus (kp EOC)) (.mul notFirst (.sub (k WST) (kp WST)))) (by simp [txC]) hj
      simp only [Expr.eval, ev_notFirst hj, ev_k hj, ev_kp hj, oneMinus, one, eval_cst, Nat.cast_one, he0,
        sub_zero, one_mul, sub_eq_zero] at this
      rw [show rw + (i + 1) = rw + i + 1 by ring, this, ih (by omega)]
  have hws := wst (r' - rw) le_rfl
  rw [show rw + (r' - rw) = r' by omega] at hws
  exact ⟨tx, r', rw, v, nIn, l, htx, h1, h2, hr'm, hl, htok, hlock, hseg, hnw, hta, hws, hsg, notxh, nolock⟩

omit hsat hcs hmn hpad hfit in
theorem locks_const {a b : ℕ} (h : ∀ j, a ≤ j → j < b → M K_LOCK j ≠ 1) (hab : a ≤ b) : locks M b = locks M a := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih => rw [locks_succ, if_neg (h b hab (by omega)), ih (fun j x y => h j x (by omega))]; rfl

/-- Transaction `tx` ends at lock-time row `ρ`: its header row `rh` is the last header row before `ρ`
and its tokens parse to `tx`, up to row `ρ`. -/
def TxAt (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (m ρ : ℕ) (tx : Spec.Block.Tx) : Prop :=
  ∃ rh, rh < ρ ∧ M K_TXH rh = 1 ∧ (∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) ∧
    Spec.Block.txT (toksFrom M R m rh) = some (tx, toksFrom M R m (ρ + 1))

omit hcs hmn hpad hfit in
theorem txh_of_txT {r : ℕ} (hr : r < n) {ts' : List Spec.Block.Tok} {t : Spec.Block.Tx} {rest : List Spec.Block.Tok}
    (h : Spec.Block.txT (tokOf M R r :: ts') = some (t, rest)) : M K_TXH r = 1 := by
  unfold tokOf at h
  split_ifs at h with h1 h2 <;> simp [Spec.Block.txT] at h
  exact h2

/-- **The transactions of a run of rows.** If `k` transactions parse from header row `rh`, the `j`-th
ends at a lock-time row with `locks rh + j` lock-time rows above it, and the run ends at row `e`. -/
theorem txs_rows : ∀ (k rh : ℕ) (txs : List Spec.Block.Tx) (rest : List Spec.Block.Tok),
    rh < m → M K_TXH rh = 1 → Spec.Block.txsT k (toksFrom M R m rh) = some (txs, rest) →
    txs.length = k ∧ (∀ j < k, ∃ ρ tx, ρ < m ∧ M K_LOCK ρ = 1 ∧ locks M ρ = locks M rh + j ∧
      txs[j]? = some tx ∧ TxAt M R m ρ tx) ∧
    ∃ e, e ≤ m ∧ rest = toksFrom M R m e ∧ locks M e = locks M rh + k
  | 0, rh, txs, rest, _, _, h => by
    simp [Spec.Block.txsT] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _), rh, by omega, rfl, rfl⟩
  | k + 1, rh, txs, rest, hr, ht, h => by
    obtain ⟨tx, r', rw, v, nIn, l, htx, h1, h2, hr'm, hl, htok, hlock, hseg, hnw, hta, hws, hsg, notxh, nolock⟩ :=
      tx_cols hsat R hcs hmn hpad hfit hr ht
    simp only [Spec.Block.txsT, htx] at h
    cases hk : Spec.Block.txsT k (toksFrom M R m (r' + 1)) with
    | none => simp [hk] at h
    | some p =>
      obtain ⟨txs', rest'⟩ := p
      rw [hk] at h; simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      -- locks: none in `[rh, r')`, one at `r'`
      have e1 : locks M r' = locks M rh :=
        locks_const (fun j a b => by rw [nolock j a b]; exact zero_ne_one) (by omega)
      have hlk : locks M (r' + 1) = locks M rh + 1 := by
        rw [locks_succ, if_pos hl, e1]
      have hhead : TxAt M R m r' tx := ⟨rh, by omega, ht, notxh, htx⟩
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · subst hk0
        simp [Spec.Block.txsT] at hk; obtain ⟨rfl, rfl⟩ := hk
        refine ⟨rfl, fun j hj => ?_, r' + 1, by omega, rfl, by rw [hlk]⟩
        have : j = 0 := by omega
        subst this
        exact ⟨r', tx, hr'm, hl, by simpa using e1, by simp, hhead⟩
      · -- the next transaction starts right after the lock time
        have hr1 : r' + 1 < m := by
          by_contra hc
          have e : m - (r' + 1) = 0 := by omega
          have : toksFrom M R m (r' + 1) = [] := by simp [toksFrom, e]
          rw [this] at hk
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          simp [Spec.Block.txsT, Spec.Block.txT] at hk
        have ht1 : M K_TXH (r' + 1) = 1 := by
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          rw [toksFrom_cons hr1] at hk
          simp only [Spec.Block.txsT] at hk
          cases hh : Spec.Block.txT (tokOf M R (r' + 1) :: toksFrom M R m (r' + 1 + 1)) with
          | none => simp [hh] at hk
          | some q => exact txh_of_txT hsat R (r := r' + 1) (by omega) (t := q.1) (rest := q.2) (by rw [hh])
        obtain ⟨hlen, hrows, e, he, hrest, hle⟩ := txs_rows k (r' + 1) txs' rest' hr1 ht1 hk
        refine ⟨by simp [hlen], fun j hj => ?_, e, he, hrest, by rw [hle, hlk]; ring⟩
        rcases Nat.eq_zero_or_pos j with hj0 | hj0
        · subst hj0; exact ⟨r', tx, hr'm, hl, by simpa using e1, by simp, hhead⟩
        · obtain ⟨ρ, t, a, b, c, d, e'⟩ := hrows (j - 1) (by omega)
          refine ⟨ρ, t, a, b, by rw [c, hlk]; omega, ?_, e'⟩
          rw [show j = (j - 1) + 1 by omega]; simpa using d

end Layout

end StarkedAir.Block.Fields
