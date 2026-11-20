/-
**The walker automaton with a decoration (CONNECT-RULES step 3).** `Spec/BlockFlat.lean` walks a script
byte by byte (`wstep`) and counts the legacy sigops. The accurate count, `IsPushOnly` and the last push
need more than a weight per opcode: the previous opcode's value, a count of opcodes above `OP_16`, the
length of the last operation's data. `runG` runs the automaton with such a decoration; `runG_opsD` says
it computes a fold over `opsD`, Core's `GetOp` with the pushed data. Three instances:

* `acc_run`: the accurate sigop count (`sigOpsAccurate`);
* `po_run`: `pushOnly`, as "the run ends between two operations and saw no opcode above `OP_16`";
* `last_run`: the last operation's data is the script's suffix of the length the run ends with.
-/
import StarkedAir.Spec.BlockFlat
import StarkedAir.Spec.ConnectRules

namespace StarkedAir.Spec.ConnectRules

open StarkedAir.Spec StarkedAir.Spec.Block

/-- A decoration `σ` of the automaton: `g` at an opcode (new decoration and a count), `h` when an
operation's data length is known (0 when it has none). -/
def fGH {σ : Type} (g : σ → UInt8 → σ × ℕ) (h : σ → ℕ → σ) : WS → σ → UInt8 → σ × ℕ
  | .op, st, x => (if 0x4c ≤ x.toNat ∧ x.toNat ≤ 0x4e then (g st x).1
      else h (g st x).1 (if x.toNat < 0x4c then x.toNat else 0), (g st x).2)
  | .len k i acc, st, x => (if i + 1 = k then h st (acc + x.toNat * 256 ^ i) else st, 0)
  | .data _, st, _ => (st, 0)

/-- The run: the sum of the counts, the final automaton state and the final decoration. -/
def runG {σ : Type} (f : WS → σ → UInt8 → σ × ℕ) : WS → σ → Bytes → ℕ × WS × σ
  | s, st, [] => (0, s, st)
  | s, st, x :: rest =>
    ((f s st x).2 + (runG f (wstep s x).1 (f s st x).1 rest).1, (runG f (wstep s x).1 (f s st x).1 rest).2)

/-- The same decoration folded over the parsed operations. -/
def foldD {σ : Type} (g : σ → UInt8 → σ × ℕ) (h : σ → ℕ → σ) : σ → List (UInt8 × Bytes) → ℕ × σ
  | st, [] => (0, st)
  | st, p :: r =>
    ((g st p.1).2 + (foldD g h (h (g st p.1).1 p.2.length) r).1, (foldD g h (h (g st p.1).1 p.2.length) r).2)

theorem wstep_opN (x : UInt8) : (wstep .op x).1 =
    if x.toNat < 0x4c then (if x.toNat = 0 then .op else .data x.toNat)
    else if x.toNat = 0x4c then .len 1 0 0 else if x.toNat = 0x4d then .len 2 0 0
    else if x.toNat = 0x4e then .len 4 0 0 else .op := by
  simp only [wstep, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, show (0x4c : UInt8).toNat = 0x4c from rfl,
    show (0x4d : UInt8).toNat = 0x4d from rfl, show (0x4e : UInt8).toNat = 0x4e from rfl,
    show (0 : UInt8).toNat = 0 from rfl]
  split_ifs <;> rfl

theorem opsD_cons (o : UInt8) (r : Bytes) : opsD (o :: r) =
    if o.toNat ≤ 0x4e then
      if r.length < (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)
      then ([], false) else
      if (r.drop (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)).length <
          (if o.toNat < 0x4c then o.toNat else le (r.take
            (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)))
      then ([], false) else
        ((o, ((r.drop (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)).take
            (if o.toNat < 0x4c then o.toNat else le (r.take
              (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0))))) ::
          (opsD ((r.drop (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)).drop
            (if o.toNat < 0x4c then o.toNat else le (r.take
              (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0))))).1,
         (opsD ((r.drop (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)).drop
            (if o.toNat < 0x4c then o.toNat else le (r.take
              (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0))))).2)
    else ((o, []) :: (opsD r).1, (opsD r).2) := by
  rw [opsD]
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, show (0x4c : UInt8).toNat = 0x4c from rfl,
    show (0x4d : UInt8).toNat = 0x4d from rfl, show (0x4e : UInt8).toNat = 0x4e from rfl]

/-! ### Skipping data and reading a length -/

theorem runG_data {σ : Type} (g : σ → UInt8 → σ × ℕ) (h : σ → ℕ → σ) : ∀ (l : Bytes) (r : ℕ) (st : σ), 1 ≤ r →
    runG (fGH g h) (.data r) st l =
      if r ≤ l.length then runG (fGH g h) .op st (l.drop r) else (0, .data (r - l.length), st)
  | [], r, st, hr => by simp [runG]; omega
  | x :: l, r, st, hr => by
    simp only [runG, wstep, fGH, zero_add, List.length_cons, Prod.mk.eta]
    by_cases h1 : r = 1
    · subst h1; simp
    · simp only [h1, ite_false]
      rw [runG_data g h l (r - 1) st (by omega)]
      have : List.drop r (x :: l) = List.drop (r - 1) l := by
        rw [show r = (r - 1) + 1 by omega, List.drop_succ_cons]; simp
      rw [this]
      by_cases h2 : r - 1 ≤ l.length
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega), show r - 1 - l.length = r - (l.length + 1) by omega]

theorem runG_len {σ : Type} (g : σ → UInt8 → σ × ℕ) (h : σ → ℕ → σ) :
    ∀ (l : Bytes) (k i acc : ℕ) (st : σ), i < k → k - i ≤ l.length →
    runG (fGH g h) (.len k i acc) st l =
      if acc + 256 ^ i * le (l.take (k - i)) = 0 then
        runG (fGH g h) .op (h st (acc + 256 ^ i * le (l.take (k - i)))) (l.drop (k - i))
      else runG (fGH g h) (.data (acc + 256 ^ i * le (l.take (k - i)))) (h st (acc + 256 ^ i * le (l.take (k - i))))
        (l.drop (k - i))
  | [], k, i, acc, st, hi, hf => by simp at hf; omega
  | x :: l, k, i, acc, st, hi, hf => by
    simp only [runG, wstep, fGH, zero_add, Prod.mk.eta]
    have hm : k - i = (k - i - 1) + 1 := by omega
    have htake : List.take (k - i) (x :: l) = x :: List.take (k - i - 1) l := by
      conv_lhs => rw [hm]
      simp
    have hdrop : List.drop (k - i) (x :: l) = List.drop (k - i - 1) l := by
      conv_lhs => rw [hm]
      simp
    rw [htake, hdrop, le_cons]
    by_cases h1 : i + 1 = k
    · subst h1
      have e1 : acc + x.toNat * 256 ^ i = acc + 256 ^ i * x.toNat := by ring
      simp only [ite_true, e1, Nat.add_sub_cancel_left, Nat.sub_self, List.take_zero, List.drop_zero,
        show le [] = 0 from rfl, mul_zero, add_zero]
      by_cases h0 : acc + 256 ^ i * x.toNat = 0 <;> simp only [h0, ite_true, ite_false]
    · simp only [h1, ite_false]
      simp only [List.length_cons] at hf
      rw [runG_len g h l k (i + 1) _ st (by omega) (by omega)]
      have hk : k - (i + 1) = k - i - 1 := by omega
      rw [hk]
      have hn : acc + x.toNat * 256 ^ i + 256 ^ (i + 1) * le (List.take (k - i - 1) l) =
          acc + 256 ^ i * (x.toNat + 256 * le (List.take (k - i - 1) l)) := by ring
      rw [hn]

/-- A length cut by the script's end: nothing is counted and the run does not end at an opcode. -/
theorem runG_len_short {σ : Type} (g : σ → UInt8 → σ × ℕ) (h : σ → ℕ → σ) :
    ∀ (l : Bytes) (k i acc : ℕ) (st : σ), l.length < k - i →
    (runG (fGH g h) (.len k i acc) st l).1 = 0 ∧ (runG (fGH g h) (.len k i acc) st l).2.1 ≠ .op
  | [], k, i, acc, st, _ => by simp [runG]
  | x :: l, k, i, acc, st, hf => by
    simp only [List.length_cons] at hf
    simp only [runG, wstep, fGH, zero_add, show ¬ (i + 1 = k) by omega, ite_false]
    exact runG_len_short g h l k (i + 1) _ st (by omega)

/-! ### The run is the fold over the parsed operations -/

/-- **The decorated run and `GetOp`.** With counts of 0 at push opcodes: the run's sum is the fold's; the
script parses exactly when the run ends at an opcode; and then the final decoration is the fold's. -/
theorem runG_opsD {σ : Type} (g : σ → UInt8 → σ × ℕ) (h : σ → ℕ → σ)
    (hpush : ∀ st (o : UInt8), o.toNat ≤ 0x4e → (g st o).2 = 0) : ∀ (s : Bytes) (st : σ),
    (runG (fGH g h) .op st s).1 = (foldD g h st (opsD s).1).1 ∧
    ((opsD s).2 = true ↔ (runG (fGH g h) .op st s).2.1 = .op) ∧
    ((opsD s).2 = true → (runG (fGH g h) .op st s).2.2 = (foldD g h st (opsD s).1).2) := by
  intro s
  induction hn : s.length using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    intro st
    match s, hn with
    | [], _ => simp [runG, opsD, foldD]
    | o :: r, hn =>
      have ihr : ∀ (t : Bytes), t.length < n → ∀ st', (runG (fGH g h) .op st' t).1 = (foldD g h st' (opsD t).1).1 ∧
          ((opsD t).2 = true ↔ (runG (fGH g h) .op st' t).2.1 = .op) ∧
          ((opsD t).2 = true → (runG (fGH g h) .op st' t).2.2 = (foldD g h st' (opsD t).1).2) :=
        fun t ht st' => ih _ ht t rfl st'
      have hr : r.length < n := by simp at hn; omega
      have hdrop : ∀ m, (r.drop m).length < n := fun m => by simp; omega
      have hdrop2 : ∀ m m', ((r.drop m).drop m').length < n := fun m m' => by simp; omega
      rw [opsD_cons]
      simp only [runG, wstep_opN, fGH]
      by_cases h1 : o.toNat < 0x4c
      · -- a direct push of `o` bytes
        have c0 := hpush st o (by omega)
        have e4c : ¬ o.toNat = 0x4c := by omega
        have e4d : ¬ o.toNat = 0x4d := by omega
        have e4e : ¬ o.toNat = 0x4e := by omega
        simp only [h1, if_true, e4c, e4d, e4e, if_false, show o.toNat ≤ 0x4e by omega, List.drop_zero,
          Nat.not_lt_zero, show ¬ (0x4c ≤ o.toNat) by omega, false_and, c0, zero_add]
        by_cases h0 : o.toNat = 0
        · simp only [h0, if_true, Nat.not_lt_zero, if_false, List.take_zero, List.drop_zero, foldD, List.length_nil,
            c0, zero_add]
          exact ihr r hr _
        · simp only [h0, if_false]
          rw [runG_data g h r o.toNat _ (by omega)]
          by_cases h2 : o.toNat ≤ r.length
          · simp only [h2, if_true, show ¬ r.length < o.toNat by omega, if_false, foldD, c0, zero_add,
              List.length_take, Nat.min_eq_left h2]
            exact ihr _ (hdrop _) _
          · simp [h2, show r.length < o.toNat by omega, foldD]
      · by_cases hk : o.toNat = 0x4c ∨ o.toNat = 0x4d ∨ o.toNat = 0x4e
        · -- `PUSHDATA1/2/4`: `k` length bytes, then the data
          have c0 := hpush st o (by omega)
          obtain ⟨k, hk1, hkd, hw⟩ : ∃ k, 1 ≤ k ∧
              (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0) = k ∧
              (if o.toNat = 0x4c then WS.len 1 0 0 else if o.toNat = 0x4d then .len 2 0 0
                else if o.toNat = 0x4e then .len 4 0 0 else .op) = .len k 0 0 := by
            rcases hk with e | e | e
            · exact ⟨1, le_rfl, by simp [e], by simp [e]⟩
            · exact ⟨2, by norm_num, by simp [e], by simp [e]⟩
            · exact ⟨4, by norm_num, by simp [e], by simp [e]⟩
          simp only [h1, if_false, hkd, hw, show o.toNat ≤ 0x4e by omega, if_true,
            show (0x4c ≤ o.toNat) by omega, and_self, c0, zero_add]
          by_cases hf : r.length < k
          · obtain ⟨a, b⟩ := runG_len_short g h r k 0 0 (g st o).1 (by omega)
            simp [hf, a, b, foldD]
          · rw [runG_len g h r k 0 0 _ (by omega) (by omega)]
            simp only [hf, if_false, Nat.sub_zero, pow_zero, one_mul, zero_add]
            by_cases hv : le (r.take k) = 0
            · simp only [hv, if_true, Nat.not_lt_zero, if_false, List.take_zero, List.drop_zero, foldD,
                List.length_nil, c0, zero_add]
              exact ihr _ (hdrop _) _
            · simp only [hv, if_false]
              rw [runG_data g h _ _ _ (by omega)]
              by_cases h2 : le (r.take k) ≤ (r.drop k).length
              · simp only [h2, if_true, show ¬ (r.drop k).length < le (r.take k) by omega, if_false, foldD, c0,
                  zero_add, List.length_take, Nat.min_eq_left h2]
                exact ihr _ (hdrop2 _ _) _
              · have h2' : ¬ le (r.take k) ≤ r.length - k := by simpa using h2
                simp [h2', show r.length - k < le (r.take k) by omega, foldD]
        · -- any other opcode
          have e4c : ¬ o.toNat = 0x4c := by omega
          have e4d : ¬ o.toNat = 0x4d := by omega
          have e4e : ¬ o.toNat = 0x4e := by omega
          simp only [h1, if_false, e4c, e4d, e4e, show ¬ o.toNat ≤ 0x4e by omega,
            and_false, foldD, List.length_nil]
          obtain ⟨a, b, c⟩ := ihr r hr (h (g st o).1 0)
          exact ⟨by rw [a], b, c⟩

/-! ### `opsD` and `ops` -/

/-- One step of `opsD`: it stops, or yields the first operation `(o, d)` and goes on with `t`, where
`d ++ t` is a suffix of the script. -/
theorem opsD_step (o : UInt8) (r : Bytes) : opsD (o :: r) = ([], false) ∨
    ∃ d t, opsD (o :: r) = ((o, d) :: (opsD t).1, (opsD t).2) ∧ t.length ≤ r.length ∧ d ++ t <:+ o :: r := by
  rw [opsD_cons]
  by_cases h1 : o.toNat ≤ 0x4e
  · simp only [h1, if_true]
    generalize (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0) = hdr
    generalize (if o.toNat < 0x4c then o.toNat else le (r.take hdr)) = nn
    by_cases ha : r.length < hdr
    · exact Or.inl (if_pos ha)
    · rw [if_neg ha]
      by_cases hb : (r.drop hdr).length < nn
      · exact Or.inl (if_pos hb)
      · rw [if_neg hb]
        refine Or.inr ⟨_, _, rfl, by simp, ?_⟩
        rw [List.take_append_drop]
        exact (List.drop_suffix _ r).trans (List.suffix_cons o r)
  · simp only [h1, if_false]
    exact Or.inr ⟨[], r, rfl, le_rfl, List.suffix_cons o r⟩

theorem ops_cons (o : UInt8) (r : Bytes) : ops (o :: r) =
    if o.toNat ≤ 0x4e then
      if r.length < (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)
      then [] else
      if (r.drop (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)).length <
          (if o.toNat < 0x4c then o.toNat else le (r.take
            (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)))
      then [] else
        o :: ops ((r.drop (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0)).drop
            (if o.toNat < 0x4c then o.toNat else le (r.take
              (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0))))
    else o :: ops r := by
  rw [ops]
  simp only [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt, ← UInt8.toNat_inj, show (0x4c : UInt8).toNat = 0x4c from rfl,
    show (0x4d : UInt8).toNat = 0x4d from rfl, show (0x4e : UInt8).toNat = 0x4e from rfl]
  by_cases h1 : o.toNat < 0x4c
  · have e4c : ¬ o.toNat = 0x4c := by omega
    have e4d : ¬ o.toNat = 0x4d := by omega
    have e4e : ¬ o.toNat = 0x4e := by omega
    simp [h1, e4c, e4d, e4e, show o.toNat ≤ 0x4e by omega]
  · by_cases h2 : o.toNat = 0x4c
    · simp only [h2]
      by_cases hf : r.length < 1
      · simp [hf, show ¬ 1 ≤ r.length by omega]
      · simp [hf, show 1 ≤ r.length by omega]
    by_cases h3 : o.toNat = 0x4d
    · simp only [h3]
      by_cases hf : r.length < 2
      · simp [hf, show ¬ 2 ≤ r.length by omega]
      · simp [hf, show 2 ≤ r.length by omega]
    by_cases h4 : o.toNat = 0x4e
    · simp only [h4]
      by_cases hf : r.length < 4
      · simp [hf, show ¬ 4 ≤ r.length by omega]
      · simp [hf, show 4 ≤ r.length by omega]
    simp [h1, h2, h3, h4, show ¬ o.toNat ≤ 0x4e by omega]

/-- **`opsD` lists the opcodes of `ops`.** -/
theorem opsD_ops (s : Bytes) : (opsD s).1.map Prod.fst = ops s := by
  induction hn : s.length using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    match s, hn with
    | [], _ => simp [opsD, ops]
    | o :: r, hn =>
      have ihr : ∀ t : Bytes, t.length < n → (opsD t).1.map Prod.fst = ops t := fun t ht => ih _ ht t rfl
      have hr : r.length < n := by simp at hn; omega
      rw [opsD_cons, ops_cons]
      by_cases h1 : o.toNat ≤ 0x4e
      · simp only [h1, if_true]
        generalize (if o.toNat = 0x4c then 1 else if o.toNat = 0x4d then 2 else if o.toNat = 0x4e then 4 else 0) = hdr
        generalize (if o.toNat < 0x4c then o.toNat else le (r.take hdr)) = nn
        by_cases ha : r.length < hdr
        · rw [if_pos ha, if_pos ha]; rfl
        · rw [if_neg ha, if_neg ha]
          by_cases hb : (r.drop hdr).length < nn
          · rw [if_pos hb, if_pos hb]; rfl
          · rw [if_neg hb, if_neg hb]
            simp only [List.map_cons]; rw [ihr _ (by simp; omega)]
      · simp only [h1, if_false, List.map_cons]; rw [ihr _ hr]

/-! ### The accurate count -/

/-- What a multisig counts after opcode `o`: `OP_1 … OP_16` give 1 … 16, anything else 20. -/
def dvW (o : UInt8) : ℕ := if 0x51 ≤ o.toNat ∧ o.toNat ≤ 0x60 then o.toNat - 0x50 else 20

/-- An opcode's accurate count when a multisig counts `pv`. -/
def accW (pv : ℕ) (o : UInt8) : ℕ :=
  if o.toNat = 0xac ∨ o.toNat = 0xad then 1 else if o.toNat = 0xae ∨ o.toNat = 0xaf then pv else 0

def gA (pv : ℕ) (o : UInt8) : ℕ × ℕ := (dvW o, accW pv o)

/-- The accurate walker: the decoration is the value a multisig would count. -/
def fA : WS → ℕ → UInt8 → ℕ × ℕ := fGH gA (fun st _ => st)

theorem accGo_fold : ∀ (l : List (UInt8 × Bytes)) (last : UInt8),
    (foldD gA (fun st _ => st) (dvW last) l).1 = accGo last (l.map Prod.fst)
  | [], _ => rfl
  | p :: l, last => by
    simp only [foldD, List.map_cons, accGo, gA]
    rw [accGo_fold l p.1]
    congr 1
    simp only [accW, dvW, UInt8.le_iff_toNat_le, ← UInt8.toNat_inj, show (0xac : UInt8).toNat = 0xac from rfl,
      show (0xad : UInt8).toNat = 0xad from rfl, show (0xae : UInt8).toNat = 0xae from rfl,
      show (0xaf : UInt8).toNat = 0xaf from rfl, show (0x51 : UInt8).toNat = 0x51 from rfl,
      show (0x60 : UInt8).toNat = 0x60 from rfl]

/-- **The accurate walker counts `GetSigOpCount(true)`.** -/
theorem acc_run (s : Bytes) : (runG fA .op 20 s).1 = sigOpsAccurate s := by
  have h := (runG_opsD gA (fun st _ => st) (fun st o ho => by
    simp only [gA, accW]; rw [if_neg (by omega), if_neg (by omega)]) s 20).1
  rw [fA, h, show (20 : ℕ) = dvW 0xff from rfl, accGo_fold, opsD_ops]; rfl

/-! ### `IsPushOnly` -/

def gH (_ : Unit) (o : UInt8) : Unit × ℕ := ((), if 0x60 < o.toNat then 1 else 0)

/-- The walker counting the opcodes above `OP_16`. -/
def fH : WS → Unit → UInt8 → Unit × ℕ := fGH gH (fun st _ => st)

theorem hi_fold : ∀ (l : List (UInt8 × Bytes)),
    (foldD gH (fun st _ => st) () l).1 = 0 ↔ (l.all fun p => p.1 ≤ 0x60) = true
  | [] => by simp [foldD]
  | p :: l => by
    simp only [foldD, gH, List.all_cons, Bool.and_eq_true, decide_eq_true_eq, Nat.add_eq_zero_iff, hi_fold l,
      UInt8.le_iff_toNat_le, show (0x60 : UInt8).toNat = 0x60 from rfl]
    constructor
    · rintro ⟨a, b⟩; exact ⟨by by_contra hc; rw [if_pos (by omega)] at a; omega, b⟩
    · rintro ⟨a, b⟩; exact ⟨by rw [if_neg (by omega)], b⟩

/-- **`IsPushOnly`**: the run ends at an opcode and saw none above `OP_16`. -/
theorem po_run (s : Bytes) : pushOnly s = true ↔ (runG fH .op () s).2.1 = .op ∧ (runG fH .op () s).1 = 0 := by
  obtain ⟨a, b, -⟩ := runG_opsD gH (fun st _ => st) (fun st o ho => by
    simp only [gH]; rw [if_neg (by omega)]) s ()
  unfold pushOnly
  rw [Bool.and_eq_true, b, fH, a, hi_fold]

/-! ### The last push -/

def gL (l : ℕ) (_ : UInt8) : ℕ × ℕ := (l, 0)

/-- The walker remembering the length of the last operation's data. -/
def fL : WS → ℕ → UInt8 → ℕ × ℕ := fGH gL (fun _ v => v)

theorem last_fold : ∀ (l : List (UInt8 × Bytes)) (st : ℕ),
    (foldD gL (fun _ v => v) st l).2 = (l.getLast?.map fun p => p.2.length).getD st
  | [], _ => rfl
  | p :: l, st => by
    simp only [foldD, gL]
    rw [last_fold l, List.getLast?_cons]
    cases l.getLast? <;> simp

/-- **The last operation's data length** is the decoration a parsed script's run ends with. -/
theorem last_run (s : Bytes) (hp : (opsD s).2 = true) : (runG fL .op 0 s).2.2 = (lastPush s).length := by
  have h := (runG_opsD gL (fun _ v => v) (fun st o _ => rfl) s 0).2.2 hp
  rw [fL, h, last_fold, lastPush]
  cases (opsD s).1.getLast? <;> simp

/-- In a script that parses, the last operation's data is the script's end. -/
theorem lastPush_suffix (s : Bytes) (hp : (opsD s).2 = true) : lastPush s <:+ s := by
  have key : ∀ n (s : Bytes), s.length = n → (opsD s).2 = true → s ≠ [] →
      ∃ e, (opsD s).1.getLast? = some e ∧ e.2 <:+ s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro s hn hp hne
      match s, hn, hne with
      | o :: r, hn, _ =>
        rcases opsD_step o r with e | ⟨d, t, e, hlen, hsuf⟩
        · rw [e] at hp; exact absurd hp (by simp)
        · rw [e] at hp ⊢
          by_cases ht : t = []
          · subst ht
            refine ⟨(o, d), by simp [opsD], ?_⟩
            simpa using hsuf
          · obtain ⟨e', he', hs'⟩ := ih t.length (by simp at hn; omega) t rfl hp ht
            refine ⟨e', ?_, hs'.trans ((List.suffix_append d t).trans hsuf)⟩
            rw [List.getLast?_cons, he']; rfl
  by_cases hne : s = []
  · subst hne; simp [lastPush, opsD]
  · obtain ⟨e, he, hs⟩ := key s.length s rfl hp hne
    rw [lastPush, he]; exact hs

/-- The count of opcodes above `OP_16` is at most the bytes walked. -/
theorem hi_run_le : ∀ (l : Bytes) (s : WS) (st : Unit), (runG fH s st l).1 ≤ l.length
  | [], _, _ => by simp [runG]
  | x :: l, s, st => by
    simp only [runG, List.length_cons]
    have h1 : (fH s st x).2 ≤ 1 := by
      cases s <;> simp only [fH, fGH, gH, le_refl, Nat.zero_le]
      split_ifs <;> omega
    have := hi_run_le l (wstep s x).1 (fH s st x).1
    omega

/-- A parsed script's run ends at an opcode, whatever the decoration. -/
theorem last_ws (s : Bytes) : (opsD s).2 = true ↔ (runG fL .op 0 s).2.1 = .op :=
  (runG_opsD gL (fun _ v => v) (fun _ _ _ => rfl) s 0).2.1

/-- The accurate count is at most 20 per byte. -/
theorem acc_run_le : ∀ (l : Bytes) (s : WS) (pv : ℕ), pv ≤ 20 → (runG fA s pv l).1 ≤ 20 * l.length
  | [], _, _, _ => by simp [runG]
  | x :: l, s, pv, hpv => by
    simp only [runG, List.length_cons]
    have h1 : (fA s pv x).2 ≤ 20 ∧ (fA s pv x).1 ≤ 20 := by
      cases s with
      | op =>
        simp only [fA, fGH, gA, accW, dvW, ite_self]
        constructor <;> split_ifs <;> omega
      | len k i acc => simp only [fA, fGH, ite_self]; omega
      | data d => simp only [fA, fGH]; omega
    have := acc_run_le l (wstep s x).1 (fA s pv x).1 h1.2
    omega

theorem acc_le (s : Bytes) : sigOpsAccurate s ≤ 20 * s.length := by
  rw [← acc_run]; exact acc_run_le s .op 20 le_rfl

end StarkedAir.Spec.ConnectRules
