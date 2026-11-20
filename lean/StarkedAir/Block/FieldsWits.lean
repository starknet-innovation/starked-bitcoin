/-
**Witness scripts to count (CONNECT-RULES step 3).** A witness stack is a count row and its item rows.
A stack row marked `WS` passes the mark down its items, and the last item, if not empty, is requested as
an accurate span (`WQ · (1 − ZV)`). `stack_q`: over a stack's rows, the requested spans' accurate counts
sum to `lastAcc` of the stack's items when the stack is marked, to 0 otherwise. `wq_sum`: over all rows.
-/
import StarkedAir.Block.FieldsScripts
import StarkedAir.Block.TxWits
import StarkedAir.Block.TxRows
import StarkedAir.Spec.SigClass

namespace StarkedAir.Spec.Block

/-- The tokens `itemsT` reads are the items, in order. -/
theorem itemsT_toks : ∀ (k : ℕ) (ts : List Tok) (w : List Bytes) (rest : List Tok),
    itemsT k ts = some (w, rest) → ts = w.map Tok.witem ++ rest ∧ w.length = k
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
        obtain ⟨e, hl⟩ := itemsT_toks k ts w' rest' hr
        exact ⟨by rw [e]; simp, by simp [hl]⟩
    | _ => simp [itemsT] at h

end StarkedAir.Spec.Block

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)
open StarkedAir.Spec.ConnectRules (sigOpsAccurate lastAcc)

/-- The items of the witness stack whose count row is `c`. -/
def stackItems (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (m c : ℕ) : List Spec.Block.Bytes :=
  ((Spec.Block.itemsT (M VAL c).val (toksFrom M R m (c + 1))).map Prod.fst).getD []

/-- A row's requested witness script: its accurate count when `WQ · (1 − ZV) = 1`. -/
noncomputable def qN (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (r : ℕ) : ℕ :=
  if M WQ r * (1 - M ZV r) = 1 then sigOpsAccurate (slice R (M SSC r).val (M VAL r).val) else 0

section Wits

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
include hsat hcs hmn hpad hfit

/-- A row whose token is a witness item is an item row, and the item is its bytes. -/
theorem witem_of_tok {j : ℕ} (hj : j < n) {it : Spec.Block.Bytes} (h : tokOf M R j = .witem it) :
    M K_WITEM j = 1 ∧ it = slice R ((M START j).val + prefOf M j) (M VAL j).val := by
  have hw : (tokOf M R j).isWit = true := by rw [h]; rfl
  rcases tokk_wit hw with g | g
  · rw [tok_wcnt hsat R hcs hmn hpad hfit hj g] at h; cases h
  · rw [tok_witem hsat R hcs hmn hpad hfit hj g] at h
    exact ⟨g, by injection h with h; exact h.symm⟩

/-- An item row's script start: `SSC = START + pref`. -/
theorem ssc_witem {r : ℕ} (hr : r < m) (h1 : M K_WITEM r = 1) :
    (M SSC r).val = (M START r).val + prefOf M r := by
  have hrn : r < n := by omega
  have e := chk_defn hsat (a := SSC) (e := .add (.add (k START) (k OFF)) pref) (by simp [chkC, totalsC]) hrn
  obtain ⟨hoff, -⟩ := kind_vals hsat hrn (a := K_WITEM) (by simp [K_WITEM]) h1
  have ka := kinds_at hsat hrn (a := K_WITEM) (by simp [K_WITEM]) h1
  have hlp : M K_LOCK r + M K_PAD r = 0 := by
    rw [ka K_LOCK (by simp [K_LOCK]), ka K_PAD (by simp [K_PAD])]; simp [K_WITEM, K_LOCK, K_PAD]
  have pc := pref_cast hsat hrn
  rw [if_pos hlp] at pc
  have hpre : 1 ≤ prefOf M r ∧ prefOf M r ≤ 5 := by unfold prefOf; split_ifs <;> omega
  have hst := start_lt hsat hrn
  have hoffv : offN K_WITEM (M SEG r).val = 0 := by simp [offN, K_WITEM, K_BLK, K_TXH, K_IN, K_OUT]
  have hv : M SSC r = (((M START r).val + prefOf M r : ℕ) : F) := by
    rw [e]
    simp only [Expr.eval, ev_k hrn, pref, eval_cst, hoff, hoffv]
    push_cast
    rw [pc, ZMod.natCast_zmod_val]; ring
  rw [hv, ZMod.val_natCast_of_lt (lt_P (by omega))]

/-- **A stack's rows.** The count row `r` is followed by its items' rows, each an item row carrying its
item; only the last ends the stack. -/
theorem stack_rows {r : ℕ} (hr : r < m) (hw : M K_WCNT r = 1) :
    ∃ items re, Spec.Block.itemsT (M VAL r).val (toksFrom M R m (r + 1)) = some (items, toksFrom M R m (re + 1)) ∧
      re = r + items.length ∧ re < m ∧ M Z1 re = 1 ∧ (M K_WCNT re = 1 ∨ M K_WITEM re = 1) ∧ M WINL re = M WINL r ∧
      (∀ i < items.length, M K_WITEM (r + 1 + i) = 1 ∧ items[i]? = some (slice R ((M START (r + 1 + i)).val +
        prefOf M (r + 1 + i)) (M VAL (r + 1 + i)).val)) ∧
      (∀ i, i + 1 < items.length → M Z1 (r + 1 + i) = 0) := by
  obtain ⟨items, re, hit, hre, hrem, hk, hz, w1, -⟩ := stack_sim hsat R hcs hmn hpad hfit hr hw
  obtain ⟨hts, -⟩ := Spec.Block.itemsT_toks _ _ _ _ hit
  have hlen := congrArg List.length hts
  simp only [toksFrom_length, List.length_append, List.length_map] at hlen
  have hre' : re = r + items.length := by omega
  have hrow : ∀ i < items.length, M K_WITEM (r + 1 + i) = 1 ∧ items[i]? = some (slice R ((M START (r + 1 + i)).val +
      prefOf M (r + 1 + i)) (M VAL (r + 1 + i)).val) := by
    intro i hi
    have g : (toksFrom M R m (r + 1))[i]? = (items.map Spec.Block.Tok.witem ++ toksFrom M R m (re + 1))[i]? := by
      rw [← hts]
    rw [toksFrom_get (by omega), List.getElem?_append_left (by simpa using hi), List.getElem?_map,
      List.getElem?_eq_getElem hi] at g
    simp only [Option.map_some, Option.some.injEq] at g
    obtain ⟨a, b⟩ := witem_of_tok hsat R hcs hmn hpad hfit (j := r + 1 + i) (by omega) g
    exact ⟨a, by rw [List.getElem?_eq_getElem hi, b]⟩
  refine ⟨items, re, hit, hre', hrem, hz, hk, w1, hrow, fun i hi => ?_⟩
  have h1 := (hrow i (by omega)).1
  have h2 := (hrow (i + 1) hi).1
  have hj : r + 1 + i + 1 < n := by omega
  have t := (trans_all hsat hj).2.2.2.2.2.1
  have ka := kinds_at hsat (show r + 1 + i < n by omega) (a := K_WITEM) (by simp [K_WITEM]) h1
  rw [show r + 1 + (i + 1) = r + 1 + i + 1 by omega] at h2
  rw [h2, h1, ka K_WCNT (by simp [K_WCNT])] at t
  simp only [K_WCNT, K_WITEM] at t
  norm_num at t
  linear_combination t

omit hcs hmn hpad hfit in
theorem wq_eq {j : ℕ} (hj : j < n) : M WQ j = M K_WITEM j * (M WS j * M Z1 j) := by
  have := defn hsat (mem_sig (c := .sub (k WQ) (.mul (k K_WITEM) (.mul (k WS) (k Z1)))) (by simp [sigC])) hj
  simpa only [Expr.eval, ev_k hj] using this

omit hcs hmn hpad hfit in
/-- A row that is not an item row requests no witness script. -/
theorem qN_zero {j : ℕ} (hj : j < n) (h : M K_WITEM j = 0) : qN M R j = 0 := by
  unfold qN
  rw [if_neg]
  rw [wq_eq hsat hj, h]; simp

/-- **A stack's requests.** Over the rows of the stack at count row `r`, the requested witness scripts'
accurate counts sum to `lastAcc` of the stack's items when the stack is marked (`WS`), to 0 otherwise. -/
theorem stack_q {r : ℕ} (hr : r < m) (hw : M K_WCNT r = 1) :
    ∃ items re, Spec.Block.itemsT (M VAL r).val (toksFrom M R m (r + 1)) = some (items, toksFrom M R m (re + 1)) ∧
      re = r + items.length ∧ re < m ∧ M Z1 re = 1 ∧ (M K_WCNT re = 1 ∨ M K_WITEM re = 1) ∧ M WINL re = M WINL r ∧
      (∀ i < items.length, M K_WITEM (r + 1 + i) = 1) ∧
      ∑ i ∈ Finset.range (items.length + 1), qN M R (r + i) = if M WS r = 1 then lastAcc items else 0 := by
  obtain ⟨items, re, hit, hre, hrem, hz, hk, w1, hrow, hz0⟩ := stack_rows hsat R hcs hmn hpad hfit hr hw
  refine ⟨items, re, hit, hre, hrem, hz, hk, w1, fun i hi => (hrow i hi).1, ?_⟩
  have hrn : r < n := by omega
  have kw0 : M K_WITEM r = 0 :=
    kinds_at hsat hrn (a := K_WCNT) (by simp [K_WCNT]) hw K_WITEM (by simp [K_WITEM]) |>.trans (by simp [K_WCNT, K_WITEM])
  -- the mark passes down the items
  have ws : ∀ i < items.length, M WS (r + 1 + i) = M WS r := by
    intro i
    induction i with
    | zero =>
      intro hi
      have c := sat hsat (mem_sig (c := .mul (k K_WITEM) (.sub (k WS) (kp WS))) (by simp [sigC]))
        (show r + 1 < n by omega)
      simp only [Expr.eval, ev_k (show r + 1 < n by omega), ev_kp (show r + 1 < n by omega)] at c
      have h1 := (hrow 0 hi).1
      rw [Nat.add_zero] at h1 ⊢
      rw [h1, one_mul] at c; linear_combination c
    | succ i ih =>
      intro hi
      have hj : r + 1 + i + 1 < n := by omega
      have c := sat hsat (mem_sig (c := .mul (k K_WITEM) (.sub (k WS) (kp WS))) (by simp [sigC])) hj
      simp only [Expr.eval, ev_k hj, ev_kp hj] at c
      have h1 := (hrow (i + 1) hi).1
      rw [show r + 1 + (i + 1) = r + 1 + i + 1 by omega] at h1 ⊢
      rw [h1, one_mul] at c
      rw [← ih (by omega)]; linear_combination c
  rw [Finset.sum_range_succ', Nat.add_zero, qN_zero hsat R hrn kw0, add_zero]
  rw [Finset.sum_congr rfl (fun i _ => show qN M R (r + (i + 1)) = qN M R (r + 1 + i) by
    rw [show r + (i + 1) = r + 1 + i by omega])]
  rcases Nat.eq_zero_or_pos items.length with h0 | hpos
  · have : items = [] := List.length_eq_zero_iff.mp h0
    subst this; simp [lastAcc]
  obtain ⟨L, hL⟩ : ∃ L, items.length = L + 1 := ⟨items.length - 1, by omega⟩
  rw [hL, Finset.sum_range_succ]
  -- the items before the last request nothing
  have hmid : ∑ i ∈ Finset.range L, qN M R (r + 1 + i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hiL := Finset.mem_range.mp hi
    unfold qN
    rw [if_neg]
    rw [wq_eq hsat (show r + 1 + i < n by omega), hz0 i (by omega)]; simp
  rw [hmid, zero_add]
  -- the last item
  obtain ⟨hkL, hitem⟩ := hrow L (by omega)
  have hreL : re = r + 1 + L := by omega
  rw [← hreL] at hkL hitem ⊢
  have hren : re < n := by omega
  have hws : M WS re = M WS r := by rw [hreL]; exact ws L (by omega)
  have hwq : M WQ re = M WS r := by rw [wq_eq hsat hren, hkL, hws, hz]; ring
  have hlast : lastAcc items = sigOpsAccurate (slice R ((M START re).val + prefOf M re) (M VAL re).val) := by
    unfold lastAcc
    rw [List.getLast?_eq_getElem?, show items.length - 1 = L by omega, hitem]; rfl
  have hssc := ssc_witem hsat R hcs hmn hpad hfit hrem hkL
  obtain ⟨hzb, hz1, -⟩ := zv_spec hsat hren
  have wsb := bool_of hsat (mem_sig (c := boolC (k WS)) (by simp [sigC])) hrn
  unfold qN
  rw [hwq, hlast, hssc]
  rcases wsb with w0 | w1'
  · rw [w0, if_neg (by simp), if_neg (by simp)]
  · rw [w1', if_pos rfl]
    rcases hzb with z0 | z1
    · rw [z0, if_pos (by ring)]
    · rw [z1, if_neg (by simp), hz1 z1]
      simp [slice, sigOpsAccurate, Spec.Block.ops, Spec.ConnectRules.accGo]

/-- **All the requested witness scripts.** The requests' accurate counts over all rows are the marked
stacks' `lastAcc`. -/
theorem wq_sum : ∑ r ∈ Finset.range m, qN M R r =
    ∑ c ∈ Finset.range m, (if M K_WCNT c = 1 ∧ M WS c = 1 then lastAcc (stackItems M R m c) else 0) := by
  have claim : ∀ d r, m - r = d → r ≤ m → M K_WITEM r = 0 →
      ∑ j ∈ Finset.Ico r m, qN M R j =
        ∑ j ∈ Finset.Ico r m, (if M K_WCNT j = 1 ∧ M WS j = 1 then lastAcc (stackItems M R m j) else 0) := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro r hd hrm hk0
      rcases Nat.eq_or_lt_of_le hrm with rfl | hr
      · simp
      have hrn : r < n := by omega
      rcases kind_bool hsat (c := K_WCNT) (by simp [kinds, K_WCNT]) hrn with c0 | c1
      · -- not a stack: the next row is no item
        have hr1 : r + 1 < n := by omega
        have t := (trans_all hsat hr1).2.2.2.2.2.1
        rw [c0, hk0] at t
        have hk1 : M K_WITEM (r + 1) = 0 := by rw [t]; ring
        have ih' := ih (m - (r + 1)) (by omega) (r + 1) rfl (by omega) hk1
        rw [Finset.sum_eq_sum_Ico_succ_bot hr, Finset.sum_eq_sum_Ico_succ_bot hr, ih', qN_zero hsat R hrn hk0,
          if_neg (by rw [c0]; simp)]
      · obtain ⟨items, re, hit, hre, hrem, hz, hk, -, hitems, hsum⟩ := stack_q hsat R hcs hmn hpad hfit hr c1
        have hr1 : re + 1 < n := by omega
        have t := (trans_all hsat hr1).2.2.2.2.2.1
        have hk1 : M K_WITEM (re + 1) = 0 := by
          rw [t, hz]; ring
        have ih' := ih (m - (re + 1)) (by omega) (re + 1) rfl (by omega) hk1
        rw [← Finset.sum_Ico_consecutive _ (show r ≤ re + 1 by omega) (show re + 1 ≤ m by omega),
          ← Finset.sum_Ico_consecutive (fun j => if M K_WCNT j = 1 ∧ M WS j = 1 then lastAcc (stackItems M R m j) else 0)
            (show r ≤ re + 1 by omega) (show re + 1 ≤ m by omega), ih']
        congr 1
        rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range, show re + 1 - r = items.length + 1 by omega, hsum,
          Finset.sum_range_succ', Nat.add_zero]
        have hz' : ∑ i ∈ Finset.range items.length,
            (if M K_WCNT (r + (i + 1)) = 1 ∧ M WS (r + (i + 1)) = 1 then lastAcc (stackItems M R m (r + (i + 1))) else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          have hiL := Finset.mem_range.mp hi
          have h1 := hitems i hiL
          rw [show r + 1 + i = r + (i + 1) by omega] at h1
          have := kinds_at hsat (show r + (i + 1) < n by omega) (a := K_WITEM) (by simp [K_WITEM]) h1 K_WCNT
            (by simp [K_WCNT])
          rw [if_neg]
          rintro ⟨hc, -⟩
          rw [this] at hc; simp [K_WCNT, K_WITEM] at hc
        rw [hz', zero_add]
        have hst : stackItems M R m r = items := by unfold stackItems; rw [hit]; rfl
        rw [hst]
        by_cases hws : M WS r = 1
        · rw [if_pos hws, if_pos ⟨c1, hws⟩]
        · rw [if_neg hws, if_neg (fun h => hws h.2)]
  have h0 : M K_WITEM 0 = 0 := by
    have hn0 : 0 < n := by omega
    exact kinds_at hsat hn0 (a := K_BLK) (by simp [K_BLK]) (first_blk hsat hn0) K_WITEM (by simp [K_WITEM]) |>.trans
      (by simp [K_BLK, K_WITEM])
  have := claim m 0 (by simp) (by omega) h0
  rwa [← Finset.range_eq_Ico] at this

/-- **The stacks of a witness section.** From a count row `r` with `w + 1` stacks left, parsed by `witsT`
into `ws`: the parse ends at a row `r'`; every count row `c` before it has between 1 and `w + 1` stacks
left, and its stack is `ws[w + 1 − left]`; all rows in between are witness rows. -/
theorem wits_rows : ∀ w r, r < m → M K_WCNT r = 1 → (M WINL r).val = w + 1 →
    ∀ (ws : List (List Spec.Block.Bytes)) (rest : List Spec.Block.Tok),
    Spec.Block.witsT (w + 1) (toksFrom M R m r) = some (ws, rest) →
    ∃ r', r < r' ∧ r' ≤ m ∧ rest = toksFrom M R m r' ∧
      (∀ c, r ≤ c → c < r' → M K_WCNT c = 1 → 1 ≤ (M WINL c).val ∧ (M WINL c).val ≤ w + 1 ∧
        stackItems M R m c = ws.getD (w + 1 - (M WINL c).val) []) := by
  intro w
  induction w with
  | zero =>
    intro r hr hw hwl ws rest hws
    obtain ⟨items, re, hit, hre, hrem, hz, hk, w1, hrow, -⟩ := stack_rows hsat R hcs hmn hpad hfit hr hw
    rw [toksFrom_cons hr, tok_wcnt hsat R hcs hmn hpad hfit (by omega) hw] at hws
    simp only [Spec.Block.witsT] at hws
    split_ifs at hws with hc
    rw [hit] at hws
    simp only [Spec.Block.witsT, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hws
    obtain ⟨rfl, rfl⟩ := hws
    refine ⟨re + 1, by omega, by omega, rfl, fun c h1 h2 hcw => ?_⟩
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · refine ⟨by omega, by omega, ?_⟩
      rw [hwl]; simp [stackItems, hit]
    · exfalso
      have h := (hrow (c - (r + 1)) (by omega)).1
      rw [show r + 1 + (c - (r + 1)) = c by omega] at h
      have := kinds_at hsat (show c < n by omega) (a := K_WITEM) (by simp [K_WITEM]) h K_WCNT (by simp [K_WCNT])
      rw [hcw] at this; simp [K_WCNT, K_WITEM] at this
  | succ w ih =>
    intro r hr hw hwl ws rest hws
    obtain ⟨items, re, hit, hre, hrem, hz, hk, w1, hrow, -⟩ := stack_rows hsat R hcs hmn hpad hfit hr hw
    obtain ⟨hlt, -, -, -, -, -, hnext⟩ := stack_end hsat R hcs hmn hpad hfit hrem hk hz (w := w + 1)
      (by rw [w1]; exact hwl)
    obtain ⟨hw1, hwl1⟩ := hnext (by omega)
    rw [toksFrom_cons hr, tok_wcnt hsat R hcs hmn hpad hfit (by omega) hw] at hws
    simp only [Spec.Block.witsT] at hws
    split_ifs at hws with hc
    rw [hit] at hws
    dsimp only at hws
    cases hws' : Spec.Block.witsT (w + 1) (toksFrom M R m (re + 1)) with
    | none => rw [hws'] at hws; simp at hws
    | some p =>
      obtain ⟨ws', rest'⟩ := p
      rw [hws'] at hws
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hws
      obtain ⟨rfl, rfl⟩ := hws
      obtain ⟨r', hr', hr'm, hrest, hall⟩ := ih (re + 1) hlt hw1 hwl1 ws' rest' hws'
      refine ⟨r', by omega, hr'm, hrest, fun c h1 h2 hcw => ?_⟩
      rcases Nat.eq_or_lt_of_le h1 with rfl | hlt'
      · refine ⟨by omega, by omega, ?_⟩
        rw [hwl]; simp [stackItems, hit]
      · by_cases hcre : c ≤ re
        · exfalso
          have h := (hrow (c - (r + 1)) (by omega)).1
          rw [show r + 1 + (c - (r + 1)) = c by omega] at h
          have := kinds_at hsat (show c < n by omega) (a := K_WITEM) (by simp [K_WITEM]) h K_WCNT (by simp [K_WCNT])
          rw [hcw] at this; simp [K_WCNT, K_WITEM] at this
        · obtain ⟨a, b, e⟩ := hall c (by omega) h2 hcw
          refine ⟨a, by omega, ?_⟩
          rw [e, show w + 1 + 1 - (M WINL c).val = (w + 1 - (M WINL c).val) + 1 by omega]
          simp

/-- **A row's transaction.** Every row after the block row and before the padding lies between a
transaction's head row `rh` and its lock-time row `ρ`. -/
theorem row_tx (hnp : ∀ r < m, M K_PAD r = 0) {c : ℕ} (h1 : 1 ≤ c) (hc : c < m) :
    ∃ rh ρ tx, rh ≤ c ∧ c ≤ ρ ∧ ρ < m ∧ M K_TXH rh = 1 ∧ M K_LOCK ρ = 1 ∧
      Spec.Block.txT (toksFrom M R m rh) = some (tx, toksFrom M R m (ρ + 1)) ∧
      (∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) ∧ (∀ j, rh ≤ j → j < ρ → M K_LOCK j = 0) := by
  classical
  have hn0 : 0 < n := by omega
  have ht1 : M K_TXH 1 = 1 := (next_kind hsat (show 0 + 1 < n by omega)).1 (first_blk hsat hn0)
  set rh := Nat.findGreatest (fun r => M K_TXH r = 1) c with hrh
  have hspec : M K_TXH rh = 1 := Nat.findGreatest_spec (P := fun r => M K_TXH r = 1) h1 ht1
  have hle : rh ≤ c := Nat.findGreatest_le c
  have hmax : ∀ k, rh < k → k ≤ c → ¬ M K_TXH k = 1 := fun k a b => Nat.findGreatest_is_greatest a b
  obtain ⟨tx, r', rw, v, nIn, l, htx, hrw1, hrw2, hr'm, hl, -, -, -, -, -, -, -, notxh, nolock, -⟩ :=
    tx_cols hsat R hcs hmn hpad hfit (show rh < m by omega) hspec
  refine ⟨rh, r', tx, hle, ?_, hr'm, hspec, hl, htx, notxh, nolock⟩
  by_contra hcon
  have hr1 : r' + 1 < n := by omega
  have nk := next_kind hsat hr1
  rcases (z1_spec hsat (show r' < n by omega)).1 with z0 | z1
  · exact hmax (r' + 1) (by omega) (by omega) (nk.2.2.2.2.2.2.2.2.2.2.1 hl z0)
  · have := nk.2.2.2.2.2.2.2.2.2.2.2.1 hl z1
    rw [hnp (r' + 1) (by omega)] at this; exact zero_ne_one this

omit hcs hpad hfit in
/-- Within a transaction's rows, the segwit flag and the input count are the head row's. -/
theorem tx_const {rh ρ : ℕ} (hρ : ρ < m) (notxh : ∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) :
    ∀ j, rh ≤ j → j ≤ ρ → M SEG j = M SEG rh ∧ M NIN j = M NIN rh := by
  intro j h1
  induction j, h1 using Nat.le_induction with
  | base => intro _; exact ⟨rfl, rfl⟩
  | succ j hj ih =>
    intro h2
    obtain ⟨a, b⟩ := ih (by omega)
    obtain ⟨-, -, c3, -, -, -, -, c8, -⟩ := counters hsat (show j + 1 < n by omega)
    have hT := notxh (j + 1) (by omega) h2
    exact ⟨by rw [c8 hT, a], by rw [c3 hT, b]⟩

/-- **An input row's place.** An input row is row `rh + 1 + i` of a transaction with head row `rh` and
lock-time row `ρ`: it carries input `i`, has `nIn − i` inputs left, and the transaction's segwit flag. -/
theorem in_tx (hnp : ∀ r < m, M K_PAD r = 0) {c : ℕ} (hc : c < m) (hk : M K_IN c = 1) :
    ∃ rh ρ tx i inp, c = rh + 1 + i ∧ ρ < m ∧ M K_TXH rh = 1 ∧ M K_LOCK ρ = 1 ∧ c < ρ ∧ TxAt M R m ρ tx ∧
      (∀ j, rh ≤ j → j < ρ → M K_LOCK j = 0) ∧ (∀ j, rh < j → j ≤ ρ → M K_TXH j = 0) ∧
      i < tx.vin.length ∧ tx.vin[i]? = some inp ∧ InRow M R c inp ∧
      (M INL c).val + i = tx.vin.length ∧ (M SEG c = 1 ↔ tx.hasWitness = true) := by
  have hcn : c < n := by omega
  have ku : ∀ b < 9, K_IN ≠ b → M b c = 0 := fun b hb hne =>
    kind_unique hsat hcn (a := K_IN) (b := b) (by simp [K_IN]) hb hne hk
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with rfl | h
    · have := ku K_BLK (by simp [K_BLK]) (by simp [K_IN, K_BLK])
      rw [first_blk hsat (by omega)] at this; exact absurd this one_ne_zero
    · exact h
  obtain ⟨rh, ρ, tx, hle, hcρ, hρm, ht, hl, htx, notxh, nolock⟩ := row_tx hsat R hcs hmn hpad hfit hnp hc1 hc
  have ne1 : ∀ {b : ℕ}, b < 9 → K_IN ≠ b → M b c = 1 → False := fun hb hne h => by
    rw [ku _ hb hne] at h; exact zero_ne_one h
  have hrc : rh < c := by
    rcases Nat.eq_or_lt_of_le hle with e | e
    · exact (ne1 (by simp [K_TXH]) (by simp [K_IN, K_TXH]) (e ▸ ht)).elim
    · exact e
  have hcl : c < ρ := by
    rcases Nat.eq_or_lt_of_le hcρ with e | e
    · exact (ne1 (by simp [K_LOCK]) (by simp [K_IN, K_LOCK]) (e ▸ hl)).elim
    · exact e
  have hat : TxAt M R m ρ tx := ⟨rh, by omega, ht, notxh, htx⟩
  obtain ⟨rh', hrh', ht', hnt', hvl, -, hins, hno, -, houts, hwr, -, hseg, hle2⟩ :=
    tx_rows hsat R hcs hmn hpad hfit hat hρm
  obtain rfl : rh' = rh := by
    rcases lt_trichotomy rh' rh with h | h | h
    · have := hnt' rh h (by omega); rw [ht] at this; exact absurd this one_ne_zero
    · exact h
    · have := notxh rh' h (by omega); rw [ht'] at this; exact absurd this one_ne_zero
  -- the row is one of the inputs
  have hi : c < rh' + 1 + tx.vin.length := by
    by_contra hcon
    rcases Nat.lt_or_ge c (rh' + 2 + tx.vin.length) with a | a
    · have : c = rh' + 1 + tx.vin.length := by omega
      exact ne1 (by simp [K_NOUT]) (by simp [K_IN, K_NOUT]) (this ▸ hno)
    rcases Nat.lt_or_ge c (rh' + 2 + tx.vin.length + tx.vout.length) with b | b
    · obtain ⟨out, -, hrow⟩ := houts (c - (rh' + 2 + tx.vin.length)) (by omega)
      have := hrow.kind
      rw [show rh' + 2 + tx.vin.length + (c - (rh' + 2 + tx.vin.length)) = c by omega] at this
      exact ne1 (by simp [K_OUT]) (by simp [K_IN, K_OUT]) this
    · rcases hwr c b hcl with g | g
      · exact ne1 (by simp [K_WCNT]) (by simp [K_IN, K_WCNT]) g
      · exact ne1 (by simp [K_WITEM]) (by simp [K_IN, K_WITEM]) g
  obtain ⟨i, rfl⟩ : ∃ i, c = rh' + 1 + i := ⟨c - (rh' + 1), by omega⟩
  have hiv : i < tx.vin.length := by omega
  obtain ⟨inp, hinp, hrow⟩ := hins i hiv
  -- the inputs left
  have inl : ∀ q, q < tx.vin.length → M INL (rh' + 1 + q) = M VAL rh' - (q : F) := by
    intro q
    induction q with
    | zero =>
      intro _
      obtain ⟨-, c2, -⟩ := counters hsat (show rh' + 1 < n by omega)
      rw [Nat.add_zero, c2 (notxh (rh' + 1) (by omega) (by omega)), ((row_sets hsat (show rh' < n by omega)).2.1 ht).1,
        kinds_at hsat (show rh' < n by omega) (a := K_TXH) (by simp [K_TXH]) ht K_IN (by simp [K_IN])]
      simp [K_TXH, K_IN]
    | succ q ih =>
      intro hq
      obtain ⟨-, c2, -⟩ := counters hsat (show rh' + 1 + q + 1 < n by omega)
      obtain ⟨inp', -, hr'⟩ := hins q (by omega)
      rw [show rh' + 1 + (q + 1) = rh' + 1 + q + 1 by omega, c2 (notxh _ (by omega) (by omega)), ih (by omega), hr'.kind]
      push_cast; ring
  have hval : (M INL (rh' + 1 + i)).val + i = tx.vin.length := by
    have e : M INL (rh' + 1 + i) = ((tx.vin.length - i : ℕ) : F) := by
      rw [inl i hiv, Nat.cast_sub (by omega), hvl, ZMod.natCast_zmod_val]
    rw [e, ZMod.val_natCast_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) (by rw [hvl]; exact ZMod.val_lt _))]
    omega
  refine ⟨rh', ρ, tx, i, inp, rfl, hρm, ht, hl, hcl, hat, nolock, notxh, hiv, hinp, hrow, hval, ?_⟩
  rw [(tx_const hsat hmn hρm notxh _ (by omega) (by omega)).1]; exact hseg

end Wits

end StarkedAir.Block.Fields
