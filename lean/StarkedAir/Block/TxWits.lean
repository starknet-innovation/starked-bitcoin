/-
**A segwit transaction's witness section (M3a.5e).** The rows between the outputs and the lock time
serialize the inputs' witness stacks; and a one-input stack whose bytes are `01 20 nonce` is `[nonce]`
(the coinbase witness the commitment check reads).
-/
import StarkedAir.Block.FieldsTotals
import StarkedAir.Block.TxBytes

namespace StarkedAir.Block.Fields

open StarkedAir

/-- A CompactSize starting with a byte below `253` is that byte alone. -/
theorem serCompact_head {x : ℕ} {b : UInt8} {t : Spec.Block.Bytes} (h : Spec.Block.serCompact x = b :: t)
    (hb : b.toNat < 253) : x = b.toNat ∧ t = [] := by
  unfold Spec.Block.serCompact at h
  split_ifs at h with h1 h2 h3
  · simp only [List.cons.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨?_, rfl⟩
    simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show x < 256 by omega)]
  all_goals (simp only [List.cons.injEq] at h; obtain ⟨rfl, -⟩ := h; simp at hb)

/-- **A one-input stack read as `01 20 nonce`** is the single 32-byte item `nonce`. -/
theorem stack_nonce {ws : List (List Spec.Block.Bytes)} (hl : ws.length = 1) {nonce : Spec.Block.Bytes}
    (hn : nonce.length = 32) (h : ws.flatMap Spec.Block.serStack = 1 :: 0x20 :: nonce) : ws = [[nonce]] := by
  match ws, hl with
  | [w], _ =>
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Spec.Block.serStack] at h
    cases hc : Spec.Block.serCompact w.length with
    | nil => unfold Spec.Block.serCompact at hc; split_ifs at hc <;> simp at hc
    | cons b t =>
      rw [hc] at h
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, ht⟩ := h
      obtain ⟨hw1, rfl⟩ := serCompact_head hc (by decide)
      simp only [List.nil_append] at ht
      match w, hw1 with
      | [it], _ =>
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, Spec.Block.serVarBytes] at ht
        cases hc2 : Spec.Block.serCompact it.length with
        | nil => unfold Spec.Block.serCompact at hc2; split_ifs at hc2 <;> simp at hc2
        | cons b2 t2 =>
          rw [hc2] at ht
          simp only [List.cons_append, List.cons.injEq] at ht
          obtain ⟨rfl, ht2⟩ := ht
          obtain ⟨-, rfl⟩ := serCompact_head hc2 (by decide)
          simp only [List.nil_append] at ht2
          rw [ht2]

theorem toksFrom_drop {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m r j : ℕ} (h : r + j ≤ m) :
    (toksFrom M R m r).drop j = toksFrom M R m (r + j) := by
  rw [toksFrom_split (b := r + j) (by omega) h, List.drop_left' (by rw [toksFrom_length]; omega)]

section Wits

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
  (hcs : ∀ r < n, M K_LOCK r + M K_PAD r = 0 → ∀ o : ℕ, M OFF r = (o : F) → o ≤ 86 →
    (M START r).val + o + prefOf M r ≤ R.length ∧ (M VAL r).val ≤ MAXS ∧
    Spec.Block.serCompact (M VAL r).val = slice R ((M START r).val + o) (prefOf M r))
  {m : ℕ} (hmn : m < n) (hpad : ∀ r < n, m ≤ r → M K_PAD r = 1)
  (hfit : ∀ r < m, (M START r).val + (M LEN r).val ≤ R.length)
  (cat : ∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (tokOf M R r)) = slice R 0 (M START k).val)
  (mono : ∀ k j, k ≤ j → j ≤ m → (M START k).val ≤ (M START j).val)
include hsat hcs hmn hpad hfit cat mono

/-- **A segwit transaction's witness section**: `WST` on its lock-time row starts the bytes of its inputs'
stacks, which end at the lock time. -/
theorem tx_wits {ρ : ℕ} {tx : Spec.Block.Tx} (hat : TxAt M R m ρ tx) (hρm : ρ < m) (hseg : M SEG ρ = 1) :
    ∃ rw, rw ≤ ρ ∧ M WST ρ = M START rw ∧
      slice R (M START rw).val ((M START ρ).val - (M START rw).val) = (tx.vin.map (·.witness)).flatMap Spec.Block.serStack := by
  obtain ⟨rh, hrh, ht, hnt, htx⟩ := hat
  obtain ⟨tx', r', rw, v, nIn, l, htx', h1, h2, hr'm, hl, htok, hlock, hsegrw, hnw, hta, hws, hsg, notxh, nolock,
    hwit, hpre⟩ := tx_cols hsat R hcs hmn hpad hfit (by omega) ht
  rw [htx] at htx'
  simp only [Option.some.injEq, Prod.mk.injEq] at htx'
  obtain ⟨rfl, hrest⟩ := htx'
  obtain rfl : ρ = r' := by
    have := congrArg List.length hrest; simp only [toksFrom_length] at this; omega
  have hsrh : M SEG rh = 1 := hsg ▸ hseg
  rw [toksFrom_cons (by omega), htok, show decide (M SEG rh = 1) = true by simp [hsrh]] at htx
  obtain ⟨pin, k, pout, pw, l', hsplit, hpl, hpo, -, -, -, -, -, hwit', hins, houts, -, hsegT⟩ := Spec.Block.txT_vals htx
  obtain ⟨-, ws, hws', hmap⟩ := hsegT rfl
  have hlen := congrArg List.length hsplit
  simp only [toksFrom_length, List.length_append, List.length_cons] at hlen
  set rw0 := rh + 2 + pin.length + pout.length with hrw0
  have hρ : ρ = rw0 + pw.length := by omega
  have tk : ∀ i, i < m - (rh + 1) → (toksFrom M R m (rh + 1))[i]? = some (tokOf M R (rh + 1 + i)) :=
    fun i hi => toksFrom_get hi
  -- rows before `rw0` (after the head) are not witness rows; rows from `rw0` to the lock time are
  have before : ∀ j, rh < j → j < rw0 → (tokOf M R j).isWit = false := by
    intro j a b
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l' :: toksFrom M R m (ρ + 1))) =
        (pin ++ .nout k :: pout) ++ (pw ++ .lock l' :: toksFrom M R m (ρ + 1)) := by simp
    have g := congrArg (fun L => L[j - (rh + 1)]?) (hsplit.trans e)
    rw [tk _ (by omega), List.getElem?_append_left (by simp; omega), show rh + 1 + (j - (rh + 1)) = j by omega] at g
    set i := j - (rh + 1) with hi
    rcases Nat.lt_or_ge i pin.length with h | h
    · rw [List.getElem?_append_left h] at g
      obtain ⟨hh, nn, ss, qq, hg, -⟩ := hins i (by omega)
      rw [hg] at g; simp only [Option.some.injEq] at g; rw [g]; rfl
    · rw [List.getElem?_append_right h] at g
      rcases Nat.eq_or_lt_of_le h with h' | h'
      · rw [← h', Nat.sub_self] at g; simp only [List.getElem?_cons_zero, Option.some.injEq] at g; rw [g]; rfl
      · rw [show i - pin.length = (i - pin.length - 1) + 1 by omega, List.getElem?_cons_succ] at g
        obtain ⟨vv, ss, hg, -⟩ := houts (i - pin.length - 1) (by omega)
        rw [hg] at g; simp only [Option.some.injEq] at g; rw [g]; rfl
  have inside : ∀ j, rw0 ≤ j → j < ρ → (tokOf M R j).isWit = true := by
    intro j a b
    have e : pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l' :: toksFrom M R m (ρ + 1))) =
        (pin ++ .nout k :: pout) ++ (pw ++ .lock l' :: toksFrom M R m (ρ + 1)) := by simp
    have g := get_app (hsplit.trans e) (j - rw0)
    rw [tk _ (by simp; omega)] at g
    simp only [List.length_append, List.length_cons] at g
    rw [List.getElem?_append_left (by omega), show rh + 1 + (pin.length + (pout.length + 1) + (j - rw0)) = j by omega] at g
    exact hwit' _ (List.mem_of_getElem? g.symm)
  -- so the layout's `rw` is `rw0`
  have hrw : rw = rw0 := by
    rcases lt_trichotomy rw rw0 with h | h | h
    · exfalso
      have hj : rw < ρ := by omega
      have := before rw (by omega) h
      rcases hwit rw le_rfl hj with g | g
      · rw [tok_wcnt hsat R hcs hmn hpad hfit (by omega) g] at this; simp [Spec.Block.Tok.isWit] at this
      · rw [tok_witem hsat R hcs hmn hpad hfit (by omega) g] at this; simp [Spec.Block.Tok.isWit] at this
    · exact h
    · exfalso
      have := tokk_wit (inside (rw - 1) (by omega) (by omega))
      have hn : rw - 1 < n := by omega
      rcases hpre with g | g <;> rcases this with g' | g'
      · rw [kind_unique hsat hn (a := K_NOUT) (b := K_WCNT) (by simp [K_NOUT]) (by simp [K_WCNT]) (by simp [K_NOUT, K_WCNT]) g] at g'
        exact zero_ne_one g'
      · rw [kind_unique hsat hn (a := K_NOUT) (b := K_WITEM) (by simp [K_NOUT]) (by simp [K_WITEM]) (by simp [K_NOUT, K_WITEM]) g] at g'
        exact zero_ne_one g'
      · rw [kind_unique hsat hn (a := K_OUT) (b := K_WCNT) (by simp [K_OUT]) (by simp [K_WCNT]) (by simp [K_OUT, K_WCNT]) g] at g'
        exact zero_ne_one g'
      · rw [kind_unique hsat hn (a := K_OUT) (b := K_WITEM) (by simp [K_OUT]) (by simp [K_WITEM]) (by simp [K_OUT, K_WITEM]) g] at g'
        exact zero_ne_one g'
  subst hrw
  refine ⟨rw0, by omega, hws, ?_⟩
  -- the witness tokens are the rows `rw0 … ρ − 1`
  have hd : toksFrom M R m rw0 = pw ++ .lock l' :: toksFrom M R m (ρ + 1) := by
    rw [show rw0 = rh + 1 + (pin.length + 1 + pout.length) by omega, ← toksFrom_drop (by omega), hsplit]
    rw [show pin.length + 1 + pout.length = (pin ++ [Spec.Block.Tok.nout k] ++ pout).length by simp; omega]
    rw [show pin ++ Spec.Block.Tok.nout k :: (pout ++ (pw ++ .lock l' :: toksFrom M R m (ρ + 1))) =
      (pin ++ [Spec.Block.Tok.nout k] ++ pout) ++ (pw ++ .lock l' :: toksFrom M R m (ρ + 1)) by simp, List.drop_left]
  have hsp := toksFrom_split (M := M) (R := R) (show rw0 ≤ ρ by omega) (show ρ ≤ m by omega)
  rw [hd] at hsp
  have hpw : toksFrom M R ρ rw0 = pw :=
    (List.append_inj hsp.symm (by rw [toksFrom_length]; omega)).1
  obtain ⟨-, -, hb⟩ := Spec.Block.witsT_sound _ _ _ _ hws'
  simp only [Spec.Block.toksBytes, List.flatMap_append] at hb
  have hb' : Spec.Block.toksBytes pw = ws.flatMap Spec.Block.serStack := List.append_cancel_right hb
  rw [← rows_slice cat mono (show rw0 ≤ ρ by omega) (show ρ ≤ m by omega), hpw, hb', hmap]

end Wits

end StarkedAir.Block.Fields
