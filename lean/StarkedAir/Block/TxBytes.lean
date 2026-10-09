/-
**Transaction serializations in the block (M3a.3).** With the fields' byte reads answered by the byte
table, a transaction's lock-time row holds its byte ranges: `[TXA, START + 4)` is `serWit`, and
`serNoWit` is `[TXA, TXA + 4) ++ [TXA + 6, WST) ++ [START, START + 4)` for segwit (else the whole range).
-/
import StarkedAir.Block.TxRanges

namespace StarkedAir.Block.Fields

open StarkedAir

theorem slice_add (R : Spec.Block.Bytes) (a b c : ℕ) : slice R a (b + c) = slice R a b ++ slice R (a + b) c := by
  simp [slice, List.take_add, List.drop_drop, Nat.add_comm]

theorem toksFrom_split {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    toksFrom M R c a = toksFrom M R b a ++ toksFrom M R c b := by
  unfold toksFrom
  rw [show c - a = (b - a) + (c - b) by omega, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left; intro i _; simp [Function.comp]; congr 1; omega

/-- Rows `a … b − 1` serialize to the block's bytes `[START a, START b)`, given the prefix property. -/
theorem rows_slice {M : ℕ → ℕ → F} {R : Spec.Block.Bytes} {m : ℕ}
    (cat : ∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (tokOf M R r)) = slice R 0 (M START k).val)
    (mono : ∀ k j, k ≤ j → j ≤ m → (M START k).val ≤ (M START j).val) {a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) :
    Spec.Block.toksBytes (toksFrom M R b a) = slice R (M START a).val ((M START b).val - (M START a).val) := by
  have hb := cat b hbm
  have ha := cat a (by omega)
  rw [show b = a + (b - a) by omega, List.range_add, List.flatMap_append, ha] at hb
  rw [show a + (b - a) = b by omega, show (M START b).val = (M START a).val + ((M START b).val - (M START a).val) by
    have := mono a b hab hbm; omega, slice_add, Nat.zero_add] at hb
  have := List.append_cancel_left hb
  rw [← this]
  simp [Spec.Block.toksBytes, toksFrom, List.flatMap_map]

theorem toksFrom_append_bytes (A B : List Spec.Block.Tok) :
    Spec.Block.toksBytes (A ++ B) = Spec.Block.toksBytes A ++ Spec.Block.toksBytes B := by
  simp [Spec.Block.toksBytes]

section Reads

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ} (hL : L ≤ 25)
  (fs : ∀ r < 2 ^ L, ∀ c ∈ constraints, c.eval (2 ^ L) preCols pub (inst 1).main r = 0)
  (hb0 : bytes.air.Satisfied L pub (inst 0).main)
  (hread : ∀ {r : ℕ}, r < 2 ^ L → ∀ {kk : ℕ}, kk < 7 →
    (lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) preCols pub (inst 1).main r = -1 →
    ∃ r0, r0 < (pub 0).val ∧
      ((lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) preCols pub (inst 1).main r)) =
        [(r0 : F), (inst 0).main BYTE r0])
include hL fs hb0 hread

/-- The grammar context: the first padding row `m`, the rows' fit, the CompactSize facts, and row
`k`'s start as the length of the block's prefix serialized by rows `< k`. -/
theorem block_ctx :
    ∃ m, m < 2 ^ L ∧ (∀ r < m, (inst 1).main K_PAD r = 0) ∧ (∀ r < 2 ^ L, m ≤ r → (inst 1).main K_PAD r = 1) ∧
      (∀ r < m, ((inst 1).main START r).val + ((inst 1).main LEN r).val ≤ (blockBytes (inst 0).main (pub 0).val).length) ∧
      (∀ r < 2 ^ L, (inst 1).main K_LOCK r + (inst 1).main K_PAD r = 0 → ∀ o : ℕ, (inst 1).main OFF r = (o : F) →
        o ≤ 86 → ((inst 1).main START r).val + o + prefOf (inst 1).main r ≤ (blockBytes (inst 0).main (pub 0).val).length ∧
        ((inst 1).main VAL r).val ≤ MAXS ∧
        Spec.Block.serCompact ((inst 1).main VAL r).val =
          slice (blockBytes (inst 0).main (pub 0).val) (((inst 1).main START r).val + o) (prefOf (inst 1).main r)) ∧
      (∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (tokOf (inst 1).main (blockBytes (inst 0).main (pub 0).val) r)) =
        slice (blockBytes (inst 0).main (pub 0).val) 0 ((inst 1).main START k).val) ∧
      (∀ k j, k ≤ j → j ≤ m → ((inst 1).main START k).val ≤ ((inst 1).main START j).val) ∧
      ((inst 1).main START m).val = (blockBytes (inst 0).main (pub 0).val).length := by
  have hRl : (blockBytes (inst 0).main (pub 0).val).length = (pub 0).val := blockBytes_length _ _
  have hcs : ∀ r < 2 ^ L, (inst 1).main K_LOCK r + (inst 1).main K_PAD r = 0 → ∀ o : ℕ, (inst 1).main OFF r = (o : F) →
      o ≤ 86 → ((inst 1).main START r).val + o + prefOf (inst 1).main r ≤ (blockBytes (inst 0).main (pub 0).val).length ∧
      ((inst 1).main VAL r).val ≤ MAXS ∧
      Spec.Block.serCompact ((inst 1).main VAL r).val =
        slice (blockBytes (inst 0).main (pub 0).val) (((inst 1).main START r).val + o) (prefOf (inst 1).main r) :=
    fun r hr hLP o ho hoP => by
      obtain ⟨a, b, c⟩ := compact_slice hL fs hb0 hread hr hLP ho hoP
      exact ⟨by rw [hRl]; exact a, b, c⟩
  have hmk : ∀ r < 2 ^ L, (inst 1).main K_TXH r = 1 → (inst 1).main SEG r = 1 →
      ((inst 1).main START r).val + 5 < (blockBytes (inst 0).main (pub 0).val).length ∧
      (blockBytes (inst 0).main (pub 0).val).getD (((inst 1).main START r).val + 4) 0 = 0 ∧
      (blockBytes (inst 0).main (pub 0).val).getD (((inst 1).main START r).val + 5) 0 = 1 :=
    fun r hr ht hs => by
      obtain ⟨a, b, c⟩ := marker_read hL fs hb0 hread hr ht hs
      refine ⟨by rw [hRl]; exact a, ?_, ?_⟩
      · rw [blockBytes_get (by omega), b]; rfl
      · rw [blockBytes_get (by omega), c, ZMod.val_one]; rfl
  obtain ⟨m, hmn, -, hnp, hpad, hfit, -, cat, mono, hSm⟩ := tiling fs _ hcs hmk (by positivity) hRl
  exact ⟨m, hmn, hnp, hpad, hfit, hcs, cat, mono, hSm⟩

/-- **A transaction's serializations are block slices.** For the transaction with header row `rh`
and lock-time row `r'`, with `a = TXA r'`, `w = WST r'`, `l = START r'`: `serWit = R[a, l + 4)`, and
`serNoWit = R[a, a + 4) ++ R[a + 6, w) ++ R[l, l + 4)` for segwit, else `R[a, l + 4)`. -/
theorem tx_bytes {rh : ℕ} (hr : rh < 2 ^ L) (ht : (inst 1).main K_TXH rh = 1) :
    ∃ tx r', r' < 2 ^ L ∧ rh < r' ∧ (inst 1).main K_LOCK r' = 1 ∧
      (∀ j, rh < j → j ≤ r' → (inst 1).main K_TXH j = 0) ∧ (∀ j, rh ≤ j → j < r' → (inst 1).main K_LOCK j = 0) ∧
      Spec.Block.serWit tx = slice (blockBytes (inst 0).main (pub 0).val) ((inst 1).main TXA r').val
        (((inst 1).main START r').val + 4 - ((inst 1).main TXA r').val) ∧
      ((inst 1).main SEG r' = 1 → Spec.Block.serNoWit tx =
        slice (blockBytes (inst 0).main (pub 0).val) ((inst 1).main TXA r').val 4 ++
        slice (blockBytes (inst 0).main (pub 0).val) (((inst 1).main TXA r').val + 6)
          (((inst 1).main WST r').val - (((inst 1).main TXA r').val + 6)) ++
        slice (blockBytes (inst 0).main (pub 0).val) ((inst 1).main START r').val 4) ∧
      ((inst 1).main SEG r' ≠ 1 → Spec.Block.serNoWit tx = Spec.Block.serWit tx) := by
  obtain ⟨m, hmn, hnp, hpad, hfit, hcs, cat, mono, hSm⟩ := block_ctx hL fs hb0 hread
  set R := blockBytes (inst 0).main (pub 0).val with hR
  set M := (inst 1).main with hM
  have hpad0 : M K_PAD rh = 0 := by
    rw [kind_unique fs hr (a := K_TXH) (b := K_PAD) (by simp [K_TXH]) (by simp [K_PAD]) (by simp [K_TXH, K_PAD]) ht]
  have hrm : rh < m := lt_m fs R hcs hmn hpad hfit hr hpad0
  obtain ⟨tx, r', rw, v, nIn, l, htx, h1, h2, hr'm, hl, htok, hlock, hseg, hnw, hta, hws, hsg, notxh, nolock⟩ :=
    tx_cols fs R hcs hmn hpad hfit hrm ht
  -- the header token
  have hblk : M K_BLK rh ≠ 1 := by
    rw [kind_unique fs hr (a := K_TXH) (b := K_BLK) (by simp [K_TXH]) (by simp [K_BLK]) (by simp [K_TXH, K_BLK]) ht]
    exact zero_ne_one
  have hv : v = slice R (M START rh).val 4 ∧ nIn = (M VAL rh).val := by
    have e := htok; simp only [tokOf, hblk, ht, if_false, if_true] at e
    simp only [Spec.Block.Tok.txh.injEq] at e; exact ⟨e.1.symm, e.2.2.symm⟩
  obtain ⟨-, -, -, -, -, -, -, hlv⟩ := tokk_lock hlock
  -- serializations as row ranges
  have rs := fun {a b : ℕ} (hab : a ≤ b) (hbm : b ≤ m) => rows_slice (M := M) (R := R) cat mono hab hbm
  have one : ∀ {j}, j < m → Spec.Block.toksBytes (toksFrom M R (j + 1) j) = (tokOf M R j).bytes := by
    intro j hj; simp [toksFrom, Spec.Block.toksBytes]
  have hhd := rs (a := rh) (b := rh + 1) (by omega) (by omega)
  rw [one hrm, htok] at hhd
  have hlen : (M START m).val = R.length := hSm
  have m1 := mono rh (rh + 1) (by omega) (by omega)
  have m2 := mono (rh + 1) rw (by omega) (by omega)
  have m3 := mono rw r' (by omega) (by omega)
  have m4 := mono r' m (by omega) le_rfl
  have hsegr : M SEG rh = M SEG r' := hsg.symm
  have hta' : (M TXA r').val = (M START rh).val := by rw [hta]
  have hws' : (M WST r').val = (M START rw).val := by rw [hws]
  have bytes_split : ∀ {a b c : ℕ}, a ≤ b → b ≤ c →
      Spec.Block.toksBytes (toksFrom M R c a) = Spec.Block.toksBytes (toksFrom M R b a) ++ Spec.Block.toksBytes (toksFrom M R c b) :=
    fun h1 h2 => by rw [toksFrom_split h1 h2, toksFrom_append_bytes]
  -- serWit: rows `rh … r'`
  have hw : Spec.Block.serWit tx = Spec.Block.toksBytes (toksFrom M R r' rh) ++ l := by
    have e := (Spec.Block.txT_sound htx).2
    rw [bytes_split (b := r' + 1) (by omega) (by omega)] at e
    have e2 := List.append_cancel_right e
    rw [← e2, bytes_split (b := r') (by omega) (by omega), one hr'm, hlock]; rfl
  have hwit : Spec.Block.serWit tx = slice R (M START rh).val ((M START r').val + 4 - (M START rh).val) := by
    rw [hw, rs (by omega) (by omega), hlv, show (M START r').val + 4 - (M START rh).val =
      ((M START r').val - (M START rh).val) + 4 by omega, slice_add, show (M START rh).val + ((M START r').val -
      (M START rh).val) = (M START r').val by omega]
  refine ⟨tx, r', by omega, by omega, hl, notxh, nolock, by rw [hta']; exact hwit, fun hs => ?_, fun hs => ?_⟩
  · -- segwit: drop the marker and flag, and the witness rows
    have hs' : M SEG rh = 1 := hsegr ▸ hs
    simp only [Spec.Block.Tok.bytes, hs', decide_true, if_true] at hhd
    rw [hv.1] at hhd
    set S0 := (M START rh).val
    set S1 := (M START (rh + 1)).val
    have hS1 : S1 ≤ R.length := by have := mono (rh + 1) m (by omega) le_rfl; omega
    have hl1 := congrArg List.length hhd
    simp only [slice, List.length_append, List.length_take, List.length_drop, List.length_cons,
      List.length_nil] at hl1
    have h6 : S0 + 6 ≤ S1 := by omega
    rw [show S1 - S0 = 4 + (2 + (S1 - (S0 + 6))) by omega, slice_add, slice_add,
      show S0 + 4 + 2 = S0 + 6 by omega, ← List.append_assoc] at hhd
    obtain ⟨-, hsc⟩ := List.append_inj hhd (by simp [slice_length (show S0 + 4 + 2 ≤ R.length by omega)])
    rw [hnw, hv.1, hsc, rs (by omega) (by omega), hlv, hta', hws']
    rw [show (M START rw).val - (S0 + 6) = (S1 - (S0 + 6)) + ((M START rw).val - S1) by omega,
      slice_add (a := S0 + 6), show S0 + 6 + (S1 - (S0 + 6)) = S1 by omega]
    simp only [List.append_assoc]; rfl
  · -- no witnesses: the same bytes
    have hs' : M SEG rh ≠ 1 := fun h => hs (hsegr ▸ h)
    have hrw : rw = r' := hseg hs'
    simp only [Spec.Block.Tok.bytes, hs', decide_false, if_false, Bool.false_eq_true, List.append_nil] at hhd
    rw [hnw, hw, hrw, bytes_split (a := rh) (b := rh + 1) (by omega) (by omega), one hrm, htok]
    simp only [Spec.Block.Tok.bytes, hs', decide_false, if_false, Bool.false_eq_true, List.append_nil, List.append_assoc]

/-- **A lock-time row ends a transaction** whose serializations are the row's block slices. -/
theorem lock_tx {ρ : ℕ} (hρ : ρ < 2 ^ L) (hl : (inst 1).main K_LOCK ρ = 1) :
    ∃ tx, Spec.Block.serWit tx = slice (blockBytes (inst 0).main (pub 0).val) ((inst 1).main TXA ρ).val
        (((inst 1).main START ρ).val + 4 - ((inst 1).main TXA ρ).val) ∧
      ((inst 1).main SEG ρ = 1 → Spec.Block.serNoWit tx =
        slice (blockBytes (inst 0).main (pub 0).val) ((inst 1).main TXA ρ).val 4 ++
        slice (blockBytes (inst 0).main (pub 0).val) (((inst 1).main TXA ρ).val + 6)
          (((inst 1).main WST ρ).val - (((inst 1).main TXA ρ).val + 6)) ++
        slice (blockBytes (inst 0).main (pub 0).val) ((inst 1).main START ρ).val 4) ∧
      ((inst 1).main SEG ρ ≠ 1 → Spec.Block.serNoWit tx = Spec.Block.serWit tx) := by
  classical
  have hρ0 : 0 < ρ := by
    rcases Nat.eq_zero_or_pos ρ with e | e
    · subst e
      have := kind_unique fs hρ (a := K_BLK) (b := K_LOCK) (by simp [K_BLK]) (by simp [K_LOCK])
        (by simp [K_BLK, K_LOCK]) (first_blk fs (by omega))
      rw [hl] at this; exact absurd this one_ne_zero
    · exact e
  have h1 : (inst 1).main K_TXH 1 = 1 := (next_kind fs (r := 0) (by omega)).1 (first_blk fs (by omega))
  set rh := Nat.findGreatest (fun j => (inst 1).main K_TXH j = 1) ρ with hrh
  have hrht : (inst 1).main K_TXH rh = 1 := Nat.findGreatest_spec (P := fun j => (inst 1).main K_TXH j = 1) (m := 1) (by omega) h1
  have hrhle : rh ≤ ρ := Nat.findGreatest_le ρ
  have hgr : ∀ j, rh < j → j ≤ ρ → (inst 1).main K_TXH j ≠ 1 := fun j a b => Nat.findGreatest_is_greatest a b
  obtain ⟨tx, r', hr', hrr', hlr', notxh, nolock, hw, hnw, hnn⟩ := tx_bytes hL fs hb0 hread (by omega) hrht
  have heq : r' = ρ := by
    rcases lt_trichotomy ρ r' with h | h | h
    · have := nolock ρ hrhle h; rw [hl] at this; exact absurd this one_ne_zero
    · exact h.symm
    · exfalso
      have hn : r' + 1 < 2 ^ L := by omega
      rcases (z1_spec fs (by omega : r' < 2 ^ L)).1 with z | z
      · exact hgr (r' + 1) (by omega) (by omega) ((next_kind fs hn).2.2.2.2.2.2.2.2.2.2.1 hlr' z)
      · have hp : ∀ i, r' + 1 + i ≤ ρ → (inst 1).main K_PAD (r' + 1 + i) = 1 := by
          intro i
          induction i with
          | zero => intro _; exact (next_kind fs hn).2.2.2.2.2.2.2.2.2.2.2.1 hlr' z
          | succ i ih =>
            intro hi
            have := (next_kind fs (r := r' + 1 + i) (by omega)).2.2.2.2.2.2.2.2.2.2.2.2 (ih (by omega))
            rwa [show r' + 1 + i + 1 = r' + 1 + (i + 1) by ring] at this
        have := hp (ρ - (r' + 1)) (by omega)
        rw [show r' + 1 + (ρ - (r' + 1)) = ρ by omega] at this
        have := kind_unique fs hρ (a := K_LOCK) (b := K_PAD) (by simp [K_LOCK]) (by simp [K_PAD])
          (by simp [K_LOCK, K_PAD]) hl
        rw [‹(inst 1).main K_PAD ρ = 1›] at this; exact absurd this one_ne_zero
  subst heq
  exact ⟨tx, hw, hnw, hnn⟩

end Reads

end StarkedAir.Block.Fields
