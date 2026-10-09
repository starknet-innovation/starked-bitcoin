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
      (∀ k j, k ≤ j → j ≤ m → ((inst 1).main START k).val ≤ ((inst 1).main START j).val) := by
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
  obtain ⟨m, hmn, -, hnp, hpad, hfit, -, cat, mono, -⟩ := tiling fs _ hcs hmk (by positivity) hRl
  exact ⟨m, hmn, hnp, hpad, hfit, hcs, cat, mono⟩

end Reads

end StarkedAir.Block.Fields
