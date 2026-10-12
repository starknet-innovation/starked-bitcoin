/-
**The block system's setup (M3a.5).** From a satisfied block system: the fields' grammar context (the
first padding row `m`, the rows' fit and CompactSizes, the rows' bytes) and the parsed block `b`, with its
transactions at the lock-time rows; and the fields' read oracles in terms of the block's bytes.
-/
import StarkedAir.Block.ScriptSum
import StarkedAir.Block.FieldsCommit
import StarkedAir.Block.Coinbase

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)

/-- The block's bytes. -/
abbrev Rb (inst : ℕ → Inst) (pub : ℕ → F) : Spec.Block.Bytes := blockBytes (inst 0).main (pub 0).val

/-- **The setup**: the grammar context and the parsed block. -/
structure Setup (inst : ℕ → Inst) (pub : ℕ → F) (L : ℕ) where
  m : ℕ
  b : Spec.Block.Blk
  hmn : m < 2 ^ L
  hnp : ∀ r < m, (inst 1).main Fields.K_PAD r = 0
  hpad : ∀ r < 2 ^ L, m ≤ r → (inst 1).main Fields.K_PAD r = 1
  hfit : ∀ r < m, ((inst 1).main Fields.START r).val + ((inst 1).main Fields.LEN r).val ≤ (Rb inst pub).length
  hcs : ∀ r < 2 ^ L, (inst 1).main Fields.K_LOCK r + (inst 1).main Fields.K_PAD r = 0 → ∀ o : ℕ,
    (inst 1).main Fields.OFF r = (o : F) → o ≤ 86 →
    ((inst 1).main Fields.START r).val + o + prefOf (inst 1).main r ≤ (Rb inst pub).length ∧
    ((inst 1).main Fields.VAL r).val ≤ Fields.MAXS ∧
    Spec.Block.serCompact ((inst 1).main Fields.VAL r).val =
      slice (Rb inst pub) (((inst 1).main Fields.START r).val + o) (prefOf (inst 1).main r)
  cat : ∀ k ≤ m, ((List.range k).flatMap fun r => Spec.Block.Tok.bytes (tokOf (inst 1).main (Rb inst pub) r)) =
    slice (Rb inst pub) 0 ((inst 1).main Fields.START k).val
  mono : ∀ k j, k ≤ j → j ≤ m → ((inst 1).main Fields.START k).val ≤ ((inst 1).main Fields.START j).val
  hSm : ((inst 1).main Fields.START m).val = (Rb inst pub).length
  hparse : Spec.Block.parseBlock (Rb inst pub) = some b
  hhead : b.header = slice (Rb inst pub) 0 80
  hlenv : b.txs.length = ((inst 1).main Fields.VAL 0).val
  hN1 : 1 ≤ b.txs.length
  hN25 : b.txs.length < 2 ^ L
  hidx : ∀ ρ < 2 ^ L, (inst 1).main Fields.K_LOCK ρ = 1 → ∀ tx, TxAt (inst 1).main (Rb inst pub) m ρ tx →
    b.txs[locks (inst 1).main ρ]? = some tx
  htok : Spec.Block.toksBlock (toksFrom (inst 1).main (Rb inst pub) m 0) = some b
  hsurj : ∀ j < b.txs.length, ∃ ρ tx, ρ < m ∧ (inst 1).main Fields.K_LOCK ρ = 1 ∧ locks (inst 1).main ρ = j ∧
    b.txs[j]? = some tx ∧ TxAt (inst 1).main (Rb inst pub) m ρ tx

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
include hL hsat hL24

/-- The setup's rows are the fields component's (`Setup … (Ls 1)`). -/
theorem setup_exists : Nonempty (Setup inst pub (Ls 1)) := by
  have fs := hash_fields_sat' hL hsat
  have hb0 := hash_bytes_sat hL hsat
  obtain ⟨m, hmn, hnp, hpad, hfit, hcs, cat, mono, hSm⟩ :=
    Fields.block_ctx (le_trans (hL24.1 0 (by decide)) (by norm_num)) fs hb0 (hash_fields_read hL hsat hL24)
  obtain ⟨b, hparse, hhead, hlenv, hN1, hN25, hidx, htok, hsurj⟩ :=
    Fields.block_index (le_trans (hL24.1 0 (by decide)) (by norm_num)) fs hb0 (hash_fields_read hL hsat hL24) hmn hnp hpad hfit hcs cat
      mono hSm
  exact ⟨⟨m, b, hmn, hnp, hpad, hfit, hcs, cat, mono, hSm, hparse, hhead, hlenv, hN1, hN25, hidx, htok, hsurj⟩⟩

theorem len_R : (Rb inst pub).length ≤ 2 ^ Ls 0 := by
  have hP : 2 ^ Ls 0 < P := rows_lt_P hL24 (by decide)
  have := (Block.bytes_rows (n := 2 ^ Ls 0) (pub := pub) (main := (inst 0).main) (hash_bytes_sat hL hsat) hP
    (by positivity)).2.1
  rw [Fields.blockBytes_length]; exact this

/-- **The marker read**, in terms of the block's bytes. -/
theorem hmk_R : ∀ r < 2 ^ Ls 1, (inst 1).main Fields.K_TXH r = 1 → (inst 1).main Fields.SEG r = 1 →
    ((inst 1).main Fields.START r).val + 5 < (Rb inst pub).length ∧
    (Rb inst pub).getD (((inst 1).main Fields.START r).val + 4) 0 = 0 ∧
    (Rb inst pub).getD (((inst 1).main Fields.START r).val + 5) 0 = 1 := by
  intro r hr ht hs
  obtain ⟨hlt, h4, h5⟩ := Fields.marker_read (le_trans (hL24.1 0 (by decide)) (by norm_num)) (hash_fields_sat' hL hsat)
    (hash_bytes_sat hL hsat) (hash_fields_read hL hsat hL24) hr ht hs
  refine ⟨by rw [Fields.blockBytes_length]; exact hlt, ?_, ?_⟩
  · rw [Fields.blockBytes_get (by omega), h4]; rfl
  · rw [Fields.blockBytes_get hlt, h5]; rfl

/-- **The fields' byte slots**, in terms of the block's bytes. -/
theorem hby_R (S : Setup inst pub (Ls 1)) : ∀ r < 2 ^ Ls 1, ∀ j < 8,
    (Fields.chkLookups.getD j ⟨0, .const 0, []⟩).mult.eval (2 ^ Ls 1) Fields.preCols pub (inst 1).main r = -1 →
    ((inst 1).main Fields.BASEC r).val + j < (Rb inst pub).length ∧
    ((inst 1).main (Fields.BY j) r).val = ((Rb inst pub).getD (((inst 1).main Fields.BASEC r).val + j) 0).toNat := by
  intro r hr j hj hm
  have fs := hash_fields_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  obtain ⟨r0, hr0, hp, hb⟩ := fields_by_read hL hsat hL24 hr hj hm
  -- the row is an output, lock-time or input row
  have hk : (inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_LOCK r = 1 ∨ (inst 1).main Fields.K_IN r = 1 := by
    have ko := Fields.kind_bool fs (c := Fields.K_OUT) (by simp [Fields.kinds, Fields.K_OUT]) hr
    have kl := Fields.kind_bool fs (c := Fields.K_LOCK) (by simp [Fields.kinds, Fields.K_LOCK]) hr
    have ki := Fields.kind_bool fs (c := Fields.K_IN) (by simp [Fields.kinds, Fields.K_IN]) hr
    by_contra hc
    push Not at hc
    have z : (inst 1).main Fields.K_OUT r = 0 ∧ (inst 1).main Fields.K_LOCK r = 0 ∧ (inst 1).main Fields.K_IN r = 0 :=
      ⟨ko.resolve_right hc.1, kl.resolve_right hc.2.1, ki.resolve_right hc.2.2⟩
    rcases Nat.lt_or_ge j 4 with h4 | h4
    · rw [Fields.chk_mult_byte h4] at hm
      simp [Expr.eval, Fields.ev_k hr, z.1, z.2.1, z.2.2] at hm
    · rw [Fields.chk_mult_byte2 h4 hj] at hm
      simp [Expr.eval, Fields.ev_k hr, z.1] at hm
  have hbl := Fields.basec_lt fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit
    (by have := len_R hL hsat hL24 (inst := inst); omega) hr hk
  have hl := len_R hL hsat hL24 (inst := inst) (pub := pub)
  rw [Fields.blockBytes_length] at hl
  have hpv : ((inst 1).main Fields.BASEC r).val + j = r0 := by
    have e : ((((inst 1).main Fields.BASEC r).val + j : ℕ) : F) = (r0 : F) := by
      push_cast; rw [ZMod.natCast_zmod_val]; exact hp
    exact natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
  rw [hpv, hb]; exact read_R hL hsat hL24 hr0

/-- **The fields' auxiliary read**, in terms of the block's bytes. -/
theorem hbq_R : ∀ r < 2 ^ Ls 1, (inst 1).main Fields.GIN r + (inst 1).main Fields.MMB r = 1 →
    ((inst 1).main Fields.AQ r).val < (Rb inst pub).length ∧
    ((inst 1).main Fields.BQ r).val = ((Rb inst pub).getD ((inst 1).main Fields.AQ r).val 0).toNat := by
  intro r hr hm
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  obtain ⟨r0, hr0, hp, hb⟩ := fields_bq_read hL hsat hL24 hr hm
  have hl := len_R hL hsat hL24 (inst := inst) (pub := pub)
  have hpv : ((inst 1).main Fields.AQ r).val = r0 := by
    rw [hp]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by rw [Fields.blockBytes_length] at hl; omega))
  rw [hpv, hb]; exact read_R hL hsat hL24 hr0

end System

end StarkedAir.Block
