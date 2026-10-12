/-
**The coin events of a block (M3b, D-040), layer 4.** The spec-level encoding of a coin event as the coin
component's 26-entry tuple, and the theorem that each coin row's tuple is its event's encoding.

A coin event is `(txid, vout, code, serTxOut, ctx)`: the outpoint, `code = 2·height + coinbase`, the
output's serialization (amount and script), and the creating transaction's index in its block. Its
tuple (`tupleOf`): the txid's sixteen 16-bit limbs (`txidLimb`: word `w` big-endian, low half first),
the index and code as two 16-bit limbs each, the four coordinates of `serTxOut`'s Horner fingerprint at
`γ`, its length, and `ctx`.
-/
import StarkedAir.Block.CoinLink
import StarkedAir.Spec.Coins

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Spec.QM31 (QM toQ emb coordsOf toQ_coordsOf coordsOf_toQ)

/-- Limb `i` of a 32-byte txid: word `i / 2` big-endian, its low 16 bits for even `i`, high for odd. -/
def txidLimb (b : Spec.Block.Bytes) (i : ℕ) : ℕ :=
  let w := i / 2
  if i % 2 = 0 then (b.getD (4 * w + 3) 0).toNat + 256 * (b.getD (4 * w + 2) 0).toNat
  else (b.getD (4 * w + 1) 0).toNat + 256 * (b.getD (4 * w) 0).toNat

/-- A coin event's tuple. -/
noncomputable def tupleOf (γ : QM) (txid : Spec.Block.Bytes) (vout code : ℕ) (ser : Spec.Block.Bytes) (ctx : ℕ) :
    List F :=
  let h := coordsOf (FpWalk.horner γ (ser.map fun b => emb ((b.toNat : ℕ) : F)))
  (List.range 16).map (fun i => ((txidLimb txid i : ℕ) : F)) ++
    [((vout % 65536 : ℕ) : F), ((vout / 65536 : ℕ) : F), ((code % 65536 : ℕ) : F), ((code / 65536 : ℕ) : F),
      h.a, h.b, h.c, h.d, ((ser.length : ℕ) : F), ((ctx : ℕ) : F)]

theorem tupleOf_length (γ : QM) (txid : Spec.Block.Bytes) (vout code : ℕ) (ser : Spec.Block.Bytes) (ctx : ℕ) :
    (tupleOf γ txid vout code ser ctx).length = 26 := by simp [tupleOf]

/-- A SHA state's 16-bit word halves are its bytes' txid limbs. -/
theorem half16_txidLimb (S : Spec.Sha256.State) {i : ℕ} (hi : i < 16) :
    Sha256.half16 (Spec.Bitcoin.stateWord S (i / 2)) (i % 2) = txidLimb (Spec.Block.stateBytes S) i := by
  have hw : i / 2 < 8 := by omega
  rw [HashSpec.stateWord_bytes S hw]
  set b0 := ((Spec.Block.stateBytes S).getD (4 * (i / 2)) 0).toNat
  set b1 := ((Spec.Block.stateBytes S).getD (4 * (i / 2) + 1) 0).toNat
  set b2 := ((Spec.Block.stateBytes S).getD (4 * (i / 2) + 2) 0).toNat
  set b3 := ((Spec.Block.stateBytes S).getD (4 * (i / 2) + 3) 0).toNat
  have l0 : b0 < 256 := UInt8.toNat_lt _
  have l1 : b1 < 256 := UInt8.toNat_lt _
  have l2 : b2 < 256 := UInt8.toNat_lt _
  have l3 : b3 < 256 := UInt8.toNat_lt _
  have hv : (BitVec.ofNat 32 (b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3)).toNat = b0 * 2 ^ 24 + b1 * 2 ^ 16 + b2 * 2 ^ 8 + b3 := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; omega
  unfold txidLimb
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · simp only [h, Sha256.half16, if_true, hv]; omega
  · simp only [h, Sha256.half16, one_ne_zero, if_false, hv]; omega

/-- A token's bytes are an output's serialization. -/
theorem outTok_bytes {o : Spec.Block.TxOut} {tk : Spec.Block.Tok} (h : Spec.Block.OutTok o tk) :
    Spec.Block.Tok.bytes tk = Spec.Block.serTxOut o := by
  cases tk with
  | out v s =>
    obtain ⟨hv, hval, hs⟩ := h
    simp only [Spec.Block.Tok.bytes, Spec.Block.serTxOut, hval, hs, Spec.Block.signed64_bytes hv]
  | _ => exact absurd h (by simp [Spec.Block.OutTok])

/-- Two bytes and a byte below `2^24` split as 16-bit limbs. -/
theorem limbs_of_bytes {lo hi : F} {n : ℕ} (hlo : lo.val < 65536) (hhi : hi.val < 256)
    (h : lo + 65536 * hi = (n : F)) (hn : n < 2 ^ 30) : lo = ((n % 65536 : ℕ) : F) ∧ hi = ((n / 65536 : ℕ) : F) := by
  have e : lo.val + 65536 * hi.val = n := by
    apply Coin.lift _ (lt_of_lt_of_le (show lo.val + 65536 * hi.val < 2 ^ 25 by omega) (by unfold P; norm_num))
      (lt_of_lt_of_le (show n < 2 ^ 30 from hn) (by unfold P; norm_num))
    push_cast; rw [Coin.cast_val, Coin.cast_val, h]
  constructor
  · rw [← Coin.cast_val lo]; congr 1; omega
  · rw [← Coin.cast_val hi]; congr 1; omega

/-- **Summing by transactions.** The rows `[0, Σ lengths)` are, transaction by transaction, the
positions `pre t + q`. -/
theorem sum_by_parts {β : Type} [AddCommMonoid β] (g : ℕ → β) (lens : List ℕ) :
    ∑ r ∈ Finset.range lens.sum, g r =
      ∑ t ∈ Finset.range lens.length, ∑ q ∈ Finset.range (lens.getD t 0), g ((lens.take t).sum + q) := by
  induction lens using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [List.sum_append, List.sum_singleton, Finset.sum_range_add, ih, List.length_append, List.length_singleton,
      Finset.sum_range_succ]
    congr 1
    · apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_range.mp ht
      rw [List.getD_append _ _ _ _ ht', List.take_append_of_le_length (by omega)]
    · simp [List.getD_eq_getElem?_getD, List.take_append_of_le_length (le_refl _)]

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : ∀ i < 15, Ls i ≤ 23)
include hL hsat hL24

/-- An output row's single-byte range checks: `VB 0`, `VB 1`, `VHI`, `CB 0`, `CB 1`, `CHI`. -/
theorem out_bytes {j : ℕ} (hj : j < 2 ^ Ls 14) (hko : (inst 14).main Coin.KO j = 1) :
    ((inst 14).main (Coin.VB 0) j).val < 256 ∧ ((inst 14).main (Coin.VB 1) j).val < 256 ∧
      ((inst 14).main Coin.VHI j).val < 256 ∧ ((inst 14).main (Coin.CB 0) j).val < 256 ∧
      ((inst 14).main (Coin.CB 1) j).val < 256 ∧ ((inst 14).main Coin.CHI j).val < 256 := by
  have ek : (Coin.k Coin.KO).eval (2 ^ Ls 14) Coin.preCols pub (inst 14).main j = 1 := by rw [Coin.ev_k hj]; exact hko
  exact ⟨coin_r8 hL hsat hL24 (k := 46) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 47) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 48) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 49) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 50) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 51) (by omega) (by omega) rfl hj ek⟩

/-- An output row's index limbs: `VLO + 65536·VHI = VOUT`. -/
theorem out_vlimbs {j : ℕ} (hj : j < 2 ^ Ls 14) (hko : (inst 14).main Coin.KO j = 1) :
    (inst 14).main Coin.VLO j + 65536 * (inst 14).main Coin.VHI j = (inst 14).main Coin.VOUT j := by
  have cs := coin_sat hL hsat hL24
  have := Coin.sat cs (Coin.mem_local (c := .mul (Coin.k Coin.KO) (.sub (.add (Coin.k Coin.VLO)
    (.mul (StarkedAir.Sha256.cst 65536) (Coin.k Coin.VHI))) (Coin.k Coin.VOUT))) (by simp [Coin.localC])) hj
  simp only [Expr.eval, Coin.ev_k hj, StarkedAir.Sha256.eval_cst, Nat.cast_ofNat, hko, one_mul] at this
  linear_combination this

/-- The coin tuple at a row. -/
def rowTuple (inst : ℕ → Inst) (pub : ℕ → F) (L j : ℕ) : List F :=
  Coin.tuple.map fun ex => ex.eval (2 ^ L) Coin.preCols pub (inst 14).main j

theorem rowTuple_eq {j : ℕ} (hj : j < 2 ^ Ls 14) : rowTuple inst pub (Ls 14) j =
    (List.range 16).map (fun i => (inst 14).main (Coin.TLB i) j) ++
      [(inst 14).main Coin.VLO j, (inst 14).main Coin.VHI j, (inst 14).main Coin.CLO j, (inst 14).main Coin.CHI j,
        (inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
        (inst 14).main (Coin.FH + 3) j, (inst 14).main Coin.SLEN j, (inst 14).main Coin.CTX j] := by
  simp [rowTuple, Coin.tuple, Coin.ev_k hj, List.map_append, Function.comp]

/-- **An output row's tuple is its coin's.** The created coin of output `q − |vin|` of transaction `t`:
its txid, index, code `2·height + [t = 0]`, `serTxOut`, and creating transaction `t`. -/
theorem coin_out_tuple (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23)
    {j t q : ℕ} {tx : Spec.Block.Tx} {o : Spec.Block.TxOut} (hj : j < e) (hko : (inst 14).main Coin.KO j = 1)
    (htx : S.b.txs[t]? = some tx) (hjq : j = ((parts.take t).map List.length).sum + q)
    (hq : q < tx.vin.length + tx.vout.length) (ho : tx.vout[q - tx.vin.length]? = some o) :
    rowTuple inst pub (Ls 14) j = tupleOf (FpWalk.gQ pub) (Spec.Block.txid tx) (q - tx.vin.length)
      (2 * h + if t = 0 then 1 else 0) (Spec.Block.serTxOut o) t := by
  have cs := coin_sat hL hsat hL24
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ Ls 14 := by omega
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  -- the row's transaction and output
  obtain ⟨t0, q0, tx0, htx0, htxi, hjq0, hq0, hko0, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  obtain ⟨-, o0, ho0, hot⟩ := hko0 hko
  rw [ho] at ho0; obtain rfl := Option.some.inj ho0
  have htN : t < S.b.txs.length := (List.getElem?_eq_some_iff.mp htx).1
  have hN := S.hN25
  -- txid
  obtain ⟨qq, tx', -, htx', hdig, hlimbs⟩ := coin_txid hL hsat hL24 S hj2 hko htxi htN
  rw [htx] at htx'; obtain rfl := Option.some.inj htx'
  -- index limbs
  have hv := coin_vout hL hsat hL24 S he hon hlen hst hf htg j hj hko t q tx htx hjq hq
  obtain ⟨b0, b1, bvhi, bc0, bc1, bchi⟩ := out_bytes hL hsat hL24 hj2 hko
  obtain ⟨hcode, hctx, hslen, hvlo, hclo⟩ := Coin.out_spec cs hj2 hko
  have hvl := out_vlimbs hL hsat hL24 hj2 hko
  rw [hv] at hvl
  have hvlo' : ((inst 14).main Coin.VLO j).val < 65536 := by
    rw [hvlo, Coin.pairV, ← Coin.cast_val ((inst 14).main (Coin.VB 0) j), ← Coin.cast_val ((inst 14).main (Coin.VB 1) j)]
    rw [show (((((inst 14).main (Coin.VB 0) j).val : ℕ) : F) + 256 * ((((inst 14).main (Coin.VB 1) j).val : ℕ) : F)) =
      ((((inst 14).main (Coin.VB 0) j).val + 256 * ((inst 14).main (Coin.VB 1) j).val : ℕ) : F) by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (show _ < 2 ^ 17 by omega) (by unfold P; norm_num))]; omega
  have hvq : q - tx.vin.length < 2 ^ 30 := by have := hq; omega
  obtain ⟨evlo, evhi⟩ := limbs_of_bytes hvlo' bvhi hvl hvq
  -- code limbs
  have hcbo := Coin.cbo_spec cs hj2
  rw [htxi] at hcbo
  have hcb : (inst 14).main Coin.CBO j = ((if t = 0 then 1 else 0 : ℕ) : F) := by
    have ht0 : (t : F) = 0 ↔ t = 0 := ⟨fun e => Coin.lift (a := t) (b := 0) (by simpa using e)
      (lt_of_lt_of_le (show t < 2 ^ 25 by omega) (by unfold P; norm_num)) (by unfold P; norm_num), fun e => by simp [e]⟩
    split_ifs with h0
    · simpa using hcbo.1.mpr (ht0.mpr h0)
    · rcases hcbo.2.1 with e | e
      · simpa using e
      · exact absurd (ht0.mp (hcbo.1.mp e)) h0
  have hclo' : ((inst 14).main Coin.CLO j).val < 65536 := by
    rw [hclo, Coin.pairV, ← Coin.cast_val ((inst 14).main (Coin.CB 0) j), ← Coin.cast_val ((inst 14).main (Coin.CB 1) j)]
    rw [show (((((inst 14).main (Coin.CB 0) j).val : ℕ) : F) + 256 * ((((inst 14).main (Coin.CB 1) j).val : ℕ) : F)) =
      ((((inst 14).main (Coin.CB 0) j).val + 256 * ((inst 14).main (Coin.CB 1) j).val : ℕ) : F) by push_cast; ring]
    rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (show _ < 2 ^ 17 by omega) (by unfold P; norm_num))]; omega
  have hcode' : (inst 14).main Coin.CLO j + 65536 * (inst 14).main Coin.CHI j = ((2 * h + if t = 0 then 1 else 0 : ℕ) : F) := by
    rw [hcode, hp2, hcb]; push_cast; ring
  obtain ⟨eclo, echi⟩ := limbs_of_bytes hclo' bchi hcode' (by split_ifs <;> omega)
  -- the fingerprint
  obtain ⟨len, hsl, hfit, hfp⟩ := coin_fp_out hL hsat hL24 S hj2 hko
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : ρ < 2 ^ Ls 1 := by have := S.hmn; omega
  have hrt := (coin_row_tok hL hsat hL24 S he hon hlen hst hj).1 hko
  obtain ⟨-, hT⟩ := hrt
  have hLEN : (inst 14).main Coin.LEN j = (inst 1).main Fields.LEN ρ := by
    have := congrArg (fun l => l.getD 2 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  have hSTART := hst j hj
  have hRl := len_R hL hsat hL24
  have hfitρ := S.hfit ρ hρm
  have hlenv : len = ((inst 1).main Fields.LEN ρ).val := by
    have e1 : ((len : ℕ) : F) = (inst 1).main Fields.LEN ρ := by rw [← hsl, hslen, hLEN]
    rw [← e1, ZMod.val_natCast_of_lt (lt_of_lt_of_le (show len < 2 ^ 25 by omega) (by unfold P; norm_num))]
  have hser : Spec.Block.serTxOut o = Fields.slice (Rb inst pub) ((inst 14).main Coin.START j).val len := by
    rw [← outTok_bytes hot, Fields.tok_bytes fs (Rb inst pub) S.hcs (hmk_R hL hsat hL24) hρn (S.hnp ρ hρm) hfitρ,
      hSTART, hlenv]
  have hlist : ((List.range len).map fun i =>
      emb ((((Rb inst pub).getD (((inst 14).main Coin.START j).val + i) 0).toNat : ℕ) : F)) =
      (Spec.Block.serTxOut o).map fun b => emb ((b.toNat : ℕ) : F) := by
    rw [hser]
    apply List.ext_getElem
    · simp [Fields.slice_length hfit]
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, Fields.slice]
      rw [List.getElem_take, List.getElem_drop, ← List.getD_eq_getElem _ 0]
  rw [hlist] at hfp
  have hFH : (⟨(inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
      (inst 14).main (Coin.FH + 3) j⟩ : Circuit.Q) =
      coordsOf (FpWalk.horner (FpWalk.gQ pub) ((Spec.Block.serTxOut o).map fun b => emb ((b.toNat : ℕ) : F))) := by
    rw [← hfp, coordsOf_toQ]
  have hslen' : (inst 14).main Coin.SLEN j = (((Spec.Block.serTxOut o).length : ℕ) : F) := by
    rw [hser, Fields.slice_length hfit, ← hsl]
  -- assemble
  rw [rowTuple_eq hL hsat hL24 hj2, tupleOf]
  simp only [← hFH]
  congr 1
  · apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < 16 := by simpa using h1
    rw [hlimbs i hi, half16_txidLimb _ hi, hdig]
  · simp only [List.cons.injEq, and_true]
    exact ⟨evlo, evhi, eclo, echi, trivial, trivial, trivial, trivial, hslen', by rw [hctx, htxi]⟩

omit hL hsat hL24 in
/-- A slice's element. -/
theorem slice_getD {R : Spec.Block.Bytes} {a l i : ℕ} (hi : i < l) (hal : a + l ≤ R.length) :
    (Fields.slice R a l).getD i 0 = R.getD (a + i) 0 := by
  rw [List.getD_eq_getElem _ _ (by rw [Fields.slice_length hal]; exact hi), List.getD_eq_getElem _ _ (by omega)]
  simp [Fields.slice, List.getElem_take, List.getElem_drop]

/-- **An input row's tuple is its claimed coin's.** For input `q` of transaction `t` (`t ≥ 1`): the
prevout's hash and index, and the claim of undo record `J` (URec row `rj`): its code (four undo bytes,
little-endian), its creating transaction's index (the next three), and its `serTxOut` (the record's undo
bytes from `S + 9`). -/
theorem coin_in_tuple (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {j t q : ℕ} {tx : Spec.Block.Tx} {i : Spec.Block.TxIn} (hj : j < e) (hki : (inst 14).main Coin.KI j = 1)
    (htx : S.b.txs[t]? = some tx) (hjq : j = ((parts.take t).map List.length).sum + q)
    (hq : q < tx.vin.length + tx.vout.length) (hi : tx.vin[q]? = some i) :
    ∃ rj < 2 ^ Ls 13, (inst 13).main URec.ON rj = 1 ∧ (inst 14).main Coin.J j = (inst 13).main URec.J rj ∧
      ∃ (code : ℕ) (ser : Spec.Block.Bytes) (ctx : ℕ),
        rowTuple inst pub (Ls 14) j = tupleOf (FpWalk.gQ pub) i.prevout.hash i.prevout.n code ser ctx ∧
        (inst 14).main Coin.CLO j + 65536 * (inst 14).main Coin.CHI j = (code : F) ∧
        (inst 14).main Coin.CTX j = (ctx : F) ∧ (inst 13).main URec.TL rj = (ser.length : F) ∧
        (∃ u0 : ℕ, (inst 13).main URec.S rj + 9 = (u0 : F) ∧ 9 ≤ u0 ∧ u0 + ser.length ≤ (pub 8).val ∧
          ser = (List.range ser.length).map (fun k => (Ub inst pub).getD (u0 + k) 0) ∧
          code = Spec.Block.le ((List.range 4).map fun k => (Ub inst pub).getD (u0 - 9 + k) 0) ∧
          ctx = Spec.Block.le ((List.range 3).map fun k => (Ub inst pub).getD (u0 - 5 + k) 0)) := by
  have cs := coin_sat hL hsat hL24
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ Ls 14 := by omega
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hRl := len_R hL hsat hL24
  have hU := undo_len hL hsat hL24
  have hcbi : (inst 14).main Coin.CBI j = 0 := by
    rcases Coin.kinds cs hj2 with h | h | h | h <;> simp_all
  have hkc : (inst 14).main Coin.KI j + (inst 14).main Coin.CBI j = 1 := by rw [hki, hcbi]; simp
  -- the row's input
  obtain ⟨t0, q0, tx0, htx0, htxi, hjq0, hq0, -, hki0⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  obtain ⟨-, i0, hi0, hit⟩ := hki0 hkc
  rw [hi] at hi0; obtain rfl := Option.some.inj hi0
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : ρ < 2 ^ Ls 1 := by have := S.hmn; omega
  obtain ⟨hkin, -⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hj).2 hkc
  -- the input token: the prevout's hash and index bytes
  have hSTART := hst j hj
  set sv := ((inst 14).main Coin.START j).val with hsv
  have hfitρ := S.hfit ρ hρm
  have htok : Fields.tokOf (inst 1).main (Rb inst pub) ρ = .inp (Fields.slice (Rb inst pub) sv 32)
      (Fields.slice (Rb inst pub) (sv + 32) 4) (Fields.slice (Rb inst pub) (sv + 36 + Fields.prefOf (inst 1).main ρ)
        ((inst 1).main Fields.VAL ρ).val)
      (Fields.slice (Rb inst pub) (sv + 36 + Fields.prefOf (inst 1).main ρ + ((inst 1).main Fields.VAL ρ).val) 4) := by
    have kat := Fields.kinds_at fs hρn (a := Fields.K_IN) (by decide) hkin
    unfold Fields.tokOf
    rw [if_neg (by rw [kat Fields.K_BLK (by decide)]; simp [Fields.K_BLK, Fields.K_IN]),
      if_neg (by rw [kat Fields.K_TXH (by decide)]; simp [Fields.K_TXH, Fields.K_IN]), if_pos hkin, hsv, hSTART]
  rw [htok] at hit
  obtain ⟨hh32, hix4, -, hprev, -, -⟩ := hit
  -- the prevout bytes
  have hpb : ∀ k < 36, ((inst 14).main (Coin.PB k) j).val = ((Rb inst pub).getD (sv + k) 0).toNat ∧ sv + k < (Rb inst pub).length := by
    intro k hk
    obtain ⟨hlt, hb⟩ := coin_prevout hL hsat hL24 hj2 hki hk
    have hsk : ((inst 14).main Coin.START j + (k : F)).val = sv + k := by
      have e : (inst 14).main Coin.START j + (k : F) = ((sv + k : ℕ) : F) := by rw [hsv]; push_cast; rw [Coin.cast_val]
      rw [e, ZMod.val_natCast_of_lt (lt_of_lt_of_le (show sv + k < 2 ^ 25 by
        have := coin_start_le hL hsat hL24 S hj2 ((hon j hj2).mpr hj); omega) (by unfold P; norm_num))]
    rw [hsk] at hlt hb
    exact ⟨hb, hlt⟩
  have hpbF : ∀ k < 36, (inst 14).main (Coin.PB k) j = ((((Rb inst pub).getD (sv + k) 0).toNat : ℕ) : F) := by
    intro k hk; rw [← Coin.cast_val ((inst 14).main (Coin.PB k) j), (hpb k hk).1]
  have hfit32 : sv + 32 ≤ (Rb inst pub).length := by have := (hpb 31 (by norm_num)).2; omega
  have hfit36 : sv + 36 ≤ (Rb inst pub).length := by have := (hpb 35 (by norm_num)).2; omega
  obtain ⟨-, -, -, -, -, hvlo, hvhi, htlb⟩ := Coin.in_spec cs hj2 hki
  -- the undo record
  obtain ⟨rj, hrj, honj, hJ, hclo, hchi, -, -, hcx⟩ := coin_urec hL hsat hL24 hj2 hki
  obtain ⟨len, htl, hsl, u0, hu0, hu0len, hfp⟩ := coin_fp_in hL hsat hL24 hj2 hki hrj honj hJ
  have hub : ∀ c < 7, ∃ u, u < (pub 8).val ∧ u + 9 = u0 + c ∧
      ((inst 13).main (URec.ucol c) rj).val = ((Ub inst pub).getD u 0).toNat := by
    intro c hc
    obtain ⟨u, hu, hpu, hb⟩ := urec_bytes hL hsat hL24 hrj honj (c := c) (by omega)
    refine ⟨u, hu, ?_, hb⟩
    apply Coin.lift _ (lt_of_lt_of_le (show u + 9 < 2 ^ 25 by omega) (by unfold P; norm_num))
      (lt_of_lt_of_le (show u0 + c < 2 ^ 25 by omega) (by unfold P; norm_num))
    push_cast; rw [← hpu, ← hu0]; ring
  obtain ⟨ua, -, hua, hba⟩ := hub 0 (by norm_num)
  have hu04 : 9 ≤ u0 := by omega
  have hcb : ∀ c < 4, (inst 13).main (URec.C c) rj = ((((Ub inst pub).getD (u0 - 9 + c) 0).toNat : ℕ) : F) := by
    intro c hc
    obtain ⟨u, -, hu, hb⟩ := hub c (by omega)
    have hcol : URec.ucol c = URec.C c := by simp [URec.ucol, hc]
    rw [hcol] at hb
    rw [show u0 - 9 + c = u by omega, ← hb]; exact (Coin.cast_val _).symm
  have hxb : ∀ c < 3, (inst 13).main (URec.X c) rj = ((((Ub inst pub).getD (u0 - 5 + c) 0).toNat : ℕ) : F) := by
    intro c hc
    obtain ⟨u, -, hu, hb⟩ := hub (4 + c) (by omega)
    have hcol : URec.ucol (4 + c) = URec.X c := by simp [URec.ucol]; omega
    rw [hcol] at hb
    rw [show u0 - 5 + c = u by omega, ← hb]; exact (Coin.cast_val _).symm
  set ub := fun k => ((Ub inst pub).getD (u0 - 9 + k) 0).toNat with hubdef
  have hb256 : ∀ k, ub k < 256 := fun k => UInt8.toNat_lt _
  set code := Spec.Block.le ((List.range 4).map fun k => (Ub inst pub).getD (u0 - 9 + k) 0) with hcode
  have hcodev : code = ub 0 + 256 * (ub 1 + 256 * (ub 2 + 256 * ub 3)) := by
    simp [hcode, Spec.Block.le, List.range_succ, hubdef]
  set ctxv := Spec.Block.le ((List.range 3).map fun k => (Ub inst pub).getD (u0 - 5 + k) 0) with hctxv
  have hctxF : (inst 14).main Coin.CTX j = ((ctxv : ℕ) : F) := by
    rw [hcx, hxb 0 (by norm_num), hxb 1 (by norm_num), hxb 2 (by norm_num), hctxv]
    simp [Spec.Block.le, List.range_succ]; ring
  -- the claimed bytes
  set ser : Spec.Block.Bytes := (List.range len).map fun k => (Ub inst pub).getD (u0 + k) 0 with hser
  have hserlen : ser.length = len := by simp [hser]
  have hFH : (⟨(inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
      (inst 14).main (Coin.FH + 3) j⟩ : Circuit.Q) =
      coordsOf (FpWalk.horner (FpWalk.gQ pub) (ser.map fun b => emb ((b.toNat : ℕ) : F))) := by
    have hl : (ser.map fun b => emb ((b.toNat : ℕ) : F)) =
        (List.range len).map fun k => emb ((((Ub inst pub).getD (u0 + k) 0).toNat : ℕ) : F) := by
      simp [hser, List.map_map, Function.comp]
    rw [hl, ← hfp, coordsOf_toQ]
  refine ⟨rj, hrj, honj, hJ, code, ser, ctxv, ?_, ?_, hctxF, by rw [hserlen]; exact htl,
    u0, hu0, hu04, by rw [hserlen]; exact hu0len, by rw [hserlen], rfl, rfl⟩
  · rw [rowTuple_eq hL hsat hL24 hj2, tupleOf]
    simp only [← hFH]
    rw [hprev]
    congr 1
    · apply List.ext_getElem (by simp)
      intro k h1 h2
      simp only [List.getElem_map, List.getElem_range]
      have hk : k < 16 := by simpa using h1
      rw [htlb k hk]
      unfold Coin.prevLimb txidLimb
      have e := fun (a : ℕ) (ha : a < 32) => slice_getD (R := Rb inst pub) (a := sv) (l := 32) (i := a) ha hfit32
      split_ifs with hpar
      · simp only [Coin.pair, Expr.eval, Coin.ev_k hj2, StarkedAir.Sha256.eval_cst, Nat.cast_ofNat]
        rw [hpbF _ (by omega), hpbF _ (by omega), e _ (by omega), e _ (by omega)]; push_cast; ring
      · simp only [Coin.pair, Expr.eval, Coin.ev_k hj2, StarkedAir.Sha256.eval_cst, Nat.cast_ofNat]
        rw [hpbF _ (by omega), hpbF _ (by omega), e _ (by omega), e _ (by omega)]; push_cast; ring
    · have hfit36' : sv + 32 + 4 ≤ (Rb inst pub).length := by omega
      have e := fun (a : ℕ) (ha : a < 4) => slice_getD (R := Rb inst pub) (a := sv + 32) (l := 4) (i := a) ha hfit36'
      have hix : Spec.Block.le (Fields.slice (Rb inst pub) (sv + 32) 4) =
          ((Rb inst pub).getD (sv + 32) 0).toNat + 256 * (((Rb inst pub).getD (sv + 33) 0).toNat +
            256 * (((Rb inst pub).getD (sv + 34) 0).toNat + 256 * ((Rb inst pub).getD (sv + 35) 0).toNat)) := by
        have h4 : Fields.slice (Rb inst pub) (sv + 32) 4 = [(Rb inst pub).getD (sv + 32) 0, (Rb inst pub).getD (sv + 33) 0,
            (Rb inst pub).getD (sv + 34) 0, (Rb inst pub).getD (sv + 35) 0] := by
          apply List.ext_getElem (by rw [Fields.slice_length hfit36']; rfl)
          intro a h1 h2
          rw [← List.getD_eq_getElem _ 0 h1, e a (by rw [Fields.slice_length hfit36'] at h1; exact h1)]
          have : a < 4 := by rw [Fields.slice_length hfit36'] at h1; exact h1
          interval_cases a <;> simp
        rw [h4]; simp [Spec.Block.le]
      have r32 := UInt8.toNat_lt ((Rb inst pub).getD (sv + 32) 0)
      have r33 := UInt8.toNat_lt ((Rb inst pub).getD (sv + 33) 0)
      have r34 := UInt8.toNat_lt ((Rb inst pub).getD (sv + 34) 0)
      have r35 := UInt8.toNat_lt ((Rb inst pub).getD (sv + 35) 0)
      simp only [List.cons.injEq, and_true]
      refine ⟨?_, ?_, ?_, ?_, trivial, trivial, trivial, trivial, ?_, ?_⟩
      · rw [hvlo, Coin.pairV, hpbF 32 (by norm_num), hpbF 33 (by norm_num), hix]
        rw [show ((Rb inst pub).getD (sv + 32) 0).toNat + 256 * (((Rb inst pub).getD (sv + 33) 0).toNat +
            256 * (((Rb inst pub).getD (sv + 34) 0).toNat + 256 * ((Rb inst pub).getD (sv + 35) 0).toNat)) =
            (((Rb inst pub).getD (sv + 32) 0).toNat + 256 * ((Rb inst pub).getD (sv + 33) 0).toNat) +
              65536 * (((Rb inst pub).getD (sv + 34) 0).toNat + 256 * ((Rb inst pub).getD (sv + 35) 0).toNat) by ring]
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]; push_cast; ring
      · rw [hvhi, Coin.pairV, hpbF 34 (by norm_num), hpbF 35 (by norm_num), hix]
        rw [show ((Rb inst pub).getD (sv + 32) 0).toNat + 256 * (((Rb inst pub).getD (sv + 33) 0).toNat +
            256 * (((Rb inst pub).getD (sv + 34) 0).toNat + 256 * ((Rb inst pub).getD (sv + 35) 0).toNat)) =
            (((Rb inst pub).getD (sv + 32) 0).toNat + 256 * ((Rb inst pub).getD (sv + 33) 0).toNat) +
              65536 * (((Rb inst pub).getD (sv + 34) 0).toNat + 256 * ((Rb inst pub).getD (sv + 35) 0).toNat) by ring]
        rw [Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega), zero_add]; push_cast; ring
      · rw [hclo, hcb 0 (by norm_num), hcb 1 (by norm_num), hcodev]
        have := hb256 0; have := hb256 1; have := hb256 2; have := hb256 3
        rw [show ub 0 + 256 * (ub 1 + 256 * (ub 2 + 256 * ub 3)) = (ub 0 + 256 * ub 1) + 65536 * (ub 2 + 256 * ub 3) by ring,
          Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
        simp only [hubdef]; push_cast; ring
      · rw [hchi, hcb 2 (by norm_num), hcb 3 (by norm_num), hcodev]
        have := hb256 0; have := hb256 1; have := hb256 2; have := hb256 3
        rw [show ub 0 + 256 * (ub 1 + 256 * (ub 2 + 256 * ub 3)) = (ub 0 + 256 * ub 1) + 65536 * (ub 2 + 256 * ub 3) by ring,
          Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt (by omega), zero_add]
        simp only [hubdef]; push_cast; ring
      · rw [hsl, hserlen]
      · exact hctxF
  · rw [hclo, hchi, hcb 0 (by norm_num), hcb 1 (by norm_num), hcb 2 (by norm_num), hcb 3 (by norm_num), hcodev]
    simp only [hubdef]; push_cast; ring

/-- **Unspendable, as Core decides it.** For an output row whose script `s` has length `SVAL` and first
byte `SB` (when nonempty), `UNSP` is Boolean and is 1 exactly when `s` starts with `OP_RETURN` or is over
10,000 bytes (`Spec.Coins.unspendable`). -/
theorem coin_unsp {j : ℕ} (hj : j < 2 ^ Ls 14) (hko : (inst 14).main Coin.KO j = 1) (s : Spec.Block.Bytes)
    (hsl : ((inst 14).main Coin.SVAL j).val = s.length) (hsb : ∀ b ∈ s.head?, ((inst 14).main Coin.SB j).val = b.toNat)
    (hsmall : s.length ≤ 2 ^ 25) :
    ((inst 14).main Coin.UNSP j = 1 ↔ (s.head? == some 0x6a || decide (10000 < s.length)) = true) ∧
      ((inst 14).main Coin.UNSP j = 0 ∨ (inst 14).main Coin.UNSP j = 1) := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨hzs, hu6a, hbig1, hbig0, hunsp⟩ := Coin.unsp_spec cs hj hko
  have bzs := Coin.bool_col cs (c := Coin.ZS) (by simp) hj
  have bu6 := Coin.bool_col cs (c := Coin.U6A) (by simp) hj
  have bbig := Coin.bool_col cs (c := Coin.BIG) (by simp) hj
  have ek : (Coin.k Coin.KO).eval (2 ^ Ls 14) Coin.preCols pub (inst 14).main j = 1 := by rw [Coin.ev_k hj]; exact hko
  have hgb : ∀ i < 3, ((inst 14).main (Coin.GB i) j).val < 256 := by
    intro i hi
    have fam : Coin.lookups.getD (61 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.GB i)) (Coin.k Coin.KO) := by
      interval_cases i <;> rfl
    exact coin_r8 hL hsat hL24 (k := 61 + i) (by omega) (by omega) fam hj ek
  have hgbn := Coin.b3N_lt hgb
  have hP := Coin.P_big
  -- the script length's facts
  have hsv : (inst 14).main Coin.SVAL j = ((s.length : ℕ) : F) := by rw [← hsl, Coin.cast_val]
  have hzsv : (inst 14).main Coin.ZS j = 1 ↔ s = [] := by
    rw [hzs, hsv]
    constructor
    · intro h; have := Coin.lift (a := s.length) (b := 0) (by simpa using h) (by omega) (by omega)
      exact List.length_eq_zero_iff.mp this
    · intro h; simp [h]
  have hbig : (inst 14).main Coin.BIG j = 1 ↔ 10000 < s.length := by
    constructor
    · intro h
      have e := hbig1 h
      rw [Coin.b3V_eq, hsv] at e
      have := Coin.lift (a := Coin.b3N (inst 14).main Coin.GB j + 10001) (b := s.length) (by push_cast; rw [e]; ring)
        (by omega) (by omega)
      omega
    · intro h
      rcases bbig with b | b
      · exfalso
        have e := hbig0 b
        rw [Coin.b3V_eq, hsv] at e
        have := Coin.lift (a := Coin.b3N (inst 14).main Coin.GB j + s.length) (b := 10000) (by push_cast; rw [e]; ring)
          (by omega) (by omega)
        omega
      · exact b
  have hhead : (s.head? == some 0x6a) = true ↔ s ≠ [] ∧ (inst 14).main Coin.SB j = 0x6a := by
    cases s with
    | nil => simp
    | cons b s' =>
      have hb := hsb b (by simp)
      simp only [List.head?_cons, ne_eq, reduceCtorEq, not_false_eq_true, true_and]
      constructor
      · intro h
        have hb6 : b = 0x6a := by simpa using h
        rw [← Coin.cast_val ((inst 14).main Coin.SB j), hb, hb6]; rfl
      · intro h
        have : b.toNat = 106 := by
          rw [← hb, h]; rfl
        have hb6 : b = 0x6a := UInt8.toNat_inj.mp (by simpa using this)
        simp [hb6]
  have key : ∀ z u g : F, (z = 0 ∨ z = 1) → (u = 0 ∨ u = 1) → (g = 0 ∨ g = 1) →
      ((u * (1 - z) + g - u * (1 - z) * g = 1 ↔ (u = 1 ∧ z = 0) ∨ g = 1) ∧
        (u * (1 - z) + g - u * (1 - z) * g = 0 ∨ u * (1 - z) + g - u * (1 - z) * g = 1)) := by
    intro z u g hz hu hg
    rcases hz with rfl | rfl <;> rcases hu with rfl | rfl <;> rcases hg with rfl | rfl <;> decide
  obtain ⟨k1, k2⟩ := key _ _ _ bzs bu6 bbig
  rw [hunsp]
  refine ⟨?_, k2⟩
  rw [k1, Bool.or_eq_true, hhead, decide_eq_true_eq, ← hbig, hu6a]
  constructor
  · rintro (⟨h1, h2⟩ | h)
    · left; exact ⟨fun e => by rw [(hzsv.mpr e)] at h2; exact one_ne_zero h2, h1⟩
    · right; exact h
  · rintro (⟨h1, h2⟩ | h)
    · left
      refine ⟨h2, ?_⟩
      rcases bzs with z | z
      · exact z
      · exact absurd (hzsv.mp z) h1
    · right; exact h

/-- **An output row's multiplicity**: 1 for a spendable output that is not a lost coinbase output (the
public lost bit, for transaction 0), else 0. -/
theorem coin_out_mm (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {lost : Bool} (hlost : pub Coin.PUB_LOST = if lost then 1 else 0)
    {j t q : ℕ} {tx : Spec.Block.Tx} {o : Spec.Block.TxOut} (hj : j < e) (hko : (inst 14).main Coin.KO j = 1)
    (htx : S.b.txs[t]? = some tx) (hjq : j = ((parts.take t).map List.length).sum + q)
    (hq : q < tx.vin.length + tx.vout.length) (ho : tx.vout[q - tx.vin.length]? = some o) :
    (inst 14).main Coin.MM j = if !Spec.Coins.unspendable o && !(t == 0 && lost) then 1 else 0 := by
  have cs := coin_sat hL hsat hL24
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ Ls 14 := by omega
  obtain ⟨t0, q0, tx0, htx0, htxi, hjq0, hq0, hko0, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  obtain ⟨-, o0, ho0, hot⟩ := hko0 hko
  rw [ho] at ho0; obtain rfl := Option.some.inj ho0
  have hki : (inst 14).main Coin.KI j = 0 := by
    rcases Coin.kinds cs hj2 with h | h | h | h <;> simp_all
  -- the script
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : ρ < 2 ^ Ls 1 := by have := S.hmn; omega
  obtain ⟨hk, hT⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hj).1 hko
  have hSSC : (inst 14).main Coin.SSC j = (inst 1).main Fields.SSC ρ := by
    have := congrArg (fun l => l.getD 3 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  have hSVAL : (inst 14).main Coin.SVAL j = (inst 1).main Fields.VAL ρ := by
    have := congrArg (fun l => l.getD 4 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  obtain ⟨hvmax, hlenv, -, -, hfitv⟩ := Fields.row_info fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hρm (a := Fields.K_OUT)
    (by decide) hk (by decide) (by decide)
  have hssc := Fields.ssc_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hρm (a := Fields.K_OUT) (Or.inr rfl) hk
  simp only [show ¬ (Fields.K_OUT = Fields.K_IN) by decide, if_false] at hssc
  have htok : Fields.tokOf (inst 1).main (Rb inst pub) ρ = .out (Fields.slice (Rb inst pub) ((inst 1).main Fields.START ρ).val 8)
      (Fields.slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val ((inst 1).main Fields.VAL ρ).val) := by
    have kat := Fields.kinds_at fs hρn (a := Fields.K_OUT) (by decide) hk
    unfold Fields.tokOf
    rw [if_neg (by rw [kat Fields.K_BLK (by decide)]; simp [Fields.K_BLK, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_TXH (by decide)]; simp [Fields.K_TXH, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_IN (by decide)]; simp [Fields.K_IN, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_NOUT (by decide)]; simp [Fields.K_NOUT, Fields.K_OUT]), if_pos hk, hssc]
  rw [htok] at hot
  obtain ⟨-, -, hscript⟩ := hot
  have hsfit : ((inst 1).main Fields.SSC ρ).val + ((inst 1).main Fields.VAL ρ).val ≤ (Rb inst pub).length := by
    rw [hssc]; rw [hlenv] at hfitv; simp [Fields.lenN, Fields.K_OUT, Fields.K_BLK, Fields.K_TXH, Fields.K_IN,
      Fields.K_NOUT] at hfitv; omega
  have hslen : o.scriptPubKey.length = ((inst 1).main Fields.VAL ρ).val := by rw [hscript, Fields.slice_length hsfit]
  have hzs := (Coin.unsp_spec cs hj2 hko).1
  obtain ⟨hU, hUb⟩ := coin_unsp hL hsat hL24 hj2 hko o.scriptPubKey (by rw [hSVAL, hslen]) (by
      intro b hb
      have hne : o.scriptPubKey ≠ [] := by intro h; rw [h] at hb; simp at hb
      have hz : (inst 14).main Coin.ZS j = 0 := by
        rcases Coin.bool_col cs (c := Coin.ZS) (by simp) hj2 with z | z
        · exact z
        · exfalso; apply hne
          have h0 := hzs.mp z
          rw [hSVAL, ← Coin.cast_val ((inst 1).main Fields.VAL ρ), ← hslen] at h0
          have hsP : o.scriptPubKey.length < P := by
            rw [hslen]; exact lt_of_le_of_lt hvmax (by unfold Fields.MAXS P; norm_num)
          exact List.length_eq_zero_iff.mp (Coin.lift (b := 0) (by simpa using h0) hsP (by unfold P; norm_num))
      obtain ⟨-, hsb⟩ := coin_script_byte hL hsat hL24 hj2 hko hz
      rw [hsb, hSSC]
      have hb0 : b = o.scriptPubKey.getD 0 0 := by
        cases hs : o.scriptPubKey with
        | nil => exact absurd hs hne
        | cons c cs' => rw [hs] at hb; simp at hb; simp [hb]
      rw [hb0, hscript, slice_getD (by have := List.length_pos_of_ne_nil hne; omega) hsfit, Nat.add_zero])
    (by rw [hslen]; exact hvmax)
  -- the multiplicity
  have hmm := Coin.mm_spec cs hj2
  rw [hko, hki, one_mul, sub_zero] at hmm
  have hcbo := Coin.cbo_spec cs hj2
  rw [htxi] at hcbo
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have htN : t < 2 ^ Ls 1 := by have := (List.getElem?_eq_some_iff.mp htx).1; have := S.hN25; omega
  have ht0 : (t : F) = 0 ↔ t = 0 := ⟨fun e => Coin.lift (a := t) (b := 0) (by simpa using e)
    (lt_of_lt_of_le (show t < 2 ^ 25 by omega) (by unfold P; norm_num)) (by unfold P; norm_num), fun e => by simp [e]⟩
  have hcb : (inst 14).main Coin.CBO j = if t = 0 then 1 else 0 := by
    split_ifs with h0
    · exact hcbo.1.mpr (ht0.mpr h0)
    · rcases hcbo.2.1 with e | e
      · exact e
      · exact absurd (ht0.mp (hcbo.1.mp e)) h0
  rw [hmm, hcb, hlost]
  unfold Spec.Coins.unspendable
  rcases hUb with u | u <;> rw [u] at hU ⊢
  · have hn : (o.scriptPubKey.head? == some 0x6a || decide (10000 < o.scriptPubKey.length)) = false := by
      by_contra hc; simp only [Bool.not_eq_false] at hc; exact zero_ne_one (hU.mpr hc)
    rw [hn]
    by_cases h0 : t = 0 <;> cases lost <;> simp [h0]
  · have hn : (o.scriptPubKey.head? == some 0x6a || decide (10000 < o.scriptPubKey.length)) = true := hU.mp rfl
    rw [hn]
    simp

/-! ### The block's partial sum -/

/-- A tuple's fingerprint `Σₖ αₖ tₖ` against the public weights. -/
noncomputable def phiOf (pub : ℕ → F) (tu : List F) : QM :=
  ((List.range Coin.W).map fun k => RunSum.pQ pub (Coin.PUB_ALPHA k) * emb (tu.getD k 0)).sum

omit hL hsat hL24 in
theorem phiQ_eq {j : ℕ} : Coin.phiQ pub (inst 14).main (2 ^ Ls 14) j = phiOf pub (rowTuple inst pub (Ls 14) j) := by
  unfold Coin.phiQ phiOf rowTuple
  congr 1

/-- A position's term in the block's partial sum: a created output's fraction, a spend's (negated, with
the row's claimed tuple), or nothing. -/
noncomputable def blockTerm (inst : ℕ → Inst) (pub : ℕ → F) (L : ℕ) (txs : List Spec.Block.Tx)
    (parts : List (List Spec.Block.Tok)) (h : ℕ) (lost : Bool) (t q : ℕ) : QM :=
  let z := RunSum.pQ pub Coin.PUB_Z
  match txs[t]? with
  | none => 0
  | some tx =>
    if tx.vin.length ≤ q then
      match tx.vout[q - tx.vin.length]? with
      | some o => if (!Spec.Coins.unspendable o && !(t == 0 && lost)) then
          (z - phiOf pub (tupleOf (FpWalk.gQ pub) (Spec.Block.txid tx) (q - tx.vin.length)
            (2 * h + if t = 0 then 1 else 0) (Spec.Block.serTxOut o) t))⁻¹ else 0
      | none => 0
    else if 1 ≤ t then -(z - phiOf pub (rowTuple inst pub L (((parts.take t).map List.length).sum + q)))⁻¹ else 0

/-- **The block's partial sum, by its coin events.** The public partial sum is, over the block's
transactions and their input/output positions: each created output's `1/(z − φ)` (with its coin's
tuple), minus each non-coinbase input's `1/(z − φ)` (with its row's claimed tuple). -/
theorem coin_block_sum (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23) {lost : Bool} (hlost : pub Coin.PUB_LOST = if lost then 1 else 0) :
    RunSum.pQ pub Coin.PUB_S = ∑ t ∈ Finset.range S.b.txs.length, ∑ q ∈ Finset.range ((parts.getD t []).length),
      blockTerm inst pub (Ls 14) S.b.txs parts h lost t q := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨hS, hrow⟩ := Coin.coin_runsum cs (n := 2 ^ Ls 14) (by positivity)
  rw [hS]
  -- e is the total length
  have hft := fields_tagged hL hsat hL24 S
  rw [htg] at hft
  have he' : e = (parts.map List.length).sum := by
    rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
  -- rows from e on contribute nothing
  have hoff : ∀ r ∈ Finset.range (2 ^ Ls 14), e ≤ r → RunSum.cQ (inst 14).main Coin.FC r = 0 := by
    intro r hr her
    have hr' := Finset.mem_range.mp hr
    apply (hrow r hr').2
    have hoff : Coin.onV (inst 14).main r = 0 := by
      rcases Coin.on_bool cs hr' with z | z
      · exact z
      · exact absurd ((hon r hr').mp z) (by omega)
    rw [Coin.mm_spec cs hr']
    rcases Coin.kinds cs hr' with k | k | k | k
    · rw [k.2.2.2] at hoff; exact absurd hoff one_ne_zero
    · rw [k.2.2.2] at hoff; exact absurd hoff one_ne_zero
    · rw [k.2.2.2] at hoff; exact absurd hoff one_ne_zero
    · rw [k.1, k.2.1]; ring
  rw [← Finset.sum_range_add_sum_Ico _ (show e ≤ 2 ^ Ls 14 by omega),
    Finset.sum_eq_zero (fun r hr => hoff r (Finset.mem_range.mpr (Finset.mem_Ico.mp hr).2) (Finset.mem_Ico.mp hr).1),
    add_zero, he', sum_by_parts, List.length_map, ← hf.length_eq]
  apply Finset.sum_congr rfl
  intro t ht
  have htl := Finset.mem_range.mp ht
  obtain ⟨tx, htx⟩ := exists_get htl
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  have hlens : (parts.map List.length).getD t 0 = (parts.getD t []).length := by
    rw [List.getD_eq_getElem _ _ (by simpa using hpl), List.getElem_map, List.getD_eq_getElem _ _ hpl]
  have htake : ((parts.map List.length).take t).sum = ((parts.take t).map List.length).sum := by
    rw [List.map_take]
  rw [hlens]
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_range.mp hq
  rw [htake]
  set j := ((parts.take t).map List.length).sum + q with hjdef
  have hj : j < e := by
    have := pre_succ parts hpl
    have := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
    rw [he', ← List.take_length (l := parts), ← List.take_length (l := parts)] at *
    simp only [List.take_length] at *; omega
  have hj2 : j < 2 ^ Ls 14 := by omega
  have hqt : q < tx.vin.length + tx.vout.length := by omega
  obtain ⟨hko, hki, hcbi⟩ := coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg hj htx hjdef hqt
  obtain ⟨hfrac, hzero⟩ := hrow j hj2
  rw [phiQ_eq] at hfrac
  simp only [blockTerm, htx]
  by_cases hout : tx.vin.length ≤ q
  · rw [if_pos hout]
    obtain ⟨o, ho⟩ := exists_get (show q - tx.vin.length < tx.vout.length by omega)
    simp only [ho]
    have hko1 := hko.mpr hout
    have hmm := coin_out_mm hL hsat hL24 S he hon hlen hst hf htg hlost hj hko1 htx hjdef hqt ho
    have htu := coin_out_tuple hL hsat hL24 S he hon hlen hst hf htg hp2 hh hj hko1 htx hjdef hqt ho
    rw [hmm] at hfrac hzero
    by_cases hlive : (!Spec.Coins.unspendable o && !(t == 0 && lost)) = true
    · rw [if_pos hlive] at hfrac ⊢
      rw [htu, Spec.QM31.emb_one] at hfrac
      exact eq_inv_of_mul_eq_one_right hfrac
    · rw [if_neg hlive] at hzero ⊢
      exact hzero rfl
  · rw [if_neg hout]
    split_ifs with ht1
    · have hki1 := hki.mpr ⟨by omega, ht1⟩
      have hmm := Coin.mm_spec cs hj2
      have hko0 : (inst 14).main Coin.KO j = 0 := by
        rcases Coin.kinds cs hj2 with k | k | k | k
        · rw [k.2.1] at hki1; exact absurd hki1 zero_ne_one
        · exact k.1
        · rw [k.2.1] at hki1; exact absurd hki1 zero_ne_one
        · rw [k.2.1] at hki1; exact absurd hki1 zero_ne_one
      rw [hko0, hki1, zero_mul, zero_sub] at hmm
      have hneg : emb (-1 : F) = -1 := by simp [Spec.QM31.emb]
      rw [hmm, hneg] at hfrac
      have : (RunSum.pQ pub Coin.PUB_Z - phiOf pub (rowTuple inst pub (Ls 14) j)) * -RunSum.cQ (inst 14).main Coin.FC j = 1 := by
        rw [mul_neg, hfrac, neg_neg]
      rw [← neg_neg (RunSum.cQ (inst 14).main Coin.FC j), eq_inv_of_mul_eq_one_right this]
    · have hcbi1 := hcbi.mpr ⟨by omega, by omega⟩
      apply hzero
      rw [Coin.mm_spec cs hj2]
      rcases Coin.kinds cs hj2 with k | k | k | k
      · rw [k.2.2.1] at hcbi1; exact absurd hcbi1 zero_ne_one
      · rw [k.2.2.1] at hcbi1; exact absurd hcbi1 zero_ne_one
      · rw [k.1, k.2.1]; ring
      · rw [k.2.2.1] at hcbi1; exact absurd hcbi1 zero_ne_one

end System

end StarkedAir.Block
