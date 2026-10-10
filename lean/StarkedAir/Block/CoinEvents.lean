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

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- An output row's single-byte range checks: `VB 0`, `VB 1`, `VHI`, `CB 0`, `CB 1`, `CHI`. -/
theorem out_bytes {j : ℕ} (hj : j < 2 ^ L) (hko : (inst 14).main Coin.KO j = 1) :
    ((inst 14).main (Coin.VB 0) j).val < 256 ∧ ((inst 14).main (Coin.VB 1) j).val < 256 ∧
      ((inst 14).main Coin.VHI j).val < 256 ∧ ((inst 14).main (Coin.CB 0) j).val < 256 ∧
      ((inst 14).main (Coin.CB 1) j).val < 256 ∧ ((inst 14).main Coin.CHI j).val < 256 := by
  have ek : (Coin.k Coin.KO).eval (2 ^ L) Coin.preCols pub (inst 14).main j = 1 := by rw [Coin.ev_k hj]; exact hko
  exact ⟨coin_r8 hL hsat hL24 (k := 46) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 47) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 48) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 49) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 50) (by omega) (by omega) rfl hj ek,
    coin_r8 hL hsat hL24 (k := 51) (by omega) (by omega) rfl hj ek⟩

/-- An output row's index limbs: `VLO + 65536·VHI = VOUT`. -/
theorem out_vlimbs {j : ℕ} (hj : j < 2 ^ L) (hko : (inst 14).main Coin.KO j = 1) :
    (inst 14).main Coin.VLO j + 65536 * (inst 14).main Coin.VHI j = (inst 14).main Coin.VOUT j := by
  have cs := coin_sat hL hsat hL24
  have := Coin.sat cs (Coin.mem_local (c := .mul (Coin.k Coin.KO) (.sub (.add (Coin.k Coin.VLO)
    (.mul (StarkedAir.Sha256.cst 65536) (Coin.k Coin.VHI))) (Coin.k Coin.VOUT))) (by simp [Coin.localC])) hj
  simp only [Expr.eval, Coin.ev_k hj, StarkedAir.Sha256.eval_cst, Nat.cast_ofNat, hko, one_mul] at this
  linear_combination this

/-- The coin tuple at a row. -/
def rowTuple (inst : ℕ → Inst) (pub : ℕ → F) (L j : ℕ) : List F :=
  Coin.tuple.map fun ex => ex.eval (2 ^ L) Coin.preCols pub (inst 14).main j

theorem rowTuple_eq {j : ℕ} (hj : j < 2 ^ L) : rowTuple inst pub L j =
    (List.range 16).map (fun i => (inst 14).main (Coin.TLB i) j) ++
      [(inst 14).main Coin.VLO j, (inst 14).main Coin.VHI j, (inst 14).main Coin.CLO j, (inst 14).main Coin.CHI j,
        (inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
        (inst 14).main (Coin.FH + 3) j, (inst 14).main Coin.SLEN j, (inst 14).main Coin.CTX j] := by
  simp [rowTuple, Coin.tuple, Coin.ev_k hj, List.map_append, Function.comp]

/-- **An output row's tuple is its coin's.** The created coin of output `q − |vin|` of transaction `t`:
its txid, index, code `2·height + [t = 0]`, `serTxOut`, and creating transaction `t`. -/
theorem coin_out_tuple (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23)
    {j t q : ℕ} {tx : Spec.Block.Tx} {o : Spec.Block.TxOut} (hj : j < e) (hko : (inst 14).main Coin.KO j = 1)
    (htx : S.b.txs[t]? = some tx) (hjq : j = ((parts.take t).map List.length).sum + q)
    (hq : q < tx.vin.length + tx.vout.length) (ho : tx.vout[q - tx.vin.length]? = some o) :
    rowTuple inst pub L j = tupleOf (FpWalk.gQ pub) (Spec.Block.txid tx) (q - tx.vin.length)
      (2 * h + if t = 0 then 1 else 0) (Spec.Block.serTxOut o) t := by
  have cs := coin_sat hL hsat hL24
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ L := by omega
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
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
  have hρn : ρ < 2 ^ L := by have := S.hmn; omega
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

end System

end StarkedAir.Block
