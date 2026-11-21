/-
**Time-based relative locks (BIP68), block level (CONNECT-RULES step 4).** An input whose time lock is
enforced carries, in its undo record, a claimed median time past `m` (4 bytes after the record's
`serTxOut`, so under the block commitment). `in_time_lock`: the block system then has
`m + 512 · lock ≤ MTP(h − 1)` (`Spec.Coins.timeLockOk`), with `MTP(h − 1)` the public inputs 3 and 7 that
the ancestry component proves. That `m` is the chain's median time past of the block before the coin's is
NOT proven here: the block adds the claim `(coin height, m)` to its public sum (`claimSum`,
`claim_frac`), to be consumed by the epoch's resolver.
-/
import StarkedAir.Block.CoinClaims

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo
open StarkedAir.Spec.QM31 (QM)
open StarkedAir.Sha256 (cst)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
include hL hsat hL24

/-- **A record's claim bytes.** On URec row `r`, claim byte `i` is the undo byte at `S + 9 + i + TL`. -/
theorem urec_mt_bytes {r : ℕ} (hr : r < 2 ^ Ls 13) (hon : (inst 13).main URec.ON r = 1) {i : ℕ} (hi : i < 4) :
    ∃ u, u < (pub 8).val ∧ (inst 13).main URec.S r + ((URec.HDR + i : ℕ) : F) + (inst 13).main URec.TL r = (u : F) ∧
      ((inst 13).main (URec.MT i) r).val = ((Ub inst pub).getD u 0).toNat := by
  have hpre : (hashSys.comp 13).air.pre = URec.preCols := rfl
  have hlen : 24 + i < (hashSys.comp 13).lookups.length := by
    show 24 + i < URec.lookups.length
    simp [URec.lookups]; omega
  have hsite := site_mem hL (i := 13) (by decide) hr hlen
  have hsl : siteLookup hashSys ((13, r, 24 + i) : Site) =
      ⟨Undo.REL_UBYTE, .neg (URec.k URec.ON),
        [.add (.add (URec.k URec.S) (cst (URec.HDR + i))) (URec.k URec.TL), URec.k (URec.MT i)]⟩ := by
    interval_cases i <;> rfl
  have huse : isUse 13 (24 + i) = true := by interval_cases i <;> rfl
  obtain ⟨u, hu, hp, hb⟩ := undo_read hL hsat hL24 hsite huse (by simp [siteRel, hsl])
    (p := (inst 13).main URec.S r + ((URec.HDR + i : ℕ) : F) + (inst 13).main URec.TL r)
    (b := (inst 13).main (URec.MT i) r)
    (by
      show siteEval hashSys inst pub (13, r, 24 + i) (siteLookup hashSys (13, r, 24 + i)).mult = -1
      rw [hsl]
      simp [siteEval, hpre, hL 13 (by decide), Expr.eval, URec.k, StarkedAir.Sha256.eval_col, wrap_zero hr, hon])
    (by
      show (siteLookup hashSys (13, r, 24 + i)).vals.map (siteEval hashSys inst pub (13, r, 24 + i)) = _
      rw [hsl]
      simp [siteEval, hpre, hL 13 (by decide), Expr.eval, URec.k, StarkedAir.Sha256.eval_col,
        StarkedAir.Sha256.eval_cst, wrap_zero hr])
  exact ⟨u, hu, hp, hb⟩

/-- An input row's claimed median time past: two 16-bit limbs. -/
theorem coin_mtp_lt {j : ℕ} (hj : j < 2 ^ Ls 14) (hki : (inst 14).main Coin.KI j = 1) :
    ((inst 14).main Coin.ML j).val < 65536 ∧ ((inst 14).main Coin.MH j).val < 65536 := by
  obtain ⟨rj, hrj, hon, -, e1, e2⟩ := coin_urec_mtp hL hsat hL24 hj hki
  have hb : ∀ i < 4, ((inst 13).main (URec.MT i) rj).val < 256 := fun i hi => by
    obtain ⟨u, -, -, hb⟩ := urec_mt_bytes hL hsat hL24 hrj hon hi
    rw [hb]; exact UInt8.toNat_lt _
  have hP : P = 2147483647 := rfl
  have key : ∀ (a b x : F), a.val < 256 → b.val < 256 → x = a + 256 * b → x.val < 65536 := by
    intro a b x ha hb' hx
    have : x = ((a.val + 256 * b.val : ℕ) : F) := by rw [hx]; push_cast; simp only [ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast_of_lt (by omega)]; omega
  exact ⟨key _ _ _ (hb 0 (by norm_num)) (hb 1 (by norm_num)) e1, key _ _ _ (hb 2 (by norm_num)) (hb 3 (by norm_num)) e2⟩

/-- The range check of `2 · SA` on a time-locked row. -/
theorem coin_r8_2sa {r : ℕ} (hr : r < 2 ^ Ls 14)
    (hm : Coin.tm.eval (2 ^ Ls 14) Coin.preCols pub (inst 14).main r = 1) :
    ((2 : F) * (inst 14).main Coin.SA r).val < 256 := by
  have hlen : 102 < (hashSys.comp 14).lookups.length := by
    show 102 < Coin.lookups.length; rw [Coin.lookups_len]; norm_num
  have hs := site_mem hL (i := 14) (by decide) hr hlen
  have hsl : siteLookup hashSys ((14, r, 102) : Site) = Coin.r8 (.mul (cst 2) (Coin.k Coin.SA)) Coin.tm := rfl
  refine r8_lt hL hsat hL24 hs (by simp [isUse]) (by simp [siteRel, hsl, Coin.r8]) ?_
    (v := (2 : F) * (inst 14).main Coin.SA r) ?_
  · show siteEval hashSys inst pub (14, r, 102) (siteLookup hashSys (14, r, 102)).mult = -1
    rw [hsl]
    have hpre : (hashSys.comp 14).air.pre = Coin.preCols := rfl
    simp only [siteEval, Coin.r8, Expr.eval, hpre, hL 14 (by decide), hm]
  · show (siteLookup hashSys (14, r, 102)).vals.map (siteEval hashSys inst pub (14, r, 102)) = _
    rw [hsl]
    have hpre : (hashSys.comp 14).air.pre = Coin.preCols := rfl
    simp [siteEval, Coin.r8, hpre, hL 14 (by decide), Coin.k, Expr.eval, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hr]

/-- **An enforced time lock is met against the record's claim (BIP68, time-based).** For input `k` of
transaction `t` (coin row `j`, a non-coinbase input): when CSV is active at the block's height, the
transaction's version is at least 2, bit 31 of the input's sequence is clear and bit 22 is set, the claimed
median time past of the row (`ML`, `MH`: its undo record's four claim bytes, `coin_urec_mtp`) plus
`512 ·` the sequence's low 16 bits is at most the block's previous median time past (public inputs 3 and
7, 16-bit limbs). `pub 5` is the CSV bit. -/
theorem in_time_lock (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23)
    (hp5 : pub 5 = if Spec.Block.CSV_HEIGHT ≤ h then 1 else 0)
    (hp3 : (pub 3).val < 65536) (hp7 : (pub 7).val < 65536)
    {t k : ℕ} {tx : Spec.Block.Tx} {i : Spec.Block.TxIn} (htx : S.b.txs[t]? = some tx) (hi : tx.vin[k]? = some i)
    {j : ℕ} (hjq : j = ((parts.take t).map List.length).sum + k) (hje : j < e)
    (hki : (inst 14).main Coin.KI j = 1) :
    Spec.Coins.timeLockOk h tx.version i.sequence
      (((inst 14).main Coin.ML j).val + 65536 * ((inst 14).main Coin.MH j).val)
      ((pub 3).val + 65536 * (pub 7).val) = true := by
  unfold Spec.Coins.timeLockOk
  by_cases hen : (decide (Spec.Block.CSV_HEIGHT ≤ h) && decide (2 ≤ tx.version) &&
      decide (i.sequence / 2 ^ 31 % 2 = 0) && decide (i.sequence / 2 ^ 22 % 2 = 1)) = true
  swap
  · rw [Bool.not_eq_true] at hen; rw [hen]; rfl
  rw [hen]
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hen
  obtain ⟨⟨⟨hcsv, hv⟩, h31⟩, h22⟩ := hen
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq]
  have cs := coin_sat hL hsat hL24
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ Ls 14 := by omega
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hkc : (inst 14).main Coin.KI j + (inst 14).main Coin.CBI j = 1 := by
    rcases Coin.kinds cs hj2 with g | g | g | g
    · rw [g.2.1] at hki; exact absurd hki zero_ne_one
    · rw [g.2.1, g.2.2.1]; simp
    · rw [g.2.1] at hki; exact absurd hki zero_ne_one
    · rw [g.2.1] at hki; exact absurd hki zero_ne_one
  have hkl : k < tx.vin.length := (List.getElem?_eq_some_iff.mp hi).1
  -- the row's transaction and input
  obtain ⟨t0, q0, tx0, htx0, hT0, hjq0, hq0, -, hin0⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hje
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  obtain ⟨-, i0, hi0, hintok⟩ := hin0 hkc
  rw [hi] at hi0; obtain rfl := Option.some.inj hi0
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : ρ < 2 ^ Ls 1 := by have := S.hmn; omega
  obtain ⟨hkin, hTXI, hT⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hje).2 hkc
  -- the sequence: the input token's last four bytes
  rw [Fields.tok_in fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hρn hkin] at hintok
  obtain ⟨-, -, -, -, -, hseq⟩ := hintok
  -- the transaction's head and lock-time rows
  have htl : t < S.b.txs.length := (List.getElem?_eq_some_iff.mp htx).1
  obtain ⟨ρl, tx', hρl, hlk, hlocks, hget, hat⟩ := S.hsurj t htl
  rw [htx] at hget; obtain rfl := Option.some.inj hget
  have h25 : 2 ^ Ls 1 ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) (by have := hL24.1 1 (by decide); omega)
  obtain ⟨rh, hrh, ht, hnt, -, -, -, -, -, -, -, -, -, -, hlc⟩ :=
    Fields.tx_rows' fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit h25 hat hρl
  have hρln : ρl < 2 ^ Ls 1 := by have := S.hmn; omega
  -- the row's lock count is the transaction's index, so the row is one of the transaction's
  have hlρ : Fields.locks (inst 1).main ρ = t := by
    have e1 := Fields.txi_count fs ρ hρn
    have e2 : ((Fields.locks (inst 1).main ρ : ℕ) : F) = (t : F) := by rw [← e1, ← hTXI, hT0]
    have l1 := Fields.locks_le (M := (inst 1).main) ρ
    have l2 := S.hN25
    exact natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e2
  obtain ⟨hr1, hr2⟩ := Fields.row_in_tx fs h25 hrh hρln ht hlk (hlc rh le_rfl (by omega)) hρn hkin
    (by rw [hlρ, hlocks])
  -- the version: the head token's four bytes
  have hver : tx.version = Spec.Block.le (Fields.slice (Rb inst pub) ((inst 1).main Fields.START rh).val 4) := by
    obtain ⟨rh', hrh', ht', hnt', htxT⟩ := hat
    have hrr : rh' = rh := by
      rcases Nat.lt_trichotomy rh' rh with a | a | a
      · have := hnt' rh a (by omega); rw [ht] at this; exact absurd this one_ne_zero
      · exact a
      · have := hnt rh' a (by omega); rw [ht'] at this; exact absurd this one_ne_zero
    subst hrr
    rw [Fields.toksFrom_cons (by omega),
      Fields.tok_txh fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (by omega) ht] at htxT
    exact Spec.Block.txT_version htxT
  have hrgs : ∀ r < 2 ^ Ls 1, ∀ j < 13, ((inst 1).main (Fields.RG j) r).val < 256 :=
    fun r hr j hj => fields_rg_lt hL hsat hL24 hr hj
  -- the fields' bit and lock, received by the coin row
  have hlkt := Fields.lkt_of fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (hby_R hL hsat hL24 S) hrgs
    (hvb_R hL hsat hL24) h25 (le_of_lt hr1) hρm ht (fun j a b => hnt j a (by omega)) hkin
    (by rw [hp5, if_pos hcsv]) (by rw [← hver]; exact hv) hseq h31 h22
  have hSQL : (inst 14).main Coin.SQL j = ((i.sequence % 65536 : ℕ) : F) := by
    have := congrArg (fun l => l.getD 2 0) hT
    simp only [cIn, fIn, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]
    exact (Fields.seq_bits fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (hby_R hL hsat hL24 S) hrgs h25 hρm hkin hseq).2.2
  have hLKT : (inst 14).main Coin.LKT j = 1 := by
    have := congrArg (fun l => l.getD 4 0) hT
    simp only [cIn, fIn, List.getD_cons_succ, List.getD_cons_zero] at this
    rw [this]; exact hlkt
  -- the coin row's time lock is enforced
  obtain ⟨-, bSHB, bBW0, bBW1, hTMd⟩ := Coin.time_bits cs hj2
  have hTM : (inst 14).main Coin.TM j = 1 := by rw [hTMd, hki, hLKT]; ring
  have ek : Coin.tm.eval (2 ^ Ls 14) Coin.preCols pub (inst 14).main j = 1 := by
    rw [Coin.tm, Coin.ev_k hj2]; exact hTM
  have q0 := coin_r8 hL hsat hL24 (k := 97) (c := Coin.TQ 0) (by omega) (by omega) rfl hj2 ek
  have q1 := coin_r8 hL hsat hL24 (k := 98) (c := Coin.TQ 1) (by omega) (by omega) rfl hj2 ek
  have q2 := coin_r8 hL hsat hL24 (k := 99) (c := Coin.TQ 2) (by omega) (by omega) rfl hj2 ek
  have q3 := coin_r8 hL hsat hL24 (k := 100) (c := Coin.TQ 3) (by omega) (by omega) rfl hj2 ek
  have qa := coin_r8 hL hsat hL24 (k := 101) (c := Coin.SA) (by omega) (by omega) rfl hj2 ek
  have qh := coin_r8 hL hsat hL24 (k := 103) (c := Coin.SH0) (by omega) (by omega) rfl hj2 ek
  have qa2 := coin_r8_2sa hL hsat hL24 hj2 ek
  obtain ⟨hml, hmh⟩ := coin_mtp_lt hL hsat hL24 hj2 hki
  obtain ⟨t1, t2, t3⟩ := Coin.time_row cs hj2 hTM
  have hP : P = 2147483647 := rfl
  have hsa2 : 2 * ((inst 14).main Coin.SA j).val < 256 := by
    have e : (2 : F) * (inst 14).main Coin.SA j = ((2 * ((inst 14).main Coin.SA j).val : ℕ) : F) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [e, ZMod.val_natCast_of_lt (by omega)] at qa2; exact qa2
  have vb : ∀ {x : F}, (x = 0 ∨ x = 1) → x.val ≤ 1 := by
    rintro x (rfl | rfl)
    · simp
    · simp [ZMod.val_one]
  have lB := vb bSHB
  have l0 := vb bBW0
  have l1 := vb bBW1
  have hlock : i.sequence % 65536 = ((inst 14).main Coin.SA j).val + 128 * (((inst 14).main Coin.SH0 j).val + 256 * ((inst 14).main Coin.SHB j).val) := by
    apply Coin.lift _ (by omega) (by omega)
    rw [← hSQL, t1]; push_cast; simp only [ZMod.natCast_zmod_val]
  have hlo : (pub 3).val + 65536 * (((inst 14).main Coin.BW0 j).val + ((inst 14).main Coin.BW1 j).val) =
      ((inst 14).main (Coin.TQ 0) j).val + 256 * ((inst 14).main (Coin.TQ 1) j).val + ((inst 14).main Coin.ML j).val + 512 * ((inst 14).main Coin.SA j).val := by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; simp only [ZMod.natCast_zmod_val]
    linear_combination t2
  have hhi : (pub 7).val = ((inst 14).main (Coin.TQ 2) j).val + 256 * ((inst 14).main (Coin.TQ 3) j).val + ((inst 14).main Coin.MH j).val +
      (((inst 14).main Coin.SH0 j).val + 256 * ((inst 14).main Coin.SHB j).val) + (((inst 14).main Coin.BW0 j).val + ((inst 14).main Coin.BW1 j).val) := by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; simp only [ZMod.natCast_zmod_val]
    linear_combination t3
  rw [show (2 : ℕ) ^ 16 = 65536 by norm_num, hlock]
  omega

open StarkedAir.Spec.QM31 (emb emb_one emb_zero) in
/-- **The block's time claims, as fractions.** `claimSum` (the part of the public sum that is not coin
events, `coin_block_sum`) is one fraction `1/(z − φ₂)` per row whose time lock is enforced, `φ₂` the
weighted claim tuple of the row (`Coin.phi2Q`, `phi2Q_eq`). -/
theorem claim_sum_eq :
    claimSum inst (Ls 14) = ∑ r ∈ Finset.range (2 ^ Ls 14),
      if (inst 14).main Coin.TM r = 1 then
        (RunSum.pQ pub Coin.PUB_Z - Coin.phi2Q pub (inst 14).main (2 ^ Ls 14) r)⁻¹ else 0 := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨-, -, h2⟩ := Coin.coin_runsum cs (by positivity)
  unfold claimSum
  refine Finset.sum_congr rfl fun r hr => ?_
  have hr' := Finset.mem_range.mp hr
  obtain ⟨e1, e0⟩ := h2 r hr'
  obtain ⟨bL, -, -, -, hTM⟩ := Coin.time_bits cs hr'
  have hb : (inst 14).main Coin.TM r = 0 ∨ (inst 14).main Coin.TM r = 1 := by
    rcases Coin.bool_col cs (c := Coin.KI) (by simp) hr' with a | a <;> rcases bL with b | b <;> simp [hTM, a, b]
  rcases hb with h0 | h1
  · rw [if_neg (by rw [h0]; exact zero_ne_one), e0 h0]
  · rw [if_pos h1]
    rw [h1, emb_one] at e1
    exact eq_inv_of_mul_eq_one_right e1

omit hL hsat hL24 in
open StarkedAir.Spec.QM31 (emb emb_zero) in
/-- **A time claim's key**: the coin's height, the claimed time's two limbs, and the tag `65536` in slot 19
(a slot that holds a 16-bit limb in every coin tuple), weighted by the epoch's `αᵏ`. -/
theorem phi2Q_eq {n r : ℕ} (hr : r < n) {M : ℕ → ℕ → F} :
    Coin.phi2Q pub M n r = RunSum.pQ pub (Coin.PUB_ALPHA 0) * emb (M Coin.HC r) +
      RunSum.pQ pub (Coin.PUB_ALPHA 1) * emb (M Coin.ML r) + RunSum.pQ pub (Coin.PUB_ALPHA 2) * emb (M Coin.MH r) +
      RunSum.pQ pub (Coin.PUB_ALPHA 19) * emb (65536 : F) := by
  unfold Coin.phi2Q
  simp [Coin.W, List.range_succ, Coin.tuple2, List.replicate, Coin.CLAIM_TAG, Coin.k, StarkedAir.Sha256.eval_col,
    StarkedAir.Sha256.eval_cst, wrap_zero hr, emb_zero]
  ring

end System

end StarkedAir.Block
