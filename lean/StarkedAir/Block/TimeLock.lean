/-
**Time-based relative locks (BIP68), block level (CONNECT-RULES step 4; D-058, R5).** Every coin carries
its time: the median time past of the block before its creating block, 4 bytes after its `serTxOut` in
the bytes the coin tuple fingerprints (`Spec.CoinEpoch.coinBytes`). An output's time is the block's own
previous median time past (public inputs 3 and 7, `coin_out_tuple`); an input's is its undo record's four
time bytes (`coin_in_tuple`, `ClaimAt`), under the block commitment.

`in_time_lock`: for an input whose time lock is enforced, the block system has
`claim.mtp + 512 · lock ≤ MTP(h − 1)` (`Spec.Coins.timeLockOk`), with `MTP(h − 1)` the public inputs 3 and 7
that the ancestry component proves. That the claim's time is the coin's own is the epoch's coin balance:
the spent event `(prevout, (code, serTxOut ‖ time), index)` equals a created or an initial one
(`SigEpoch.epoch_systems_coreS`).
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

/-- **The public median time past is two 16-bit limbs** when the block has an output row: its time bytes
are range-checked and are those limbs' bytes. -/
theorem pub_mtp_lt {j : ℕ} (hj : j < 2 ^ Ls 14) (hko : (inst 14).main Coin.KO j = 1) :
    (pub 3).val < 65536 ∧ (pub 7).val < 65536 := by
  have cs := coin_sat hL hsat hL24
  have ek : (Coin.k Coin.KO).eval (2 ^ Ls 14) Coin.preCols pub (inst 14).main j = 1 := by rw [Coin.ev_k hj]; exact hko
  have t0 := coin_r8 hL hsat hL24 (k := 104) (c := Coin.TB 0) (by omega) (by omega) rfl hj ek
  have t1 := coin_r8 hL hsat hL24 (k := 105) (c := Coin.TB 1) (by omega) (by omega) rfl hj ek
  have t2 := coin_r8 hL hsat hL24 (k := 106) (c := Coin.TB 2) (by omega) (by omega) rfl hj ek
  have t3 := coin_r8 hL hsat hL24 (k := 107) (c := Coin.TB 3) (by omega) (by omega) rfl hj ek
  obtain ⟨e3, e7⟩ := Coin.time_out cs hj hko
  have hP : P = 2147483647 := rfl
  have key : ∀ (a b x : F), a.val < 256 → b.val < 256 → a + 256 * b = x → x.val < 65536 := by
    intro a b x ha hb' hx
    have : x = ((a.val + 256 * b.val : ℕ) : F) := by rw [← hx]; push_cast; simp only [ZMod.natCast_zmod_val]
    rw [this, ZMod.val_natCast_of_lt (by omega)]; omega
  exact ⟨key _ _ _ t0 t1 e3, key _ _ _ t2 t3 e7⟩

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

/-- **An enforced time lock is met against the claim's time (BIP68, time-based).** For input `k` of
transaction `t` (coin row `j`, a non-coinbase input) with claim `c` (its undo record, `ClaimAt`): when CSV
is active at the block's height, the transaction's version is at least 2, bit 31 of the input's sequence
is clear and bit 22 is set, the claim's time plus `512 ·` the sequence's low 16 bits is at most the block's
previous median time past (`pubMtp`: public inputs 3 and 7). `pub 5` is the CSV bit. -/
theorem in_time_lock (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23)
    (hp5 : pub 5 = if Spec.Block.CSV_HEIGHT ≤ h then 1 else 0)
    {t k : ℕ} {tx : Spec.Block.Tx} {i : Spec.Block.TxIn} (htx : S.b.txs[t]? = some tx) (hi : tx.vin[k]? = some i)
    (hvo : tx.vout ≠ [])
    {j : ℕ} (hjq : j = ((parts.take t).map List.length).sum + k) (hje : j < e)
    {c : Claim} (hc : ClaimAt inst pub (Ls 13) j c) :
    Spec.Coins.timeLockOk h tx.version i.sequence c.mtp (pubMtp pub) = true := by
  have hki : (inst 14).main Coin.KI j = 1 := hc.1
  -- the transaction's first output row: the public time's limbs are 16 bits
  obtain ⟨hp3, hp7⟩ : (pub 3).val < 65536 ∧ (pub 7).val < 65536 := by
    obtain ⟨hplx, hpex⟩ := part_len hf htx
    have hvl : 0 < tx.vout.length := List.length_pos_iff.mpr hvo
    have hkl' : k < tx.vin.length := (List.getElem?_eq_some_iff.mp hi).1
    have hft := fields_tagged hL hsat hL24 S
    rw [htg] at hft
    have he' : e = (parts.map List.length).sum := by rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
    have h1 := pre_succ parts hplx
    have h2 := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
    have htot : ((parts.take parts.length).map List.length).sum = (parts.map List.length).sum := by rw [List.take_length]
    have hjo : ((parts.take t).map List.length).sum + tx.vin.length < e := by omega
    have hko := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg hjo htx rfl (by omega)).1.mpr le_rfl
    exact pub_mtp_lt hL hsat hL24 (by omega) hko
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
  -- the claim's time: the row's four time bytes
  obtain ⟨-, -, rjc, -, -, -, -, u0c, -, -, -, -, -, -, hmtp, htbc⟩ := hc
  set tb := fun n => ((Ub inst pub).getD (u0c + c.ser.length + n) 0).toNat with htbdef
  have tbl : ∀ n, tb n < 256 := fun n => UInt8.toNat_lt _
  have htbv : ∀ n < 4, ((inst 14).main (Coin.TB n) j).val = tb n := by
    intro n hn
    rw [htbc n hn, ZMod.val_natCast_of_lt (lt_of_lt_of_le (tbl n) (by unfold P; norm_num))]
  have hmtpv : c.mtp = tb 0 + 256 * (tb 1 + 256 * (tb 2 + 256 * tb 3)) := by
    rw [hmtp]; simp [Spec.Block.le, List.range_succ, htbdef]
  have b0 := htbv 0 (by norm_num); have b1 := htbv 1 (by norm_num)
  have b2 := htbv 2 (by norm_num); have b3 := htbv 3 (by norm_num)
  have l0' := tbl 0; have l1' := tbl 1; have l2' := tbl 2; have l3' := tbl 3
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
      ((inst 14).main (Coin.TQ 0) j).val + 256 * ((inst 14).main (Coin.TQ 1) j).val +
        (((inst 14).main (Coin.TB 0) j).val + 256 * ((inst 14).main (Coin.TB 1) j).val) + 512 * ((inst 14).main Coin.SA j).val := by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; simp only [ZMod.natCast_zmod_val]
    linear_combination t2
  have hhi : (pub 7).val = ((inst 14).main (Coin.TQ 2) j).val + 256 * ((inst 14).main (Coin.TQ 3) j).val +
      (((inst 14).main (Coin.TB 2) j).val + 256 * ((inst 14).main (Coin.TB 3) j).val) +
      (((inst 14).main Coin.SH0 j).val + 256 * ((inst 14).main Coin.SHB j).val) + (((inst 14).main Coin.BW0 j).val + ((inst 14).main Coin.BW1 j).val) := by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; simp only [ZMod.natCast_zmod_val]
    linear_combination t3
  rw [show (2 : ℕ) ^ 16 = 65536 by norm_num, hlock, hmtpv, pubMtp]
  omega

end System

end StarkedAir.Block
