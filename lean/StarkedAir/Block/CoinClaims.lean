/-
**The coin component's amounts, per transaction (M3b, layer 5).** The circuit's per-row amounts are
Core's: an output row's limbs `VL`, `VH` are its output's value (`out_amount`), and an input row's are
its claim's amount, the first bytes of the claimed `serTxOut` (`in_amount`). Summed over a
transaction's rows (`in_nat`, `out_nat`, `tend_nat`), they give `ClaimsOK`'s amount conditions.
-/
import StarkedAir.Block.CoinEpochSound
import StarkedAir.Block.ValueSound

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **An output row's amount is its output's value.** -/
theorem out_amount (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {j t q : ℕ} {tx : Spec.Block.Tx} {o : Spec.Block.TxOut} (hj : j < e) (hko : (inst 14).main Coin.KO j = 1)
    (htx : S.b.txs[t]? = some tx) (hjq : j = ((parts.take t).map List.length).sum + q)
    (hq : q < tx.vin.length + tx.vout.length) (ho : tx.vout[q - tx.vin.length]? = some o) :
    ((inst 14).main Coin.VL j).val < 2 ^ 24 ∧ ((inst 14).main Coin.VH j).val < 2 ^ 27 ∧
      0 ≤ o.value ∧ o.value < 2 ^ 51 ∧
      ((((inst 14).main Coin.VH j).val * 2 ^ 24 + ((inst 14).main Coin.VL j).val : ℕ) : ℤ) = o.value := by
  have fs := fields_sat' hL hsat hL24
  have hj2 : j < 2 ^ L := by omega
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  obtain ⟨t0, q0, tx0, htx0, -, hjq0, hq0, hko0, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  obtain ⟨-, o0, ho0, hot⟩ := hko0 hko
  rw [ho] at ho0; obtain rfl := Option.some.inj ho0
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : ρ < 2 ^ L := by have := S.hmn; omega
  obtain ⟨hkout, hT⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hj).1 hko
  have hVL : (inst 14).main Coin.VL j = Fields.vlo.eval (2 ^ L) Fields.preCols pub (inst 1).main ρ := by
    have := congrArg (fun l => l.getD 5 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  have hVH : (inst 14).main Coin.VH j = Fields.vhi.eval (2 ^ L) Fields.preCols pub (inst 1).main ρ := by
    have := congrArg (fun l => l.getD 6 0) hT
    rw [hρdef, List.getD_eq_getElem?_getD]; simpa [cOut, fOut] using this
  obtain ⟨hv51, hlo, hhi, hvsum⟩ := Fields.out_value fs (Rb inst pub) (hby_R hL hsat hL24 S)
    (fun r hr j hj => fields_rg_lt hL hsat hL24 hr hj) (by omega) hρn hkout
  have htok : Fields.tokOf (inst 1).main (Rb inst pub) ρ = .out (Fields.slice (Rb inst pub) ((inst 1).main Fields.START ρ).val 8)
      (Fields.slice (Rb inst pub) (((inst 1).main Fields.START ρ).val + 8 + Fields.prefOf (inst 1).main ρ)
        ((inst 1).main Fields.VAL ρ).val) := by
    have kat := Fields.kinds_at fs hρn (a := Fields.K_OUT) (by decide) hkout
    unfold Fields.tokOf
    rw [if_neg (by rw [kat Fields.K_BLK (by decide)]; simp [Fields.K_BLK, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_TXH (by decide)]; simp [Fields.K_TXH, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_IN (by decide)]; simp [Fields.K_IN, Fields.K_OUT]),
      if_neg (by rw [kat Fields.K_NOUT (by decide)]; simp [Fields.K_NOUT, Fields.K_OUT]), if_pos hkout]
  rw [htok] at hot
  obtain ⟨-, hval, -⟩ := hot
  rw [Fields.signed64_of_lt (by omega)] at hval
  rw [hVL, hVH]
  refine ⟨hlo, hhi, by rw [hval]; positivity, by rw [hval]; exact_mod_cast hv51, ?_⟩
  rw [hval, hvsum]; push_cast; ring

omit hL hsat hL24 in
/-- The first 8 bytes' little-endian value, byte by byte. -/
theorem le_take8 {s : Spec.Block.Bytes} (hs : 8 ≤ s.length) :
    Spec.Block.le (s.take 8) = ∑ i ∈ Finset.range 8, (s.getD i 0).toNat * 256 ^ i := by
  rw [← Fields.le_range_map 8 (fun i => s.getD i 0)]
  congr 1
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_take, List.getElem_map, List.getElem_range]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

omit hL hsat hL24 in
/-- An amount within `MAX_MONEY` has its top byte zero and its seventh byte below 8. -/
theorem amount_bytes {b : ℕ → ℕ} (hb : ∀ i, b i < 256)
    (hv : ∑ i ∈ Finset.range 8, b i * 256 ^ i ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO) : b 7 = 0 ∧ b 6 < 8 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Fields.MAXHI, Fields.MAXLO] at hv
  have := hb 0; have := hb 1; have := hb 2; have := hb 3; have := hb 4; have := hb 5; have := hb 6; have := hb 7
  constructor <;> omega

/-- **An input row's amount is its claim's.** For input row `j` with claim `c` (its undo record), the
amount limbs are the claim's first seven `serTxOut` bytes; with the claimed amount (the first 8 bytes)
within `MAX_MONEY`, they are in range and sum to it. -/
theorem in_amount {j : ℕ} (hj : j < 2 ^ L) {c : Claim} (hc : ClaimAt inst pub L j c) (h8 : 8 ≤ c.ser.length)
    (hmax : Spec.Block.le (c.ser.take 8) ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO) :
    ((inst 14).main Coin.VL j).val < 2 ^ 24 ∧ ((inst 14).main Coin.VH j).val < 2 ^ 27 ∧
      ((inst 14).main Coin.VH j).val * 2 ^ 24 + ((inst 14).main Coin.VL j).val = Spec.Block.le (c.ser.take 8) := by
  obtain ⟨hki, rj, hrj, honj, hJ, u0, hu0, -, hu0l, hser, -, -⟩ := hc
  obtain ⟨rj', hrj', hon', hJ', -, -, hvl, hvh, -⟩ := coin_urec hL hsat hL24 hj hki
  have hrr : rj' = rj := urec_j_inj hL hsat hL24 hrj' hrj hon' honj (by rw [← hJ', hJ])
  rw [hrr] at hvl hvh
  have hU := undo_len hL hsat hL24
  have hPv : (pub 8).val < P := ZMod.val_lt _
  -- the amount bytes
  have hb : ∀ i < 8, ((inst 13).main (URec.V i) rj).val = (c.ser.getD i 0).toNat := by
    intro i hi
    obtain ⟨u, hu, hpu, hbu⟩ := urec_bytes hL hsat hL24 hrj honj (c := 7 + i) (by omega)
    have hcol : URec.ucol (7 + i) = URec.V i := by simp [URec.ucol]; omega
    rw [hcol] at hbu
    have hue : u = u0 + i := by
      apply Coin.lift _ (lt_of_lt_of_le hu (le_of_lt hPv)) (by omega)
      push_cast; rw [← hpu, show ((7 + i : ℕ) : F) = 7 + (i : F) by push_cast; ring, ← add_assoc, hu0]
    have hgi : c.ser.getD i 0 = (Ub inst pub).getD (u0 + i) 0 := by
      conv_lhs => rw [hser]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]; simp
    rw [hbu, hue, hgi]
  rw [le_take8 h8] at hmax ⊢
  have hb256 : ∀ i, (c.ser.getD i 0).toNat < 256 := fun i => UInt8.toNat_lt _
  obtain ⟨h7, h6⟩ := amount_bytes hb256 hmax
  have hVF : ∀ i < 8, (inst 13).main (URec.V i) rj = (((c.ser.getD i 0).toNat : ℕ) : F) := by
    intro i hi; rw [← Coin.cast_val ((inst 13).main (URec.V i) rj), hb i hi]
  have hlo : (inst 14).main Coin.VL j = (((c.ser.getD 0 0).toNat + 256 * (c.ser.getD 1 0).toNat +
      65536 * (c.ser.getD 2 0).toNat : ℕ) : F) := by
    rw [hvl, hVF 0 (by norm_num), hVF 1 (by norm_num), hVF 2 (by norm_num)]; push_cast; ring
  have hhi : (inst 14).main Coin.VH j = (((c.ser.getD 3 0).toNat + 256 * (c.ser.getD 4 0).toNat +
      65536 * (c.ser.getD 5 0).toNat + 16777216 * (c.ser.getD 6 0).toNat : ℕ) : F) := by
    rw [hvh, hVF 3 (by norm_num), hVF 4 (by norm_num), hVF 5 (by norm_num), hVF 6 (by norm_num)]; push_cast; ring
  have b0 := hb256 0; have b1 := hb256 1; have b2 := hb256 2; have b3 := hb256 3; have b4 := hb256 4
  have b5 := hb256 5
  rw [hlo, hhi, ZMod.val_natCast_of_lt (lt_of_lt_of_le (show _ < 2 ^ 24 by omega) (by unfold P; norm_num)),
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (show _ < 2 ^ 27 by omega) (by unfold P; norm_num))]
  refine ⟨by omega, by omega, ?_⟩
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [h7]; ring

/-- **An input's claim is mature.** With the claimed code `code` (below `2^30`, as for any real coin),
a coinbase claim (`code` odd) was created at least 100 blocks before height `h`. -/
theorem in_maturity {j : ℕ} (hj : j < 2 ^ L) (hki : (inst 14).main Coin.KI j = 1) {h code : ℕ}
    (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23)
    (hcode : (inst 14).main Coin.CLO j + 65536 * (inst 14).main Coin.CHI j = (code : F)) (hc : code < 2 ^ 30) :
    ¬ (code % 2 = 1 ∧ h < code / 2 + Spec.Coins.COINBASE_MATURITY) := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨e1, e2, -, -, e5, -⟩ := Coin.in_spec cs hj hki
  have ek : (Coin.k Coin.KI).eval (2 ^ L) Coin.preCols pub (inst 14).main j = 1 := by rw [Coin.ev_k hj]; exact hki
  have hb : ∀ i < 3, ((inst 14).main (Coin.HB i) j).val < 256 := by
    intro i hi
    interval_cases i
    · exact coin_r8 hL hsat hL24 (k := 52) (by omega) (by omega) rfl hj ek
    · exact coin_r8 hL hsat hL24 (k := 53) (by omega) (by omega) rfl hj ek
    · exact coin_r8 hL hsat hL24 (k := 54) (by omega) (by omega) rfl hj ek
  have hbn := Coin.b3N_lt hb
  have hP := Coin.P_big
  rw [Coin.b3V_eq] at e2
  have cbc := Coin.bool_col cs (c := Coin.CBC) (by simp) hj
  -- the code splits exactly
  have hsplit : code = 2 * Coin.b3N (inst 14).main Coin.HB j + (if (inst 14).main Coin.CBC j = 1 then 1 else 0) := by
    apply Coin.lift _ (by omega) (by split_ifs <;> omega)
    rw [← hcode, e1, e2]
    rcases cbc with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  rintro ⟨hodd, hlt⟩
  have hc1 : (inst 14).main Coin.CBC j = 1 := by
    rcases cbc with h0 | h1
    · rw [hsplit, h0] at hodd; simp at hodd
    · exact h1
  rw [hsplit, if_pos hc1] at hlt
  have ek2 : (Expr.mul (Coin.k Coin.KI) (Coin.k Coin.CBC)).eval (2 ^ L) Coin.preCols pub (inst 14).main j = 1 := by
    simp [Expr.eval, Coin.ev_k hj, hki, hc1]
  have hm : ∀ i < 3, ((inst 14).main (Coin.MB i) j).val < 256 := by
    intro i hi
    interval_cases i
    · exact coin_r8 hL hsat hL24 (k := 58) (by omega) (by omega) rfl hj ek2
    · exact coin_r8 hL hsat hL24 (k := 59) (by omega) (by omega) rfl hj ek2
    · exact coin_r8 hL hsat hL24 (k := 60) (by omega) (by omega) rfl hj ek2
  have hmn := Coin.b3N_lt hm
  have e5' := e5 hc1
  rw [Coin.b3V_eq, e2, hp2] at e5'
  have : Coin.b3N (inst 14).main Coin.MB j + Coin.b3N (inst 14).main Coin.HB j + 100 = h := by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; rw [e5']; ring
  simp only [Spec.Coins.COINBASE_MATURITY] at hlt
  omega

/-- **A transaction's coin rows.** For transaction `t ≥ 1`, its rows `pre t + q` (`q` below its token
count) are in use, inputs first then outputs; with every transaction's inputs and outputs nonempty, the
row before is not an input and the row after is not an output. -/
theorem tx_rows (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    (hne : ∀ (t' : ℕ) (tx' : Spec.Block.Tx), S.b.txs[t']? = some tx' → tx'.vin ≠ [] ∧ tx'.vout ≠ [])
    {t : ℕ} {tx : Spec.Block.Tx} (htx : S.b.txs[t]? = some tx) (ht1 : 1 ≤ t) :
    let j0 := ((parts.take t).map List.length).sum
    (∀ q < tx.vin.length + tx.vout.length, j0 + q < e ∧
      ((inst 14).main Coin.KI (j0 + q) = 1 ↔ q < tx.vin.length) ∧
      ((inst 14).main Coin.KO (j0 + q) = 1 ↔ tx.vin.length ≤ q)) ∧
    1 ≤ j0 ∧ (inst 14).main Coin.KI (j0 - 1) = 0 ∧
    j0 + (tx.vin.length + tx.vout.length) < 2 ^ L ∧
      (inst 14).main Coin.KO (j0 + (tx.vin.length + tx.vout.length)) = 0 := by
  intro j0
  have cs := coin_sat hL hsat hL24
  have htl := (List.getElem?_eq_some_iff.mp htx).1
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  have hft := fields_tagged hL hsat hL24 S
  rw [htg] at hft
  have he' : e = (parts.map List.length).sum := by rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
  have htot : ((parts.take parts.length).map List.length).sum = (parts.map List.length).sum := by
    rw [List.take_length]
  have hsucc := pre_succ parts hpl
  have hmono := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
  have hrow : ∀ q < tx.vin.length + tx.vout.length, j0 + q < e := fun q hq => by omega
  refine ⟨fun q hq => ⟨hrow q hq, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (hrow q hq) htx rfl hq).2.1
    rw [this]; exact ⟨fun h => h.1, fun h => ⟨h, ht1⟩⟩
  · exact (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (hrow q hq) htx rfl hq).1
  · -- the coinbase's tokens come first
    obtain ⟨tx0, htx0⟩ : ∃ tx0, S.b.txs[0]? = some tx0 :=
      ⟨S.b.txs[0]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
    have h1 := pre_succ parts hpl0
    have h2 := pre_mono parts (t := 1) (t' := t) ht1 (by omega)
    have := (hne 0 tx0 htx0).1
    have : 0 < tx0.vin.length := List.length_pos_iff.mpr this
    have h0 : ((parts.take 0).map List.length).sum = 0 := by simp
    simp only [Nat.zero_add] at h1
    show 1 ≤ ((parts.take t).map List.length).sum
    omega
  · -- the previous transaction's last token is an output
    obtain ⟨txp, htxp⟩ : ∃ txp, S.b.txs[t - 1]? = some txp :=
      ⟨S.b.txs[t - 1]'(by omega), List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨hplp, hpep⟩ := part_len hf htxp
    have hs := pre_succ parts hplp
    rw [show t - 1 + 1 = t by omega] at hs
    have hvo : 0 < txp.vout.length := List.length_pos_iff.mpr (hne _ _ htxp).2
    have hjp : j0 - 1 = ((parts.take (t - 1)).map List.length).sum + (txp.vin.length + txp.vout.length - 1) := by
      omega
    have hq : txp.vin.length + txp.vout.length - 1 < txp.vin.length + txp.vout.length := by omega
    have hk := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (j := j0 - 1) (by omega) htxp hjp hq).2.1
    have hb := Coin.bool_col cs (c := Coin.KI) (by simp) (show j0 - 1 < 2 ^ L by omega)
    rcases hb with h0 | h1
    · exact h0
    · exact absurd (hk.mp h1).1 (by omega)
  · omega
  · by_cases hlast : j0 + (tx.vin.length + tx.vout.length) < e
    · -- the next transaction's first token is an input
      have hnext : t + 1 < S.b.txs.length := by
        by_contra hc
        have : t + 1 = parts.length := by have := hf.length_eq; omega
        rw [this] at hsucc; omega
      obtain ⟨txn, htxn⟩ : ∃ txn, S.b.txs[t + 1]? = some txn := ⟨_, List.getElem?_eq_getElem hnext⟩
      have hvi : 0 < txn.vin.length := List.length_pos_iff.mpr (hne _ _ htxn).1
      have hk := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (j := j0 + (tx.vin.length + tx.vout.length))
        hlast htxn (by omega) (q := 0) (by omega)).1
      have hb := Coin.bool_col cs (c := Coin.KO) (by simp) (show j0 + (tx.vin.length + tx.vout.length) < 2 ^ L by omega)
      rcases hb with h0 | h1
      · exact h0
      · exact absurd (hk.mp h1) (by omega)
    · have hr : j0 + (tx.vin.length + tx.vout.length) < 2 ^ L := by omega
      have hoff : Coin.onV (inst 14).main (j0 + (tx.vin.length + tx.vout.length)) ≠ 1 := fun h => hlast ((hon _ hr).mp h)
      rcases Coin.kinds cs hr with ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨h, -⟩
      · exact absurd h hoff
      · exact absurd h hoff
      · exact absurd h hoff
      · exact h

/-- An input row's range-checked bytes: the normalized sum's and the `MAX_MONEY` comparator's. -/
theorem in_row_bytes {r : ℕ} (hr : r + 1 < 2 ^ L) (hki : (inst 14).main Coin.KI r = 1) :
    (∀ i < 3, ((inst 14).main (Coin.NB i) r).val < 256) ∧ (∀ i < 3, ((inst 14).main (Coin.Q1 i) r).val < 256) ∧
      (∀ i < 4, ((inst 14).main (Coin.H1 i) r).val < 256) ∧ ((inst 14).main Coin.H1C r).val < 256 := by
  have cs := coin_sat hL hsat hL24
  have hr' : r < 2 ^ L := by omega
  have hko : (inst 14).main Coin.KO r = 0 := by
    rcases Coin.kinds cs hr' with h | h | h | h <;> simp_all
  have e1 := Coin.sat cs (Coin.mem_amount (c := .sub (Coin.k Coin.MNB) (.add (Coin.k Coin.KI) (Coin.k Coin.KO)))
    (by simp [Coin.amountC])) hr'
  have e2 := Coin.sat cs (Coin.mem_amount (c := .sub (Coin.k Coin.MC1) (.add (Coin.k Coin.KI) Coin.tf))
    (by simp [Coin.amountC])) hr'
  have ht := Coin.tend_spec cs hr
  simp only [Expr.eval, Coin.ev_k hr', Coin.tf, Coin.om, Coin.one, StarkedAir.Sha256.eval_cst, Nat.cast_one] at e1 e2
  rw [hko, zero_mul] at ht
  rw [hki, hko] at e1
  rw [hki, ht] at e2
  have hmnb : (inst 14).main Coin.MNB r = 1 := by linear_combination e1
  have hmc1 : (inst 14).main Coin.MC1 r = 1 := by linear_combination e2
  have bb := coin_bytes hL hsat hL24 hr'
  obtain ⟨q1, h1, h1c, -, -, -⟩ := bb.2.1 hmc1
  exact ⟨bb.1 hmnb, q1, h1, h1c⟩

/-- **A transaction's input sums.** Over its input rows `j0 + k` (the row before not an input), the running
input sum is the claimed amounts' prefix sum, normalized and within `MAX_MONEY`. -/
theorem in_sums {j0 nin : ℕ} (hj0 : 1 ≤ j0) (hn : j0 + nin < 2 ^ L)
    (hki : ∀ k < nin, (inst 14).main Coin.KI (j0 + k) = 1) (hprev : (inst 14).main Coin.KI (j0 - 1) = 0)
    (a : ℕ → ℕ) (ha : ∀ k < nin, ((inst 14).main Coin.VL (j0 + k)).val < 2 ^ 24 ∧
      ((inst 14).main Coin.VH (j0 + k)).val < 2 ^ 27 ∧
      ((inst 14).main Coin.VH (j0 + k)).val * 2 ^ 24 + ((inst 14).main Coin.VL (j0 + k)).val = a k) :
    ∀ k < nin, ((inst 14).main Coin.INL (j0 + k)).val < 2 ^ 24 ∧ ((inst 14).main Coin.INH (j0 + k)).val ≤ Fields.MAXHI ∧
      ((inst 14).main Coin.INH (j0 + k)).val * 2 ^ 24 + ((inst 14).main Coin.INL (j0 + k)).val =
        ∑ k' ∈ Finset.range (k + 1), a k' ∧
      ∑ k' ∈ Finset.range (k + 1), a k' ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO := by
  have cs := coin_sat hL hsat hL24
  intro k
  induction k with
  | zero =>
    intro hk
    obtain ⟨nb, q1, h1, h1c⟩ := in_row_bytes hL hsat hL24 (r := j0 + 0) (by omega) (hki 0 hk)
    obtain ⟨vl, vh, vs⟩ := ha 0 hk
    have hpv : Coin.prevV (inst 14).main (2 ^ L) Coin.KI (j0 + 0) = 0 := by
      unfold Coin.prevV; rw [if_neg (by omega)]; simpa using hprev
    obtain ⟨i1, i2, i3, i4⟩ := Coin.in_nat cs (by omega) (hki 0 hk) (by rw [hpv]; simp) nb q1 h1 h1c vl vh
    rw [hpv, if_neg (by simp)] at i3
    refine ⟨i1, i2, ?_, ?_⟩
    · rw [i3, vs]; simp
    · rw [Finset.sum_range_one, ← vs]
      rw [i3, zero_add] at i4; exact i4
  | succ k ih =>
    intro hk
    obtain ⟨p1, p2, p3, -⟩ := ih (by omega)
    obtain ⟨nb, q1, h1, h1c⟩ := in_row_bytes hL hsat hL24 (r := j0 + (k + 1)) (by omega) (hki (k + 1) hk)
    obtain ⟨vl, vh, vs⟩ := ha (k + 1) hk
    have hpk : ∀ c, Coin.prevV (inst 14).main (2 ^ L) c (j0 + (k + 1)) = (inst 14).main c (j0 + k) := by
      intro c; unfold Coin.prevV; rw [if_neg (by omega)]; rfl
    have hpv : Coin.prevV (inst 14).main (2 ^ L) Coin.KI (j0 + (k + 1)) = 1 := by rw [hpk]; exact hki k (by omega)
    obtain ⟨i1, i2, i3, i4⟩ := Coin.in_nat cs (by omega) (hki (k + 1) hk)
      (fun _ => by rw [hpk, hpk]; exact ⟨p1, p2⟩) nb q1 h1 h1c vl vh
    rw [if_pos hpv, hpk, hpk] at i3
    refine ⟨i1, i2, ?_, ?_⟩
    · rw [i3, p3, vs, Finset.sum_range_succ _ (k + 1)]
    · rw [Finset.sum_range_succ _ (k + 1), ← vs, ← p3, ← i3]; exact i4

/-- An output row's normalized output sum is range-checked. -/
theorem out_row_bytes {r : ℕ} (hr : r < 2 ^ L) (hko : (inst 14).main Coin.KO r = 1) :
    ∀ i < 3, ((inst 14).main (Coin.NB i) r).val < 256 := by
  have cs := coin_sat hL hsat hL24
  have hki : (inst 14).main Coin.KI r = 0 := by
    rcases Coin.kinds cs hr with h | h | h | h <;> simp_all
  have e1 := Coin.sat cs (Coin.mem_amount (c := .sub (Coin.k Coin.MNB) (.add (Coin.k Coin.KI) (Coin.k Coin.KO)))
    (by simp [Coin.amountC])) hr
  simp only [Expr.eval, Coin.ev_k hr] at e1
  rw [hki, hko] at e1
  exact (coin_bytes hL hsat hL24 hr).1 (by linear_combination e1)

omit hL hsat hL24 in
theorem hi_le_of {hi lo : ℕ} (h : hi * 2 ^ 24 + lo ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO) : hi ≤ Fields.MAXHI := by
  have hm : Fields.MAXLO < 2 ^ 24 := by unfold Fields.MAXLO; norm_num
  by_contra hc
  have : (Fields.MAXHI + 1) * 2 ^ 24 ≤ hi * 2 ^ 24 := Nat.mul_le_mul_right _ (by omega)
  rw [add_mul, one_mul] at this
  omega

/-- **A transaction's output sums.** Over its output rows `j1 + q` (the row before not an output), the
input sum is carried, and the running output sum is the outputs' prefix sum, normalized. -/
theorem out_sums {j1 nout : ℕ} (hj1 : 1 ≤ j1) (hn : j1 + nout < 2 ^ L)
    (hko : ∀ q < nout, (inst 14).main Coin.KO (j1 + q) = 1) (hprev : (inst 14).main Coin.KO (j1 - 1) = 0)
    (v : ℕ → ℕ) (hv : ∀ q < nout, ((inst 14).main Coin.VL (j1 + q)).val < 2 ^ 24 ∧
      ((inst 14).main Coin.VH (j1 + q)).val < 2 ^ 27 ∧
      ((inst 14).main Coin.VH (j1 + q)).val * 2 ^ 24 + ((inst 14).main Coin.VL (j1 + q)).val = v q)
    (htot : ∑ q ∈ Finset.range nout, v q ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO) :
    ∀ q < nout, ((inst 14).main Coin.OUL (j1 + q)).val < 2 ^ 24 ∧ ((inst 14).main Coin.OUH (j1 + q)).val ≤ Fields.MAXHI ∧
      ((inst 14).main Coin.OUH (j1 + q)).val * 2 ^ 24 + ((inst 14).main Coin.OUL (j1 + q)).val =
        ∑ q' ∈ Finset.range (q + 1), v q' ∧
      ((inst 14).main Coin.INL (j1 + q)).val = ((inst 14).main Coin.INL (j1 - 1)).val ∧
      ((inst 14).main Coin.INH (j1 + q)).val = ((inst 14).main Coin.INH (j1 - 1)).val := by
  have cs := coin_sat hL hsat hL24
  have hpart : ∀ q < nout, ∑ q' ∈ Finset.range (q + 1), v q' ≤ Fields.MAXHI * 2 ^ 24 + Fields.MAXLO := fun q hq =>
    le_trans (Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (show q + 1 ≤ nout by omega))) htot
  intro q
  induction q with
  | zero =>
    intro hq
    obtain ⟨vl, vh, vs⟩ := hv 0 hq
    have hpk : ∀ c, Coin.prevV (inst 14).main (2 ^ L) c (j1 + 0) = (inst 14).main c (j1 - 1) := by
      intro c; unfold Coin.prevV; rw [if_neg (by omega)]; rfl
    have hpv : Coin.prevV (inst 14).main (2 ^ L) Coin.KO (j1 + 0) = 0 := by rw [hpk]; exact hprev
    obtain ⟨o1, o2, o3, o4⟩ := Coin.out_nat cs (by omega) (hko 0 hq) (by rw [hpv]; simp)
      (out_row_bytes hL hsat hL24 (by omega) (hko 0 hq)) vl vh
    rw [hpv, if_neg (by simp), zero_add] at o4
    have hs : ((inst 14).main Coin.OUH (j1 + 0)).val * 2 ^ 24 + ((inst 14).main Coin.OUL (j1 + 0)).val =
        ∑ q' ∈ Finset.range (0 + 1), v q' := by rw [o4, vs]; simp
    refine ⟨o3, hi_le_of (by rw [hs]; exact hpart 0 hq), hs, by rw [o1, hpk], by rw [o2, hpk]⟩
  | succ q ih =>
    intro hq
    obtain ⟨p1, p2, p3, p4, p5⟩ := ih (by omega)
    obtain ⟨vl, vh, vs⟩ := hv (q + 1) hq
    have hpk : ∀ c, Coin.prevV (inst 14).main (2 ^ L) c (j1 + (q + 1)) = (inst 14).main c (j1 + q) := by
      intro c; unfold Coin.prevV; rw [if_neg (by omega)]; rfl
    have hpv : Coin.prevV (inst 14).main (2 ^ L) Coin.KO (j1 + (q + 1)) = 1 := by rw [hpk]; exact hko q (by omega)
    obtain ⟨o1, o2, o3, o4⟩ := Coin.out_nat cs (by omega) (hko (q + 1) hq) (fun _ => by rw [hpk, hpk]; exact ⟨p1, p2⟩)
      (out_row_bytes hL hsat hL24 (by omega) (hko (q + 1) hq)) vl vh
    rw [if_pos hpv, hpk, hpk] at o4
    have hs : ((inst 14).main Coin.OUH (j1 + (q + 1))).val * 2 ^ 24 + ((inst 14).main Coin.OUL (j1 + (q + 1))).val =
        ∑ q' ∈ Finset.range (q + 1 + 1), v q' := by rw [o4, p3, vs, Finset.sum_range_succ _ (q + 1)]
    refine ⟨o3, hi_le_of (by rw [hs]; exact hpart (q + 1) hq), hs, ?_, ?_⟩
    · rw [o1, hpk, p4]
    · rw [o2, hpk, p5]

end System

end StarkedAir.Block
