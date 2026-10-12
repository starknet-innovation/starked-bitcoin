/-
**The witness commitment (M3a.5e), system level.** With segwit active, the fields' marked output is the
coinbase's last output matching the commitment pattern (its `commitmentIndex`), and then the coinbase
witness is one 32-byte nonce and `SHA256d(witnessRoot ++ nonce)` is the 32 bytes after the pattern;
without a marked output (or without segwit), no transaction has a witness.
-/
import StarkedAir.Block.BlockFinal

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : ∀ i < 15, Ls i ≤ 23)
include hL hsat hL24

theorem zt_of_locks {r : ℕ} (hr : r < 2 ^ Ls 1) (h : locks (inst 1).main r = 0) : (inst 1).main Fields.ZT r = 1 := by
  have fs := hash_fields_sat' hL hsat
  have hti : (inst 1).main Fields.TXI r = 0 := by rw [Fields.txi_count fs r hr, h]; simp
  have := Fields.sat fs (Fields.mem_chk (c := .mul (Fields.oneMinus (Fields.k Fields.ZT))
    (.sub (.mul (Fields.k Fields.TXI) (Fields.k Fields.INVT)) Fields.one)) (by simp [Fields.chkC, Fields.prevoutC])) hr
  simp only [Expr.eval, Fields.ev_k hr, hti, zero_mul, Fields.oneMinus, Fields.one, StarkedAir.Sha256.eval_cst,
    Nat.cast_one, zero_sub, mul_neg, mul_one, neg_eq_zero, sub_eq_zero] at this
  exact this.symm

theorem locks_of_zt {r : ℕ} (hr : r < 2 ^ Ls 1) (h : (inst 1).main Fields.ZT r = 1) : locks (inst 1).main r = 0 := by
  have fs := hash_fields_sat' hL hsat
  have hP : 2 ^ Ls 1 < P := by have := rows_lt_P hL24 (i := 1) (by decide); omega
  have := Fields.sat fs (Fields.mem_chk (c := .mul (Fields.k Fields.ZT) (Fields.k Fields.TXI))
    (by simp [Fields.chkC, Fields.prevoutC])) hr
  simp only [Expr.eval, Fields.ev_k hr, h, one_mul] at this
  have hv := (Fields.txi_val fs hP hr).1
  rw [this, ZMod.val_zero] at hv; exact hv.symm

omit hL hsat hL24 in
/-- A state from its 16 limbs, given as big-endian byte pairs (limb `j` is pair `j xor 1`). -/
theorem state_of_limbs {o : Spec.Sha256.State} {B : Spec.Block.Bytes} (hB : B.length = 32)
    (h : ∀ j < 16, ((Sha256.half16 (Spec.Bitcoin.stateWord o (j / 2)) (j % 2) : ℕ) : F) =
      ((256 * (B.getD (2 * (if j % 2 = 0 then j + 1 else j - 1)) 0).toNat +
        (B.getD (2 * (if j % 2 = 0 then j + 1 else j - 1) + 1) 0).toNat : ℕ) : F)) :
    Spec.Block.stateBytes o = B := by
  apply HashSpec.stateBytes_of_words hB
  intro w hw
  have lo := h (2 * w) (by omega)
  have hi := h (2 * w + 1) (by omega)
  rw [show 2 * w / 2 = w by omega, show 2 * w % 2 = 0 by omega, if_pos rfl,
    show 2 * (2 * w + 1) = 4 * w + 2 by ring, show 4 * w + 2 + 1 = 4 * w + 3 by ring] at lo
  rw [show (2 * w + 1) / 2 = w by omega, show (2 * w + 1) % 2 = 1 by omega, if_neg (by norm_num),
    show 2 * (2 * w + 1 - 1) = 4 * w by omega] at hi
  have bl := fun i => UInt8.toNat_lt (B.getD i 0)
  have b0 := bl (4 * w); have b1 := bl (4 * w + 1); have b2 := bl (4 * w + 2); have b3 := bl (4 * w + 3)
  have h0 := half16_lt (Spec.Bitcoin.stateWord o w) 0
  have h1 := half16_lt (Spec.Bitcoin.stateWord o w) 1
  have lo' := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) lo
  have hi' := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) hi
  simp only [Sha256.half16] at lo' hi'
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  have := (Spec.Bitcoin.stateWord o w).isLt
  omega

omit hL hsat hL24 in
/-- A script given as block bytes matches the commitment pattern iff it is at least 38 bytes long and its
first six bytes are the pattern's. -/
theorem isCommit_iff {cb : Spec.Block.Tx} {o : ℕ} {out : Spec.Block.TxOut} (hget : cb.vout[o]? = some out)
    {R : Spec.Block.Bytes} {a v : ℕ} (hs : out.scriptPubKey = slice R a v) (hfit : a + v ≤ R.length) :
    Spec.Block.IsCommit cb o ↔ 38 ≤ v ∧ ∀ j < 6, (R.getD (a + j) 0).toNat = Fields.pat.getD j 0 := by
  have hg : cb.vout.getD o ⟨0, []⟩ = out := by rw [List.getD_eq_getElem?_getD, hget]; rfl
  unfold Spec.Block.IsCommit
  rw [hg, hs, Fields.slice_length hfit]
  constructor
  · rintro ⟨h38, h6⟩
    refine ⟨h38, fun j hj => ?_⟩
    have e := congrArg (fun l : Spec.Block.Bytes => l.getD j 0) h6
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj, ← List.getD_eq_getElem?_getD,
      Fields.slice_getD (by omega) hfit] at e
    rw [e]; interval_cases j <;> rfl
  · rintro ⟨h38, h6⟩
    refine ⟨h38, ?_⟩
    apply List.ext_getElem
    · simp [Fields.slice_length hfit]; omega
    · intro j h1 h2
      have hj : j < 6 := by simpa using h2
      rw [← List.getD_eq_getElem _ (0 : UInt8) h1, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj,
        ← List.getD_eq_getElem?_getD, Fields.slice_getD (by omega) hfit]
      apply UInt8.toNat_inj.mp
      rw [h6 j hj]
      interval_cases j <;> rfl

/-- A transaction without the segwit flag has its witness start at its lock time. -/
theorem wst_noseg (S : Setup inst pub (Ls 1)) {ρ : ℕ} {t : Spec.Block.Tx} (hat : TxAt (inst 1).main (Rb inst pub) S.m ρ t)
    (hρ : ρ < S.m) (hs : (inst 1).main Fields.SEG ρ ≠ 1) : (inst 1).main Fields.WST ρ = (inst 1).main Fields.START ρ := by
  have fs := hash_fields_sat' hL hsat
  obtain ⟨rh, hrh, ht, hnt, htx⟩ := hat
  obtain ⟨tx', r', rw, -, -, -, htx', -, -, hr'm, -, -, -, hsegrw, -, -, hws, hsg, -⟩ :=
    Fields.tx_cols fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (show rh < S.m by omega) ht
  rw [htx] at htx'
  simp only [Option.some.injEq, Prod.mk.injEq] at htx'
  obtain rfl : ρ = r' := by
    have := congrArg List.length htx'.2; simp only [Fields.toksFrom_length] at this; omega
  rw [hws, hsegrw (by rwa [← hsg])]

/-- **The coinbase's outputs**: output `o` is row `rh + 2 + nI + o`, an output row of transaction 0 whose
script starts at `SSC`; and every output row of transaction 0 is one of them. -/
theorem cb_outputs (S : Setup inst pub (Ls 1)) {ρ : ℕ} {t : Spec.Block.Tx} (hρ : ρ < S.m)
    (hl : (inst 1).main Fields.K_LOCK ρ = 1) (hlk : locks (inst 1).main ρ = 0)
    (hat : TxAt (inst 1).main (Rb inst pub) S.m ρ t) :
    ∃ b0, (∀ o < t.vout.length, ∃ out, t.vout[o]? = some out ∧ b0 + o < S.m ∧
        (inst 1).main Fields.K_OUT (b0 + o) = 1 ∧ (inst 1).main Fields.ZT (b0 + o) = 1 ∧
        out.scriptPubKey = slice (Rb inst pub) ((inst 1).main Fields.SSC (b0 + o)).val ((inst 1).main Fields.VAL (b0 + o)).val ∧
        (∀ r < b0 + o, (inst 1).main Fields.ISC r = 1 → ∃ o' < o, r = b0 + o')) ∧
      ∀ r < 2 ^ Ls 1, (inst 1).main Fields.K_OUT r = 1 → (inst 1).main Fields.ZT r = 1 → ∃ o < t.vout.length, r = b0 + o := by
  have fs := hash_fields_sat' hL hsat
  have hn0 : 0 < 2 ^ Ls 1 := by positivity
  have hmn := S.hmn
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  obtain ⟨rh, hrh, ht, hnt, hvl, h1, hins, hno, hnv, houts, hwit, -, -, hle, hlks⟩ :=
    Fields.tx_rows' fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (by norm_num; omega) hat hρ
  set nI := t.vin.length
  set nO := t.vout.length
  -- the head is row 1
  have hrh1 : rh = 1 := by
    have hb0 := Fields.first_blk fs hn0
    have hrh0 : rh ≠ 0 := by
      intro h0; subst h0
      rw [Fields.kind_unique fs hn0 (a := Fields.K_BLK) (b := Fields.K_TXH) (by simp [Fields.K_BLK]) (by simp [Fields.K_TXH])
        (by simp [Fields.K_BLK, Fields.K_TXH]) hb0] at ht
      exact zero_ne_one ht
    by_contra hne
    have ht1 : (inst 1).main Fields.K_TXH 1 = 1 := (Fields.next_kind fs (r := 0) (by omega)).1 hb0
    obtain ⟨-, r', -, -, -, -, -, h1', h2', hr'm, hl', -, -, -, -, -, -, -, notxh, -, -, -⟩ :=
      Fields.tx_cols fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (show 1 < S.m by omega) ht1
    have hr'rh : r' < rh := by
      by_contra hc
      have := notxh rh (by omega) (by omega); rw [ht] at this; exact one_ne_zero this
    have := Fields.locks_mono (M := (inst 1).main) hr'rh hl'
    rw [hlks rh le_rfl (by omega), hlk] at this; omega
  subst hrh1
  have hall : ∀ r < 2 ^ Ls 1, (inst 1).main Fields.K_OUT r = 1 → (inst 1).main Fields.ZT r = 1 →
      ∃ o < nO, r = 1 + 2 + nI + o := by
    intro r hr hk hz
    have hl0 := locks_of_zt hL hsat hL24 hr hz
    have ku := fun (b : ℕ) (hb : b < 9) (hne : Fields.K_OUT ≠ b) =>
      Fields.kind_unique fs hr (a := Fields.K_OUT) (b := b) (by simp [Fields.K_OUT]) hb hne hk
    have hrρ : r < ρ := by
      rcases lt_trichotomy r ρ with h | h | h
      · exact h
      · subst h; rw [ku Fields.K_LOCK (by simp [Fields.K_LOCK]) (by simp [Fields.K_OUT, Fields.K_LOCK])] at hl
        exact absurd hl zero_ne_one
      · have := Fields.locks_mono (M := (inst 1).main) h hl; rw [hl0] at this; omega
    have hr2 : 2 ≤ r := by
      by_contra hc
      interval_cases r
      · have := Fields.first_blk fs hn0
        rw [ku Fields.K_BLK (by simp [Fields.K_BLK]) (by simp [Fields.K_OUT, Fields.K_BLK])] at this
        exact absurd this zero_ne_one
      · rw [ku Fields.K_TXH (by simp [Fields.K_TXH]) (by simp [Fields.K_OUT, Fields.K_TXH])] at ht
        exact absurd ht zero_ne_one
    rcases Nat.lt_or_ge r (2 + nI) with h | h
    · obtain ⟨inp, -, hrow⟩ := hins (r - 2) (by omega)
      have := hrow.kind
      rw [show 1 + 1 + (r - 2) = r by omega, ku Fields.K_IN (by simp [Fields.K_IN]) (by simp [Fields.K_OUT, Fields.K_IN])] at this
      exact absurd this zero_ne_one
    rcases Nat.eq_or_lt_of_le h with h' | h'
    · rw [show 1 + 1 + nI = r by omega, ku Fields.K_NOUT (by simp [Fields.K_NOUT]) (by simp [Fields.K_OUT, Fields.K_NOUT])] at hno
      exact absurd hno zero_ne_one
    rcases Nat.lt_or_ge r (1 + 2 + nI + nO) with g | g
    · exact ⟨r - (1 + 2 + nI), by omega, by omega⟩
    · rcases hwit r (by omega) hrρ with w | w
      · rw [ku Fields.K_WCNT (by simp [Fields.K_WCNT]) (by simp [Fields.K_OUT, Fields.K_WCNT])] at w
        exact absurd w zero_ne_one
      · rw [ku Fields.K_WITEM (by simp [Fields.K_WITEM]) (by simp [Fields.K_OUT, Fields.K_WITEM])] at w
        exact absurd w zero_ne_one
  refine ⟨1 + 2 + nI, fun o ho => ?_, hall⟩
  · obtain ⟨out, hget, hrow⟩ := houts o ho
    have hro : 1 + 2 + nI + o < S.m := by omega
    have hzt : (inst 1).main Fields.ZT (1 + 2 + nI + o) = 1 :=
      zt_of_locks hL hsat hL24 (by omega) (by rw [hlks _ (by omega) (by omega), hlk])
    have hssc := Fields.ssc_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hro (a := Fields.K_OUT) (Or.inr rfl) hrow.kind
    simp only [show Fields.K_OUT ≠ Fields.K_IN by simp [Fields.K_OUT, Fields.K_IN], if_false] at hssc
    refine ⟨out, hget, hro, hrow.kind, hzt, by rw [hrow.script, hssc], fun r hr hi => ?_⟩
    -- a marked row below is an earlier output of the coinbase
    obtain ⟨hk, hz, -⟩ := Fields.isc_out fs (by omega) hi
    obtain ⟨o', ho', rfl⟩ := hall r (by omega) hk hz
    exact ⟨o', by omega, rfl⟩

/-- The witness start is a row start. -/
theorem wst_lt (S : Setup inst pub (Ls 1)) {ρ : ℕ} {t : Spec.Block.Tx} (hat : TxAt (inst 1).main (Rb inst pub) S.m ρ t)
    (hρ : ρ < S.m) : ((inst 1).main Fields.WST ρ).val < 2 ^ 25 := by
  have fs := hash_fields_sat' hL hsat
  obtain ⟨rh, hrh, ht, hnt, htx⟩ := hat
  obtain ⟨tx', r', rw, -, -, -, htx', -, h2, hr'm, -, -, -, -, -, -, hws, -⟩ :=
    Fields.tx_cols fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (show rh < S.m by omega) ht
  rw [htx] at htx'
  simp only [Option.some.injEq, Prod.mk.injEq] at htx'
  obtain rfl : ρ = r' := by
    have := congrArg List.length htx'.2; simp only [Fields.toksFrom_length] at this; omega
  rw [hws]; exact Fields.start_lt fs (show rw < 2 ^ Ls 1 by have := S.hmn; omega)

/-- An output's script lies in the block. -/
theorem out_fit (S : Setup inst pub (Ls 1)) {r : ℕ} (hr : r < S.m) (hk : (inst 1).main Fields.K_OUT r = 1) :
    ((inst 1).main Fields.SSC r).val + ((inst 1).main Fields.VAL r).val ≤ (Rb inst pub).length := by
  have fs := hash_fields_sat' hL hsat
  have hssc := Fields.ssc_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr (a := Fields.K_OUT) (Or.inr rfl) hk
  simp only [show Fields.K_OUT ≠ Fields.K_IN by simp [Fields.K_OUT, Fields.K_IN], if_false] at hssc
  obtain ⟨-, hlen, -, -, hf⟩ := Fields.row_info fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr (a := Fields.K_OUT)
    (by simp [Fields.K_OUT]) hk (by simp [Fields.K_OUT, Fields.K_LOCK]) (by simp [Fields.K_OUT, Fields.K_PAD])
  simp [Fields.lenN, Fields.K_BLK, Fields.K_TXH, Fields.K_IN, Fields.K_NOUT, Fields.K_OUT] at hlen
  omega

/-- The marked rows below `r`, when there is exactly one, at `rs`. -/
theorem iscN_one {r rs : ℕ} (hr : r ≤ 2 ^ Ls 1) (hrs : rs < r) (h1 : (inst 1).main Fields.ISC rs = 1)
    (hu : ∀ j < 2 ^ Ls 1, (inst 1).main Fields.ISC j = 1 → j = rs) : Fields.iscN (inst 1).main r = 1 := by
  have fs := hash_fields_sat' hL hsat
  unfold Fields.iscN
  rw [Finset.sum_eq_single rs]
  · rw [h1, ZMod.val_one]
  · intro j hj hne
    rcases Fields.isc_bool fs (r := j) (by simp at hj; omega) with g | g
    · rw [g, ZMod.val_zero]
    · exact absurd (hu j (by simp at hj; omega) g) hne
  · intro h; exact absurd (Finset.mem_range.mpr hrs) h

omit hL hsat hL24 in
theorem limbs_at {o : Spec.Sha256.State} {f : ℕ → F} (h : stLimbs o = (List.range 16).map f) {j : ℕ} (hj : j < 16) :
    ((Sha256.half16 (Spec.Bitcoin.stateWord o (j / 2)) (j % 2) : ℕ) : F) = f j := by
  have e := congrArg (fun l => l[j]?) h
  simpa [stLimbs, List.getElem?_map, List.getElem?_range hj] using e

omit hL hsat hL24 in
/-- The block's bytes as limbs: `256·R[a + 2i] + R[a + 2i + 1]`. -/
theorem state_of_reg {o : Spec.Sha256.State} {R : Spec.Block.Bytes} {a r : ℕ} {M : ℕ → ℕ → F}
    (ha : a + 32 ≤ R.length) (h : stLimbs o = (List.range 16).map (ctxLimb M r))
    (hreg : ∀ i < 16, M (Ctx.LG i) r = ((256 * (R.getD (a + 2 * i) 0).toNat + (R.getD (a + 2 * i + 1) 0).toNat : ℕ) : F)) :
    Spec.Block.stateBytes o = slice R a 32 := by
  apply state_of_limbs (Fields.slice_length ha)
  intro j hj
  rw [limbs_at h hj, ctxLimb]
  have hi : (if j % 2 = 0 then j + 1 else j - 1) < 16 := by split_ifs <;> omega
  rw [hreg _ hi, Fields.slice_getD (by split_ifs <;> omega) ha, Fields.slice_getD (by split_ifs <;> omega) ha]
  ring_nf

/-- **The witness commitment.** -/
theorem commit_ok (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) {c : Spec.Block.Ctx}
    (p6 : pub 6 = if Spec.Block.SEGWIT_HEIGHT ≤ c.height then 1 else 0) :
    (match Spec.Block.commitOf c S.b with
      | some pos => Spec.Block.witCheck S.b pos = none
      | none => ∀ t ∈ S.b.txs, t.hasWitness = false) := by
  classical
  have fs := hash_fields_sat' hL hsat
  have cs := hash_ctx_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have h256 := ctx_sat8 hL hsat hL24 hL8
  have hn0 : 0 < 2 ^ Ls 1 := by positivity
  have hn7 : 0 < 2 ^ Ls 7 := by positivity
  have hmn := S.hmn
  have hlenR := len_R hL hsat hL24 (inst := inst) (pub := pub)
  obtain ⟨ρ0, t0, inp, hρ0, hl0, hlk0, hget0, hat0, hta, hsg, hws, hst, hv0, -⟩ := cb_facts hL hsat hL24 hL8 S
  have hcb : Spec.Block.cbOf S.b = t0 := by
    unfold Spec.Block.cbOf
    match h : S.b.txs, hget0 with
    | a :: _, hg => simp at hg; simp [hg]
  obtain ⟨b0, hout, hall⟩ := cb_outputs hL hsat hL24 S hρ0 hl0 hlk0 hat0
  obtain ⟨g1, g2, g3, -⟩ := Ctx.glob_eqs cs hn7
  obtain ⟨-, hnseg, hhasc⟩ := tot_link hL hsat hL24
  obtain ⟨hb01, hconst, hiff⟩ := Fields.hasc_iff fs hn0 (by omega)
  have hhc : (inst 7).main Ctx.HC 0 = pub 6 * (inst 1).main Fields.HASC 0 := by
    rw [g1, hhasc, hconst _ (by omega)]
  obtain ⟨hseg, ha0⟩ := ctx_seg_a0 hL hsat hL24 S
  -- without the commitment check, no transaction has a witness
  have noWit : (inst 7).main Ctx.HC 0 = 0 → ∀ t ∈ S.b.txs, t.hasWitness = false := by
    intro h0 t ht
    rw [h0, sub_zero, one_mul] at g3
    rw [g3] at hnseg
    have hz := Fields.ns_zero fs hn0 (by omega) hnseg.symm
    obtain ⟨j, ρ, -, -, hρ, hl, -, hat⟩ := tx_at hL hsat hL24 S ht
    obtain ⟨rh, hrh, ht', -, -, -, -, -, -, -, -, -, hsw, -⟩ :=
      Fields.tx_rows fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hat hρ
    by_contra hw
    have := hsw.mpr (by simpa using hw)
    rw [hz rh (by omega) ht'] at this; exact zero_ne_one this
  -- outputs that must not match don't
  have noMatch : pub 6 = 1 → ∀ o < t0.vout.length, (inst 1).main Fields.ISC (b0 + o) = 0 →
      (((inst 1).main Fields.HASC 0 = 0 ∧ (inst 1).main Fields.AFT (b0 + o) = 0) ∨
       ((inst 1).main Fields.HASC 0 = 1 ∧ (inst 1).main Fields.AFT (b0 + o) = 1)) → ¬ Spec.Block.IsCommit t0 o := by
    intro h6 o ho hisc hreq hcm
    obtain ⟨out, hget, hrm, hk, hz, hsc, -⟩ := hout o ho
    rw [← hconst (b0 + o) (by omega)] at hreq
    have mm := Fields.req_mismatch fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit (hbq_R hL hsat hL24)
      (fun r hr j hj => fields_rg_lt hL hsat hL24 hr hj) (by norm_num; omega) (by omega) hk hz h6 hisc hreq
    rw [isCommit_iff hget hsc (out_fit hL hsat hL24 S hrm hk)] at hcm
    rcases mm with h37 | ⟨j, hj, -, hne⟩
    · omega
    · exact hne (hcm.2 j hj)
  unfold Spec.Block.commitOf
  rw [hcb]
  by_cases hsw : Spec.Block.SEGWIT_HEIGHT ≤ c.height
  · have h6 : pub 6 = 1 := by rw [p6, if_pos hsw]
    rw [if_pos (show c.height ≥ Spec.Block.SEGWIT_HEIGHT from hsw)]
    rcases hb01 with h0 | h1
    · -- no marked output: no commitment, and no witness
      have hno : ∀ r < 2 ^ Ls 1, (inst 1).main Fields.ISC r = 0 := by
        intro r hr
        rcases Fields.isc_bool fs hr with g | g
        · exact g
        · rw [hiff.mpr ⟨r, hr, g⟩] at h0; exact absurd h0 one_ne_zero
      have hnone : Spec.Block.commitmentIndex t0 = none := by
        rw [Spec.Block.commitmentIndex_eq, dif_neg]
        rintro ⟨o, ho, hcm⟩
        obtain ⟨-, -, hrm, -⟩ := hout o ho
        refine noMatch h6 o ho (hno _ (by omega)) (Or.inl ⟨h0, ?_⟩) hcm
        rw [(Fields.aft_nat fs hn0 (by omega) (r := b0 + o) (by omega)).1]
        have : Fields.iscN (inst 1).main (b0 + o) = 0 := by
          unfold Fields.iscN
          exact Finset.sum_eq_zero (fun j hj => by rw [hno j (by simp at hj; omega), ZMod.val_zero])
        rw [this]; simp
      rw [hnone]
      exact noWit (by rw [hhc, h6, h0, mul_zero])
    · -- the marked output is the commitment
      have hHC : (inst 7).main Ctx.HC 0 = 1 := by rw [hhc, h6, h1, one_mul]
      obtain ⟨rs, hrs, hisc⟩ := hiff.mp h1
      obtain ⟨hk, hz, -⟩ := Fields.isc_out fs hrs hisc
      obtain ⟨os, hos, rfl⟩ := hall _ hrs hk hz
      have hu : ∀ j < 2 ^ Ls 1, (inst 1).main Fields.ISC j = 1 → j = b0 + os := fun j hj g =>
        Fields.isc_unique fs hn0 (by omega) hj hrs g hisc
      obtain ⟨out, hget, hrm, -, -, hsc, -⟩ := hout os hos
      have hfit' := out_fit hL hsat hL24 S hrm hk
      -- the context's commitment reads
      obtain ⟨r', hr', hi', hcpos, hclen⟩ := commit_link hL hsat hL24 (by rw [hhasc, hconst _ (by omega), h1])
      have hr's : r' = b0 + os := hu r' hr' ((Fields.isc_bool fs hr').resolve_left hi')
      subst hr's
      have hw0 : ((inst 7).main Ctx.W0 0).val < 2 ^ 25 := by rw [← hws]; exact wst_lt hL hsat hL24 S hat0 hρ0
      have hcp : ((inst 7).main Ctx.CPOS 0).val < 2 ^ 25 := by rw [← hcpos]; omega
      obtain ⟨cw, cw1, cw2, cnonce, ccp, cpat, cdig, D, hD, hDe⟩ :=
        Ctx.commit_fact cs h256 (by omega) (Rb inst pub) (ctx_read hL hsat hL24) (ctx_ra hL hsat hL24) hseg ha0 hHC hw0 hcp
      rw [← hcpos] at ccp cpat cdig
      rw [← hclen] at hDe
      have hv38 : ((inst 1).main Fields.VAL (b0 + os)).val = D + 38 := by
        have e : (inst 1).main Fields.VAL (b0 + os) = ((D + 38 : ℕ) : F) := by push_cast; rw [hDe]; ring
        rw [e]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
      have hcm : Spec.Block.IsCommit t0 os := (isCommit_iff hget hsc hfit').mpr ⟨by omega, cpat⟩
      have hidx : Spec.Block.commitmentIndex t0 = some os := by
        rw [Spec.Block.commitmentIndex_eq, dif_pos ⟨os, hos, hcm⟩, Option.some.injEq, Nat.findGreatest_eq_iff]
        refine ⟨by omega, fun _ => hcm, fun o h1o h2o hc => ?_⟩
        obtain ⟨-, -, hrm', -⟩ := hout o (by omega)
        refine noMatch h6 o (by omega) ?_ (Or.inr ⟨h1, ?_⟩) hc
        · rcases Fields.isc_bool fs (r := b0 + o) (by omega) with g | g
          · exact g
          · have := hu _ (by omega) g; omega
        · rw [(Fields.aft_nat fs hn0 (by omega) (r := b0 + o) (by omega)).1,
            iscN_one hL hsat hL24 (by omega) (by omega) hisc hu]; simp
      rw [hidx]
      show Spec.Block.witCheck S.b os = none
      unfold Spec.Block.witCheck
      rw [hcb]
      simp only [hv0, List.headD_cons]
      set R := Rb inst pub
      set W := ((inst 7).main Ctx.W0 0).val with hW
      set C := ((inst 1).main Fields.SSC (b0 + os)).val with hC
      rw [hHC, one_mul, sub_eq_zero] at g2
      -- the coinbase is segwit
      have hseg1 : (inst 1).main Fields.SEG ρ0 = 1 := by
        by_contra hne
        have e := wst_noseg hL hsat hL24 S hat0 hρ0 hne
        rw [hws, hst, g2] at e
        have e' : (((inst 7).main Ctx.W0 0).val + 34 : ℕ) = (((inst 7).main Ctx.W0 0).val : ℕ) := by
          apply natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega))
          push_cast; rw [ZMod.natCast_zmod_val]; exact e.symm
        omega
      obtain ⟨rw, -, hwst, hsl⟩ := Fields.tx_wits fs R S.hcs S.hmn S.hpad S.hfit S.cat S.mono hat0 hρ0 hseg1
      rw [hv0] at hsl
      have hsw : ((inst 1).main Fields.START rw).val = W := by rw [← hwst, hws]
      have hsl0 : ((inst 1).main Fields.START ρ0).val = W + 34 := by
        rw [hst, g2]
        have : (inst 7).main Ctx.W0 0 + 34 = ((W + 34 : ℕ) : F) := by push_cast; rw [ZMod.natCast_zmod_val]
        rw [this]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by omega))
      rw [hsw, hsl0, show W + 34 - W = 34 by omega] at hsl
      -- the witness: `01 20 nonce`
      set nonce := slice R (W + 2) 32 with hnonce
      have hnl : nonce.length = 32 := Fields.slice_length (by omega)
      have hbytes : slice R W 34 = 1 :: 0x20 :: nonce := by
        apply List.ext_getElem
        · rw [Fields.slice_length (by omega)]; simp [hnl]
        · intro i h1 h2
          rw [← List.getD_eq_getElem _ (0 : UInt8) h1, Fields.slice_getD (by simpa [Fields.slice_length (show W + 34 ≤ R.length by omega)] using h1) (by omega),
            ← List.getD_eq_getElem _ (0 : UInt8) h2]
          rcases i with _ | _ | i
          · apply UInt8.toNat_inj.mp; rw [Nat.add_zero, cw1]; rfl
          · apply UInt8.toNat_inj.mp; rw [cw2]; rfl
          · simp only [List.getD_cons_succ]
            rw [hnonce, Fields.slice_getD (by simp at h2; omega) (by omega)]; congr 1; ring
      have hw : inp.witness = [nonce] := by
        have := Fields.stack_nonce (ws := [inp.witness]) rfl hnl (by simpa using hsl.symm.trans hbytes)
        simpa using this
      simp only [hw, hnl, ne_eq, not_true_eq_false, if_false]
      rw [if_neg (not_not.mpr ?_)]
      -- the digest
      have hN : pub 1 = (S.b.txs.length : F) := by
        have := fs 0 hn0 (.mul Fields.first (.sub (Fields.k Fields.VAL) (.pub 1))) (by simp [Fields.constraints, Fields.pubC])
        simp only [Expr.eval, Fields.ev_first hn0, if_true, one_mul, Fields.ev_k hn0, sub_eq_zero] at this
        rw [← this, S.hlenv, ZMod.natCast_zmod_val]
      obtain ⟨oN, oC, hlN, hlC, hdig⟩ := wmerkle_sound hL hsat hL24 h256 S.hparse hN S.hN1 S.hN25 hHC
      have bN : Spec.Block.stateBytes oN = nonce := state_of_reg (by omega) hlN (fun i hi => by
        rw [cnonce i hi]; congr 2 <;> congr 1 <;> ring)
      have bC : Spec.Block.stateBytes oC = slice R (C + 6) 32 := state_of_reg (by omega) hlC (fun i hi => by
        rw [cdig i hi]; congr 2 <;> congr 1 <;> ring)
      rw [bN, bC] at hdig
      simp only [wleaves] at hdig
      have hg : t0.vout.getD os ⟨0, []⟩ = out := by rw [List.getD_eq_getElem?_getD, hget]; rfl
      rw [hg, hsc, ← hdig]
      simp only [slice, List.drop_take, List.drop_drop, List.take_take]
      congr 1; omega
  · have h6 : pub 6 = 0 := by rw [p6, if_neg hsw]
    rw [if_neg (show ¬ c.height ≥ Spec.Block.SEGWIT_HEIGHT from hsw)]
    exact noWit (by rw [hhc, h6, zero_mul])

end System

end StarkedAir.Block
