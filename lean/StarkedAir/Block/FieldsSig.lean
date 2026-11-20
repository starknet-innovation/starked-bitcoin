/-
**An input's sigop flags (CONNECT-RULES step 3).** On a non-coinbase input row, given the spent script's
class (`CP`, `CW20`, `CW32`, from the coin component) and the scriptSig's walk (`SPO`, `SRS`, `SRL`, from
the walker): the requested redeem script's count is `4 · p2shSigOps`, and the flags `GIN·CW20 + RW20` and
`N32` are the two flags of `CountWitnessSigOps` (`w20Of`, `n32Of`, `Spec/SigClass.lean`).
-/
import StarkedAir.Block.FieldsWits
import StarkedAir.Spec.SigWalk

namespace StarkedAir.Block.Fields

open StarkedAir
open StarkedAir.Sha256 (col pre cst eval_col eval_cst boolC)
open StarkedAir.Spec.ConnectRules (sigOpsAccurate lastAcc pushOnly lastPush isP2SH isW p2shSigOps w20Of n32Of opsD)

/-- A row's requested redeem script: 4 times its accurate count when `ARQ = 1`. -/
noncomputable def aN (M : ℕ → ℕ → F) (R : Spec.Block.Bytes) (r : ℕ) : ℕ :=
  if M ARQ r = 1 then 4 * sigOpsAccurate (slice R (M SRS r).val (M SRL r).val) else 0

theorem slice_drop' {R : Spec.Block.Bytes} {a v d : ℕ} (hd : d ≤ v) :
    (slice R a v).drop d = slice R (a + d) (v - d) := by
  simp [slice, List.drop_take, List.drop_drop]

theorem slice_get0 {R : Spec.Block.Bytes} {a l i : ℕ} (hi : i < l) :
    (slice R a l).getD i 0 = R.getD (a + i) 0 := by
  simp [slice, List.getD_eq_getElem?_getD, List.getElem?_take, hi, List.getElem?_drop]

section Sig

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (R : Spec.Block.Bytes)
include hsat

theorem zsig {z inv : ℕ} {e : Expr} (h1 : boolC (k z) ∈ sigC) (h2 : Expr.mul (k z) e ∈ sigC)
    (h3 : Expr.mul (oneMinus (k z)) (.sub (.mul e (k inv)) one) ∈ sigC) {r : ℕ} (hr : r < n) :
    (M z r = 0 ∨ M z r = 1) ∧ (M z r = 1 ↔ e.eval n preCols pub M r = 0) :=
  z_spec hsat (fun c hc => by
    simp only [isZero, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact mem_sig h1
    · exact mem_sig h2
    · exact mem_sig h3) hr

/-- The sigop columns' defining equations on a row. -/
theorem sig_defs {r : ℕ} (hr : r < n) :
    M NZI r = M GIN r * (1 - M ZV r) ∧ M AR0 r = M NZI r * (M CP r * M SPO r) ∧
    M ARQ r = M AR0 r * (1 - M ZRL r) ∧ M LQ r = (M SRL r - 22) * (M SRL r - 34) ∧
    M RDF r = M AR0 r * M ZLN r ∧ M RWA r = M RDF r * M ZPG r ∧
    12 * M RW32 r = M RWA r * (M SRL r - 22) ∧ M N32 r = M GIN r * M CW32 r + M RW32 r ∧
    M RW20 r = M RWA r - M RW32 r := by
  have d := fun (a : ℕ) (e : Expr) (h : Expr.sub (k a) e ∈ sigC) => defn hsat (mem_sig h) hr
  have e1 := d NZI (.mul (k GIN) (oneMinus (k ZV))) (by simp [sigC])
  have e2 := d AR0 (.mul (k NZI) (.mul (k CP) (k SPO))) (by simp [sigC])
  have e3 := d ARQ (.mul (k AR0) (oneMinus (k ZRL))) (by simp [sigC])
  have e4 := d LQ (.mul (.sub (k SRL) (c 22)) (.sub (k SRL) (c 34))) (by simp [sigC])
  have e5 := d RDF (.mul (k AR0) (k ZLN)) (by simp [sigC])
  have e6 := d RWA (.mul (k RDF) (k ZPG)) (by simp [sigC])
  have e7 := sat hsat (mem_sig (c := .sub (.mul (c 12) (k RW32)) (.mul (k RWA) (.sub (k SRL) (c 22))))
    (by simp [sigC])) hr
  have e8 := d N32 (.add (.mul (k GIN) (k CW32)) (k RW32)) (by simp [sigC])
  have e9 := d RW20 (.sub (k RWA) (k RW32)) (by simp [sigC])
  simp only [Expr.eval, ev_k hr, oneMinus, one, c, eval_cst, Nat.cast_one, Nat.cast_ofNat, sub_eq_zero]
    at e1 e2 e3 e4 e5 e6 e7 e8 e9
  exact ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩

omit hsat in
theorem twelve_ne : (12 : F) ≠ 0 := by
  intro h
  have := natCast_inj_of_lt (a := 12) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num) (by simpa using h)
  omega

/-- With no redeem script (`AR0 = 0`) the redeem flags are 0. -/
theorem no_redeem {r : ℕ} (hr : r < n) (h0 : M AR0 r = 0) : M ARQ r = 0 ∧ M RW20 r = 0 ∧ M RW32 r = 0 := by
  obtain ⟨-, -, dARQ, -, dRDF, dRWA, d32, -, dRW20⟩ := sig_defs hsat hr
  have hrwa : M RWA r = 0 := by rw [dRWA, dRDF, h0]; ring
  have h32 : M RW32 r = 0 := by
    rw [hrwa, zero_mul] at d32
    rcases mul_eq_zero.mp d32 with h | h
    · exact absurd h twelve_ne
    · exact h
  exact ⟨by rw [dARQ, h0]; ring, by rw [dRW20, hrwa, h32]; ring, h32⟩

/-- **A non-coinbase input row's sigop flags.** `sp` is the spent script, with its class in `CP`, `CW20`,
`CW32`; `hout` is the walker's output for a non-empty scriptSig; `hrd` the two bytes read at the redeem
script's start. -/
theorem in_cost {ρ : ℕ} (hρ : ρ < n) (hgin : M GIN ρ = 1) (sp : Spec.Block.Bytes)
    (hcp : (M CP ρ = 1 ∧ isP2SH sp = true) ∨ (M CP ρ = 0 ∧ isP2SH sp = false))
    (h20 : (M CW20 ρ = 1 ∧ isW 20 sp = true) ∨ (M CW20 ρ = 0 ∧ isW 20 sp = false))
    (h32 : (M CW32 ρ = 1 ∧ isW 32 sp = true) ∨ (M CW32 ρ = 0 ∧ isW 32 sp = false))
    (hfit : (M SSC ρ).val + (M VAL ρ).val ≤ R.length) (hRl : R.length ≤ 2 ^ 25)
    (hout : M ZV ρ = 0 →
      ((M SPO ρ = 1 ∧ pushOnly (slice R (M SSC ρ).val (M VAL ρ).val) = true) ∨
        (M SPO ρ = 0 ∧ pushOnly (slice R (M SSC ρ).val (M VAL ρ).val) = false)) ∧
      (pushOnly (slice R (M SSC ρ).val (M VAL ρ).val) = true →
        M SRL ρ = (((lastPush (slice R (M SSC ρ).val (M VAL ρ).val)).length : ℕ) : F) ∧
        ((lastPush (slice R (M SSC ρ).val (M VAL ρ).val)).length ≠ 0 →
          M SRS ρ + (((lastPush (slice R (M SSC ρ).val (M VAL ρ).val)).length : ℕ) : F) = M SSC ρ + M VAL ρ)))
    (hrd : M RDF ρ = 1 → (M RB0 ρ).val = (R.getD (M SRS ρ).val 0).toNat ∧
      (M RB1 ρ).val = (R.getD ((M SRS ρ).val + 1) 0).toNat) :
    aN M R ρ = 4 * p2shSigOps sp (slice R (M SSC ρ).val (M VAL ρ).val) ∧
    M GIN ρ * M CW20 ρ + M RW20 ρ = ((w20Of (slice R (M SSC ρ).val (M VAL ρ).val) sp : ℕ) : F) ∧
    M N32 ρ = ((n32Of (slice R (M SSC ρ).val (M VAL ρ).val) sp : ℕ) : F) := by
  have hsl : (slice R (M SSC ρ).val (M VAL ρ).val).length = (M VAL ρ).val := slice_length hfit
  obtain ⟨sig, hsigdef⟩ : ∃ sig, sig = slice R (M SSC ρ).val (M VAL ρ).val := ⟨_, rfl⟩
  rw [← hsigdef] at hout hsl ⊢
  obtain ⟨dNZI, dAR0, dARQ, dLQ, dRDF, dRWA, d32, dN32, dRW20⟩ := sig_defs hsat hρ
  have hc20 : M CW20 ρ = ((if isW 20 sp then 1 else 0 : ℕ) : F) := by
    rcases h20 with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b]
  have hc32 : M CW32 ρ = ((if isW 32 sp then 1 else 0 : ℕ) : F) := by
    rcases h32 with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b]
  suffices key : aN M R ρ = 4 * p2shSigOps sp sig ∧
      M RW20 ρ = ((if (isP2SH sp && pushOnly sig && isW 20 (lastPush sig)) then 1 else 0 : ℕ) : F) ∧
      M RW32 ρ = ((if (isP2SH sp && pushOnly sig && isW 32 (lastPush sig)) then 1 else 0 : ℕ) : F) by
    obtain ⟨k1, k2, k3⟩ := key
    refine ⟨k1, ?_, ?_⟩
    · rw [hgin, one_mul, hc20, k2]; unfold w20Of; push_cast; rfl
    · rw [dN32, hgin, one_mul, hc32, k3]; unfold n32Of; push_cast; rfl
  -- without a redeem script
  have none : M AR0 ρ = 0 → ((isP2SH sp && pushOnly sig) = false ∨ lastPush sig = []) →
      aN M R ρ = 4 * p2shSigOps sp sig ∧
      M RW20 ρ = ((if (isP2SH sp && pushOnly sig && isW 20 (lastPush sig)) then 1 else 0 : ℕ) : F) ∧
      M RW32 ρ = ((if (isP2SH sp && pushOnly sig && isW 32 (lastPush sig)) then 1 else 0 : ℕ) : F) := by
    intro h0 hcase
    obtain ⟨a, b, c'⟩ := no_redeem hsat hρ h0
    refine ⟨?_, ?_, ?_⟩
    · unfold aN; rw [if_neg (by rw [a]; exact zero_ne_one)]
      unfold p2shSigOps
      rcases hcase with h | h
      · rw [h]; simp
      · rw [h, Spec.ConnectRules.acc_nil]; simp
    · rw [b]; rcases hcase with h | h
      · rw [h]; simp
      · rw [h]; simp [isW]
    · rw [c']; rcases hcase with h | h
      · rw [h]; simp
      · rw [h]; simp [isW]
  obtain ⟨hzb, hz1, -⟩ := zv_spec hsat hρ
  rcases hzb with z0 | z1
  swap
  · -- an empty scriptSig
    have hv : (M VAL ρ).val = 0 := by rw [hz1 z1]; simp
    have hs : sig = [] := by rw [hsigdef]; simp [slice, hv]
    exact none (by rw [dAR0, dNZI, z1]; ring) (Or.inr (by rw [hs]; exact Spec.ConnectRules.lastPush_nil))
  obtain ⟨hpo, hlast⟩ := hout z0
  have hnzi : M NZI ρ = 1 := by rw [dNZI, hgin, z0]; ring
  rcases hcp with ⟨cp1, hp⟩ | ⟨cp0, hp⟩
  swap
  · exact none (by rw [dAR0, cp0]; ring) (Or.inl (by rw [hp]; rfl))
  rcases hpo with ⟨po1, hpt⟩ | ⟨po0, hpf⟩
  swap
  · exact none (by rw [dAR0, po0]; ring) (Or.inl (by rw [hpf]; simp))
  -- P2SH spent by a push-only scriptSig: the last push is the redeem script
  have har0 : M AR0 ρ = 1 := by rw [dAR0, hnzi, cp1, po1]; ring
  obtain ⟨hsrl, hsrs⟩ := hlast hpt
  have hparse : (opsD sig).2 = true := by
    unfold pushOnly at hpt; rw [Bool.and_eq_true] at hpt; exact hpt.1
  have hsuf := Spec.ConnectRules.lastPush_suffix sig hparse
  obtain ⟨lp, hlp⟩ : ∃ lp, lp = lastPush sig := ⟨_, rfl⟩
  rw [← hlp] at hsrl hsrs hsuf ⊢
  have hlen : lp.length ≤ (M VAL ρ).val := by rw [← hsl]; exact hsuf.length_le
  have hsrlv : (M SRL ρ).val = lp.length := by rw [hsrl]; exact ZMod.val_natCast_of_lt (lt_P (by omega))
  have cond : (isP2SH sp && pushOnly sig) = true := by rw [hp, hpt]; rfl
  have zrl := zsig hsat (z := ZRL) (inv := INVRL) (e := k SRL) (by simp [sigC, isZero]) (by simp [sigC, isZero])
    (by simp [sigC, isZero]) hρ
  have zln := zsig hsat (z := ZLN) (inv := INVLN) (e := k LQ) (by simp [sigC, isZero]) (by simp [sigC, isZero])
    (by simp [sigC, isZero]) hρ
  have zpg := zsig hsat (z := ZPG) (inv := INVPG) (e := .add (k RB0) (.mul (c 256) (.add (.sub (k RB1) (k SRL)) (c 2))))
    (by simp [sigC, isZero]) (by simp [sigC, isZero]) (by simp [sigC, isZero]) hρ
  simp only [ev_k hρ] at zrl zln
  simp only [Expr.eval, ev_k hρ, c, eval_cst, Nat.cast_ofNat] at zpg
  have lq : M LQ ρ = 0 ↔ (lp.length = 22 ∨ lp.length = 34) := by
    rw [dLQ, hsrl, mul_eq_zero, sub_eq_zero, sub_eq_zero]
    constructor
    · rintro (h | h)
      · exact Or.inl (natCast_inj_of_lt (lt_P (by omega)) (lt_P (by norm_num)) (by simpa using h))
      · exact Or.inr (natCast_inj_of_lt (lt_P (by omega)) (lt_P (by norm_num)) (by simpa using h))
    · rintro (h | h) <;> simp [h]
  have rw32z : M RWA ρ = 0 → M RW32 ρ = 0 := by
    intro h
    rw [h, zero_mul] at d32
    rcases mul_eq_zero.mp d32 with h' | h'
    · exact absurd h' twelve_ne
    · exact h'
  by_cases h0 : lp.length = 0
  · -- an empty last push
    have hl0 : lp = [] := List.length_eq_zero_iff.mp h0
    have hzrl : M ZRL ρ = 1 := zrl.2.2 (by rw [hsrl, h0]; simp)
    have hzln : M ZLN ρ = 0 := by
      rcases zln.1 with h | h
      · exact h
      · exfalso; have := lq.mp (zln.2.1 h); omega
    have hrwa : M RWA ρ = 0 := by rw [dRWA, dRDF, hzln]; ring
    have h32' := rw32z hrwa
    refine ⟨?_, ?_, ?_⟩
    · unfold aN; rw [if_neg (by rw [dARQ, hzrl]; simp)]
      unfold p2shSigOps; rw [cond, if_pos rfl, ← hlp, hl0, Spec.ConnectRules.acc_nil]
    · rw [dRW20, hrwa, h32', hl0]; simp [isW]
    · rw [h32', hl0]; simp [isW]
  -- a redeem script
  have hzrl : M ZRL ρ = 0 := by
    rcases zrl.1 with h | h
    · exact h
    · exfalso; have := zrl.2.1 h; rw [hsrl] at this
      exact h0 (natCast_inj_of_lt (b := 0) (lt_P (by omega)) (lt_P (by norm_num)) (by simpa using this))
  have harq : M ARQ ρ = 1 := by rw [dARQ, har0, hzrl]; ring
  have hs := hsrs h0
  have hsrsv : (M SRS ρ).val = (M SSC ρ).val + (M VAL ρ).val - lp.length := by
    have e : M SRS ρ = (((M SSC ρ).val + (M VAL ρ).val - lp.length : ℕ) : F) := by
      rw [Nat.cast_sub (by omega)]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      linear_combination hs
    rw [e]; exact ZMod.val_natCast_of_lt (lt_P (by omega))
  have hslice : slice R (M SRS ρ).val (M SRL ρ).val = lp := by
    have e := List.suffix_iff_eq_drop.mp hsuf
    rw [hsl] at e
    have e2 : slice R ((M SSC ρ).val + ((M VAL ρ).val - lp.length))
        ((M VAL ρ).val - ((M VAL ρ).val - lp.length)) = lp := by
      rw [← slice_drop' (by omega), ← hsigdef]; exact e.symm
    rw [hsrsv, hsrlv]
    convert e2 using 2 <;> omega
  have E1 : aN M R ρ = 4 * p2shSigOps sp sig := by
    unfold aN; rw [if_pos harq, hslice]
    unfold p2shSigOps; rw [cond, if_pos rfl, ← hlp]
  refine ⟨E1, ?_⟩
  by_cases hl : lp.length = 22 ∨ lp.length = 34
  swap
  · -- not a program's length
    have hzln : M ZLN ρ = 0 := by
      rcases zln.1 with h | h
      · exact h
      · exact absurd (lq.mp (zln.2.1 h)) hl
    have hrwa : M RWA ρ = 0 := by rw [dRWA, dRDF, hzln]; ring
    have h32' := rw32z hrwa
    have w20 : isW 20 lp = false := by
      rw [Bool.eq_false_iff]; intro h; have := ((Spec.ConnectRules.isW_iff 20 lp).mp h).1; omega
    have w32 : isW 32 lp = false := by
      rw [Bool.eq_false_iff]; intro h; have := ((Spec.ConnectRules.isW_iff 32 lp).mp h).1; omega
    exact ⟨by rw [dRW20, hrwa, h32', w20]; simp, by rw [h32', w32]; simp⟩
  -- 22 or 34 bytes: the first two bytes decide
  have hzln : M ZLN ρ = 1 := zln.2.2 (lq.mpr hl)
  have hrdf : M RDF ρ = 1 := by rw [dRDF, har0, hzln]; ring
  obtain ⟨r0, r1⟩ := hrd hrdf
  have g0 : lp.getD 0 0 = R.getD (M SRS ρ).val 0 := by
    rw [← hslice, slice_get0 (by rw [hsrlv]; omega)]; rfl
  have g1 : lp.getD 1 0 = R.getD ((M SRS ρ).val + 1) 0 := by
    rw [← hslice, slice_get0 (by rw [hsrlv]; omega)]
  rw [← g0] at r0; rw [← g1] at r1
  have rb0 : M RB0 ρ = (((lp.getD 0 0).toNat : ℕ) : F) := by rw [← r0, ZMod.natCast_zmod_val]
  have rb1 : M RB1 ρ = (((lp.getD 1 0).toNat : ℕ) : F) := by rw [← r1, ZMod.natCast_zmod_val]
  have b0 := (lp.getD 0 0).toNat_lt
  have b1 := (lp.getD 1 0).toNat_lt
  have zpgN : M ZPG ρ = 1 ↔ ((lp.getD 0 0).toNat = 0 ∧ (lp.getD 1 0).toNat + 2 = lp.length) := by
    rw [zpg.2, rb0, rb1, hsrl]
    constructor
    · intro h
      have e : (((lp.getD 0 0).toNat + 256 * ((lp.getD 1 0).toNat + 2) : ℕ) : F) = ((256 * lp.length : ℕ) : F) := by
        push_cast; linear_combination h
      have := natCast_inj_of_lt (lt_P (by omega)) (lt_P (by omega)) e
      omega
    · rintro ⟨a, b⟩
      rw [a, ← b]; push_cast; ring
  have wk : ∀ kk : ℕ, kk < 256 → (isW kk lp = true ↔ lp.length = kk + 2 ∧ (lp.getD 0 0).toNat = 0 ∧
      (lp.getD 1 0).toNat = kk) := by
    intro kk hkk
    rw [Spec.ConnectRules.isW_iff, List.getElem?_eq_getElem (show 0 < lp.length by omega),
      List.getElem?_eq_getElem (show 1 < lp.length by omega), Option.some.injEq, Option.some.injEq,
      Spec.ConnectRules.u8_toNat_iff _ (show 0 < 256 by norm_num), Spec.ConnectRules.u8_toNat_iff _ hkk,
      List.getD_eq_getElem _ _ (show 0 < lp.length by omega), List.getD_eq_getElem _ _ (show 1 < lp.length by omega)]
    rfl
  have hrwa : M RWA ρ = M ZPG ρ := by rw [dRWA, hrdf]; ring
  rcases hl with l22 | l34
  · have h32' : M RW32 ρ = 0 := by
      rw [hsrl, l22] at d32
      have : (12 : F) * M RW32 ρ = 0 := by rw [d32]; push_cast; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h twelve_ne
      · exact h
    have w32 : isW 32 lp = false := by
      rw [Bool.eq_false_iff]; intro h; have := ((wk 32 (by norm_num)).mp h).1; omega
    refine ⟨?_, by rw [h32', w32]; simp⟩
    rw [dRW20, hrwa, h32', sub_zero]
    rcases zpg.1 with z | z
    · have w20 : isW 20 lp = false := by
        rw [Bool.eq_false_iff]; intro h
        obtain ⟨-, a, b⟩ := (wk 20 (by norm_num)).mp h
        rw [zpgN.mpr ⟨a, by omega⟩] at z; exact one_ne_zero z
      rw [z, w20]; simp
    · obtain ⟨a, b⟩ := zpgN.mp z
      have w20 : isW 20 lp = true := (wk 20 (by norm_num)).mpr ⟨l22, a, by omega⟩
      rw [z, w20, hp, hpt]; simp
  · have h32' : M RW32 ρ = M ZPG ρ := by
      rw [hsrl, l34, hrwa] at d32
      have : (12 : F) * (M RW32 ρ - M ZPG ρ) = 0 := by
        have e : ((34 : ℕ) : F) - 22 = 12 := by norm_num
        rw [mul_sub, d32, e]; ring
      rcases mul_eq_zero.mp this with h | h
      · exact absurd h twelve_ne
      · exact sub_eq_zero.mp h
    have w20 : isW 20 lp = false := by
      rw [Bool.eq_false_iff]; intro h; have := ((wk 20 (by norm_num)).mp h).1; omega
    refine ⟨by rw [dRW20, hrwa, h32', sub_self, w20]; simp, ?_⟩
    rw [h32']
    rcases zpg.1 with z | z
    · have w32 : isW 32 lp = false := by
        rw [Bool.eq_false_iff]; intro h
        obtain ⟨-, a, b⟩ := (wk 32 (by norm_num)).mp h
        rw [zpgN.mpr ⟨a, by omega⟩] at z; exact one_ne_zero z
      rw [z, w32]; simp
    · obtain ⟨a, b⟩ := zpgN.mp z
      have w32 : isW 32 lp = true := (wk 32 (by norm_num)).mpr ⟨l34, a, by omega⟩
      rw [z, w32, hp, hpt]; simp

omit R in
/-- The request multiplicities are bits: a redeem script (`ARQ`), a witness script (`WQ · (1 − ZV)`), a
witness request and its use. -/
theorem req_bools {r : ℕ} (hr : r < n) :
    (M ARQ r = 0 ∨ M ARQ r = 1) ∧ (M WQ r * (1 - M ZV r) = 0 ∨ M WQ r * (1 - M ZV r) = 1) ∧
    (M N32 r * M SEG r = 0 ∨ M N32 r * M SEG r = 1) ∧ (M K_WCNT r * M WS r = 0 ∨ M K_WCNT r * M WS r = 1) := by
  have hb : ∀ {x y : F}, (x = 0 ∨ x = 1) → (y = 0 ∨ y = 1) → (x * y = 0 ∨ x * y = 1) := by
    intro x y hx hy; rcases hx with h | h <;> rcases hy with h' | h' <;> simp [h, h']
  have om : ∀ {x : F}, (x = 0 ∨ x = 1) → (1 - x = 0 ∨ 1 - x = 1) := by
    intro x hx; rcases hx with h | h <;> simp [h]
  obtain ⟨dNZI, dAR0, dARQ, -⟩ := sig_defs hsat hr
  have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr
  simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hgin
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
  have zv := chk_bool hsat (e := ZV) (by simp [chkC, totalsC]) hr
  have kin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
  have cp := bool_of hsat (mem_sig (c := boolC (k CP)) (by simp [sigC])) hr
  have spo := bool_of hsat (mem_sig (c := boolC (k SPO)) (by simp [sigC])) hr
  have zrl := bool_of hsat (mem_sig (c := boolC (k ZRL)) (by simp [sigC, isZero])) hr
  have n32 := bool_of hsat (mem_sig (c := boolC (k N32)) (by simp [sigC])) hr
  have ws := bool_of hsat (mem_sig (c := boolC (k WS)) (by simp [sigC])) hr
  have kw := kind_bool hsat (c := K_WCNT) (by simp [kinds, K_WCNT]) hr
  have ki := kind_bool hsat (c := K_WITEM) (by simp [kinds, K_WITEM]) hr
  refine ⟨?_, ?_, hb n32 (seg_bool hsat hr), hb kw ws⟩
  · rw [dARQ, dAR0, dNZI, hgin]
    exact hb (hb (hb (hb kin (om zt)) (om zv)) (hb cp spo)) (om zrl)
  · have := defn hsat (mem_sig (c := .sub (k WQ) (.mul (k K_WITEM) (.mul (k WS) (k Z1)))) (by simp [sigC])) hr
    simp only [Expr.eval, ev_k hr] at this
    rw [this]
    exact hb (hb ki (hb ws (z1_spec hsat hr).1)) (om zv)

omit R in
/-- A row that is no non-coinbase input has no redeem request and adds nothing to the two flags. -/
theorem nongin {r : ℕ} (hr : r < n) (h : M GIN r ≠ 1) :
    M ARQ r = 0 ∧ M GIN r * M CW20 r + M RW20 r = 0 ∧ M N32 r = 0 := by
  obtain ⟨dNZI, dAR0, -, -, -, -, -, dN32, -⟩ := sig_defs hsat hr
  have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr
  simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hgin
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
  have kin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
  have g0 : M GIN r = 0 := by
    rcases kin with a | a <;> rcases zt with b | b <;> rw [hgin, a, b] at h ⊢ <;> simp at h ⊢
  obtain ⟨a, b, c'⟩ := no_redeem hsat hr (by rw [dAR0, dNZI, g0]; ring)
  exact ⟨a, by rw [g0, b]; ring, by rw [dN32, g0, c']; ring⟩

omit R in
/-- A row's addition to the 20-byte program count is a natural of at most 2. -/
theorem w20_term {r : ℕ} (hr : r < n) : M GIN r * M CW20 r + M RW20 r =
    (((M GIN r * M CW20 r + M RW20 r).val : ℕ) : F) ∧ (M GIN r * M CW20 r + M RW20 r).val ≤ 2 := by
  have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) hr
  simp only [Expr.eval, oneMinus, one, ev_k hr, eval_cst, Nat.cast_one] at hgin
  have zt := chk_bool hsat (e := ZT) (by simp [chkC, prevoutC]) hr
  have kin := kind_bool hsat (c := K_IN) (by simp [kinds, K_IN]) hr
  have cw := bool_of hsat (mem_sig (c := boolC (k CW20)) (by simp [sigC])) hr
  have rw := bool_of hsat (mem_sig (c := boolC (k RW20)) (by simp [sigC])) hr
  have x01 : M GIN r * M CW20 r = 0 ∨ M GIN r * M CW20 r = 1 := by
    rw [hgin]
    rcases zt with a | a <;> rcases kin with b | b <;> rcases cw with d | d <;> simp [a, b, d]
  refine ⟨(ZMod.natCast_zmod_val _).symm, ?_⟩
  rcases x01 with x | x <;> rcases rw with e | e <;> rw [x, e]
  · simp
  · simp [ZMod.val_one]
  · simp [ZMod.val_one]
  · rw [show (1 : F) + 1 = ((2 : ℕ) : F) by norm_num, ZMod.val_natCast_of_lt (by unfold P; norm_num)]

omit R in
/-- **The 20-byte program count** is the sum of the rows' additions. -/
theorem w20_sum : ∀ r < n, M W20S r = ∑ j ∈ Finset.range (r + 1), (M GIN j * M CW20 j + M RW20 j) := by
  intro r
  induction r with
  | zero =>
    intro h0
    have c1 := sat hsat (mem_sig (c := .mul first (k W20S)) (by simp [sigC])) h0
    simp only [Expr.eval, ev_first h0, if_true, one_mul, ev_k h0] at c1
    have hk : M K_IN 0 = 0 :=
      (kinds_at hsat h0 (a := K_BLK) (by simp [K_BLK]) (first_blk hsat h0) K_IN (by simp [K_IN])).trans
        (by simp [K_BLK, K_IN])
    have hgin := chk_defn hsat (a := GIN) (e := .mul (k K_IN) (oneMinus (k ZT))) (by simp [chkC, prevoutC]) h0
    simp only [Expr.eval, oneMinus, one, ev_k h0, eval_cst, Nat.cast_one] at hgin
    have := (nongin hsat h0 (by rw [hgin, hk]; simp)).2.1
    rw [c1]; simp [this]
  | succ r ih =>
    intro hr
    have c1 := sat hsat (mem_sig (c := .mul notFirst (.sub (.sub (.sub (k W20S) (kp W20S)) (.mul (k GIN) (k CW20)))
      (k RW20))) (by simp [sigC])) hr
    simp only [Expr.eval, ev_notFirst hr, one_mul, ev_k hr, ev_kp hr] at c1
    rw [Finset.sum_range_succ, ← ih (by omega)]; linear_combination c1

end Sig

end StarkedAir.Block.Fields
