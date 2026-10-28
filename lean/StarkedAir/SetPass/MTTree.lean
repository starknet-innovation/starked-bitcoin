/-
**The segment's Merkle root is the heap tree of its leaves (D-050).** With `set_lc`'s yields the leaves'
words (`hleaf`), every node yield of node `j` (`1 ≤ j < 2·HALF`) carries `node HALF ls j`'s words
(`node_ok`, strong induction from the bottom), and the public root is node 1's (`root_ok`).
-/
import StarkedAir.SetPass.MTLink

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst half16)
open StarkedAir.Spec.HeaderTree (hnode stWord toState)
open StarkedAir.Blake2s (outWord msgWord)

section Tree

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
  (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls)
include hL hsat hHL hsz

omit hL hsat hHL hsz in
/-- Three bytes' value. -/
theorem b3_eval {n r : ℕ} {M : ℕ → ℕ → F} {f : ℕ → ℕ} (hr : r < n)
    (hb : ∀ i < 3, (M (f i) r).val < 256) :
    (MT.b3 f).eval n MT.preCols pub M r =
      ((((M (f 0) r).val + 256 * (M (f 1) r).val + 65536 * (M (f 2) r).val : ℕ)) : F) ∧
    (M (f 0) r).val + 256 * (M (f 1) r).val + 65536 * (M (f 2) r).val < 2 ^ 24 := by
  have := hb 0 (by norm_num); have := hb 1 (by norm_num); have := hb 2 (by norm_num)
  refine ⟨?_, by omega⟩
  simp only [MT.b3, Expr.eval, MT.ev_k (pub := pub) (M := M) hr, StarkedAir.Sha256.eval_cst]
  push_cast
  simp only [ZMod.natCast_zmod_val]

/-- **A tree range read** (lookups 18–32) gated by `m` evaluating to 1 is a byte. -/
theorem mt_r8 {r k c : ℕ} {m : Expr} (hr : r < 2 ^ Ls 11) (hk : 18 ≤ k) (hk33 : k < 33)
    (hl : MT.lookups.getD k ⟨0, .const 0, []⟩ = MT.r8 (MT.k c) m)
    (hm : m.eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r = 1) : ((inst 11).main c r).val < 256 := by
  have hsite := site_mem hL (i := 11) (by decide) hr (k := k) (by
    show k < MT.lookups.length; simp [MT.lookups]; omega)
  have hpre : (segSys.comp 11).air.pre = MT.preCols := rfl
  have hsl : siteLookup segSys ((11, r, k) : Site) = _ := hl
  exact r8_read hL hsat hHL hsz hsite (by simp [isUse]; omega) (by simp [siteRel, hsl, MT.r8])
    (by simp only [siteMult, hsl, siteEval, hpre, hL 11 (by decide), MT.r8, Expr.eval, hm])
    (by simp [siteVals, hsl, siteEval, hpre, hL 11 (by decide), MT.r8, MT.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr])

omit hHL hsz in
theorem mt_r8_lookups :
    (∀ i < 3, MT.lookups.getD (18 + i) ⟨0, .const 0, []⟩ = MT.r8 (MT.k (MT.DD i)) (.mul (MT.k MT.USEW) (MT.p MT.P_R0))) ∧
    (∀ i < 3, MT.lookups.getD (21 + i) ⟨0, .const 0, []⟩ = MT.r8 (MT.k (MT.UL i)) (.mul (MT.k MT.LU) (MT.p MT.P_R0))) ∧
    (∀ i < 3, MT.lookups.getD (24 + i) ⟨0, .const 0, []⟩ = MT.r8 (MT.k (MT.UR i)) (.mul (MT.k MT.LU) (MT.p MT.P_R0))) ∧
    (∀ i < 3, MT.lookups.getD (27 + i) ⟨0, .const 0, []⟩ = MT.r8 (MT.k (MT.EB i)) (MT.p MT.P_FIRST)) ∧
    (∀ i < 3, MT.lookups.getD (30 + i) ⟨0, .const 0, []⟩ = MT.r8 (MT.k (MT.HB i)) (MT.p MT.P_FIRST)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (intro i hi; interval_cases i <;> rfl)

/-- **`HALF` and the record count**: `1 ≤ HALF ≤ 2^24` and `cnt ≤ 2·HALF`. -/
theorem half_facts {cnt : ℕ} (hcnt : pub PUB_I_OUT - pub PUB_I_IN = (cnt : F)) (hc24 : cnt ≤ 2 ^ 24) :
    pub PUB_HALF = ((pub PUB_HALF).val : F) ∧ 1 ≤ (pub PUB_HALF).val ∧ (pub PUB_HALF).val ≤ 2 ^ 24 ∧
      cnt ≤ 2 * (pub PUB_HALF).val := by
  have ms := mt_sat hL hsat
  obtain ⟨-, -, -, l4, l5⟩ := mt_r8_lookups (hL := hL) (hsat := hsat) (inst := inst) (pub := pub) (Ls := Ls)
  have h0 : 0 < 2 ^ Ls 11 := by positivity
  have hf : (MT.p MT.P_FIRST).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main 0 = 1 := by
    rw [MT.ev_first (pub := pub) (M := (inst 11).main) h0, if_pos rfl]
  have eb := b3_eval (pub := pub) (M := (inst 11).main) (f := MT.EB) h0 (fun i hi =>
    mt_r8 hL hsat hHL hsz h0 (by omega) (by omega) (l4 i hi) hf)
  have hb := b3_eval (pub := pub) (M := (inst 11).main) (f := MT.HB) h0 (fun i hi =>
    mt_r8 hL hsat hHL hsz h0 (by omega) (by omega) (l5 i hi) hf)
  have cE := MT.sat ms (MT.mem_flag (c := .mul (MT.p MT.P_FIRST) (.sub (.sub (.mul (cst 2) MT.half) MT.cnt) (MT.b3 MT.EB))) (by simp [MT.flagC])) h0
  have cH := MT.sat ms (MT.mem_flag (c := .mul (MT.p MT.P_FIRST) (.sub (.sub MT.half MT.one) (MT.b3 MT.HB))) (by simp [MT.flagC])) h0
  simp only [Expr.eval, hf, one_mul, eb.1, hb.1, MT.half, MT.cnt, MT.one, StarkedAir.Sha256.eval_cst, Nat.cast_one,
    Nat.cast_ofNat, sub_eq_zero, hcnt] at cE cH
  set e := ((inst 11).main (MT.EB 0) 0).val + 256 * ((inst 11).main (MT.EB 1) 0).val + 65536 * ((inst 11).main (MT.EB 2) 0).val
  set h := ((inst 11).main (MT.HB 0) 0).val + 256 * ((inst 11).main (MT.HB 1) 0).val + 65536 * ((inst 11).main (MT.HB 2) 0).val
  have hh : pub PUB_HALF = ((h + 1 : ℕ) : F) := by push_cast; linear_combination cH
  have hv : (pub PUB_HALF).val = h + 1 := by
    rw [hh, ZMod.val_natCast_of_lt (by unfold P; omega)]
  refine ⟨by rw [hv, hh], by omega, by omega, ?_⟩
  have : ((2 * (h + 1) : ℕ) : F) = ((cnt + e : ℕ) : F) := by
    have hh' : (h : F) + 1 = pub PUB_HALF := by rw [hh]; push_cast; ring
    push_cast; rw [hh']; linear_combination cE
  have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) this
  omega

/-- **A node read** (`MUN = 1`) is a tree node yield with the same values. -/
theorem node_use {t : ℕ} (ht : t < 2 ^ Ls 11) (hmun : (inst 11).main MT.MUN t = 1) :
    ∃ r' k', r' < 2 ^ Ls 11 ∧ 2 ≤ k' ∧ k' < 10 ∧ siteMult segSys inst pub (11, r', k') ≠ 0 ∧
      siteVals segSys inst pub (11, r', k') = [(inst 11).main MT.CK t,
        (MT.p MT.P_W8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t, (inst 11).main MT.WLO t,
        (inst 11).main MT.WHI t] := by
  have hpre : (segSys.comp 11).air.pre = MT.preCols := rfl
  have hsite := site_mem hL (i := 11) (by decide) ht (k := 0) (by simp [segSys, comps, MT.mt, MT.lookups])
  have hm : siteMult segSys inst pub (11, t, 0) = -1 := by
    simp [siteMult, siteEval, siteLookup, hpre, hL 11 (by decide), segSys, comps, MT.mt, MT.lookups, Expr.eval,
      MT.ev_k (pub := pub) (M := (inst 11).main) ht, hmun]
  obtain ⟨i, r', k', hr', hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse]) hm
  rw [show siteRel segSys ((11, t, 0) : Site) = 40 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, h2, h10⟩ : i = 11 ∧ 2 ≤ k' ∧ k' < 10 := by omega
  refine ⟨r', k', hr', h2, h10, hsm, ?_⟩
  rw [hsv]
  simp [siteVals, siteEval, siteLookup, hpre, hL 11 (by decide), segSys, comps, MT.mt, MT.lookups,
    MT.ev_k (pub := pub) (M := (inst 11).main) ht]

/-- **A leaf read** (`MUL = 1`) is a leaf compression yield with the same values. -/
theorem leaf_use {t : ℕ} (ht : t < 2 ^ Ls 11) (hmul : (inst 11).main MT.MUL t = 1) :
    ∃ r' k', r' < 2 ^ Ls 10 ∧ 2 ≤ k' ∧ k' < 10 ∧ siteMult segSys inst pub (10, r', k') ≠ 0 ∧
      siteVals segSys inst pub (10, r', k') = [(inst 11).main MT.CK t,
        (MT.p MT.P_W8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t, (inst 11).main MT.WLO t,
        (inst 11).main MT.WHI t] := by
  have hpre : (segSys.comp 11).air.pre = MT.preCols := rfl
  have hsite := site_mem hL (i := 11) (by decide) ht (k := 1) (by simp [segSys, comps, MT.mt, MT.lookups])
  have hm : siteMult segSys inst pub (11, t, 1) = -1 := by
    simp [siteMult, siteEval, siteLookup, hpre, hL 11 (by decide), segSys, comps, MT.mt, MT.lookups, Expr.eval,
      MT.ev_k (pub := pub) (M := (inst 11).main) ht, hmul]
  obtain ⟨i, r', k', hr', hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse]) hm
  rw [show siteRel segSys ((11, t, 1) : Site) = 39 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, h2, h10⟩ : i = 10 ∧ 2 ≤ k' ∧ k' < 10 := by omega
  refine ⟨r', k', hr', h2, h10, hsm, ?_⟩
  rw [hsv]
  simp [siteVals, siteEval, siteLookup, hpre, hL 11 (by decide), segSys, comps, MT.mt, MT.lookups,
    MT.ev_k (pub := pub) (M := (inst 11).main) ht]

omit hHL hsz in
/-- The row's derived columns. -/
theorem row_defs {t : ℕ} (ht : t < 2 ^ Ls 11) :
    (inst 11).main MT.MUN t = (inst 11).main MT.USEW t * (MT.p MT.P_LT16).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t *
      (1 - (inst 11).main MT.LEAFL t) ∧
    (inst 11).main MT.MUL t = (inst 11).main MT.LU t * (MT.p MT.P_LT16).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t *
      (inst 11).main MT.USEROW t ∧
    (inst 11).main MT.LU t = (inst 11).main MT.USEW t * (inst 11).main MT.LEAFL t ∧
    (inst 11).main MT.USEROW t = (MT.p MT.P_LT8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t * (inst 11).main MT.USEL t +
      (1 - (MT.p MT.P_LT8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t) * (inst 11).main MT.USER t ∧
    (inst 11).main MT.ZW t = (inst 11).main MT.LU t * (1 - (inst 11).main MT.USEROW t) ∧
    (inst 11).main MT.CK t = 2 * (inst 11).main MT.ID t + (1 - (MT.p MT.P_LT8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main t) -
      2 * pub PUB_HALF * (inst 11).main MT.LEAFL t := by
  have ms := mt_sat hL hsat
  have ev := fun c => MT.ev_k (pub := pub) (M := (inst 11).main) (c := c) ht
  have d := fun a e (h : Expr.sub (MT.k a) e ∈ MT.flagC) => MT.defn ms h ht
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [d MT.MUN (.mul (.mul (MT.k MT.USEW) (MT.p MT.P_LT16)) (MT.om (MT.k MT.LEAFL))) (by simp [MT.flagC])]; simp [Expr.eval, ev, MT.om, MT.one, StarkedAir.Sha256.eval_cst]
  · rw [d MT.MUL (.mul (.mul (MT.k MT.LU) (MT.p MT.P_LT16)) (MT.k MT.USEROW)) (by simp [MT.flagC])]; simp [Expr.eval, ev]
  · rw [d MT.LU (.mul (MT.k MT.USEW) (MT.k MT.LEAFL)) (by simp [MT.flagC])]; simp [Expr.eval, ev]
  · rw [d MT.USEROW (.add (.mul (MT.p MT.P_LT8) (MT.k MT.USEL)) (.mul (MT.om (MT.p MT.P_LT8)) (MT.k MT.USER))) (by simp [MT.flagC])]; simp [Expr.eval, ev, MT.om, MT.one, StarkedAir.Sha256.eval_cst]
  · rw [d MT.ZW (.mul (MT.k MT.LU) (MT.om (MT.k MT.USEROW))) (by simp [MT.flagC])]; simp [Expr.eval, ev, MT.om, MT.one, StarkedAir.Sha256.eval_cst]
  · rw [d MT.CK (.sub (.add (.mul (cst 2) (MT.k MT.ID)) (MT.om (MT.p MT.P_LT8))) (.mul (.mul (cst 2) MT.half) (MT.k MT.LEAFL))) (by simp [MT.flagC])]
    simp [Expr.eval, ev, MT.om, MT.one, MT.half, StarkedAir.Sha256.eval_cst]

/-- **The level**: a used period of node `j < 2·HALF` hashes leaf slots iff `HALF ≤ j`. -/
theorem level {s j half : ℕ} (hs : s < 2 ^ Ls 11) (hs0 : s % 88 = 0) (hu : (inst 11).main MT.USEW s = 1)
    (hid : (inst 11).main MT.ID s = (j : F)) (hhalf : pub PUB_HALF = (half : F)) (h24 : half ≤ 2 ^ 24)
    (hj : j < 2 * half) :
    ((inst 11).main MT.LEAFL s = 0 ∧ j < half) ∨ ((inst 11).main MT.LEAFL s = 1 ∧ half ≤ j) := by
  have ms := mt_sat hL hsat
  obtain ⟨l1, -, -, -, -⟩ := mt_r8_lookups (hL := hL) (hsat := hsat) (inst := inst) (pub := pub) (Ls := Ls)
  have hr0 : (Expr.mul (MT.k MT.USEW) (MT.p MT.P_R0)).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main s = 1 := by
    simp [Expr.eval, MT.ev_k (pub := pub) (M := (inst 11).main) hs, MT.ev_r0 (pub := pub) (M := (inst 11).main) hs,
      hs0, hu]
  have dd := b3_eval (pub := pub) (M := (inst 11).main) (f := MT.DD) hs (fun i hi =>
    mt_r8 hL hsat hHL hsz hs (by omega) (by omega) (l1 i hi) hr0)
  have c := MT.sat ms (MT.mem_flag (c := .mul (MT.k MT.USEW) (.sub (.add (.mul (MT.k MT.LEAFL) (.sub (MT.k MT.ID) MT.half))
    (.mul (MT.om (MT.k MT.LEAFL)) (.sub (.sub MT.half MT.one) (MT.k MT.ID)))) (MT.b3 MT.DD))) (by simp [MT.flagC])) hs
  simp only [Expr.eval, MT.ev_k (pub := pub) (M := (inst 11).main) hs, hu, one_mul, dd.1, MT.half, MT.om, MT.one,
    StarkedAir.Sha256.eval_cst, Nat.cast_one, hid, hhalf, sub_eq_zero] at c
  set d := ((inst 11).main (MT.DD 0) s).val + 256 * ((inst 11).main (MT.DD 1) s).val +
    65536 * ((inst 11).main (MT.DD 2) s).val
  rcases MT.bool_flag ms (c := MT.LEAFL) (by simp) hs with h0 | h1
  · rw [h0] at c
    have e : ((half : ℕ) : F) = ((j + 1 + d : ℕ) : F) := by push_cast; linear_combination c
    have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e
    exact Or.inl ⟨h0, by omega⟩
  · rw [h1] at c
    have e : ((j : ℕ) : F) = ((half + d : ℕ) : F) := by push_cast; linear_combination c
    have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e
    exact Or.inr ⟨h1, by omega⟩

/-- **The slot flags**: a leaf-level period's left (right) slot flag is set iff the slot holds a record. -/
theorem slot_flags {s j half cnt : ℕ} (hs : s < 2 ^ Ls 11) (hs0 : s % 88 = 0) (hlu : (inst 11).main MT.LU s = 1)
    (hid : (inst 11).main MT.ID s = (j : F)) (hhalf : pub PUB_HALF = (half : F)) (hhj : half ≤ j) (hj : j < 2 * half)
    (h24 : half ≤ 2 ^ 24) (hcnt : pub PUB_I_OUT - pub PUB_I_IN = (cnt : F)) (hc : cnt ≤ 2 * half) :
    ((inst 11).main MT.USEL s = 1 ↔ 2 * (j - half) < cnt) ∧ ((inst 11).main MT.USER s = 1 ↔ 2 * (j - half) + 1 < cnt) := by
  have ms := mt_sat hL hsat
  obtain ⟨-, l2, l3, -, -⟩ := mt_r8_lookups (hL := hL) (hsat := hsat) (inst := inst) (pub := pub) (Ls := Ls)
  have hr0 : (Expr.mul (MT.k MT.LU) (MT.p MT.P_R0)).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main s = 1 := by
    simp [Expr.eval, MT.ev_k (pub := pub) (M := (inst 11).main) hs, MT.ev_r0 (pub := pub) (M := (inst 11).main) hs,
      hs0, hlu]
  have ul := b3_eval (pub := pub) (M := (inst 11).main) (f := MT.UL) hs (fun i hi =>
    mt_r8 hL hsat hHL hsz hs (by omega) (by omega) (l2 i hi) hr0)
  have ur := b3_eval (pub := pub) (M := (inst 11).main) (f := MT.UR) hs (fun i hi =>
    mt_r8 hL hsat hHL hsz hs (by omega) (by omega) (l3 i hi) hr0)
  have hsl : MT.slotL.eval (2 ^ Ls 11) MT.preCols pub (inst 11).main s = ((2 * (j - half) : ℕ) : F) := by
    simp only [MT.slotL, Expr.eval, MT.ev_k (pub := pub) (M := (inst 11).main) hs, MT.half, StarkedAir.Sha256.eval_cst,
      hid, hhalf]
    rw [Nat.cast_mul, Nat.cast_sub hhj]
  have hcn : MT.cnt.eval (2 ^ Ls 11) MT.preCols pub (inst 11).main s = (cnt : F) := by
    simp only [MT.cnt, Expr.eval, hcnt]
  have cL := MT.sat ms (MT.mem_flag (c := .mul (MT.k MT.LU) (.sub (.add (.mul (MT.k MT.USEL) (.sub (.sub MT.cnt MT.one) MT.slotL))
    (.mul (MT.om (MT.k MT.USEL)) (.sub MT.slotL MT.cnt))) (MT.b3 MT.UL))) (by simp [MT.flagC])) hs
  have cR := MT.sat ms (MT.mem_flag (c := .mul (MT.k MT.LU) (.sub (.add (.mul (MT.k MT.USER) (.sub (.sub MT.cnt MT.one)
    (.add MT.slotL MT.one))) (.mul (MT.om (MT.k MT.USER)) (.sub (.add MT.slotL MT.one) MT.cnt))) (MT.b3 MT.UR)))
    (by simp [MT.flagC])) hs
  simp only [Expr.eval, MT.ev_k (pub := pub) (M := (inst 11).main) hs, hlu, one_mul, ul.1, ur.1, hsl, hcn, MT.om, MT.one,
    StarkedAir.Sha256.eval_cst, Nat.cast_one, sub_eq_zero] at cL cR
  set u := ((inst 11).main (MT.UL 0) s).val + 256 * ((inst 11).main (MT.UL 1) s).val + 65536 * ((inst 11).main (MT.UL 2) s).val
  set v := ((inst 11).main (MT.UR 0) s).val + 256 * ((inst 11).main (MT.UR 1) s).val + 65536 * ((inst 11).main (MT.UR 2) s).val
  have hu24 := ul.2
  have hv24 := ur.2
  constructor
  · rcases MT.bool_flag ms (c := MT.USEL) (by simp) hs with h0 | h1
    · rw [h0] at cL
      have e : ((2 * (j - half) : ℕ) : F) = ((cnt + u : ℕ) : F) := by push_cast at cL ⊢; linear_combination cL
      have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e
      rw [h0]; constructor
      · intro h; exact absurd h zero_ne_one
      · intro h; omega
    · rw [h1] at cL
      have e : ((cnt : ℕ) : F) = ((2 * (j - half) + 1 + u : ℕ) : F) := by push_cast at cL ⊢; linear_combination cL
      have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e
      rw [h1]; exact ⟨fun _ => by omega, fun _ => rfl⟩
  · rcases MT.bool_flag ms (c := MT.USER) (by simp) hs with h0 | h1
    · rw [h0] at cR
      have e : ((2 * (j - half) + 1 : ℕ) : F) = ((cnt + v : ℕ) : F) := by push_cast at cR ⊢; linear_combination cR
      have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e
      rw [h0]; constructor
      · intro h; exact absurd h zero_ne_one
      · intro h; omega
    · rw [h1] at cR
      have e : ((cnt : ℕ) : F) = ((2 * (j - half) + 1 + 1 + v : ℕ) : F) := by push_cast at cR ⊢; linear_combination cR
      have := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) e
      rw [h1]; exact ⟨fun _ => by omega, fun _ => rfl⟩

end Tree

namespace MT

open Spec.SetMerkle in
theorem node_unfold (half : ℕ) (ls : List Spec.Sha256.State) (j : ℕ) : node half ls j =
    if 1 ≤ j ∧ j < half then hnode (node half ls (2 * j)) (node half ls (2 * j + 1))
    else hnode (slot ls (2 * (j - half))) (slot ls (2 * (j - half) + 1)) := by
  rw [node]; simp only [dite_eq_ite]

open Spec.SetMerkle in
theorem slot_map {cnt : ℕ} (lf : ℕ → Spec.Sha256.State) (s : ℕ) :
    slot ((List.range cnt).map lf) s = if s < cnt then lf s else zero := by
  unfold slot
  split_ifs with h
  · rw [List.getD_eq_getElem _ _ (by simpa using h)]; simp
  · rw [List.getD_eq_default _ _ (by simpa using h)]

theorem stWord_zero (w : ℕ) : stWord Spec.SetMerkle.zero w = 0 := by
  unfold stWord Spec.SetMerkle.zero
  split <;> rfl

theorem half16_zero (h : ℕ) : half16 (0 : Spec.Blake2s.Word) h = 0 := by
  cases h <;> simp [half16]

end MT

section Nodes

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
  (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls)
  {half cnt : ℕ} (hhalf : pub PUB_HALF = (half : F)) (h24 : half ≤ 2 ^ 24)
  (hcnt : pub PUB_I_OUT - pub PUB_I_IN = (cnt : F)) (hc : cnt ≤ 2 * half)
  {lf : ℕ → Spec.Sha256.State}
  (hleaf : ∀ r k, r < 2 ^ Ls 10 → 2 ≤ k → k < 10 → siteMult segSys inst pub (10, r, k) ≠ 0 →
    ∃ s < cnt, siteVals segSys inst pub (10, r, k) = [(s : F), ((MT.widx k : ℕ) : F),
      ((half16 (stWord (lf s) (MT.widx k)) 0 : ℕ) : F), ((half16 (stWord (lf s) (MT.widx k)) 1 : ℕ) : F)])
include hL hsat hHL hsz hhalf h24 hcnt hc hleaf

/-- A used period of node `j` outputs `node HALF ls j`. -/
def NodeOk (inst : ℕ → Inst) (Ls : ℕ → ℕ) (half : ℕ) (ls : List Spec.Sha256.State) (j : ℕ) : Prop :=
  ∀ s, s % 88 = 0 → s + 88 ≤ 2 ^ Ls 11 → (inst 11).main MT.USEW s = 1 → (inst 11).main MT.ID s = (j : F) →
    ∀ w < 8, outWord (inst 11).main s w = stWord (Spec.SetMerkle.node half ls j) w

/-- **Every node is the heap tree's.** -/
theorem node_ok : ∀ m j, 2 * half - j = m → 1 ≤ j → j < 2 * half →
    NodeOk inst Ls half ((List.range cnt).map lf) j := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro j hm hj1 hj s hs0 hsn hu hid
  have ms := mt_sat hL hsat
  have hs : s < 2 ^ Ls 11 := by omega
  -- the children
  let child : ℕ → Spec.Sha256.State := fun b =>
    if j < half then Spec.SetMerkle.node half ((List.range cnt).map lf) (2 * j + b)
    else Spec.SetMerkle.slot ((List.range cnt).map lf) (2 * (j - half) + b)
  have hrow : ∀ kk < 16, (inst 11).main (Blake2s.ML kk 0) s = ((half16 (stWord (child (kk / 8)) (kk % 8)) 0 : ℕ) : F) ∧
      (inst 11).main (Blake2s.ML kk 1) s = ((half16 (stWord (child (kk / 8)) (kk % 8)) 1 : ℕ) : F) := by
    intro kk hkk
    have ht : s + kk < 2 ^ Ls 11 := by omega
    obtain ⟨mw0, mw1⟩ := MT.msg_word ms hs0 hsn hkk
    rw [← mw0, ← mw1]
    obtain ⟨dMUN, dMUL, dLU, dROW, dZW, dCK⟩ := row_defs hL hsat (pub := pub) ht
    have e16 : (MT.p MT.P_LT16).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main (s + kk) = 1 := by
      rw [MT.ev_lt16 ht, if_pos (by omega)]
    have e8 : (MT.p MT.P_LT8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main (s + kk) = ((1 - kk / 8 : ℕ) : F) := by
      rw [MT.ev_lt8 ht]
      split_ifs with h
      · rw [show 1 - kk / 8 = 1 by omega]; simp
      · rw [show 1 - kk / 8 = 0 by omega]; simp
    have ew : (MT.p MT.P_W8).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main (s + kk) = ((kk % 8 : ℕ) : F) := by
      rw [MT.ev_w8 ht (by omega), show (s + kk) % 88 % 8 = kk % 8 by omega]
    have pc := fun X (hX : X ∈ MT.perConst) => MT.per_const ms hX hs0 kk (by omega) ht
    have huw : (inst 11).main MT.USEW (s + kk) = 1 := by rw [MT.usew_const ms hs0 kk (by omega) ht, hu]
    have hidt : (inst 11).main MT.ID (s + kk) = (j : F) := by rw [pc MT.ID (by simp [MT.perConst]), hid]
    rcases level hL hsat hHL hsz hs hs0 hu hid hhalf h24 hj with ⟨hl0, hjh⟩ | ⟨hl1, hjh⟩
    · -- an internal node: the child is a node yield
      have hlt : (inst 11).main MT.LEAFL (s + kk) = 0 := by rw [pc MT.LEAFL (by simp [MT.perConst]), hl0]
      have hmun : (inst 11).main MT.MUN (s + kk) = 1 := by rw [dMUN, huw, e16, hlt]; ring
      obtain ⟨r', k', hr', hk2, hk10, hsm, hv⟩ := node_use hL hsat hHL hsz ht hmun
      obtain ⟨hs0', hsn', hu', hv'⟩ := mt_yield hL hsat hr' hk2 hk10 hsm
      rw [hv'] at hv
      simp only [List.cons.injEq, and_true] at hv
      obtain ⟨eid, ewx, elo, ehi⟩ := hv
      set j' := 2 * j + kk / 8 with hj'
      have hid' : (inst 11).main MT.ID (r' - r' % 88) = (j' : F) := by
        rw [eid, dCK, hidt, e8, hlt, hj']; push_cast
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      have hok := ih (2 * half - j') (by omega) j' rfl (by omega) (by omega) _ hs0' hsn' hu' hid'
      have hwx : MT.widx k' = kk % 8 := natCast_inj_of_lt (by have := MT.widx_lt hk2 hk10; unfold P; omega)
        (by unfold P; omega) (by rw [ewx, ew])
      have hc' : child (kk / 8) = Spec.SetMerkle.node half ((List.range cnt).map lf) j' := by
        simp only [child, if_pos hjh, hj']
      rw [hc', ← elo, ← ehi, hok _ (MT.widx_lt hk2 hk10), hwx]
      exact ⟨rfl, rfl⟩
    · -- a leaf-level node: the child is a slot
      have hlt : (inst 11).main MT.LEAFL (s + kk) = 1 := by rw [pc MT.LEAFL (by simp [MT.perConst]), hl1]
      have hlu : (inst 11).main MT.LU (s + kk) = 1 := by rw [dLU, huw, hlt]; ring
      have hlus : (inst 11).main MT.LU s = 1 := by
        have := (row_defs hL hsat (pub := pub) hs).2.2.1; rw [this, hu, hl1]; ring
      obtain ⟨fl, fr⟩ := slot_flags hL hsat hHL hsz hs hs0 hlus hid hhalf hjh hj h24 hcnt hc
      set sl := 2 * (j - half) + kk / 8 with hsl
      have hrowf : (inst 11).main MT.USEROW (s + kk) = 1 ↔ sl < cnt := by
        rw [dROW, e8, pc MT.USEL (by simp [MT.perConst]), pc MT.USER (by simp [MT.perConst])]
        rcases Nat.lt_or_ge kk 8 with h8 | h8
        · rw [show 1 - kk / 8 = 1 by omega, hsl, show kk / 8 = 0 by omega]
          simp only [Nat.cast_one, one_mul, sub_self, zero_mul, add_zero, add_zero]
          exact fl
        · rw [show 1 - kk / 8 = 0 by omega, hsl, show kk / 8 = 1 by omega]
          simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add]
          exact fr
      have hc' : child (kk / 8) = Spec.SetMerkle.slot ((List.range cnt).map lf) sl := by
        simp only [child, if_neg (show ¬ j < half by omega), hsl]
      rw [hc', MT.slot_map]
      have hck : (inst 11).main MT.CK (s + kk) = (sl : F) := by
        rw [dCK, hidt, e8, hlt, hhalf, hsl]; push_cast
        rw [Nat.cast_sub hjh, Nat.cast_sub (by omega)]; push_cast; ring
      by_cases hsc : sl < cnt
      · rw [if_pos hsc]
        have hro : (inst 11).main MT.USEROW (s + kk) = 1 := hrowf.mpr hsc
        have hmul : (inst 11).main MT.MUL (s + kk) = 1 := by rw [dMUL, hlu, e16, hro]; ring
        obtain ⟨r', k', hr', hk2, hk10, hsm, hv⟩ := leaf_use hL hsat hHL hsz ht hmul
        obtain ⟨s', hs', hv'⟩ := hleaf r' k' hr' hk2 hk10 hsm
        rw [hv'] at hv
        simp only [List.cons.injEq, and_true] at hv
        obtain ⟨eid, ewx, elo, ehi⟩ := hv
        have hss : s' = sl := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) (by rw [eid, hck])
        have hwx : MT.widx k' = kk % 8 := natCast_inj_of_lt (by have := MT.widx_lt hk2 hk10; unfold P; omega)
          (by unfold P; omega) (by rw [ewx, ew])
        rw [← elo, ← ehi, hss, hwx]
        exact ⟨rfl, rfl⟩
      · rw [if_neg hsc]
        have hro : (inst 11).main MT.USEROW (s + kk) = 0 := by
          have hb : (inst 11).main MT.USEROW (s + kk) = 0 ∨ (inst 11).main MT.USEROW (s + kk) = 1 := by
            rw [dROW, e8, pc MT.USEL (by simp [MT.perConst]), pc MT.USER (by simp [MT.perConst])]
            rcases Nat.lt_or_ge kk 8 with h8 | h8
            · rw [show 1 - kk / 8 = 1 by omega]
              simp only [Nat.cast_one, one_mul, sub_self, zero_mul, add_zero]
              exact MT.bool_flag ms (c := MT.USEL) (by simp) hs
            · rw [show 1 - kk / 8 = 0 by omega]
              simp only [Nat.cast_zero, zero_mul, sub_zero, one_mul, zero_add]
              exact MT.bool_flag ms (c := MT.USER) (by simp) hs
          rcases hb with h | h
          · exact h
          · exact absurd (hrowf.mp h) hsc
        have hzw : (inst 11).main MT.ZW (s + kk) = 1 := by rw [dZW, hlu, hro]; ring
        have z := fun (c : ℕ) (hm : Expr.mul (MT.p MT.P_LT16) (.mul (MT.k MT.ZW) (MT.k c)) ∈ MT.flagC) => by
          have := MT.sat ms (MT.mem_flag hm) ht
          simp only [Expr.eval, e16, MT.ev_k (pub := pub) (M := (inst 11).main) ht, hzw, one_mul] at this
          exact this
        rw [z MT.WLO (by simp [MT.flagC]), z MT.WHI (by simp [MT.flagC]), MT.stWord_zero, MT.half16_zero, MT.half16_zero]
        simp
  -- the digest
  have hm : ∀ kk < 16, ∀ h ≤ 1, ((inst 11).main (Blake2s.ML kk h) s).val < 65536 := by
    intro kk hkk h hh
    have v : ∀ x, (((half16 x h : ℕ) : F)).val < 65536 := fun x => by
      rw [ZMod.val_natCast_of_lt (lt_of_lt_of_le (Sha256.half16_lt x h) (by unfold P; norm_num))]
      exact Sha256.half16_lt x h
    interval_cases h
    · rw [(hrow kk hkk).1]; exact v _
    · rw [(hrow kk hkk).2]; exact v _
  have hmsg : ∀ kk < 16, msgWord (inst 11).main kk s =
      (fun k => if k < 8 then stWord (child 0) k else stWord (child 1) (k - 8)) kk := by
    intro kk hkk
    rw [MT.msgWord_halves (hrow kk hkk).1 (hrow kk hkk).2]
    rcases Nat.lt_or_ge kk 8 with h8 | h8
    · simp only [if_pos h8, show kk / 8 = 0 by omega, Nat.mod_eq_of_lt h8]
    · simp only [if_neg (show ¬ kk < 8 by omega), show kk / 8 = 1 by omega, show kk % 8 = kk - 8 by omega]
  have hnode : Spec.SetMerkle.node half ((List.range cnt).map lf) j = hnode (child 0) (child 1) := by
    rw [MT.node_unfold]
    by_cases h : j < half
    · simp only [child, if_pos h, if_pos (And.intro hj1 h), Nat.add_zero]
    · simp only [child, if_neg h, if_neg (show ¬ (1 ≤ j ∧ j < half) by omega), Nat.add_zero]
  intro w hw
  rw [← MT.period_digest ms hs0 hsn hu hm w hw, hnode, Circuit.stWord_hnode _ _ hw]
  exact Spec.Blake2s.compress_congr (fun _ _ => rfl) hmsg _ _ w hw

/-- **The public root is the heap tree's root**: `ROOT`'s limbs are node 1's words' halves. -/
theorem root_ok (h1 : 1 ≤ half) : ∀ i < 16, pub (PUB_ROOT i) =
    ((half16 (stWord (Spec.SetMerkle.node half ((List.range cnt).map lf) 1) (i / 2)) (i % 2) : ℕ) : F) := by
  have hpre : (segSys.comp 11).air.pre = MT.preCols := rfl
  have h0 : 0 < 2 ^ Ls 11 := by positivity
  have hf : (MT.p MT.P_FIRST).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main 0 = 1 := by
    rw [MT.ev_first (pub := pub) (M := (inst 11).main) h0, if_pos rfl]
  intro i hi
  set w := i / 2 with hw
  have hw8 : w < 8 := by omega
  have hl : MT.lookups.getD (10 + w) ⟨0, .const 0, []⟩ = ⟨REL_NODE, .neg (MT.p MT.P_FIRST),
      [cst 1, cst w, .pub (PUB_ROOT (2 * w)), .pub (PUB_ROOT (2 * w + 1))]⟩ := by
    interval_cases w <;> rfl
  have hsl : siteLookup segSys ((11, 0, 10 + w) : Site) = _ := hl
  have hsite := site_mem hL (i := 11) (by decide) h0 (k := 10 + w) (by
    show 10 + w < MT.lookups.length; simp [MT.lookups]; omega)
  have hm : siteMult segSys inst pub (11, 0, 10 + w) = -1 := by
    simp only [siteMult, hsl, siteEval, hpre, hL 11 (by decide), Expr.eval, hf]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hHL hsz hsite (by simp [isUse]) hm
  rw [show siteRel segSys ((11, 0, 10 + w) : Site) = 40 by simp [siteRel, hsl, REL_NODE]] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, hk2, hk10⟩ : i' = 11 ∧ 2 ≤ k' ∧ k' < 10 := by omega
  obtain ⟨hs0', hsn', hu', hv'⟩ := mt_yield hL hsat hr' hk2 hk10 hsm
  have hv0 : siteVals segSys inst pub (11, 0, 10 + w) = [1, (w : F), pub (PUB_ROOT (2 * w)), pub (PUB_ROOT (2 * w + 1))] := by
    simp [siteVals, hsl, siteEval, hpre, hL 11 (by decide), Expr.eval, StarkedAir.Sha256.eval_cst]
  rw [hv', hv0] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨eid, ewx, elo, ehi⟩ := hsv
  have hok := node_ok hL hsat hHL hsz hhalf h24 hcnt hc hleaf (2 * half - 1) 1 rfl le_rfl (by omega) _ hs0' hsn' hu'
    (by rw [eid]; simp)
  have hwx : MT.widx k' = w := natCast_inj_of_lt (by have := MT.widx_lt hk2 hk10; unfold P; omega)
    (by unfold P; omega) ewx
  rw [hok _ (MT.widx_lt hk2 hk10), hwx] at elo ehi
  rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
  · rw [h2, show i = 2 * w by omega, ← elo]
  · rw [h2, show i = 2 * w + 1 by omega, ← ehi]

end Nodes

end StarkedAir.SetPass
