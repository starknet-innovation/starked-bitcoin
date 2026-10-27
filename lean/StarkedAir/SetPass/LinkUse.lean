/-
**The segment system's use multiplicities and `link`.** Every use site has multiplicity `−1` or `0` at
every row (`use_mult`), so with fewer than `P` sites a use with multiplicity `−1` is matched by a yield
(`link`).
-/
import StarkedAir.SetPass.Link

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (col pre cst)
open StarkedAir.Block (neg01 mul01 air_bool)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub [])
include hL hsat

omit hL hsat in
theorem om01 {x : F} (h : x = 0 ∨ x = 1) : 1 - x = 0 ∨ 1 - x = 1 := by rcases h with h | h <;> simp [h]

omit hL hsat in
theorem pre01 {n : ℕ} {pc : List PreCol} {M : ℕ → ℕ → F} {i r : ℕ} {vs : List ℕ}
    (hi : pc.getD i (.periodic [0]) = .periodic vs) (hvs : ∀ v ∈ vs, v ≤ 1) (hr : r < n) :
    (pre i).eval n pc pub M r = 0 ∨ (pre i).eval n pc pub M r = 1 := by
  simp only [pre, Expr.eval, hi, PreCol.eval, wrap_zero hr]
  by_cases h : r % vs.length < vs.length
  · rw [List.getD_eq_getElem _ _ h]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hvs _ (List.getElem_mem h)) with e | e <;> simp [e]
  · rw [List.getD_eq_default _ _ (by omega)]; simp

omit hsat in
/-- The site multiplicity of component `i`'s lookup `k`, as its expression's value. -/
theorem site_mult_eq {i r k : ℕ} (hi : i < 12) :
    siteMult segSys inst pub (i, r, k) =
      ((segSys.comp i).lookups.getD k ⟨0, .const 0, []⟩).mult.eval (2 ^ Ls i) (segSys.comp i).air.pre pub (inst i).main r := by
  simp only [siteMult, siteEval, siteLookup, hL i hi]

omit hL hsat in
theorem rec_cmp_eval {n r : ℕ} {M : ℕ → ℕ → F} (hs : ∀ r < n, ∀ c ∈ Rec.constraints, c.eval n Rec.preCols pub M r = 0)
    (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hr : r < n) :
    Rec.cmp.eval n Rec.preCols pub M r = 0 ∨ Rec.cmp.eval n Rec.preCols pub M r = 1 := by
  have bON := air_bool (air := Rec.rec.air) hs (c := Rec.ON) (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k]) hr
  by_cases h0 : r = 0
  · subst h0
    have := hs 0 hr (.mul Rec.first (Rec.om (Rec.k Rec.ON))) (by simp [Rec.constraints, Rec.localC])
    simp only [Rec.first, Rec.om, Rec.one, Rec.k, pre, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
      Rec.preCols, PreCol.eval, wrap_zero hr, List.getD_cons_zero, if_true, one_mul, Nat.cast_one] at this
    have hon : M Rec.ON 0 = 1 := by linear_combination -this
    simp only [Rec.cmp, Rec.first, Rec.k, pre, Expr.eval, StarkedAir.Sha256.eval_col, Rec.preCols, PreCol.eval,
      wrap_zero hr, List.getD_cons_zero, if_true, hon, one_mul, sub_self, zero_add]
    exact hHL
  · simp only [Rec.cmp, Rec.first, Rec.k, pre, Expr.eval, StarkedAir.Sha256.eval_col, Rec.preCols, PreCol.eval,
      wrap_zero hr, List.getD_cons_zero, h0, if_false, zero_mul, sub_zero, add_zero]
    exact bON

/-- **Every use site has multiplicity `−1` or `0`.** -/
theorem use_mult (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) : ∀ s ∈ sites segSys inst, isUse s.1 s.2.2 = true →
    siteMult segSys inst pub s = -1 ∨ siteMult segSys inst pub s = 0 := by
  rintro ⟨i, r, k⟩ hs hu
  obtain ⟨hi, hr, hk⟩ := (mem_sites hL).mp hs
  simp only at hu
  rw [site_mult_eq hL hi]
  interval_cases i
  · simp [isUse] at hu
  · simp [isUse] at hu
  · simp [isUse] at hu
  · -- records: `−ON`, `−1`, `−cmp`
    have rs := rec_sat hL hsat
    have hk98 : k < 98 := by have h := lookups_len 3 (by decide); rw [h] at hk; simpa using hk
    have hm := rec_mult_cases k hk98 hu
    have e : ((segSys.comp 3).lookups.getD k ⟨0, .const 0, []⟩) = Rec.lookups.getD k ⟨0, .const 0, []⟩ := rfl
    have ep : (segSys.comp 3).air.pre = Rec.preCols := rfl
    rw [e, ep]
    simp only [recUseMults, List.mem_cons, List.not_mem_nil, or_false] at hm
    have bON := air_bool (air := Rec.rec.air) rs (c := Rec.ON) (by simp [Rec.rec, Rec.constraints, Rec.localC, Rec.k]) hr
    rcases hm with h | h | h <;> rw [h]
    · simp only [Expr.eval, Rec.k, StarkedAir.Sha256.eval_col, wrap_zero hr]; exact neg01 bON
    · simp [Expr.eval, Rec.one, StarkedAir.Sha256.eval_cst]
    · simp only [Expr.eval]; exact neg01 (rec_cmp_eval rs hHL hr)
  · -- segment fingerprints: `−ON·(1 − STR)`, `−ON·STR`, `−FST`
    have fw := fpwalk_sat hL hsat
    have hk3 : k < 3 := by simpa [isUse] using hu
    have bON := Block.FpWalk.bool fw (c := Block.FpWalk.ON) (by simp) hr
    have bSTR := Block.FpWalk.bool fw (c := Block.FpWalk.STR) (by simp) hr
    have bFST := Block.FpWalk.bool fw (c := Block.FpWalk.FST) (by simp) hr
    have e : ∀ kk, ((segSys.comp 4).lookups.getD kk ⟨0, .const 0, []⟩) = Block.FpWalk.lookups.getD kk ⟨0, .const 0, []⟩ :=
      fun _ => rfl
    have ep : (segSys.comp 4).air.pre = Block.FpWalk.preCols := rfl
    rw [e, ep]
    interval_cases k <;>
      simp only [Block.FpWalk.lookups, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, Block.FpWalk.k,
        Block.FpWalk.om, Block.FpWalk.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr,
        Nat.cast_one] <;>
      first
        | exact neg01 (mul01 bON (om01 bSTR))
        | exact neg01 (mul01 bON bSTR)
        | exact neg01 bFST
  · -- Blake2s words: `−N`, `−(A − N)`, `−HELD·A`, `−first`
    have ws := b2w_sat hL hsat
    have hk14 : k < 14 := by simpa [segSys, comps, B2w.b2w, B2w.lookups] using hk
    have e : ∀ kk, ((segSys.comp 5).lookups.getD kk ⟨0, .const 0, []⟩) = B2w.lookups.getD kk ⟨0, .const 0, []⟩ :=
      fun _ => rfl
    have ep : (segSys.comp 5).air.pre = B2w.preCols := rfl
    rw [e, ep]
    have bc : ∀ c ∈ B2w.boolCols, (inst 5).main c r = 0 ∨ (inst 5).main c r = 1 := fun c hc =>
      air_bool (air := B2w.b2w.air) ws (c := c) (by
        simp only [B2w.b2w, B2w.constraints, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨c, hc, rfl⟩)))))))) hr
    have bN : ∀ j < 4, (inst 5).main (B2w.N j) r = 0 ∨ (inst 5).main (B2w.N j) r = 1 := fun j hj =>
      bc _ (by simp only [B2w.boolCols, List.mem_append, List.mem_map, List.mem_range]; exact Or.inr ⟨j, hj, rfl⟩)
    have bA : ∀ j < 4, (inst 5).main (B2w.A j) r = 0 ∨ (inst 5).main (B2w.A j) r = 1 := fun j hj =>
      bc _ (by simp only [B2w.boolCols, List.mem_append, List.mem_map, List.mem_range]; exact Or.inl (Or.inr ⟨j, hj, rfl⟩))
    have bH : (inst 5).main B2w.HELD r = 0 ∨ (inst 5).main B2w.HELD r = 1 := bc _ (by simp [B2w.boolCols])
    have bAN : ∀ j < 4, (inst 5).main (B2w.A j) r - (inst 5).main (B2w.N j) r = 0 ∨
        (inst 5).main (B2w.A j) r - (inst 5).main (B2w.N j) r = 1 := by
      intro j hj
      have := ws r hr (.mul (B2w.k (B2w.N j)) (B2w.om (B2w.k (B2w.A j)))) (by
        simp only [B2w.constraints, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inr ⟨j, hj, rfl⟩))
      simp only [Expr.eval, B2w.k, B2w.om, B2w.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
        wrap_zero hr, Nat.cast_one] at this
      rcases bN j hj with h | h <;> rcases bA j hj with g | g <;> simp_all
    have bF : (B2w.first).eval (2 ^ Ls 5) B2w.preCols pub (inst 5).main r = 0 ∨
        (B2w.first).eval (2 ^ Ls 5) B2w.preCols pub (inst 5).main r = 1 := by
      simp only [B2w.first, B2w.p, pre, Expr.eval, B2w.preCols, B2w.P_FIRST, PreCol.eval, wrap_zero hr,
        List.getD_cons_zero]
      split_ifs <;> simp
    have hu' : k ≠ 12 := by simpa [isUse] using hu
    interval_cases k
    all_goals first
      | (exfalso; exact hu' rfl)
      | (simp only [B2w.lookups, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
          List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, B2w.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr]
         first
          | exact neg01 (bN 0 (by norm_num)) | exact neg01 (bN 1 (by norm_num)) | exact neg01 (bN 2 (by norm_num))
          | exact neg01 (bN 3 (by norm_num)) | exact neg01 (bAN 0 (by norm_num)) | exact neg01 (bAN 1 (by norm_num))
          | exact neg01 (bAN 2 (by norm_num)) | exact neg01 (bAN 3 (by norm_num))
          | exact neg01 (mul01 bH (bA 0 (by norm_num))) | exact neg01 (mul01 bH (bA 1 (by norm_num)))
          | exact neg01 (mul01 bH (bA 2 (by norm_num))) | exact neg01 (mul01 bH (bA 3 (by norm_num)))
          | exact neg01 bF)
  · -- Blake2s compressions: `−MU`
    have cs := b2c_sat hL hsat
    have hk0 : k = 0 := by simpa [isUse] using hu
    subst hk0
    have e : ((segSys.comp 6).lookups.getD 0 ⟨0, .const 0, []⟩) = B2c.lookups.getD 0 ⟨0, .const 0, []⟩ := rfl
    have ep : (segSys.comp 6).air.pre = B2c.preCols := rfl
    rw [e, ep]
    have hmem : ∀ c ∈ B2c.flagC, c ∈ B2c.constraints := fun c hc =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_left _ (List.mem_append_right _ hc)))))
    have bNIL := air_bool (air := B2c.b2c.air) cs (c := B2c.NIL) (hmem _ (by
      simp only [B2c.flagC, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨B2c.NIL, by simp, rfl⟩))) hr
    have dUSEW := cs r hr _ (hmem (.sub (B2c.k B2c.USEW) (B2c.om (B2c.k B2c.NIL))) (by simp [B2c.flagC]))
    have dMU := cs r hr _ (hmem (.sub (B2c.k B2c.MU) (.mul (B2c.k B2c.USEW) (B2c.p B2c.P_LT16))) (by simp [B2c.flagC]))
    have bLT := pre01 (pub := pub) (pc := B2c.preCols) (M := (inst 6).main) (i := B2c.P_LT16)
      (vs := (List.range 88).map fun r => if r < 16 then 1 else 0) (by simp [B2c.preCols, B2c.P_LT16, Blake2s.preCols, Block.B2s.per88, Blake2s.PERIOD])
      (fun v hv => by simp only [List.mem_map, List.mem_range] at hv; obtain ⟨q, -, rfl⟩ := hv; split_ifs <;> omega) hr
    simp only [B2c.k, B2c.om, B2c.one, B2c.p, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
      wrap_zero hr, Nat.cast_one, sub_eq_zero] at dUSEW dMU
    simp only [B2c.lookups, List.getD_cons_zero, Expr.eval, B2c.k, StarkedAir.Sha256.eval_col, wrap_zero hr, dMU, dUSEW]
    exact neg01 (mul01 (om01 bNIL) bLT)
  · -- the `TxOutSer` stream: `−PND`, `−P0`, `−PC`, `−PS`, `−NEW`, `−TAIL`, `−first`
    have ts := tmsg_sat hL hsat
    have hk8 : k < 8 := by simpa [segSys, comps, TMsg.tmsg, TMsg.lookups] using hk
    have hu' : k ≠ 6 := by simpa [isUse] using hu
    have e : ∀ kk, ((segSys.comp 7).lookups.getD kk ⟨0, .const 0, []⟩) = TMsg.lookups.getD kk ⟨0, .const 0, []⟩ :=
      fun _ => rfl
    have ep : (segSys.comp 7).air.pre = TMsg.preCols := rfl
    rw [e, ep]
    have bc : ∀ c ∈ [TMsg.ON, TMsg.PND, TMsg.P0, TMsg.PC, TMsg.PS, TMsg.NEW, TMsg.ENDR, TMsg.TAIL],
        (inst 7).main c r = 0 ∨ (inst 7).main c r = 1 := fun c hc =>
      air_bool (air := TMsg.tmsg.air) ts (c := c) (by
        simp only [TMsg.tmsg, TMsg.constraints, List.mem_append, List.mem_map]
        exact Or.inl ⟨c, hc, rfl⟩) hr
    have bF : (TMsg.first).eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main r = 0 ∨
        (TMsg.first).eval (2 ^ Ls 7) TMsg.preCols pub (inst 7).main r = 1 := by
      simp only [TMsg.first, TMsg.p, pre, Expr.eval, TMsg.preCols, TMsg.P_FIRST, PreCol.eval, wrap_zero hr,
        List.getD_cons_zero]
      split_ifs <;> simp
    interval_cases k
    all_goals first
      | (exfalso; exact hu' rfl)
      | (simp only [TMsg.lookups, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, TMsg.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr]
         first
          | exact neg01 (bc TMsg.PND (by simp)) | exact neg01 (bc TMsg.P0 (by simp))
          | exact neg01 (bc TMsg.PC (by simp)) | exact neg01 (bc TMsg.PS (by simp))
          | exact neg01 (bc TMsg.NEW (by simp)) | exact neg01 (bc TMsg.TAIL (by simp))
          | exact neg01 bF)
  · -- SHA-256 compressions: `−MSGROW·USEW`
    have cs := shac_sat hL hsat
    have hk0 : k = 0 := by simpa [isUse] using hu
    subst hk0
    have e : ((segSys.comp 8).lookups.getD 0 ⟨0, .const 0, []⟩) = ShaC.lookups.getD 0 ⟨0, .const 0, []⟩ := rfl
    have ep : (segSys.comp 8).air.pre = ShaC.preCols := rfl
    rw [e, ep]
    have hmem : ∀ c ∈ ShaC.flagC, c ∈ ShaC.constraints := fun c hc =>
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hc)))
    have bNIL := air_bool (air := ShaC.shac.air) cs (c := ShaC.NIL) (hmem _ (by simp [ShaC.flagC, ShaC.k])) hr
    have dUSEW := cs r hr _ (hmem (.sub (ShaC.k ShaC.USEW) (ShaC.om (ShaC.k ShaC.NIL))) (by simp [ShaC.flagC]))
    have bMR := pre01 (pub := pub) (pc := ShaC.preCols) (M := (inst 8).main) (i := ShaC.MSGROW)
      (vs := (List.range 72).map fun q => if 4 ≤ q ∧ q < 20 then 1 else 0) (by simp [ShaC.preCols, ShaC.MSGROW, Sha256.preCols, Block.Sha.per72, Sha256.PERIOD])
      (fun v hv => by simp only [List.mem_map, List.mem_range] at hv; obtain ⟨q, -, rfl⟩ := hv; split_ifs <;> omega) hr
    simp only [ShaC.k, ShaC.om, ShaC.one, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
      wrap_zero hr, Nat.cast_one, sub_eq_zero] at dUSEW
    simp only [ShaC.lookups, List.getD_cons_zero, Expr.eval, ShaC.k, StarkedAir.Sha256.eval_col, wrap_zero hr, dUSEW]
    exact neg01 (mul01 bMR (om01 bNIL))
  · -- leaf words: `−PKU`, `−NEWR`, `−A j·(1 − PKU)`
    have ws := lw_sat hL hsat
    have hk6 : k < 6 := by simpa [isUse] using hu
    have e : ∀ kk, ((segSys.comp 9).lookups.getD kk ⟨0, .const 0, []⟩) = LW.lookups.getD kk ⟨0, .const 0, []⟩ :=
      fun _ => rfl
    have ep : (segSys.comp 9).air.pre = LW.preCols := rfl
    rw [e, ep]
    have bc : ∀ c ∈ LW.boolCols, (inst 9).main c r = 0 ∨ (inst 9).main c r = 1 := fun c hc =>
      air_bool (air := LW.lw.air) ws (c := c) (by
        simp only [LW.lw, LW.constraints, List.mem_append, List.mem_map]
        exact Or.inl (Or.inl (Or.inl (Or.inl ⟨c, hc, rfl⟩)))) hr
    interval_cases k <;>
      simp only [LW.lookups, List.range_succ, List.range_zero, List.map_cons, List.map_nil, List.nil_append,
        List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, LW.k, LW.om, LW.one,
        StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr, Nat.cast_one] <;>
      first
        | exact neg01 (bc LW.PKU (by simp [LW.boolCols])) | exact neg01 (bc LW.NEWR (by simp [LW.boolCols]))
        | exact neg01 (mul01 (bc (LW.A 0) (by simp [LW.boolCols])) (om01 (bc LW.PKU (by simp [LW.boolCols]))))
        | exact neg01 (mul01 (bc (LW.A 1) (by simp [LW.boolCols])) (om01 (bc LW.PKU (by simp [LW.boolCols]))))
        | exact neg01 (mul01 (bc (LW.A 2) (by simp [LW.boolCols])) (om01 (bc LW.PKU (by simp [LW.boolCols]))))
        | exact neg01 (mul01 (bc (LW.A 3) (by simp [LW.boolCols])) (om01 (bc LW.PKU (by simp [LW.boolCols]))))
  · -- leaf compressions: `−MU0`, `−MU1`
    have cs := lc_sat hL hsat
    have hk2 : k < 2 := by simpa [isUse] using hu
    have e : ∀ kk, ((segSys.comp 10).lookups.getD kk ⟨0, .const 0, []⟩) = LC.lookups.getD kk ⟨0, .const 0, []⟩ :=
      fun _ => rfl
    have ep : (segSys.comp 10).air.pre = LC.preCols := rfl
    rw [e, ep]
    have hb : ∀ c ∈ [LC.FST, LC.NIL, LC.LASTF, LC.MU0, LC.MU1], (inst 10).main c r = 0 ∨ (inst 10).main c r = 1 :=
      fun c hc => air_bool (air := LC.lc.air) cs (c := c)
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (by
            simp only [LC.flagC, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩))))))) hr
    interval_cases k <;>
      simp only [LC.lookups, List.cons_append, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, LC.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr] <;>
      first | exact neg01 (hb LC.MU0 (by simp)) | exact neg01 (hb LC.MU1 (by simp))
  · -- tree nodes: `−MUN`, `−MUL`, `−first` (the root), range reads `−USEW·R0`, `−LU·R0`, `−first`
    have cs := mt_sat hL hsat
    have e : ∀ kk, ((segSys.comp 11).lookups.getD kk ⟨0, .const 0, []⟩) = MT.lookups.getD kk ⟨0, .const 0, []⟩ :=
      fun _ => rfl
    have ep : (segSys.comp 11).air.pre = MT.preCols := rfl
    rw [e, ep]
    have hk30 : k < 30 := by simpa [segSys, comps, MT.mt, MT.lookups] using hk
    have hb : ∀ c ∈ [MT.NIL, MT.LEAFL, MT.USEL, MT.USER, MT.USEW, MT.LU, MT.MUN, MT.MUL],
        (inst 11).main c r = 0 ∨ (inst 11).main c r = 1 :=
      fun c hc => air_bool (air := MT.mt.air) cs (c := c)
        (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
          (List.mem_append_right _ (by
            simp only [MT.flagC, List.mem_append, List.mem_map]; exact Or.inl (Or.inl ⟨c, hc, rfl⟩)))))) hr
    have bR0 := pre01 (pub := pub) (pc := MT.preCols) (M := (inst 11).main) (i := MT.P_R0)
      (vs := (List.range 88).map fun r => if r = 0 then 1 else 0)
      (by simp [MT.preCols, MT.P_R0, Blake2s.preCols, Block.B2s.per88, Blake2s.PERIOD])
      (fun v hv => by simp only [List.mem_map, List.mem_range] at hv; obtain ⟨q, -, rfl⟩ := hv; split_ifs <;> omega) hr
    have bF : (pre MT.P_FIRST).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r = 0 ∨
        (pre MT.P_FIRST).eval (2 ^ Ls 11) MT.preCols pub (inst 11).main r = 1 := by
      have hg : MT.preCols.getD MT.P_FIRST (.periodic [0]) = .isFirst := by
        simp [MT.preCols, MT.P_FIRST, Blake2s.preCols, List.getD_eq_getElem?_getD]
      simp only [pre, Expr.eval, hg, PreCol.eval, wrap_zero hr]
      split_ifs <;> simp
    interval_cases k
    all_goals first
      | (simp [isUse] at hu; done)
      | (simp only [MT.lookups, MT.r8, List.range_succ, List.range_zero, List.map_cons, List.map_nil,
          List.flatMap_cons, List.flatMap_nil, List.nil_append, List.cons_append, List.append_nil,
          List.getD_cons_zero, List.getD_cons_succ, Expr.eval, MT.k, MT.p, StarkedAir.Sha256.eval_col, wrap_zero hr]
         first
          | exact neg01 (hb MT.MUN (by simp)) | exact neg01 (hb MT.MUL (by simp)) | exact neg01 bF
          | exact neg01 (mul01 (hb MT.USEW (by simp)) bR0) | exact neg01 (mul01 (hb MT.LU (by simp)) bR0))

/-- **A use is matched by a yield.** -/
theorem linked (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls) {s0 : Site}
    (hs0 : s0 ∈ sites segSys inst) (hu : isUse s0.1 s0.2.2 = true) (hm : siteMult segSys inst pub s0 = -1) :
    ∃ s ∈ sites segSys inst, isUse s.1 s.2.2 = false ∧ siteMult segSys inst pub s ≠ 0 ∧
      siteRel segSys s = siteRel segSys s0 ∧ siteVals segSys inst pub s = siteVals segSys inst pub s0 := by
  classical
  obtain ⟨s, hs, hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2 (use := fun i k => isUse i k = true)
    (use_mult hL hsat hHL) (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide (isUse s.1 s.2.2 = true)) (sites segSys inst)
      rw [sites_len hL] at this
      have := hsz.2
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨s0, hs0, hu, hm, rfl, rfl⟩)
  exact ⟨s, hs, by simpa using hnu, hsm, hsr, hsv⟩

omit hsat in
theorem yield_of {i r k : ℕ} (hs : ((i, r, k) : Site) ∈ sites segSys inst) (hnu : isUse i k = false) :
    (i, k, siteRel segSys (i, r, k)) ∈ yieldTable := by
  obtain ⟨hi, -, hk⟩ := (mem_sites hL).mp hs
  exact yield_table i hi k hk hnu

/-- The yield sites, as a test. -/
def YT (i k R : ℕ) : Bool :=
    (i == 0 && k == 0 && R == 3) || (i == 1 && k == 0 && R == 9) || (i == 1 && k == 1 && R == 10) || (i == 2 && k == 0 && R == 26) ||
    (i == 2 && k == 1 && R == 27) || (i == 2 && k == 2 && R == 28) || (i == 2 && k == 3 && R == 29) || (i == 3 && k == 57 && R == 32) ||
    (i == 3 && k == 58 && R == 33) || (i == 3 && k == 59 && R == 33) || (i == 3 && k == 60 && R == 33) || (i == 3 && k == 61 && R == 33) ||
    (i == 3 && k == 62 && R == 21) || (i == 4 && k == 3 && R == 22) || (i == 5 && k == 12 && R == 30) || (i == 6 && k == 1 && R == 31) ||
    (i == 7 && k == 6 && R == 34) || (i == 8 && k == 1 && R == 35) || (i == 3 && decide (89 ≤ k) && decide (k < 98) && R == 36) ||
    (i == 9 && k == 6 && R == 37) || (i == 9 && k == 7 && R == 38) || (i == 10 && decide (2 ≤ k) && decide (k < 10) && R == 39) ||
    (i == 11 && decide (2 ≤ k) && decide (k < 10) && R == 40)

omit hL hsat in
set_option maxRecDepth 20000 in
theorem yt_all : yieldTable.all (fun t => YT t.1 t.2.1 t.2.2) = true := by decide

omit hL hsat in
theorem yt {i k R : ℕ} (h : (i, k, R) ∈ yieldTable) : YT i k R = true :=
  (List.all_eq_true.mp yt_all) (i, k, R) h

/-- **Linking a use to its yield, by relation.** -/
theorem link (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls) {i0 r0 k0 : ℕ}
    (hs0 : ((i0, r0, k0) : Site) ∈ sites segSys inst) (hu : isUse i0 k0 = true)
    (hm : siteMult segSys inst pub (i0, r0, k0) = -1) :
    ∃ i r' k, r' < 2 ^ Ls i ∧ (i, k, siteRel segSys (i0, r0, k0)) ∈ yieldTable ∧
      siteMult segSys inst pub (i, r', k) ≠ 0 ∧
      siteVals segSys inst pub (i, r', k) = siteVals segSys inst pub (i0, r0, k0) := by
  obtain ⟨⟨i, r', k⟩, hs, hnu, hsm, hsr, hsv⟩ := linked hL hsat hHL hsz hs0 hu hm
  refine ⟨i, r', k, ((mem_sites hL).mp hs).2.1, ?_, hsm, hsv⟩
  rw [← hsr]; exact yield_of hL hs hnu

omit hsat in
theorem site_mem {i r k : ℕ} (hi : i < 12) (hr : r < 2 ^ Ls i) (hk : k < (segSys.comp i).lookups.length) :
    ((i, r, k) : Site) ∈ sites segSys inst := (mem_sites hL).mpr ⟨hi, hr, hk⟩

omit hsat in
theorem rows_lt_P (hsz : SegSizeOk Ls) {i : ℕ} (hi : i < 12) : 2 ^ Ls i < P := by
  have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (hsz.1 i hi)
  unfold P; omega

/-- **Byte reads are the segment's bytes.** A use of the byte relation with multiplicity `−1` reads
`(q, byte q)` with `q` below the segment length. -/
theorem byte_read (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls) {i r k : ℕ}
    (hs0 : ((i, r, k) : Site) ∈ sites segSys inst) (hu : isUse i k = true)
    (hrel : siteRel segSys (i, r, k) = Block.REL_BYTE) (hm : siteMult segSys inst pub (i, r, k) = -1) {p b : F}
    (hv : siteVals segSys inst pub (i, r, k) = [p, b]) :
    ∃ q, q < (pub PUB_LEN).val ∧ p = (q : F) ∧ b = (inst 0).main Block.BYTE q := by
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hHL hsz hs0 hu hm
  rw [hrel, show Block.REL_BYTE = 3 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i' = 0 ∧ k' = 0 := by omega
  have hb0 := bytes_sat hL hsat
  have hP : 2 ^ Ls 0 < P := rows_lt_P hL hsz (by decide)
  have hm' : (Expr.mul (StarkedAir.Sha256.col Block.ACTIVE) (StarkedAir.Sha256.col Block.MULT)).eval (2 ^ Ls 0)
      Block.preCols pub (inst 0).main r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, segSys, comps, hL 0 (by decide), Block.bytes] using hsm
  obtain ⟨hlt, hvals⟩ := Block.yield_sound hb0 hP hr' hm'
  have e : siteVals segSys inst pub (0, r', 0) = [(r' : F), (inst 0).main Block.BYTE r'] := by
    simpa [siteVals, siteEval, siteLookup, segSys, comps, hL 0 (by decide), Block.bytes] using hvals
  rw [e, hv] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨r', hlt, hsv.1.symm, hsv.2.symm⟩

/-- **Range reads are bytes.** -/
theorem r8_read (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls) {i r k : ℕ}
    (hs0 : ((i, r, k) : Site) ∈ sites segSys inst) (hu : isUse i k = true)
    (hrel : siteRel segSys (i, r, k) = Block.Tables.REL_R8) (hm : siteMult segSys inst pub (i, r, k) = -1) {v : F}
    (hv : siteVals segSys inst pub (i, r, k) = [v]) : v.val < 256 := by
  obtain ⟨i', r', k', hr', hy, -, hsv⟩ := link hL hsat hHL hsz hs0 hu hm
  rw [hrel, show Block.Tables.REL_R8 = 9 from rfl] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i' = 1 ∧ k' = 0 := by omega
  have e : siteVals segSys inst pub (1, r', 0) = [((r' % 256 : ℕ) : F)] := by
    simp [siteVals, siteEval, siteLookup, segSys, comps, hL 1 (by decide), Block.Tables.tables, Expr.eval,
      Block.Tables.preCols, Block.Tables.tab, PreCol.eval, wrap_zero hr', pre,
      List.getElem?_range (Nat.mod_lt r' (by norm_num : 0 < 256))]
  rw [e, hv] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  rw [← hsv, ZMod.val_natCast_of_lt (by unfold P; omega)]
  omega

omit hL hsat in
theorem eval_foldl_add {n : ℕ} {pc : List PreCol} {M : ℕ → ℕ → F} {r : ℕ} (f : ℕ → Expr) :
    ∀ (l : List ℕ) (a : Expr), (l.foldl (fun acc k => Expr.add acc (f k)) a).eval n pc pub M r =
      a.eval n pc pub M r + (l.map fun k => (f k).eval n pc pub M r).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, eval_foldl_add f l, List.map_cons, List.sum_cons]
    simp only [Expr.eval]; ring

omit hL hsat in
/-- A pending table's byte column is the public byte at the row's index. -/
theorem pubByte_eval {n r base : ℕ} {M : ℕ → ℕ → F} (hr : r < n) :
    (Pend.pubByte base).eval n Pend.preCols pub M r = pub (H_PEND base (r % 64)) := by
  have hsel : ∀ k ∈ List.range 64, (Expr.mul (pre (Pend.P_S k)) (.pub (H_PEND base k))).eval n Pend.preCols pub M r =
      if r % 64 = k then pub (H_PEND base k) else 0 := by
    intro k hk
    rw [List.mem_range] at hk
    have hg : Pend.preCols.getD (Pend.P_S k) (.periodic [0]) = Pend.per64 fun r => if r = k then 1 else 0 := by
      rw [Pend.P_S, show 1 + k = k + 1 by ring]
      simp [Pend.preCols, List.getD_eq_getElem?_getD, hk]
    simp only [Expr.eval, pre, hg, Pend.per64, PreCol.eval, wrap_zero hr, List.length_map, List.length_range,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.mod_lt r (by norm_num : 0 < 64)),
      Option.map_some, Option.getD_some]
    split_ifs <;> simp
  rw [Pend.pubByte, eval_foldl_add, List.map_congr_left hsel]
  simp only [Expr.eval, StarkedAir.Sha256.eval_cst, Nat.cast_zero, zero_add]
  rw [← List.sum_toFinset _ List.nodup_range]
  · simp [Finset.sum_ite_eq, Nat.mod_lt r (by norm_num : 0 < 64)]

/-- **Pending reads are the public pending bytes.** A use of pending table `j` (relation `26 + j`) with
multiplicity `−1` reads `(q, pub (H_PEND base q))` with `q < 64`, `base` the table's state block. -/
theorem pend_read (hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1) (hsz : SegSizeOk Ls) {i r k j : ℕ}
    (hj : j < 4) (hs0 : ((i, r, k) : Site) ∈ sites segSys inst) (hu : isUse i k = true)
    (hrel : siteRel segSys (i, r, k) = 26 + j) (hm : siteMult segSys inst pub (i, r, k) = -1) {p b : F}
    (hv : siteVals segSys inst pub (i, r, k) = [p, b]) :
    ∃ q : ℕ, q < 64 ∧ p = (q : F) ∧ b = pub (H_PEND ([B2_IN, B2_OUT, SHA_IN, SHA_OUT].getD j 0) q) := by
  obtain ⟨i', r', k', hr', hy, -, hsv⟩ := link hL hsat hHL hsz hs0 hu hm
  rw [hrel] at hy
  replace hy := yt hy; simp only [YT, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hy
  obtain ⟨rfl, rfl⟩ : i' = 2 ∧ j = k' := by omega
  have e : siteVals segSys inst pub (2, r', j) =
      [((r' % 64 : ℕ) : F), pub (H_PEND ([B2_IN, B2_OUT, SHA_IN, SHA_OUT].getD j 0) (r' % 64))] := by
    have hl : siteLookup segSys ((2, r', j) : Site) = ⟨[REL_PB2I, REL_PB2O, REL_PSHI, REL_PSHO].getD j 0,
        Sha256.col j, [pre Pend.P_J, Pend.pubByte ([B2_IN, B2_OUT, SHA_IN, SHA_OUT].getD j 0)]⟩ := by
      interval_cases j <;> rfl
    have hpre : (segSys.comp 2).air.pre = Pend.preCols := rfl
    simp only [siteVals, hl, siteEval, hpre, hL 2 (by decide), List.map_cons, List.map_nil, pubByte_eval hr']
    congr 1
    have hg : Pend.preCols.getD Pend.P_J (.periodic [0]) = Pend.per64 id := rfl
    simp only [Expr.eval, pre, hg, Pend.per64, PreCol.eval, wrap_zero hr', List.length_map, List.length_range,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Nat.mod_lt r' (by norm_num : 0 < 64)),
      Option.map_some, Option.getD_some, id]
  rw [e, hv] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨r' % 64, Nat.mod_lt _ (by norm_num), hsv.1.symm, hsv.2.symm⟩

end System

end StarkedAir.SetPass
