/-
**The block hashing system (M3a.3, linking).** Components, in the prover's order: bytes (0), fields (1),
messages (2), SHA (3), all at one `log_size`. This file links their lookups: SHA's message words and
padded lengths come from the message component, whose bytes come from the byte table.
-/
import StarkedAir.Block.MsgSound
import StarkedAir.Block.ShaSound
import StarkedAir.Block.TxIndex
import StarkedAir.Block.MerkleSound
import StarkedAir.Block.WMerkleSound
import StarkedAir.Block.FieldsChk
import StarkedAir.Block.B2s

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

/-- The block system (M3a.5–6): bytes, fields, messages, SHA, txid tree, tables, sigop walker, context, witness
tree, undo bytes, Blake2s message words, Blake2s. -/
def hashSys : System :=
  ⟨12, fun i => if i = 0 then bytes else if i = 1 then Fields.fields else if i = 2 then Msg.msg else if i = 3 then Sha.sha
    else if i = 4 then Merkle.merkle else if i = 5 then Tables.tables else if i = 6 then Walk.walk
    else if i = 7 then Ctx.ctx else if i = 8 then WMerkle.wmerkle else if i = 9 then Undo.undo
    else if i = 10 then B2Msg.b2msg else B2s.b2s⟩

/-- Use sites `(component, lookup)`: multiplicity `−1` or `0` at every row. All other sites yield. -/
def isUse : ℕ → ℕ → Bool
  | 1, k => !(k == 7 || k == 30 || k == 31 || k == 33)
  | 2, k => decide (k < 2)
  | 3, k => k != 2
  | 4, k => decide (2 ≤ k)
  | 6, k => decide (k < 4)
  | 7, k => !(k == 6 || k == 7 || k == 8)
  | 10, k => decide (k < 8)
  | 11, k => decide (k < 3)
  | _, _ => false

def relAt (i k : ℕ) : ℕ := ((hashSys.comp i).lookups.getD k ⟨0, .const 0, []⟩).rel

/-- The yield sites and their relations. -/
def yieldTable : List (ℕ × ℕ × ℕ) :=
  [(0, 0, REL_BYTE), (1, 7, Fields.REL_TX), (1, 30, Fields.REL_SCRIPT), (1, 31, Fields.REL_TOT),
   (1, 33, Fields.REL_COMMIT), (2, 2, Msg.REL_MSGW), (2, 3, Msg.REL_MLEN), (3, 2, Sha.REL_DIGEST),
   (4, 0, Sha.REL_NODE), (4, 1, Msg.REL_MLEN), (5, 0, Tables.REL_R8), (5, 1, Tables.REL_OPC),
   (6, 4, Walk.REL_SIGOPS), (7, 6, Fields.REL_CTX), (7, 7, Sha.REL_DIGEST), (7, 8, Sha.REL_DIGEST),
   (8, 0, Sha.REL_NODE), (8, 1, Msg.REL_MLEN), (8, 2, Ctx.REL_WCID), (9, 0, Undo.REL_UBYTE),
   (10, 8, B2Msg.REL_B2W), (10, 9, B2Msg.REL_B2B), (11, 3, B2s.REL_B2D), (11, 4, B2s.REL_B2D), (11, 5, B2s.REL_B2D),
   (11, 6, B2s.REL_B2D), (11, 7, B2s.REL_B2D), (11, 8, B2s.REL_B2D), (11, 9, B2s.REL_B2D), (11, 10, B2s.REL_B2D)]

def yieldOK : Bool :=
  (List.range 12).all fun i => (List.range (hashSys.comp i).lookups.length).all fun k =>
    isUse i k || yieldTable.contains (i, k, relAt i k)

theorem yieldOK_true : yieldOK = true := by decide

theorem yield_table : ∀ i < 12, ∀ k < (hashSys.comp i).lookups.length, isUse i k = false →
    (i, k, relAt i k) ∈ yieldTable := by
  intro i hi k hk hu
  have h := yieldOK_true
  simp only [yieldOK, List.all_eq_true, List.mem_range] at h
  have := h i hi k hk
  simp only [hu, Bool.false_or, List.contains_iff_mem] at this
  exact this

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 12, (inst i).logSize = L) (hL24 : L ≤ 24)
  (hsat : hashSys.SatisfiedExt inst pub [])
include hL hsat

theorem hash_bytes_sat : bytes.air.Satisfied L pub (inst 0).main := by
  have := hsat.1 0 (by decide); rw [hL 0 (by decide)] at this; exact this

theorem hash_fields_sat : Fields.fields.air.Satisfied L pub (inst 1).main := by
  have := hsat.1 1 (by decide); rw [hL 1 (by decide)] at this; exact this

theorem hash_msg_sat : ∀ r < 2 ^ L, ∀ c ∈ Msg.constraints, c.eval (2 ^ L) Msg.preCols pub (inst 2).main r = 0 := by
  have := hsat.1 2 (by decide); rw [hL 2 (by decide)] at this; exact this

theorem hash_sha_sat : ∀ r < 2 ^ L, ∀ c ∈ Sha.constraints, c.eval (2 ^ L) Sha.preCols pub (inst 3).main r = 0 := by
  have := hsat.1 3 (by decide); rw [hL 3 (by decide)] at this; exact this

theorem hash_merkle_sat :
    ∀ r < 2 ^ L, ∀ c ∈ Merkle.constraints, c.eval (2 ^ L) Merkle.preCols pub (inst 4).main r = 0 := by
  have := hsat.1 4 (by decide); rw [hL 4 (by decide)] at this; exact this

theorem hash_tables_sat : Tables.tables.air.Satisfied L pub (inst 5).main := by
  have := hsat.1 5 (by decide); rw [hL 5 (by decide)] at this; exact this

theorem hash_walk_sat : Walk.walk.air.Satisfied L pub (inst 6).main := by
  have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this

theorem hash_ctx_sat : Ctx.ctx.air.Satisfied L pub (inst 7).main := by
  have := hsat.1 7 (by decide); rw [hL 7 (by decide)] at this; exact this

theorem hash_wmerkle_sat : WMerkle.wmerkle.air.Satisfied L pub (inst 8).main := by
  have := hsat.1 8 (by decide); rw [hL 8 (by decide)] at this; exact this

theorem hash_undo_sat : ∀ r < 2 ^ L, ∀ c ∈ Undo.constraints, c.eval (2 ^ L) preCols pub (inst 9).main r = 0 := by
  have := hsat.1 9 (by decide); rw [hL 9 (by decide)] at this; exact this

theorem hash_b2msg_sat : ∀ r < 2 ^ L, ∀ c ∈ B2Msg.constraints, c.eval (2 ^ L) B2Msg.preCols pub (inst 10).main r = 0 := by
  have := hsat.1 10 (by decide); rw [hL 10 (by decide)] at this; exact this

theorem hash_b2s_sat : ∀ r < 2 ^ L, ∀ c ∈ B2s.constraints, c.eval (2 ^ L) B2s.preCols pub (inst 11).main r = 0 := by
  have := hsat.1 11 (by decide); rw [hL 11 (by decide)] at this; exact this

omit hsat in
theorem mem_sites {i r k : ℕ} : ((i, r, k) : Site) ∈ sites hashSys inst ↔
    i < 12 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
  simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  constructor
  · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
    exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
  · rintro ⟨hi, hr', hk'⟩
    exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩

omit hsat in
/-- 100 lookup sites per row: bytes 1, fields 34, messages 4, SHA 6, txid tree 11, tables 2, walker 5,
context 12, witness tree 3, undo bytes 1, Blake2s words 10, Blake2s 11. -/
theorem hash_sites_len : (sites hashSys inst).length = 100 * 2 ^ L := by
  simp [sites, hashSys, hL 0 (by decide), hL 1 (by decide), hL 2 (by decide), hL 3 (by decide), hL 4 (by decide),
    hL 5 (by decide), hL 6 (by decide), hL 7 (by decide), hL 8 (by decide), hL 9 (by decide), hL 10 (by decide),
    hL 11 (by decide),
    List.length_flatMap, bytes, Fields.fields, Fields.lookups, Fields.chkLookups, Msg.msg, Msg.lookups, Sha.sha,
    Sha.lookups, Merkle.merkle, Merkle.lookups, Tables.tables, Walk.walk, Walk.lookups, Ctx.ctx, Ctx.lookups,
    WMerkle.wmerkle, WMerkle.lookups, Undo.undo, B2Msg.b2msg, B2Msg.lookups, B2s.b2s, B2s.lookups, List.sum_range_succ]
  ring

omit hL hsat in
theorem hash_rows_lt_P (hL24 : L ≤ 24) : 100 * 2 ^ L < P :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_right (by norm_num) hL24)) (by unfold P; norm_num)

/-- SHA's word and length uses have multiplicity `−1` or `0`. -/
theorem sha_use_mult {r : ℕ} (hr : r < 2 ^ L) {kk : ℕ} (hk : kk < 2) :
    ((Sha.lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Sha.preCols pub (inst 3).main r = -1 ∨
     (Sha.lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Sha.preCols pub (inst 3).main r = 0) := by
  have hs := hash_sha_sat hL hsat
  have hd := Sha.fbool hs (c := Sha.DBL) (by simp) hr
  have hn := Sha.fbool hs (c := Sha.NILS) (by simp) hr
  have hx := (Sha.flags_excl hs hr).2.2
  have hu := Sha.usew_eq hs hr
  have hb : ∀ {x : F}, x = 0 ∨ x = 1 → -x = -1 ∨ -x = 0 := fun h => by rcases h with h | h <;> simp [h]
  have hpre : ∀ {f : ℕ → ℕ} {i : ℕ}, Sha.preCols.getD i (.periodic [0]) = Sha.per72 f → (∀ q, f q ≤ 1) →
      (pre i).eval (2 ^ L) Sha.preCols pub (inst 3).main r = 0 ∨ (pre i).eval (2 ^ L) Sha.preCols pub (inst 3).main r = 1 :=
    fun hi hf => by
      rw [Sha.eval_per72 hs hi hr]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hf (r % 72)) with h | h <;> simp [h]
  interval_cases kk
  · refine hb ?_
    simp only [Sha.lookups, List.getD_cons_zero, Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
    rcases hpre (i := Sha.MSGROW) (f := fun q => if 4 ≤ q ∧ q < 20 then 1 else 0) rfl (fun q => by split_ifs <;> omega)
      with m | m <;> rw [m]
    · simp
    · rw [one_mul]; exact Sha.usew_bool hs hr
  · refine hb ?_
    simp only [Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, Sha.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr]
    rcases hpre (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl (fun q => by split_ifs <;> omega)
      with m | m <;> rw [m]
    · simp
    · rw [one_mul]; exact hd

omit hL hsat in
theorem getD_app_left {α : Type} {l1 l2 : List α} {k : ℕ} (d : α) (h : k < l1.length) :
    (l1 ++ l2).getD k d = l1.getD k d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

omit hL hsat in
theorem getD_app_right {α : Type} {l1 l2 : List α} {k : ℕ} (d : α) (h : l1.length ≤ k) :
    (l1 ++ l2).getD k d = l2.getD (k - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

omit hL hsat in
theorem air_bool {air : Air} {n : ℕ} {main : ℕ → ℕ → F} (hs : ∀ r < n, ∀ c ∈ air.constraints,
    c.eval n air.pre pub main r = 0) {c : ℕ} (hc : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ air.constraints)
    {r : ℕ} (hr : r < n) : main c r = 0 ∨ main c r = 1 := by
  have := hs r hr _ hc
  simp only [StarkedAir.Sha256.boolC, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr,
    Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

omit hL hsat in
theorem neg01 {x : F} (h : x = 0 ∨ x = 1) : -x = -1 ∨ -x = 0 := by rcases h with h | h <;> simp [h]

omit hL hsat in
theorem mul01 {x y : F} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) : x * y = 0 ∨ x * y = 1 := by
  rcases hx with h | h <;> rcases hy with g | g <;> simp [h, g]

/-- **Every use site has multiplicity `−1` or `0`.** -/
theorem use_mult : ∀ s ∈ sites hashSys inst, isUse s.1 s.2.2 = true →
    siteMult hashSys inst pub s = -1 ∨ siteMult hashSys inst pub s = 0 := by
  rintro ⟨i, r, k⟩ hs hu
  obtain ⟨hi, hr, hk⟩ := (mem_sites hL).mp hs
  simp only at hu
  have fs : ∀ r < 2 ^ L, ∀ c ∈ Fields.constraints, c.eval (2 ^ L) Fields.preCols pub (inst 1).main r = 0 :=
    hash_fields_sat hL hsat
  have ms := hash_msg_sat hL hsat
  have ss := hash_sha_sat hL hsat
  have ks := hash_merkle_sat hL hsat
  have ws := hash_walk_sat hL hsat
  have cs := hash_ctx_sat hL hsat
  have pre01 : ∀ {f : ℕ → ℕ} {ii r'}, r' < 2 ^ L → Sha.preCols.getD ii (.periodic [0]) = Sha.per72 f → (∀ q, f q ≤ 1) →
      (pre ii).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 0 ∨
      (pre ii).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 1 := by
    intro f ii r' hr' hi hf
    rw [Sha.eval_per72 ss hi hr']
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hf (r' % 72)) with h | h <;> simp [h]
  interval_cases i
  · simp [isUse] at hu
  · -- fields
    have hk34 : k < 34 := by simpa [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups] using hk
    have e : siteMult hashSys inst pub (1, r, k) =
        ((Fields.lookups ++ Fields.chkLookups).getD k ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Fields.preCols pub
          (inst 1).main r := by
      simp [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields]
    rw [e]
    by_cases h8 : k < 8
    · have hk7 : k < 7 := by
        by_contra hc; have : k = 7 := by omega
        subst this; simp [isUse] at hu
      rw [getD_app_left _ (by rw [show Fields.lookups.length = 8 from rfl]; omega)]
      exact Fields.mult_vals fs hr hk7
    · rw [getD_app_right _ (by rw [show Fields.lookups.length = 8 from rfl]; omega)]
      have hl : Fields.lookups.length = 8 := rfl
      rw [hl]
      exact Fields.chk_use_mult fs hr (j := k - 8) (by omega) (by simp [isUse] at hu; omega)
  · -- messages
    have hk2 : k < 2 := by simpa [isUse] using hu
    interval_cases k
    · have := Msg.bool_col ms (e := Msg.D) (by simp) hr
      simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr]
      rcases this with h | h <;> simp [h]
    · have a := Msg.bool_col ms (e := Msg.FIRSTM) (by simp) hr
      have b := Msg.bool_col ms (e := Msg.HDR) (by simp) hr
      simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
        Msg.om, Msg.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr]
      rcases a with h | h <;> rcases b with g | g <;> simp [h, g]
  · -- SHA
    have hk6 : k < 6 := by simpa [hashSys, Sha.sha, Sha.lookups] using hk
    have hn := Sha.kbool ss (c := Sha.NODE) (by simp) hr
    interval_cases k
    · have := sha_use_mult hL hsat hr (kk := 0) (by norm_num)
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha] using this
    · have := sha_use_mult hL hsat hr (kk := 1) (by norm_num)
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha] using this
    · simp [isUse] at hu
    · rcases pre01 (ii := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) hr rfl (fun q => by split_ifs <;> omega)
        with a | a <;> rcases hn with b | b <;>
        simp [siteMult, siteEval, siteLookup, hashSys, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval, Sha.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr, a, b]
    · rcases pre01 (ii := Sha.DLR) (f := fun q => if q = 11 then 1 else 0) hr rfl (fun q => by split_ifs <;> omega)
        with a | a <;> rcases hn with b | b <;>
        simp [siteMult, siteEval, siteLookup, hashSys, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval, Sha.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr, a, b]
    · rcases pre01 (ii := Sha.DRR) (f := fun q => if q = 19 then 1 else 0) hr rfl (fun q => by split_ifs <;> omega)
        with a | a <;> rcases hn with b | b <;>
        simp [siteMult, siteEval, siteLookup, hashSys, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval, Sha.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr, a, b]
  · -- txid tree
    have hk11 : k < 11 := by simpa [hashSys, Merkle.merkle, Merkle.lookups] using hk
    have hk2 : 2 ≤ k := by simpa [isUse] using hu
    have hrt := Merkle.kbool ks (c := Merkle.RT) (by simp) hr
    have e : siteMult hashSys inst pub (4, r, k) = -((inst 4).main Merkle.RT r) := by
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 4 (by decide)]
      interval_cases k <;> simp [Merkle.merkle, Merkle.lookups, Expr.eval, Merkle.ev_k hr]
    rw [e]; exact neg01 hrt
  · simp [isUse] at hu
  · -- walker
    have hk4 : k < 4 := by simpa [isUse] using hu
    have wb : ∀ c ∈ Walk.bools, (inst 6).main c r = 0 ∨ (inst 6).main c r = 1 := by
      intro c hc
      have hm : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ Walk.walk.air.constraints := by
        have : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ Walk.bools.map (fun x => StarkedAir.Sha256.boolC (Walk.k x)) :=
          List.mem_map.mpr ⟨c, hc, rfl⟩
        simp only [Walk.walk, Walk.constraints, Walk.localC, List.mem_append]
        tauto
      exact air_bool ws hm hr
    interval_cases k <;>
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups,
        show (6 : ℕ) ≠ 0 by decide, show (6 : ℕ) ≠ 1 by decide, show (6 : ℕ) ≠ 2 by decide, show (6 : ℕ) ≠ 3 by decide,
        show (6 : ℕ) ≠ 4 by decide, show (6 : ℕ) ≠ 5 by decide, if_false, if_true, List.getD_cons_zero,
        List.getD_cons_succ, Expr.eval, Walk.k, StarkedAir.Sha256.eval_col, wrap_zero hr] <;>
      exact neg01 (wb _ (by simp [Walk.bools]))
  · -- context
    have hk11 : k < 12 := by simpa [hashSys, Ctx.ctx, Ctx.lookups] using hk
    have actr := air_bool cs (c := Ctx.ACTR) (by simp [Ctx.ctx, Ctx.constraints, Ctx.k]) hr
    have hasc := air_bool cs (c := Ctx.HASC) (by simp [Ctx.ctx, Ctx.constraints, Ctx.k]) hr
    have hc := air_bool cs (c := Ctx.HC) (by simp [Ctx.ctx, Ctx.constraints, Ctx.k]) hr
    have fst : (if r = 0 then (1 : F) else 0) = 0 ∨ (if r = 0 then (1 : F) else 0) = 1 := by split_ifs <;> simp
    have lt : ((if r < 118 then (1 : F) else 0) - if r < 117 then 1 else 0) = 0 ∨
        ((if r < 118 then (1 : F) else 0) - if r < 117 then 1 else 0) = 1 := by
      by_cases h1 : r < 117
      · simp [h1, show r < 118 by omega]
      · by_cases h2 : r < 118 <;> simp [h1, h2]
    have ev : ∀ kk, siteMult hashSys inst pub (7, r, kk) =
        ((Ctx.lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Ctx.preCols pub (inst 7).main r) := by
      intro kk; simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]; rfl
    rw [ev]
    have pe : ∀ i, (pre i).eval (2 ^ L) Ctx.preCols pub (inst 7).main r = (Ctx.preCols.getD i (.periodic [0])).eval
        (2 ^ L) r := fun i => by simp [pre, Expr.eval, wrap_zero hr]
    interval_cases k <;> (try simp [isUse] at hu) <;>
      simp only [Ctx.lookups, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, Ctx.k, Ctx.p, Ctx.one,
        StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr, pe, Nat.cast_one] <;>
      (try simp only [Ctx.preCols, Ctx.P_FIRST, Ctx.P_LT117, Ctx.P_LT118, List.getD_cons_zero, List.getD_cons_succ,
        PreCol.eval]) <;>
      first
        | exact neg01 actr
        | (left; trivial)
        | (left; rfl)
        | exact neg01 fst
        | exact neg01 (mul01 fst hasc)
        | exact neg01 (mul01 fst hc)
        | exact neg01 (mul01 lt hc)
  · simp [isUse] at hu
  · simp [isUse] at hu
  · -- Blake2s message words: byte reads `−A·(1 − STR)`, `−A·STR`
    have hk8 : k < 8 := by simpa [isUse] using hu
    have bs : ∀ c ∈ B2Msg.boolCols, (inst 10).main c r = 0 ∨ (inst 10).main c r = 1 := by
      intro c hc
      have hm : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ B2Msg.b2msg.air.constraints := by
        have : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ B2Msg.boolCols.map (fun x => StarkedAir.Sha256.boolC (B2Msg.k x)) :=
          List.mem_map.mpr ⟨c, hc, rfl⟩
        simp only [B2Msg.b2msg, B2Msg.constraints, List.mem_append]
        tauto
      exact air_bool (hash_b2msg_sat hL hsat) hm hr
    have hstr := bs B2Msg.STR (by simp [B2Msg.boolCols])
    have ev : ∀ kk, siteMult hashSys inst pub (10, r, kk) =
        ((B2Msg.lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) B2Msg.preCols pub (inst 10).main r) := by
      intro kk; simp only [siteMult, siteEval, siteLookup, hashSys, hL 10 (by decide)]; rfl
    rw [ev]
    have om01 : ∀ {x : F}, (x = 0 ∨ x = 1) → (1 - x = 0 ∨ 1 - x = 1) := by
      intro x h; rcases h with h | h <;> simp [h]
    interval_cases k <;>
      simp only [B2Msg.lookups, List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, List.getD_cons_zero, List.getD_cons_succ, Expr.eval, B2Msg.k, B2Msg.om,
        B2Msg.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr, Nat.cast_one] <;>
      first
        | exact neg01 (mul01 (bs _ (by simp [B2Msg.boolCols, B2Msg.A])) (om01 hstr))
        | exact neg01 (mul01 (bs _ (by simp [B2Msg.boolCols, B2Msg.A])) hstr)
  · -- Blake2s: `−USEW·LT16`, `−OUTP·LT16`, `−USEW·R0`
    have hk3 : k < 3 := by simpa [isUse] using hu
    have bs : ∀ c ∈ [B2s.MU0, B2s.MU1, B2s.MU2], (inst 11).main c r = 0 ∨ (inst 11).main c r = 1 := by
      intro c hc
      have hm : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ B2s.b2s.air.constraints := by
        have h1 : StarkedAir.Sha256.boolC (StarkedAir.Sha256.col c) ∈ B2s.flagC := by
          simp only [B2s.flagC, List.mem_append, List.mem_map]
          left; left; refine ⟨c, ?_, rfl⟩
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢; tauto
        simp only [B2s.b2s, B2s.constraints, List.mem_append]
        tauto
      exact air_bool (hash_b2s_sat hL hsat) hm hr
    interval_cases k <;>
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 11 (by decide), B2s.b2s, B2s.lookups,
        show (11 : ℕ) ≠ 0 by decide, show (11 : ℕ) ≠ 1 by decide, show (11 : ℕ) ≠ 2 by decide, show (11 : ℕ) ≠ 3 by decide,
        show (11 : ℕ) ≠ 4 by decide, show (11 : ℕ) ≠ 5 by decide, show (11 : ℕ) ≠ 6 by decide, show (11 : ℕ) ≠ 7 by decide,
        show (11 : ℕ) ≠ 8 by decide, show (11 : ℕ) ≠ 9 by decide, show (11 : ℕ) ≠ 10 by decide, if_false, if_true,
        List.getD_cons_zero, List.getD_cons_succ, List.cons_append, Expr.eval, B2s.k, StarkedAir.Sha256.eval_col,
        wrap_zero hr] <;>
      exact neg01 (bs _ (by simp))

/-- **A use is matched by a yield.** A use site with multiplicity `−1` has a yield site (not a use) with
nonzero multiplicity, the same relation and the same tuple. -/
theorem linked (hL24 : L ≤ 24) {s0 : Site} (hs0 : s0 ∈ sites hashSys inst) (hu : isUse s0.1 s0.2.2 = true)
    (hm : siteMult hashSys inst pub s0 = -1) :
    ∃ s ∈ sites hashSys inst, isUse s.1 s.2.2 = false ∧ siteMult hashSys inst pub s ≠ 0 ∧
      siteRel hashSys s = siteRel hashSys s0 ∧ siteVals hashSys inst pub s = siteVals hashSys inst pub s0 := by
  classical
  obtain ⟨s, hs, hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2 (use := fun i k => isUse i k = true)
    (use_mult hL hsat) (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide (isUse s.1 s.2.2 = true)) (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL24
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨s0, hs0, hu, hm, rfl, rfl⟩)
  exact ⟨s, hs, by simpa using hnu, hsm, hsr, hsv⟩

omit hsat in
/-- A yield site of relation `R` is listed in `yieldTable` with `R`. -/
theorem yield_of {i r k : ℕ} (hs : ((i, r, k) : Site) ∈ sites hashSys inst) (hnu : isUse i k = false) :
    (i, k, siteRel hashSys (i, r, k)) ∈ yieldTable := by
  obtain ⟨hi, -, hk⟩ := (mem_sites hL).mp hs
  exact yield_table i hi k hk hnu

omit hL hsat in
theorem rels : REL_BYTE = 3 ∧ Fields.REL_TX = 4 ∧ Msg.REL_MSGW = 5 ∧ Msg.REL_MLEN = 6 ∧ Sha.REL_DIGEST = 7 ∧
    Sha.REL_NODE = 8 ∧ Tables.REL_R8 = 9 ∧ Tables.REL_OPC = 10 ∧ Fields.REL_SCRIPT = 11 ∧ Fields.REL_TOT = 12 ∧
    Fields.REL_CTX = 13 ∧ Fields.REL_COMMIT = 14 ∧ Walk.REL_SIGOPS = 15 ∧ Ctx.REL_WCID = 16 ∧
    Undo.REL_UBYTE = 17 ∧ B2Msg.REL_B2W = 18 ∧ B2Msg.REL_B2B = 19 ∧ B2s.REL_B2D = 20 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

omit hL hsat in
theorem yt (i k R : ℕ) : (i, k, R) ∈ yieldTable ↔
    (i = 0 ∧ k = 0 ∧ R = 3) ∨ (i = 1 ∧ k = 7 ∧ R = 4) ∨ (i = 1 ∧ k = 30 ∧ R = 11) ∨ (i = 1 ∧ k = 31 ∧ R = 12) ∨
    (i = 1 ∧ k = 33 ∧ R = 14) ∨ (i = 2 ∧ k = 2 ∧ R = 5) ∨ (i = 2 ∧ k = 3 ∧ R = 6) ∨ (i = 3 ∧ k = 2 ∧ R = 7) ∨
    (i = 4 ∧ k = 0 ∧ R = 8) ∨ (i = 4 ∧ k = 1 ∧ R = 6) ∨ (i = 5 ∧ k = 0 ∧ R = 9) ∨ (i = 5 ∧ k = 1 ∧ R = 10) ∨
    (i = 6 ∧ k = 4 ∧ R = 15) ∨ (i = 7 ∧ k = 6 ∧ R = 13) ∨ (i = 7 ∧ k = 7 ∧ R = 7) ∨ (i = 7 ∧ k = 8 ∧ R = 7) ∨
    (i = 8 ∧ k = 0 ∧ R = 8) ∨ (i = 8 ∧ k = 1 ∧ R = 6) ∨ (i = 8 ∧ k = 2 ∧ R = 16) ∨ (i = 9 ∧ k = 0 ∧ R = 17) ∨
    (i = 10 ∧ k = 8 ∧ R = 18) ∨ (i = 10 ∧ k = 9 ∧ R = 19) ∨ (i = 11 ∧ k = 3 ∧ R = 20) ∨ (i = 11 ∧ k = 4 ∧ R = 20) ∨
    (i = 11 ∧ k = 5 ∧ R = 20) ∨ (i = 11 ∧ k = 6 ∧ R = 20) ∨ (i = 11 ∧ k = 7 ∧ R = 20) ∨ (i = 11 ∧ k = 8 ∧ R = 20) ∨
    (i = 11 ∧ k = 9 ∧ R = 20) ∨ (i = 11 ∧ k = 10 ∧ R = 20) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18⟩ := rels
  simp only [yieldTable, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18, List.mem_cons,
    Prod.mk.injEq, List.not_mem_nil, or_false]

/-- **Linking a use to its yield, by relation.** For a use site `s0` with multiplicity `−1` and relation
`R`, a yield site `(i, r', k)` with nonzero multiplicity and the same tuple, listed under `R`. -/
theorem link (hL24 : L ≤ 24) {i0 r0 k0 : ℕ} (hs0 : ((i0, r0, k0) : Site) ∈ sites hashSys inst)
    (hu : isUse i0 k0 = true) (hm : siteMult hashSys inst pub (i0, r0, k0) = -1) :
    ∃ i r' k, r' < 2 ^ L ∧ (i, k, siteRel hashSys (i0, r0, k0)) ∈ yieldTable ∧
      siteMult hashSys inst pub (i, r', k) ≠ 0 ∧
      siteVals hashSys inst pub (i, r', k) = siteVals hashSys inst pub (i0, r0, k0) := by
  obtain ⟨⟨i, r', k⟩, hs, hnu, hsm, hsr, hsv⟩ := linked hL hsat hL24 hs0 hu hm
  refine ⟨i, r', k, ((mem_sites hL).mp hs).2.1, ?_, hsm, hsv⟩
  rw [← hsr]; exact yield_of hL hs hnu

omit hsat in
theorem site_mem {i r k : ℕ} (hi : i < 12) (hr : r < 2 ^ L) (hk : k < (hashSys.comp i).lookups.length) :
    ((i, r, k) : Site) ∈ sites hashSys inst := (mem_sites hL).mpr ⟨hi, hr, hk⟩

/-- **SHA's uses are message (or tree) yields.** A SHA word use (`kk = 0`) or length use (`kk = 1`) with
multiplicity `−1` is matched by a message row yielding the same tuple (message lookup `kk + 2`) or, for a
length, by a txid-tree node row (lookup 1) or a witness-tree row (lookup 1). -/
theorem sha_use_linked (hL24 : L ≤ 24) {r : ℕ} (hr : r < 2 ^ L) {kk : ℕ} (hk : kk < 2)
    (hm : siteMult hashSys inst pub (3, r, kk) = -1) :
    ∃ r' < 2 ^ L, (siteMult hashSys inst pub (2, r', kk + 2) ≠ 0 ∧
      siteVals hashSys inst pub (2, r', kk + 2) = siteVals hashSys inst pub (3, r, kk)) ∨
      (kk = 1 ∧ siteMult hashSys inst pub (4, r', 1) ≠ 0 ∧
        siteVals hashSys inst pub (4, r', 1) = siteVals hashSys inst pub (3, r, kk)) ∨
      (kk = 1 ∧ siteMult hashSys inst pub (8, r', 1) ≠ 0 ∧
        siteVals hashSys inst pub (8, r', 1) = siteVals hashSys inst pub (3, r, kk)) := by
  have hs1 := site_mem hL (i := 3) (by decide) hr (k := kk) (by simp [hashSys, Sha.sha, Sha.lookups]; omega)
  obtain ⟨i, r', k, hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs1 (by interval_cases kk <;> rfl) hm
  refine ⟨r', hr', ?_⟩
  interval_cases kk
  · have e : siteRel hashSys (3, r, 0) = 5 := rfl
    rw [e, yt] at hy
    obtain ⟨rfl, rfl⟩ : i = 2 ∧ k = 2 := by omega
    exact Or.inl ⟨hsm, hsv⟩
  · have e : siteRel hashSys (3, r, 1) = 6 := rfl
    rw [e, yt] at hy
    rcases (by omega : (i = 2 ∧ k = 3) ∨ (i = 4 ∧ k = 1) ∨ (i = 8 ∧ k = 1)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hsm, hsv⟩
    · exact Or.inr (Or.inl ⟨rfl, hsm, hsv⟩)
    · exact Or.inr (Or.inr ⟨rfl, hsm, hsv⟩)

/-- The node tuple a SHA node block reads: yielded by a txid-tree row (`MID = NB + r'`) or a witness-tree
row (`MID = NBW + r'`), with that row's children and duplicate flag. -/
theorem node_link (hL24 : L ≤ 24) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1) :
    ∃ r' < 2 ^ L,
      ((inst 4).main Merkle.ACTN r' = 1 ∧
        (inst 3).main Sha.MID x = ((Merkle.NB + r' : ℕ) : F) ∧ (inst 3).main Sha.LID x = (inst 4).main Merkle.LEFT r' ∧
        (inst 3).main Sha.RID x = (inst 4).main Merkle.RIGHT r' ∧ (inst 3).main Sha.NDUP x = (inst 4).main Merkle.DUP r') ∨
      ((inst 3).main Sha.MID x = ((WMerkle.NBW + r' : ℕ) : F) ∧
        (inst 3).main Sha.LID x = (inst 8).main WMerkle.LEFT r' ∧ (inst 3).main Sha.RID x = (inst 8).main WMerkle.RIGHT r' ∧
        (inst 3).main Sha.NDUP x = 1) := by
  have hs1 := site_mem hL (i := 3) (by decide) hx (k := 3) (by simp [hashSys, Sha.sha, Sha.lookups])
  have hm1 : siteMult hashSys inst pub (3, x, 3) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval] at hm ⊢
    rw [hm]
  obtain ⟨i, r', k, hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs1 rfl hm1
  have e : siteRel hashSys (3, x, 3) = 8 := rfl
  rw [e, yt] at hy
  have hv3 : siteVals hashSys inst pub (3, x, 3) = [(inst 3).main Sha.MID x, (inst 3).main Sha.LID x,
      (inst 3).main Sha.RID x, (inst 3).main Sha.NDUP x] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  refine ⟨r', hr', ?_⟩
  rcases (by omega : (i = 4 ∧ k = 0) ∨ (i = 8 ∧ k = 0)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have hv4 : siteVals hashSys inst pub (4, r', 0) = [(Merkle.NB : F) + (inst 4).main Merkle.RIX r',
        (inst 4).main Merkle.LEFT r', (inst 4).main Merkle.RIGHT r', (inst 4).main Merkle.DUP r'] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 4 (by decide), Merkle.merkle, Merkle.lookups, Merkle.nodeId,
        Merkle.k, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
    rw [hv4, hv3] at hsv
    simp only [List.cons.injEq, and_true] at hsv
    obtain ⟨e1, e2, e3, e4⟩ := hsv
    rw [Merkle.rix_eq (hash_merkle_sat hL hsat) r' hr'] at e1
    have hact : (inst 4).main Merkle.ACTN r' = 1 := by
      have hm4 : (inst 4).main Merkle.ACTN r' * (inst 4).main Merkle.NM r' ≠ 0 := by
        simpa [siteMult, siteEval, siteLookup, hashSys, hL 4 (by decide), Merkle.merkle, Merkle.lookups, Expr.eval,
          Merkle.k, StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
      rcases Merkle.kbool (hash_merkle_sat hL hsat) (c := Merkle.ACTN) (by simp) hr' with h | h
      · rw [h, zero_mul] at hm4; exact absurd rfl hm4
      · exact h
    exact ⟨hact, by rw [← e1]; push_cast; ring, e2.symm, e3.symm, e4.symm⟩
  · right
    have hv8 : siteVals hashSys inst pub (8, r', 0) = [(WMerkle.NBW : F) + (inst 8).main WMerkle.RIX r',
        (inst 8).main WMerkle.LEFT r', (inst 8).main WMerkle.RIGHT r', 1] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 8 (by decide), WMerkle.wmerkle, WMerkle.lookups,
        WMerkle.nodeId, WMerkle.k, WMerkle.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr',
        Expr.eval]
    rw [hv8, hv3] at hsv
    simp only [List.cons.injEq, and_true] at hsv
    obtain ⟨e1, e2, e3, e4⟩ := hsv
    rw [WMerkle.rix_eq (hash_wmerkle_sat hL hsat) r' hr'] at e1
    exact ⟨by rw [← e1]; push_cast; ring, e2.symm, e3.symm, e4.symm⟩

/-- **A node block's id is a tree node id** (at least `NB`). -/
theorem node_mid (hL24 : L ≤ 24) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1) :
    Merkle.NB ≤ ((inst 3).main Sha.MID x).val := by
  have h24 : 2 ^ L ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hL24
  norm_num at h24
  obtain ⟨r', hr', h | h⟩ := node_link hL hsat hL24 hx hm
  · rw [h.2.1, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold Merkle.NB; omega))]; omega
  · rw [h.1, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega))]
    unfold WMerkle.NBW Merkle.NB; omega

/-- **A txid-tree node block's tuple is a txid-tree row's**: `MID = NB + r'`, children and `dup` as on row
`r'` (for ids below the witness tree's). -/
theorem node_row (hL24 : L ≤ 24) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1)
    (hlt : ((inst 3).main Sha.MID x).val < WMerkle.NBW) :
    ∃ r' < 2 ^ L, (inst 4).main Merkle.ACTN r' = 1 ∧
      (inst 3).main Sha.MID x = ((Merkle.NB + r' : ℕ) : F) ∧ (inst 3).main Sha.LID x = (inst 4).main Merkle.LEFT r' ∧
      (inst 3).main Sha.RID x = (inst 4).main Merkle.RIGHT r' ∧ (inst 3).main Sha.NDUP x = (inst 4).main Merkle.DUP r' := by
  have h24 : 2 ^ L ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hL24
  norm_num at h24
  obtain ⟨r', hr', h | h⟩ := node_link hL hsat hL24 hx hm
  · exact ⟨r', hr', h⟩
  · rw [h.1, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega))] at hlt; omega

/-- **Digest uses are second hashes' outputs.** A digest use (a node block's child read, `SHA` lookups 4–5,
or the root row's read, txid-tree lookup 2) with multiplicity `−1` and an id below `2^28` reads the tuple
yielded at the last row of a second-hash period `q'`. (Ids `2^28`, `2^28 + 1` are the context's
pseudo-digests.) -/
theorem digest_linked (hL24 : L ≤ 24) {i r k : ℕ} (hu : (i = 3 ∧ (k = 4 ∨ k = 5)) ∨ (i = 4 ∧ k = 2))
    (hr : r < 2 ^ L) (hm : siteMult hashSys inst pub (i, r, k) = -1)
    (hid : ∀ v ∈ (siteVals hashSys inst pub (i, r, k)).head?, v.val < 2 ^ 28) :
    ∃ q', 72 * q' + 72 ≤ 2 ^ L ∧ (inst 3).main Sha.DBL (72 * q') = 1 ∧
      siteVals hashSys inst pub (3, 72 * q' + 71, 2) = siteVals hashSys inst pub (i, r, k) := by
  have ss := hash_sha_sat hL hsat
  have hs1 : ((i, r, k) : Site) ∈ sites hashSys inst := by
    rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ <;> (try subst h) <;>
      exact site_mem hL (by decide) hr (by simp [hashSys, Sha.sha, Sha.lookups, Merkle.merkle, Merkle.lookups])
  have huse : isUse i k = true := by rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ <;> (try subst h) <;> rfl
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs1 huse hm
  have e : siteRel hashSys (i, r, k) = 7 := by rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ <;> (try subst h) <;> rfl
  rw [e, yt] at hy
  rcases (by omega : (i' = 3 ∧ k' = 2) ∨ (i' = 7 ∧ k' = 7) ∨ (i' = 7 ∧ k' = 8)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the yield row is a second hash's last row
    have hdy : (inst 3).main Sha.DBL r' * (inst 3).main Sha.YM r' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Expr.eval, Sha.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
    have h71 : r' % 72 = 71 := by
      have := Sha.order_sat ss (c := .mul (Sha.k Sha.YM) (Sha.om (pre Sha.FIN3))) (by simp [Sha.orderC]) hr'
      simp only [Expr.eval, Sha.k, Sha.om, Sha.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
        wrap_zero hr', Nat.cast_one] at this
      rw [Sha.eval_per72 ss (i := Sha.FIN3) (f := fun q => if q = 71 then 1 else 0) rfl hr'] at this
      by_contra h
      simp only [h, if_false, Nat.cast_zero, sub_zero, mul_one] at this
      exact hdy (by rw [this, mul_zero])
    have hd1 : (inst 3).main Sha.DBL r' = 1 := by
      rcases Sha.kbool ss (c := Sha.DBL) (by simp) hr' with h | h
      · rw [h, zero_mul] at hdy; exact absurd rfl hdy
      · exact h
    refine ⟨r' / 72, by omega, ?_, ?_⟩
    · have := Sha.per_const ss (X := Sha.DBL) (by simp) (s := 72 * (r' / 72)) (by omega) 71 (by norm_num) (by omega)
      rw [show 72 * (r' / 72) + 71 = r' by omega, hd1] at this; exact this.symm
    · rw [show 72 * (r' / 72) + 71 = r' by omega]; exact hsv
  all_goals
    exfalso
    have hh := hid
    rw [← hsv] at hh
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups,
      StarkedAir.Sha256.eval_cst] at hh
    first
      | (unfold Ctx.ZERO_ID P at hh; norm_num at hh)
      | (unfold Ctx.NONCE_ID P at hh; norm_num at hh)

/-- **The root row's header reads are message yields.** A txid-tree word use (lookups 3–10) with
multiplicity `−1` is matched by a message row yielding the same tuple. -/
theorem merkle_word_linked (hL24 : L ≤ 24) {r k : ℕ} (hk : 3 ≤ k) (hk11 : k < 11) (hr : r < 2 ^ L)
    (hm : siteMult hashSys inst pub (4, r, k) = -1) :
    ∃ r' < 2 ^ L, siteMult hashSys inst pub (2, r', 2) ≠ 0 ∧
      siteVals hashSys inst pub (2, r', 2) = siteVals hashSys inst pub (4, r, k) := by
  have hs1 := site_mem hL (i := 4) (by decide) hr (k := k) (by simp [hashSys, Merkle.merkle, Merkle.lookups]; omega)
  obtain ⟨i, r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs1 (by simp [isUse]; omega) hm
  have e : siteRel hashSys (4, r, k) = 5 := by interval_cases k <;> rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i = 2 ∧ k' = 2 := by omega
  exact ⟨r', hr', hsm, hsv⟩

/-- **SHA message words are message bytes.** At a SHA message row `x` (rows 4..19 of a period) of a
period that reads words, the word limbs are bytes `j − 3 .. j` (big-endian) of a message starting at
message row `r0`, with the same id, where `j − 3 = 64 · BLKI + 4 · (row − 4)`. -/
theorem sha_word (hL24 : L ≤ 24) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.MSGROW) (Sha.k Sha.USEW)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1) :
    ∃ r0 j, r0 + j < 2 ^ L ∧ 3 ≤ j ∧ r0 % 64 = 0 ∧ (inst 2).main Msg.FIRSTM r0 = 1 ∧
      (∀ i, r0 < i → i ≤ r0 + j → (inst 2).main Msg.FIRSTM i = 0 ∧ (inst 2).main Msg.NIL i = 0) ∧
      (inst 2).main Msg.MID r0 = (inst 3).main Sha.MID x ∧
      ((j - 3 : ℕ) : F) = (Expr.add (.mul (cst 64) (Sha.k Sha.BLKI)) (.sub (.mul (cst 4) (pre Sha.ROWIDX)) (cst 16))).eval
        (2 ^ L) Sha.preCols pub (inst 3).main x ∧
      (StarkedAir.Sha256.limb StarkedAir.Sha256.W 0).eval (2 ^ L) Sha.preCols pub (inst 3).main x =
        256 * (inst 2).main Msg.BYTE (r0 + j - 1) + (inst 2).main Msg.BYTE (r0 + j) ∧
      (StarkedAir.Sha256.limb StarkedAir.Sha256.W 1).eval (2 ^ L) Sha.preCols pub (inst 3).main x =
        256 * (inst 2).main Msg.BYTE (r0 + j - 3) + (inst 2).main Msg.BYTE (r0 + j - 2) := by
  have hm' : siteMult hashSys inst pub (3, x, 0) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide)]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false, ↓reduceIte]
    simp only [Sha.sha, Sha.lookups, List.getD_cons_zero, Expr.eval]
    rw [show Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (pre Sha.MSGROW) *
      Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (Sha.k Sha.USEW) = 1 from hm]
  obtain ⟨r', hr', hlink⟩ := sha_use_linked hL hsat hL24 hx (kk := 0) (by norm_num) hm'
  obtain ⟨hym, hyv⟩ := hlink.resolve_right (fun h => by rcases h with h | h <;> exact absurd h.1 (by norm_num))
  have ms := hash_msg_sat hL hsat
  have hmult : (pre Msg.IS3).eval (2 ^ L) Msg.preCols pub (inst 2).main r' * (inst 2).main Msg.WM r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr'] using hym
  obtain ⟨r0, j, rfl, hj, ha, hf, hnil, hb, hmid, hidx, hvals⟩ := Msg.word_yield ms hr' hmult
  have hv2 : siteVals hashSys inst pub (2, r0 + j, 2) = [(inst 2).main Msg.MID r0, ((j - 3 : ℕ) : F),
      256 * (inst 2).main Msg.BYTE (r0 + j - 1) + (inst 2).main Msg.BYTE (r0 + j),
      256 * (inst 2).main Msg.BYTE (r0 + j - 3) + (inst 2).main Msg.BYTE (r0 + j - 2)] := by
    rw [← hvals]; simp [siteVals, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups]
  have hv3 : siteVals hashSys inst pub (3, x, 0) =
      [(inst 3).main Sha.MID x,
       (Expr.add (.mul (cst 64) (Sha.k Sha.BLKI)) (.sub (.mul (cst 4) (pre Sha.ROWIDX)) (cst 16))).eval
         (2 ^ L) Sha.preCols pub (inst 3).main x,
       (StarkedAir.Sha256.limb StarkedAir.Sha256.W 0).eval (2 ^ L) Sha.preCols pub (inst 3).main x,
       (StarkedAir.Sha256.limb StarkedAir.Sha256.W 1).eval (2 ^ L) Sha.preCols pub (inst 3).main x] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  rw [hv2, hv3] at hyv
  simp only [List.cons.injEq, and_true] at hyv
  obtain ⟨e1, e2, e3, e4⟩ := hyv
  exact ⟨r0, j, hr', hj, ha, hf, hb, e1, e2, e3.symm, e4.symm⟩

/-- **A second hash checks its message's padded length.** At a `DBL` period's first row `x`, the
message with its id (starting at message row `r0`, data ending at index `d`) has padded length
`64 · BLKI(x − 1) + 64`. -/
theorem sha_len (hL24 : L ≤ 24) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.DBL)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1)
    (hmid : ((inst 3).main Sha.MID x).val < Merkle.NB) :
    ∃ r0 d, (inst 2).main Msg.FIRSTM r0 = 1 ∧ (inst 2).main Msg.ENDD (r0 + d) = 1 ∧
      (∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1) ∧
      (inst 2).main Msg.MID r0 = (inst 3).main Sha.MID x ∧
      r0 + d + 1 + 1 + (119 - (r0 + d + 1) % 64) % 64 + 7 < 2 ^ L ∧
      (((r0 + d + 1 + 1 + (119 - (r0 + d + 1) % 64) % 64 + 7) + 1 - r0 : ℕ) : F) =
        (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main x := by
  have hm' : siteMult hashSys inst pub (3, x, 1) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide)]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false, ↓reduceIte]
    simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval]
    rw [show Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (pre Sha.ROW0) *
      Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (Sha.k Sha.DBL) = 1 from hm]
  obtain ⟨r', hr', hlink⟩ := sha_use_linked hL hsat hL24 hx (kk := 1) (by norm_num) hm'
  have hv3' : siteVals hashSys inst pub (3, x, 1) = [(inst 3).main Sha.MID x,
      (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main x] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  -- not a Merkle node's length: node ids are at least `NB`
  obtain ⟨hym, hyv⟩ := hlink.resolve_right (fun hh => by
    have h24 : 2 ^ L ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hL24
    norm_num at h24
    rcases hh with ⟨-, -, hv⟩ | ⟨-, -, hv⟩
    · have hv4 : siteVals hashSys inst pub (4, r', 1) = [(Merkle.NB : F) + (inst 4).main Merkle.RIX r', 128] := by
        simp [siteVals, siteEval, siteLookup, hashSys, hL 4 (by decide), Merkle.merkle, Merkle.lookups,
          Merkle.nodeId, Merkle.k, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
      rw [hv4, hv3'] at hv
      simp only [List.cons.injEq] at hv
      rw [Merkle.rix_eq (hash_merkle_sat hL hsat) r' hr'] at hv
      have e : ((inst 3).main Sha.MID x).val = Merkle.NB + r' := by
        rw [← hv.1, show ((Merkle.NB : ℕ) : F) + (r' : F) = ((Merkle.NB + r' : ℕ) : F) by push_cast; ring]
        exact ZMod.val_natCast_of_lt (Fields.lt_P (by unfold Merkle.NB; omega))
      omega
    · have hv8 : siteVals hashSys inst pub (8, r', 1) = [(WMerkle.NBW : F) + (inst 8).main WMerkle.RIX r', 128] := by
        simp [siteVals, siteEval, siteLookup, hashSys, hL 8 (by decide), WMerkle.wmerkle, WMerkle.lookups,
          WMerkle.nodeId, WMerkle.k, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
      rw [hv8, hv3'] at hv
      simp only [List.cons.injEq] at hv
      rw [WMerkle.rix_eq (hash_wmerkle_sat hL hsat) r' hr'] at hv
      have e : ((inst 3).main Sha.MID x).val = WMerkle.NBW + r' := by
        rw [← hv.1, show ((WMerkle.NBW : ℕ) : F) + (r' : F) = ((WMerkle.NBW + r' : ℕ) : F) by push_cast; ring]
        exact ZMod.val_natCast_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega))
      unfold WMerkle.NBW Merkle.NB at *; omega)
  have ms := hash_msg_sat hL hsat
  have hmult : (inst 2).main Msg.LN r' * (inst 2).main Msg.MM r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr'] using hym
  obtain ⟨r0, d, hf, he, hc, heq, hmid, hidx⟩ := Msg.len_yield ms hr' hmult
  have hv2 : siteVals hashSys inst pub (2, r', 1 + 2) = [(inst 2).main Msg.MID r', (inst 2).main Msg.IDX r' + 1] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Msg.k, Msg.one,
      StarkedAir.Sha256.eval_col, wrap_zero hr', Expr.eval, StarkedAir.Sha256.eval_cst]
  have hv3 : siteVals hashSys inst pub (3, x, 1) = [(inst 3).main Sha.MID x,
      (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main x] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  rw [hv2, hv3] at hyv
  simp only [List.cons.injEq, and_true] at hyv
  obtain ⟨e1, e2⟩ := hyv
  refine ⟨r0, d, hf, he, hc, hmid.symm.trans e1, heq ▸ hr', ?_⟩
  rw [← heq, ← e2, hidx]

theorem hash_fields_sat' : ∀ r < 2 ^ L, ∀ c ∈ Fields.constraints,
    c.eval (2 ^ L) Fields.preCols pub (inst 1).main r = 0 := by
  have := hsat.1 1 (by decide); rw [hL 1 (by decide)] at this; exact this

/-- **Every byte read is the block's.** A byte-read site of a non-table component with multiplicity
`−1` reads `(r0, byte r0)` with `r0 < LEN`. -/
theorem hash_read (hL24 : L ≤ 24) {i r k : ℕ} (hs0 : ((i, r, k) : Site) ∈ sites hashSys inst) (hi : i ≠ 0)
    (hrel : siteRel hashSys (i, r, k) = REL_BYTE) (hm : siteMult hashSys inst pub (i, r, k) = -1) {p b : F}
    (hv : siteVals hashSys inst pub (i, r, k) = [p, b]) :
    ∃ r0, r0 < (pub 0).val ∧ p = (r0 : F) ∧ b = (inst 0).main BYTE r0 := by
  have huse : isUse i k = true := by
    by_contra hc
    have hy := yield_of hL hs0 (by simpa using hc)
    rw [hrel, show REL_BYTE = 3 from rfl, yt] at hy
    omega
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs0 huse hm
  rw [hrel, show REL_BYTE = 3 from rfl, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 0 ∧ k' = 0 := by omega
  have hb0 := hash_bytes_sat hL hsat
  have hP : 2 ^ L < P := by have := hash_rows_lt_P hL24; omega
  have hm' : (Expr.mul (StarkedAir.Sha256.col ACTIVE) (StarkedAir.Sha256.col MULT)).eval (2 ^ L) preCols pub (inst 0).main r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, hL 0 (by decide), bytes] using hsm
  obtain ⟨hlt, hvals⟩ := yield_sound hb0 hP hr' hm'
  have e : siteVals hashSys inst pub (0, r', 0) = [(r' : F), (inst 0).main BYTE r'] := by
    simpa [siteVals, siteEval, siteLookup, hashSys, hL 0 (by decide), bytes] using hvals
  rw [e, hv] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  exact ⟨r', hlt, hsv.1.symm, hsv.2.symm⟩

/-- **Fields reads are the block's bytes** (the read oracle `Fields.Reads` needs, for the hashing system). -/
theorem hash_fields_read (hL24 : L ≤ 24) : ∀ {r : ℕ}, r < 2 ^ L → ∀ {kk : ℕ}, kk < 7 →
    (Fields.lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Fields.preCols pub (inst 1).main r = -1 →
    ∃ r0, r0 < (pub 0).val ∧
      ((Fields.lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) Fields.preCols pub (inst 1).main r)) =
        [(r0 : F), (inst 0).main BYTE r0] := by
  intro r hr kk hk hm
  have hs1 := site_mem hL (i := 1) (by decide) hr (k := kk) (by
    simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups]; omega)
  have gd : ((Fields.lookups ++ Fields.chkLookups).getD kk ⟨0, .const 0, []⟩) =
      Fields.lookups.getD kk ⟨0, .const 0, []⟩ :=
    getD_app_left _ (by rw [show Fields.lookups.length = 8 from rfl]; omega)
  have hl : siteLookup hashSys ((1, r, kk) : Site) = Fields.lookups.getD kk ⟨0, .const 0, []⟩ := by
    rw [← gd]; rfl
  have hrel : siteRel hashSys ((1, r, kk) : Site) = REL_BYTE := by
    simp only [siteRel, hl]; interval_cases kk <;> rfl
  have hmult : siteMult hashSys inst pub ((1, r, kk) : Site) = -1 := by
    simp only [siteMult, hl, siteEval, hL 1 (by decide)]; exact hm
  have e : siteVals hashSys inst pub ((1, r, kk) : Site) =
      (Fields.lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) Fields.preCols pub (inst 1).main r) := by
    simp only [siteVals, hl]
    congr 1; funext e; simp only [siteEval, hL 1 (by decide)]; rfl
  obtain ⟨p, b, hpb⟩ : ∃ p b, siteVals hashSys inst pub ((1, r, kk) : Site) = [p, b] := by
    rw [e]; interval_cases kk <;> exact ⟨_, _, rfl⟩
  obtain ⟨r0, hr0, hp, hb⟩ := hash_read hL hsat hL24 hs1 (by decide) hrel hmult hpb
  exact ⟨r0, hr0, by rw [← e, hpb, hp, hb]⟩

/-- **Message data bytes are the block's.** A message data row reads the block byte at its position. -/
theorem msg_read (hL24 : L ≤ 24) {r : ℕ} (hr : r < 2 ^ L) (hd : (inst 2).main Msg.D r = 1) :
    ∃ r0, r0 < (pub 0).val ∧ (inst 2).main Msg.POS r = (r0 : F) ∧
      (inst 2).main Msg.BYTE r = (inst 0).main BYTE r0 := by
  have hs0 := site_mem hL (i := 2) (by decide) hr (k := 0) (by simp [hashSys, Msg.msg, Msg.lookups])
  have hm : siteMult hashSys inst pub (2, r, 0) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr, hd]
  have hv : siteVals hashSys inst pub (2, r, 0) = [(inst 2).main Msg.POS r, (inst 2).main Msg.BYTE r] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]
  exact hash_read hL hsat hL24 hs0 (by decide) (by simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups]) hm hv

/-- **A message's transaction tuple comes from the fields.** A non-header message start reads its
tuple `tx(i, a, seg, w, l)` from a fields row yielding it (lock-time row, multiplicity `K_LOCK · TXM`). -/
theorem msg_tuple_linked (hL24 : L ≤ 24) {r : ℕ} (hr : r < 2 ^ L) (hf : (inst 2).main Msg.FIRSTM r = 1)
    (hh : (inst 2).main Msg.HDR r = 0) :
    ∃ r' < 2 ^ L, siteMult hashSys inst pub (1, r', 7) ≠ 0 ∧
      siteVals hashSys inst pub (1, r', 7) = siteVals hashSys inst pub (2, r, 1) := by
  have hs1 := site_mem hL (i := 2) (by decide) hr (k := 1) (by simp [hashSys, Msg.msg, Msg.lookups])
  have hm : siteMult hashSys inst pub (2, r, 1) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k, Msg.om,
      Msg.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr, hf, hh]
  obtain ⟨i, r', k, hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs1 rfl hm
  have e : siteRel hashSys (2, r, 1) = 4 := rfl
  rw [e, yt] at hy
  obtain ⟨rfl, rfl⟩ : i = 1 ∧ k = 7 := by omega
  exact ⟨r', hr', hsm, hsv⟩

/-- The tuple a non-header message start reads, from the fields' lock-time row of its transaction. -/
theorem msg_tuple_row (hL24 : L ≤ 24) {r : ℕ} (hr : r < 2 ^ L) (hf : (inst 2).main Msg.FIRSTM r = 1)
    (hh : (inst 2).main Msg.HDR r = 0) :
    ∃ ρ < 2 ^ L, (inst 1).main Fields.K_LOCK ρ = 1 ∧
      (inst 1).main Fields.TXI ρ = (inst 2).main Msg.TI r ∧ (inst 1).main Fields.TXA ρ = (inst 2).main Msg.TA r ∧
      (inst 1).main Fields.SEG ρ = (inst 2).main Msg.SEG r ∧ (inst 1).main Fields.WST ρ = (inst 2).main Msg.TW r ∧
      (inst 1).main Fields.START ρ = (inst 2).main Msg.TL r := by
  obtain ⟨ρ, hρ, hm, hv⟩ := msg_tuple_linked hL hsat hL24 hr hf hh
  have fs := hash_fields_sat' hL hsat
  have hlock : (inst 1).main Fields.K_LOCK ρ = 1 := by
    have hm' : (inst 1).main Fields.K_LOCK ρ * (inst 1).main Fields.TXM ρ ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Expr.eval,
        Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hρ] using hm
    rcases Fields.kind_bool fs (c := Fields.K_LOCK) (by simp [Fields.kinds]) hρ with h | h
    · rw [h, zero_mul] at hm'; exact absurd rfl hm'
    · exact h
  have e1 : siteVals hashSys inst pub (1, ρ, 7) = [(inst 1).main Fields.TXI ρ, (inst 1).main Fields.TXA ρ,
      (inst 1).main Fields.SEG ρ, (inst 1).main Fields.WST ρ, (inst 1).main Fields.START ρ] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups, Fields.k,
      StarkedAir.Sha256.eval_col, wrap_zero hρ]
  have e2 : siteVals hashSys inst pub (2, r, 1) = [(inst 2).main Msg.TI r, (inst 2).main Msg.TA r,
      (inst 2).main Msg.SEG r, (inst 2).main Msg.TW r, (inst 2).main Msg.TL r] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]
  rw [e1, e2] at hv
  simp only [List.cons.injEq, and_true] at hv
  exact ⟨ρ, hρ, hlock, hv.1, hv.2.1, hv.2.2.1, hv.2.2.2.1, hv.2.2.2.2⟩

/-- The header message's tuple: `TA = 0`, `TL = 76`, `WTX = 0`. -/
theorem hdr_tuple {r : ℕ} (hr : r < 2 ^ L) (hh : (inst 2).main Msg.HDR r = 1) :
    (inst 2).main Msg.TA r = 0 ∧ (inst 2).main Msg.TL r = 76 ∧ (inst 2).main Msg.WTX r = 0 := by
  have ms := hash_msg_sat hL hsat
  have c := fun (e : Expr) (h : e ∈ Msg.msgC) => Msg.sat ms (Msg.mem_msgC h) hr
  have h1 := c (.mul (Msg.k Msg.HDR) (Msg.k Msg.TA)) (by simp [Msg.msgC])
  have h2 := c (.mul (Msg.k Msg.HDR) (.sub (Msg.k Msg.TL) (cst 76))) (by simp [Msg.msgC])
  have h3 := c (.mul (Msg.k Msg.WTX) (Msg.k Msg.HDR)) (by simp [Msg.msgC])
  simp only [Expr.eval, Msg.ev_k hr, hh, one_mul, mul_one, StarkedAir.Sha256.eval_cst, sub_eq_zero] at h1 h2 h3
  exact ⟨h1, by rw [h2]; norm_num, h3⟩

/-- **One tuple per message id.** Two message starts with the same id agree on the header flag, the
wtxid flag and the data range `TA`, `TL`; non-header ones also on `SEG` and `TW`. -/
theorem mid_tuple (hL24 : L ≤ 24) {r0 r1 : ℕ} (h0 : r0 < 2 ^ L) (h1 : r1 < 2 ^ L)
    (f0 : (inst 2).main Msg.FIRSTM r0 = 1) (f1 : (inst 2).main Msg.FIRSTM r1 = 1)
    (hm : (inst 2).main Msg.MID r0 = (inst 2).main Msg.MID r1) :
    (inst 2).main Msg.HDR r0 = (inst 2).main Msg.HDR r1 ∧ (inst 2).main Msg.WTX r0 = (inst 2).main Msg.WTX r1 ∧
      (inst 2).main Msg.TA r0 = (inst 2).main Msg.TA r1 ∧ (inst 2).main Msg.TL r0 = (inst 2).main Msg.TL r1 ∧
      ((inst 2).main Msg.HDR r0 = 0 →
        (inst 2).main Msg.SEG r0 = (inst 2).main Msg.SEG r1 ∧ (inst 2).main Msg.TW r0 = (inst 2).main Msg.TW r1) := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have hP : 2 ^ L < P := by have := hash_rows_lt_P hL24; omega
  have h25 : 2 ^ L ≤ 2 ^ 24 := Nat.pow_le_pow_right (by norm_num) hL24
  norm_num at h25
  rw [Msg.mid_eq ms h0, Msg.mid_eq ms h1] at hm
  -- a non-header message: its lock-time row `ρ` and its id as a natural number
  have nat_id : ∀ {r}, r < 2 ^ L → (inst 2).main Msg.FIRSTM r = 1 → (inst 2).main Msg.HDR r = 0 →
      ∃ ρ < 2 ^ L, ∃ w ≤ 1, (inst 1).main Fields.K_LOCK ρ = 1 ∧
        (1 + 2 * (inst 2).main Msg.TI r + (inst 2).main Msg.WTX r) =
          ((1 + 2 * Fields.locks (inst 1).main ρ + w : ℕ) : F) ∧ (inst 2).main Msg.WTX r = (w : F) ∧
        Fields.locks (inst 1).main ρ ≤ ρ ∧
        (inst 1).main Fields.TXA ρ = (inst 2).main Msg.TA r ∧ (inst 1).main Fields.SEG ρ = (inst 2).main Msg.SEG r ∧
        (inst 1).main Fields.WST ρ = (inst 2).main Msg.TW r ∧ (inst 1).main Fields.START ρ = (inst 2).main Msg.TL r := by
    intro r hr hf hh
    obtain ⟨ρ, hρ, hl, ti, ta, sg, tw, tl⟩ := msg_tuple_row hL hsat hL24 hr hf hh
    have hw := Fields.bool_val (Msg.bool_col ms (e := Msg.WTX) (by simp) hr)
    refine ⟨ρ, hρ, ((inst 2).main Msg.WTX r).val, hw.2, hl, ?_, hw.1, Fields.locks_le ρ, ta, sg, tw, tl⟩
    rw [← ti, Fields.txi_count fs ρ hρ]; push_cast; rw [← hw.1]
  have pos_id : ∀ {r}, r < 2 ^ L → (inst 2).main Msg.FIRSTM r = 1 → (inst 2).main Msg.HDR r = 0 →
      (1 - (inst 2).main Msg.HDR r) * (1 + 2 * (inst 2).main Msg.TI r + (inst 2).main Msg.WTX r) ≠ 0 := by
    intro r hr hf hh e
    obtain ⟨ρ, hρ, w, hw, -, e0, -, b0, -⟩ := nat_id hr hf hh
    rw [hh, sub_zero, one_mul, e0] at e
    have hb : 1 + 2 * Fields.locks (inst 1).main ρ + w ≤ 2 ^ 30 := by
      have := b0; have := hρ; omega
    have := natCast_inj_of_lt (b := 0) (Fields.lt_P hb) (by unfold P; norm_num) (by rw [e]; simp)
    omega
  rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h0 with a0 | a0 <;>
    rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h1 with a1 | a1
  · obtain ⟨ρ0, hρ0, w0, hw0, l0, e0, x0, b0, ta0, sg0, tw0, tl0⟩ := nat_id h0 f0 a0
    obtain ⟨ρ1, hρ1, w1, hw1, l1, e1, x1, b1, ta1, sg1, tw1, tl1⟩ := nat_id h1 f1 a1
    rw [a0, a1, sub_zero, one_mul, one_mul, e0, e1] at hm
    have hn := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) hm
    have hw : w0 = w1 := by omega
    have hl : Fields.locks (inst 1).main ρ0 = Fields.locks (inst 1).main ρ1 := by omega
    have hρ : ρ0 = ρ1 := Fields.lock_unique fs hP hρ0 hρ1 l0 l1
      (by rw [Fields.txi_count fs ρ0 hρ0, Fields.txi_count fs ρ1 hρ1, hl])
    subst hρ hw
    exact ⟨a0.trans a1.symm, x0.trans x1.symm, ta0.symm.trans ta1, tl0.symm.trans tl1,
      fun _ => ⟨sg0.symm.trans sg1, tw0.symm.trans tw1⟩⟩
  · exact absurd (by rw [hm, a1]; ring) (pos_id h0 f0 a0)
  · exact absurd (by rw [← hm, a0]; ring) (pos_id h1 f1 a1)
  · obtain ⟨ta0, tl0, w0⟩ := hdr_tuple hL hsat h0 a0
    obtain ⟨ta1, tl1, w1⟩ := hdr_tuple hL hsat h1 a1
    exact ⟨a0.trans a1.symm, w0.trans w1.symm, ta0.trans ta1.symm, tl0.trans tl1.symm,
      fun h => absurd (h.symm.trans a0) zero_ne_one⟩

/-- **One message per id.** Two message starts with the same id have the same data length and the
same data bytes. -/
theorem same_bytes (hL24 : L ≤ 24) {r0 r1 d0 d1 : ℕ} (h0 : r0 < 2 ^ L) (h1 : r1 < 2 ^ L)
    (f0 : (inst 2).main Msg.FIRSTM r0 = 1) (f1 : (inst 2).main Msg.FIRSTM r1 = 1)
    (hm : (inst 2).main Msg.MID r0 = (inst 2).main Msg.MID r1)
    (hc0 : ∀ j < d0, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d0) = 1)
    (hc1 : ∀ j < d1, (inst 2).main Msg.CONT (r1 + j) = 1 ∨ (inst 2).main Msg.SW (r1 + j) = 1)
    (he1 : (inst 2).main Msg.ENDD (r1 + d1) = 1) :
    d0 = d1 ∧ ∀ j ≤ d0, (inst 2).main Msg.BYTE (r0 + j) = (inst 2).main Msg.BYTE (r1 + j) := by
  have ms := hash_msg_sat hL hsat
  obtain ⟨hh, hw, ta, tl, rest⟩ := mid_tuple hL hsat hL24 h0 h1 f0 f1 hm
  have hmt : (inst 2).main Msg.MT r0 = (inst 2).main Msg.MT r1 ∧
      ((inst 2).main Msg.MT r0 = 1 → (inst 2).main Msg.TW r0 = (inst 2).main Msg.TW r1) := by
    rw [Msg.mt_eq ms h0, Msg.mt_eq ms h1]
    rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h0 with a | a
    · obtain ⟨sg, tw⟩ := rest a
      exact ⟨by rw [hw, hh, sg], fun _ => tw⟩
    · obtain ⟨-, -, w0⟩ := hdr_tuple hL hsat h0 a
      obtain ⟨-, -, w1⟩ := hdr_tuple hL hsat h1 (hh ▸ a)
      rw [a, w0, ← hh, a, w1]
      exact ⟨by ring, fun h => by simp at h⟩
  obtain ⟨hd, hpos⟩ := Msg.same_layout ms h0 h1 f0 f1 hc0 he0 hc1 he1 hmt.1 ta hmt.2 tl
  refine ⟨hd, fun j hj => ?_⟩
  obtain ⟨l0, dd0, -⟩ := Msg.data_walk ms h0 f0 j (fun i hi => hc0 i (by omega))
  obtain ⟨l1, dd1, -⟩ := Msg.data_walk ms h1 f1 j (fun i hi => hc1 i (by omega))
  obtain ⟨ρ0, hρ0, p0, b0⟩ := msg_read hL hsat hL24 l0 dd0
  obtain ⟨ρ1, hρ1, p1, b1⟩ := msg_read hL hsat hL24 l1 dd1
  have hρ : ρ0 = ρ1 := by
    have := ZMod.val_lt (pub 0)
    exact natCast_inj_of_lt (by omega) (by omega) (p0.symm.trans ((hpos j hj).trans p1))
  rw [b0, b1, hρ]

end System

end StarkedAir.Block
