/-
**The block hashing system (M3a.3, linking).** Components, in the prover's order: bytes (0), fields (1),
messages (2), SHA (3), all at one `log_size`. This file links their lookups: SHA's message words and
padded lengths come from the message component, whose bytes come from the byte table.
-/
import StarkedAir.Block.MsgSound
import StarkedAir.Block.ShaSound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

def hashSys : System := ⟨4, fun i => if i = 0 then bytes else if i = 1 then Fields.fields else if i = 2 then Msg.msg else Sha.sha⟩

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 4, (inst i).logSize = L) (hL25 : L ≤ 25)
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

omit hsat in
/-- 16 lookup sites per row: bytes 1, fields 8, messages 4, SHA 3. -/
theorem hash_sites_len : (sites hashSys inst).length = 16 * 2 ^ L := by
  simp [sites, hashSys, hL 0 (by decide), hL 1 (by decide), hL 2 (by decide), hL 3 (by decide),
    List.length_flatMap, bytes, Fields.fields, Fields.lookups, Msg.msg, Msg.lookups, Sha.sha, Sha.lookups,
    List.sum_range_succ]
  ring

omit hsat in
theorem hash_rows_lt_P (hL25 : L ≤ 25) : 16 * 2 ^ L < P :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 16 (Nat.pow_le_pow_right (by norm_num) hL25)) (by unfold P; norm_num)

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
    · rw [one_mul, hu]
      rcases hd with d | d <;> rcases hn with e | e <;> simp_all
  · refine hb ?_
    simp only [Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, Sha.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr]
    rcases hpre (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl (fun q => by split_ifs <;> omega)
      with m | m <;> rw [m]
    · simp
    · rw [one_mul]; exact hd

/-- **SHA's uses are message yields.** A SHA word use (`kk = 0`) or length use (`kk = 1`) with
multiplicity `−1` is matched by a message row yielding the same tuple (message lookup `kk + 2`). -/
theorem sha_use_linked (hL25 : L ≤ 25) {r : ℕ} (hr : r < 2 ^ L) {kk : ℕ} (hk : kk < 2)
    (hm : siteMult hashSys inst pub (3, r, kk) = -1) :
    ∃ r' < 2 ^ L, siteMult hashSys inst pub (2, r', kk + 2) ≠ 0 ∧
      siteVals hashSys inst pub (2, r', kk + 2) = siteVals hashSys inst pub (3, r, kk) := by
  classical
  have h3 : hashSys.comp 3 = Sha.sha := rfl
  have h2 : hashSys.comp 2 = Msg.msg := rfl
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 4 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have hs1 : ((3, r, kk) : Site) ∈ sites hashSys inst :=
    mem.mpr ⟨by decide, hr, by rw [h3]; simp [Sha.sha, Sha.lookups]; omega⟩
  obtain ⟨s, hs, hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2 (use := fun i k => i = 3 ∧ k < 2)
    (fun s hs hu => by
      obtain ⟨i, r', k⟩ := s
      obtain ⟨rfl, hk'⟩ := hu
      have hr' := (mem.mp hs).2.1
      have := sha_use_mult hL hsat hr' hk'
      simpa [siteMult, siteEval, siteLookup, h3, Sha.sha, hL 3 (by decide)] using this)
    (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide (s.1 = 3 ∧ s.2.2 < 2)) (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL hL25
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨(3, r, kk), hs1, ⟨rfl, hk⟩, hm, rfl, rfl⟩)
  obtain ⟨i, r', k⟩ := s
  obtain ⟨hi, hr', hk'⟩ := mem.mp hs
  refine ⟨r', hr', ?_⟩
  -- the matching site has SHA's relation (5 or 6): only message lookup `kk + 2`
  have hrel : siteRel hashSys (i, r', k) = siteRel hashSys (3, r, kk) := hsr
  have hik : i = 2 ∧ k = kk + 2 := by
    interval_cases i
    · simp [hashSys, bytes] at hk'; subst hk'
      interval_cases kk <;> simp [siteRel, siteLookup, hashSys, bytes, Sha.sha, Sha.lookups, REL_BYTE,
        Msg.REL_MSGW, Msg.REL_MLEN] at hrel
    · simp [hashSys, Fields.fields, Fields.lookups] at hk'
      interval_cases k <;> interval_cases kk <;> simp [siteRel, siteLookup, hashSys, Fields.fields, Fields.lookups,
        Sha.sha, Sha.lookups, REL_BYTE, Fields.REL_TX, Msg.REL_MSGW, Msg.REL_MLEN] at hrel
    · simp [hashSys, Msg.msg, Msg.lookups] at hk'
      interval_cases k <;> interval_cases kk <;> first | exact ⟨rfl, rfl⟩ | simp [siteRel, siteLookup, hashSys, Msg.msg,
        Msg.lookups, Sha.sha, Sha.lookups, REL_BYTE, Fields.REL_TX, Msg.REL_MSGW, Msg.REL_MLEN] at hrel
    · simp [hashSys, Sha.sha, Sha.lookups] at hk'
      interval_cases k
      · exact absurd ⟨rfl, by norm_num⟩ hnu
      · exact absurd ⟨rfl, by norm_num⟩ hnu
      · interval_cases kk <;> simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
          Sha.REL_DIGEST] at hrel
  obtain ⟨rfl, rfl⟩ := hik
  exact ⟨hsm, hsv⟩

/-- **SHA message words are message bytes.** At a SHA message row `x` (rows 4..19 of a period) of a
period that reads words, the word limbs are bytes `j − 3 .. j` (big-endian) of a message starting at
message row `r0`, with the same id, where `j − 3 = 64 · BLKI + 4 · (row − 4)`. -/
theorem sha_word (hL25 : L ≤ 25) {x : ℕ} (hx : x < 2 ^ L)
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
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false]
    simp only [Sha.sha, Sha.lookups, List.getD_cons_zero, Expr.eval]
    rw [show Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (pre Sha.MSGROW) *
      Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (Sha.k Sha.USEW) = 1 from hm]
  obtain ⟨r', hr', hym, hyv⟩ := sha_use_linked hL hsat hL25 hx (kk := 0) (by norm_num) hm'
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
theorem sha_len (hL25 : L ≤ 25) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.DBL)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1) :
    ∃ r0 d, (inst 2).main Msg.FIRSTM r0 = 1 ∧ (inst 2).main Msg.ENDD (r0 + d) = 1 ∧
      (∀ j < d, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1) ∧
      (inst 2).main Msg.MID r0 = (inst 3).main Sha.MID x ∧
      (((r0 + d + 1 + 1 + (119 - (r0 + d + 1) % 64) % 64 + 7) + 1 - r0 : ℕ) : F) =
        (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main x := by
  have hm' : siteMult hashSys inst pub (3, x, 1) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide)]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false]
    simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval]
    rw [show Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (pre Sha.ROW0) *
      Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (Sha.k Sha.DBL) = 1 from hm]
  obtain ⟨r', hr', hym, hyv⟩ := sha_use_linked hL hsat hL25 hx (kk := 1) (by norm_num) hm'
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
  refine ⟨r0, d, hf, he, hc, hmid.symm.trans e1, ?_⟩
  rw [← heq, ← e2, hidx]

end System

end StarkedAir.Block
