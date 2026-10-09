/-
**The block hashing system (M3a.3, linking).** Components, in the prover's order: bytes (0), fields (1),
messages (2), SHA (3), all at one `log_size`. This file links their lookups: SHA's message words and
padded lengths come from the message component, whose bytes come from the byte table.
-/
import StarkedAir.Block.MsgSound
import StarkedAir.Block.ShaSound
import StarkedAir.Block.TxIndex
import StarkedAir.Block.MerkleSound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)

def hashSys : System :=
  ⟨5, fun i => if i = 0 then bytes else if i = 1 then Fields.fields else if i = 2 then Msg.msg else if i = 3 then Sha.sha
    else Merkle.merkle⟩

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 5, (inst i).logSize = L) (hL25 : L ≤ 25)
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

omit hsat in
/-- 30 lookup sites per row: bytes 1, fields 8, messages 4, SHA 6, Merkle 11. -/
theorem hash_sites_len : (sites hashSys inst).length = 30 * 2 ^ L := by
  simp [sites, hashSys, hL 0 (by decide), hL 1 (by decide), hL 2 (by decide), hL 3 (by decide), hL 4 (by decide),
    List.length_flatMap, bytes, Fields.fields, Fields.lookups, Msg.msg, Msg.lookups, Sha.sha, Sha.lookups,
    Merkle.merkle, Merkle.lookups, List.sum_range_succ]
  ring

omit hsat in
theorem hash_rows_lt_P (hL25 : L ≤ 25) : 30 * 2 ^ L < P :=
  lt_of_le_of_lt (Nat.mul_le_mul_left 30 (Nat.pow_le_pow_right (by norm_num) hL25)) (by unfold P; norm_num)

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

/-- **SHA's uses are message (or Merkle) yields.** A SHA word use (`kk = 0`) or length use (`kk = 1`)
with multiplicity `−1` is matched by a message row yielding the same tuple (message lookup `kk + 2`) or,
for a length, by a Merkle node row (Merkle lookup 1). -/
theorem sha_use_linked (hL25 : L ≤ 25) {r : ℕ} (hr : r < 2 ^ L) {kk : ℕ} (hk : kk < 2)
    (hm : siteMult hashSys inst pub (3, r, kk) = -1) :
    ∃ r' < 2 ^ L, (siteMult hashSys inst pub (2, r', kk + 2) ≠ 0 ∧
      siteVals hashSys inst pub (2, r', kk + 2) = siteVals hashSys inst pub (3, r, kk)) ∨
      (kk = 1 ∧ siteMult hashSys inst pub (4, r', 1) ≠ 0 ∧
        siteVals hashSys inst pub (4, r', 1) = siteVals hashSys inst pub (3, r, kk)) := by
  classical
  have h3 : hashSys.comp 3 = Sha.sha := rfl
  have h4 : hashSys.comp 4 = Merkle.merkle := rfl
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 5 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have hs1 : ((3, r, kk) : Site) ∈ sites hashSys inst :=
    mem.mpr ⟨by decide, hr, by rw [h3]; simp [Sha.sha, Sha.lookups]; omega⟩
  have ks := hash_merkle_sat hL hsat
  obtain ⟨s, hs, hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2
    (use := fun i k => (i = 3 ∧ k < 2) ∨ (i = 4 ∧ 3 ≤ k))
    (fun s hs hu => by
      obtain ⟨i, r', k⟩ := s
      have hr' := (mem.mp hs).2.1
      rcases hu with ⟨rfl, hk'⟩ | ⟨rfl, hk3⟩
      · have := sha_use_mult hL hsat hr' hk'
        simpa [siteMult, siteEval, siteLookup, h3, Sha.sha, hL 3 (by decide)] using this
      · have hk11 : k < 11 := by have := (mem.mp hs).2.2; simpa [h4, Merkle.merkle, Merkle.lookups] using this
        have hrt := Merkle.kbool ks (c := Merkle.RT) (by simp) hr'
        have e : siteMult hashSys inst pub (4, r', k) = -((inst 4).main Merkle.RT r') := by
          simp only [siteMult, siteEval, siteLookup, h4, hL 4 (by decide)]
          interval_cases k <;> simp [Merkle.merkle, Merkle.lookups, Expr.eval, Merkle.ev_k hr']
        rw [e]; rcases hrt with h | h <;> simp [h])
    (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide ((s.1 = 3 ∧ s.2.2 < 2) ∨ (s.1 = 4 ∧ 3 ≤ s.2.2)))
        (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL hL25
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨(3, r, kk), hs1, Or.inl ⟨rfl, hk⟩, hm, rfl, rfl⟩)
  obtain ⟨i, r', k⟩ := s
  obtain ⟨hi, hr', hk'⟩ := mem.mp hs
  refine ⟨r', hr', ?_⟩
  have hrel : siteRel hashSys (i, r', k) = siteRel hashSys (3, r, kk) := hsr
  interval_cases i
  · simp [hashSys, bytes] at hk'; subst hk'
    interval_cases kk <;> simp [siteRel, siteLookup, hashSys, bytes, Sha.sha, Sha.lookups, REL_BYTE,
      Msg.REL_MSGW, Msg.REL_MLEN] at hrel
  · simp [hashSys, Fields.fields, Fields.lookups] at hk'
    interval_cases k <;> interval_cases kk <;> simp [siteRel, siteLookup, hashSys, Fields.fields, Fields.lookups,
      Sha.sha, Sha.lookups, REL_BYTE, Fields.REL_TX, Msg.REL_MSGW, Msg.REL_MLEN] at hrel
  · simp [hashSys, Msg.msg, Msg.lookups] at hk'
    interval_cases k <;> interval_cases kk <;> first | exact Or.inl ⟨hsm, hsv⟩ | simp [siteRel, siteLookup, hashSys,
      Msg.msg, Msg.lookups, Sha.sha, Sha.lookups, REL_BYTE, Fields.REL_TX, Msg.REL_MSGW, Msg.REL_MLEN] at hrel
  · simp [hashSys, Sha.sha, Sha.lookups] at hk'
    interval_cases k
    · exact absurd (Or.inl ⟨rfl, by norm_num⟩) hnu
    · exact absurd (Or.inl ⟨rfl, by norm_num⟩) hnu
    all_goals interval_cases kk <;> simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
      Sha.REL_DIGEST, Sha.REL_NODE] at hrel
  · simp [hashSys, Merkle.merkle, Merkle.lookups] at hk'
    interval_cases k
    · interval_cases kk <;> simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Sha.sha, Sha.lookups,
        Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_NODE] at hrel
    · interval_cases kk
      · simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Sha.sha, Sha.lookups, Msg.REL_MSGW,
          Msg.REL_MLEN] at hrel
      · exact Or.inr ⟨rfl, hsm, hsv⟩
    · interval_cases kk <;> simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Sha.sha, Sha.lookups,
        Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_DIGEST] at hrel
    all_goals exact absurd (Or.inr ⟨rfl, by norm_num⟩) hnu

/-- **A node block's id is a Merkle node id** (at least `NB`): its node tuple is yielded only by the Merkle
component, whose ids are `NB + row`. -/
theorem node_mid (hL25 : L ≤ 25) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1) :
    Merkle.NB ≤ ((inst 3).main Sha.MID x).val := by
  classical
  have h3 : hashSys.comp 3 = Sha.sha := rfl
  have h4 : hashSys.comp 4 = Merkle.merkle := rfl
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 5 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have ss := hash_sha_sat hL hsat
  have hs1 : ((3, x, 3) : Site) ∈ sites hashSys inst := mem.mpr ⟨by decide, hx, by simp [h3, Sha.sha, Sha.lookups]⟩
  have multv : ∀ r < 2 ^ L, siteMult hashSys inst pub (3, r, 3) =
      -((Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main r) := by
    intro r hr; simp [siteMult, siteEval, siteLookup, h3, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval]
  have hm1 : siteMult hashSys inst pub (3, x, 3) = -1 := by rw [multv x hx, hm]
  obtain ⟨s', hs', hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2 (use := fun i k => i = 3 ∧ k = 3)
    (fun s hs hu => by
      obtain ⟨i, r', k⟩ := s
      obtain ⟨rfl, rfl⟩ := hu
      have hr' := (mem.mp hs).2.1
      rw [multv r' hr']
      have hn := Sha.kbool ss (c := Sha.NODE) (by simp) hr'
      have hr0 : (pre Sha.ROW0).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 0 ∨
          (pre Sha.ROW0).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 1 := by
        rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hr']
        split_ifs <;> simp
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hr']
      rcases hr0 with a | a <;> rcases hn with b | b <;> simp [a, b])
    (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide (s.1 = 3 ∧ s.2.2 = 3)) (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL hL25
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨(3, x, 3), hs1, ⟨rfl, rfl⟩, hm1, rfl, rfl⟩)
  obtain ⟨i, r', k⟩ := s'
  obtain ⟨hi, hr', hk'⟩ := mem.mp hs'
  have hrel : siteRel hashSys (i, r', k) = Sha.REL_NODE := by
    rw [hsr]; simp [siteRel, siteLookup, h3, Sha.sha, Sha.lookups]
  have hik : i = 4 ∧ k = 0 := by
    interval_cases i
    · simp [hashSys, bytes] at hk'; subst hk'
      simp [siteRel, siteLookup, hashSys, bytes, REL_BYTE, Sha.REL_NODE] at hrel
    · simp [hashSys, Fields.fields, Fields.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Fields.fields, Fields.lookups, REL_BYTE, Fields.REL_TX,
        Sha.REL_NODE] at hrel
    · simp [hashSys, Msg.msg, Msg.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups, REL_BYTE, Fields.REL_TX,
        Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_NODE] at hrel
    · simp [hashSys, Sha.sha, Sha.lookups] at hk'
      interval_cases k
      any_goals simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_DIGEST,
        Sha.REL_NODE] at hrel
      exact absurd ⟨rfl, rfl⟩ hnu
    · simp [hashSys, Merkle.merkle, Merkle.lookups] at hk'
      interval_cases k
      · exact ⟨rfl, rfl⟩
      all_goals simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
        Sha.REL_DIGEST, Sha.REL_NODE] at hrel
  obtain ⟨rfl, rfl⟩ := hik
  have hv4 : siteVals hashSys inst pub (4, r', 0) = [(Merkle.NB : F) + (inst 4).main Merkle.RIX r',
      (inst 4).main Merkle.LEFT r', (inst 4).main Merkle.RIGHT r', (inst 4).main Merkle.DUP r'] := by
    simp [siteVals, siteEval, siteLookup, h4, hL 4 (by decide), Merkle.merkle, Merkle.lookups, Merkle.nodeId, Merkle.k,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
  have hv3 : (siteVals hashSys inst pub (3, x, 3)).head? = some ((inst 3).main Sha.MID x) := by
    simp [siteVals, siteEval, siteLookup, h3, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  rw [← hsv, hv4] at hv3
  simp only [List.head?_cons, Option.some.injEq] at hv3
  rw [Merkle.rix_eq (hash_merkle_sat hL hsat) r' hr'] at hv3
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
  rw [← hv3, show ((Merkle.NB : ℕ) : F) + (r' : F) = ((Merkle.NB + r' : ℕ) : F) by push_cast; ring,
    ZMod.val_natCast_of_lt (Fields.lt_P (by unfold Merkle.NB; norm_num at h25 ⊢; omega))]
  omega

/-- **A node block's tuple is a Merkle node row's**: `MID = NB + r'`, children and `dup` as on row `r'`. -/
theorem node_row (hL25 : L ≤ 25) {x : ℕ} (hx : x < 2 ^ L)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main x = 1) :
    ∃ r' < 2 ^ L, (inst 4).main Merkle.ACTN r' = 1 ∧
      (inst 3).main Sha.MID x = ((Merkle.NB + r' : ℕ) : F) ∧ (inst 3).main Sha.LID x = (inst 4).main Merkle.LEFT r' ∧
      (inst 3).main Sha.RID x = (inst 4).main Merkle.RIGHT r' ∧ (inst 3).main Sha.NDUP x = (inst 4).main Merkle.DUP r' := by
  classical
  have h3 : hashSys.comp 3 = Sha.sha := rfl
  have h4 : hashSys.comp 4 = Merkle.merkle := rfl
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 5 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have ss := hash_sha_sat hL hsat
  have hs1 : ((3, x, 3) : Site) ∈ sites hashSys inst := mem.mpr ⟨by decide, hx, by simp [h3, Sha.sha, Sha.lookups]⟩
  have multv : ∀ r < 2 ^ L, siteMult hashSys inst pub (3, r, 3) =
      -((Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ L) Sha.preCols pub (inst 3).main r) := by
    intro r hr; simp [siteMult, siteEval, siteLookup, h3, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval]
  have hm1 : siteMult hashSys inst pub (3, x, 3) = -1 := by rw [multv x hx, hm]
  obtain ⟨s', hs', hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2 (use := fun i k => i = 3 ∧ k = 3)
    (fun s hs hu => by
      obtain ⟨i, r', k⟩ := s
      obtain ⟨rfl, rfl⟩ := hu
      have hr' := (mem.mp hs).2.1
      rw [multv r' hr']
      have hn := Sha.kbool ss (c := Sha.NODE) (by simp) hr'
      have hr0 : (pre Sha.ROW0).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 0 ∨
          (pre Sha.ROW0).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 1 := by
        rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hr']
        split_ifs <;> simp
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hr']
      rcases hr0 with a | a <;> rcases hn with b | b <;> simp [a, b])
    (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide (s.1 = 3 ∧ s.2.2 = 3)) (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL hL25
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨(3, x, 3), hs1, ⟨rfl, rfl⟩, hm1, rfl, rfl⟩)
  obtain ⟨i, r', k⟩ := s'
  obtain ⟨hi, hr', hk'⟩ := mem.mp hs'
  have hrel : siteRel hashSys (i, r', k) = Sha.REL_NODE := by
    rw [hsr]; simp [siteRel, siteLookup, h3, Sha.sha, Sha.lookups]
  have hik : i = 4 ∧ k = 0 := by
    interval_cases i
    · simp [hashSys, bytes] at hk'; subst hk'
      simp [siteRel, siteLookup, hashSys, bytes, REL_BYTE, Sha.REL_NODE] at hrel
    · simp [hashSys, Fields.fields, Fields.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Fields.fields, Fields.lookups, REL_BYTE, Fields.REL_TX,
        Sha.REL_NODE] at hrel
    · simp [hashSys, Msg.msg, Msg.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups, REL_BYTE, Fields.REL_TX,
        Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_NODE] at hrel
    · simp [hashSys, Sha.sha, Sha.lookups] at hk'
      interval_cases k
      any_goals simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_DIGEST,
        Sha.REL_NODE] at hrel
      exact absurd ⟨rfl, rfl⟩ hnu
    · simp [hashSys, Merkle.merkle, Merkle.lookups] at hk'
      interval_cases k
      · exact ⟨rfl, rfl⟩
      all_goals simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
        Sha.REL_DIGEST, Sha.REL_NODE] at hrel
  obtain ⟨rfl, rfl⟩ := hik
  have hv4 : siteVals hashSys inst pub (4, r', 0) = [(Merkle.NB : F) + (inst 4).main Merkle.RIX r',
      (inst 4).main Merkle.LEFT r', (inst 4).main Merkle.RIGHT r', (inst 4).main Merkle.DUP r'] := by
    simp [siteVals, siteEval, siteLookup, h4, hL 4 (by decide), Merkle.merkle, Merkle.lookups, Merkle.nodeId, Merkle.k,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
  have hv3 : siteVals hashSys inst pub (3, x, 3) = [(inst 3).main Sha.MID x, (inst 3).main Sha.LID x,
      (inst 3).main Sha.RID x, (inst 3).main Sha.NDUP x] := by
    simp [siteVals, siteEval, siteLookup, h3, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  rw [hv4, hv3] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨e1, e2, e3, e4⟩ := hsv
  rw [Merkle.rix_eq (hash_merkle_sat hL hsat) r' hr'] at e1
  have hact : (inst 4).main Merkle.ACTN r' = 1 := by
    have hm4 : (inst 4).main Merkle.ACTN r' * (inst 4).main Merkle.NM r' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, h4, hL 4 (by decide), Merkle.merkle, Merkle.lookups, Expr.eval, Merkle.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
    rcases Merkle.kbool (hash_merkle_sat hL hsat) (c := Merkle.ACTN) (by simp) hr' with h | h
    · rw [h, zero_mul] at hm4; exact absurd rfl hm4
    · exact h
  exact ⟨r', hr', hact, by rw [← e1]; push_cast; ring, e2.symm, e3.symm, e4.symm⟩

/-- **Digest uses are second hashes' outputs.** A digest use (a node block's child read, `SHA` lookups 4–5,
or the root row's read, Merkle lookup 2) with multiplicity `−1` reads the tuple yielded at the last row of
a second-hash period `q'`. -/
theorem digest_linked (hL25 : L ≤ 25) {i r k : ℕ} (hu : (i = 3 ∧ (k = 4 ∨ k = 5)) ∨ (i = 4 ∧ k = 2))
    (hr : r < 2 ^ L) (hm : siteMult hashSys inst pub (i, r, k) = -1) :
    ∃ q', 72 * q' + 72 ≤ 2 ^ L ∧ (inst 3).main Sha.DBL (72 * q') = 1 ∧
      siteVals hashSys inst pub (3, 72 * q' + 71, 2) = siteVals hashSys inst pub (i, r, k) := by
  classical
  have h3 : hashSys.comp 3 = Sha.sha := rfl
  have h4 : hashSys.comp 4 = Merkle.merkle := rfl
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 5 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have ss := hash_sha_sat hL hsat
  have ks := hash_merkle_sat hL hsat
  have hs1 : ((i, r, k) : Site) ∈ sites hashSys inst := by
    refine mem.mpr ⟨?_, hr, ?_⟩
    · rcases hu with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
    · rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ <;> (try subst h) <;> simp [h3, h4, Sha.sha, Sha.lookups, Merkle.merkle,
        Merkle.lookups]
  have pre01 : ∀ {f : ℕ → ℕ} {ii r'}, r' < 2 ^ L → Sha.preCols.getD ii (.periodic [0]) = Sha.per72 f → (∀ q, f q ≤ 1) →
      (pre ii).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 0 ∨
      (pre ii).eval (2 ^ L) Sha.preCols pub (inst 3).main r' = 1 := by
    intro f ii r' hr' hi hf
    rw [Sha.eval_per72 ss hi hr']
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hf (r' % 72)) with h | h <;> simp [h]
  obtain ⟨s', hs', hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2
    (use := fun i k => (i = 3 ∧ (k = 4 ∨ k = 5)) ∨ (i = 4 ∧ k = 2))
    (fun s hs hu' => by
      obtain ⟨i', r', k'⟩ := s
      have hr' := (mem.mp hs).2.1
      rcases hu' with ⟨rfl, hk⟩ | ⟨rfl, rfl⟩
      · have hn := Sha.kbool ss (c := Sha.NODE) (by simp) hr'
        rcases hk with rfl | rfl
        · rcases pre01 (ii := Sha.DLR) (f := fun q => if q = 11 then 1 else 0) hr' rfl (fun q => by split_ifs <;> omega)
            with a | a <;> rcases hn with b | b <;>
            simp [siteMult, siteEval, siteLookup, h3, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval, Sha.k,
              StarkedAir.Sha256.eval_col, wrap_zero hr', a, b]
        · rcases pre01 (ii := Sha.DRR) (f := fun q => if q = 19 then 1 else 0) hr' rfl (fun q => by split_ifs <;> omega)
            with a | a <;> rcases hn with b | b <;>
            simp [siteMult, siteEval, siteLookup, h3, Sha.sha, Sha.lookups, hL 3 (by decide), Expr.eval, Sha.k,
              StarkedAir.Sha256.eval_col, wrap_zero hr', a, b]
      · rcases Merkle.kbool ks (c := Merkle.RT) (by simp) hr' with a | a <;>
          simp [siteMult, siteEval, siteLookup, h4, Merkle.merkle, Merkle.lookups, hL 4 (by decide), Expr.eval,
            Merkle.k, StarkedAir.Sha256.eval_col, wrap_zero hr', a])
    (by simp)
    (by
      have := List.length_filter_le (fun s : Site => decide ((s.1 = 3 ∧ (s.2.2 = 4 ∨ s.2.2 = 5)) ∨ (s.1 = 4 ∧ s.2.2 = 2)))
        (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL hL25
      simp only [List.length_nil, add_zero]; omega)
    (Or.inl ⟨(i, r, k), hs1, hu, hm, rfl, rfl⟩)
  obtain ⟨i', r', k'⟩ := s'
  obtain ⟨hi', hr', hk'⟩ := mem.mp hs'
  have hrel : siteRel hashSys (i', r', k') = Sha.REL_DIGEST := by
    rw [hsr]; rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ <;> (try subst h) <;>
      simp [siteRel, siteLookup, h3, h4, Sha.sha, Sha.lookups, Merkle.merkle, Merkle.lookups]
  have hik : i' = 3 ∧ k' = 2 := by
    interval_cases i'
    · simp [hashSys, bytes] at hk'; subst hk'
      simp [siteRel, siteLookup, hashSys, bytes, REL_BYTE, Sha.REL_DIGEST] at hrel
    · simp [hashSys, Fields.fields, Fields.lookups] at hk'
      interval_cases k' <;> simp [siteRel, siteLookup, hashSys, Fields.fields, Fields.lookups, REL_BYTE, Fields.REL_TX,
        Sha.REL_DIGEST] at hrel
    · simp [hashSys, Msg.msg, Msg.lookups] at hk'
      interval_cases k' <;> simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups, REL_BYTE, Fields.REL_TX,
        Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_DIGEST] at hrel
    · simp [hashSys, Sha.sha, Sha.lookups] at hk'
      interval_cases k'
      any_goals simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN, Sha.REL_DIGEST,
        Sha.REL_NODE] at hrel
      · exact ⟨rfl, rfl⟩
      · exact absurd (Or.inl ⟨rfl, Or.inl rfl⟩) hnu
      · exact absurd (Or.inl ⟨rfl, Or.inr rfl⟩) hnu
    · simp [hashSys, Merkle.merkle, Merkle.lookups] at hk'
      interval_cases k'
      any_goals simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
        Sha.REL_DIGEST, Sha.REL_NODE] at hrel
      exact absurd (Or.inr ⟨rfl, rfl⟩) hnu
  obtain ⟨rfl, rfl⟩ := hik
  -- the yield row is a second hash's last row
  have hdy : (inst 3).main Sha.DBL r' * (inst 3).main Sha.YM r' ≠ 0 := by
    simpa [siteMult, siteEval, siteLookup, h3, hL 3 (by decide), Sha.sha, Sha.lookups, Expr.eval, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
  have h71 : r' % 72 = 71 := by
    have := Sha.order_sat ss (c := .mul (Sha.k Sha.YM) (Sha.om (pre Sha.FIN3))) (by simp [Sha.orderC]) hr'
    simp only [Expr.eval, Sha.k, Sha.om, Sha.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr',
      Nat.cast_one] at this
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
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, if_false, ↓reduceIte]
    simp only [Sha.sha, Sha.lookups, List.getD_cons_zero, Expr.eval]
    rw [show Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (pre Sha.MSGROW) *
      Expr.eval (2 ^ L) Sha.preCols pub (inst 3).main x (Sha.k Sha.USEW) = 1 from hm]
  obtain ⟨r', hr', hlink⟩ := sha_use_linked hL hsat hL25 hx (kk := 0) (by norm_num) hm'
  obtain ⟨hym, hyv⟩ := hlink.resolve_right (fun h => absurd h.1 (by norm_num))
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
  obtain ⟨r', hr', hlink⟩ := sha_use_linked hL hsat hL25 hx (kk := 1) (by norm_num) hm'
  have hv3' : siteVals hashSys inst pub (3, x, 1) = [(inst 3).main Sha.MID x,
      (Expr.add (.mul (cst 64) (Sha.kp Sha.BLKI)) (cst 64)).eval (2 ^ L) Sha.preCols pub (inst 3).main x] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Sha.k,
      StarkedAir.Sha256.eval_col, wrap_zero hx]
  -- not a Merkle node's length: node ids are at least `NB`
  obtain ⟨hym, hyv⟩ := hlink.resolve_right (fun hh => by
    obtain ⟨-, -, hv⟩ := hh
    have hv4 : siteVals hashSys inst pub (4, r', 1) = [(Merkle.NB : F) + (inst 4).main Merkle.RIX r', 128] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 4 (by decide), Merkle.merkle, Merkle.lookups,
        Merkle.nodeId, Merkle.k, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr', Expr.eval]
    rw [hv4, hv3'] at hv
    simp only [List.cons.injEq] at hv
    rw [Merkle.rix_eq (hash_merkle_sat hL hsat) r' hr'] at hv
    have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
    have e : ((inst 3).main Sha.MID x).val = Merkle.NB + r' := by
      rw [← hv.1, show ((Merkle.NB : ℕ) : F) + (r' : F) = ((Merkle.NB + r' : ℕ) : F) by push_cast; ring]
      exact ZMod.val_natCast_of_lt (Fields.lt_P (by unfold Merkle.NB; norm_num at h25 ⊢; omega))
    omega)
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
theorem hash_read (hL25 : L ≤ 25) {i r k : ℕ} (hs0 : ((i, r, k) : Site) ∈ sites hashSys inst) (hi : i ≠ 0)
    (hrel : siteRel hashSys (i, r, k) = REL_BYTE) (hm : siteMult hashSys inst pub (i, r, k) = -1) {p b : F}
    (hv : siteVals hashSys inst pub (i, r, k) = [p, b]) :
    ∃ r0, r0 < (pub 0).val ∧ p = (r0 : F) ∧ b = (inst 0).main BYTE r0 := by
  classical
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 5 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have hb0 : bytes.air.Satisfied (inst 0).logSize pub (inst 0).main := by
    have := hash_bytes_sat hL hsat; rw [hL 0 (by decide)]; exact this
  have hP : 2 ^ (inst 0).logSize < P := by
    rw [hL 0 (by decide)]; have := hash_rows_lt_P hL hL25; omega
  have huse : ∀ s ∈ sites hashSys inst, s.1 ≠ 0 → siteRel hashSys s = REL_BYTE →
      siteMult hashSys inst pub s = -1 ∨ siteMult hashSys inst pub s = 0 := by
    intro s hs h0 hrel
    obtain ⟨i, r', k⟩ := s
    obtain ⟨hi, hr', hk'⟩ := mem.mp hs
    simp only at h0
    interval_cases i
    · exact absurd rfl h0
    · simp [hashSys, Fields.fields, Fields.lookups] at hk'
      have hk7 : k < 7 := by
        by_contra hc
        have e7 : k = 7 := by omega
        subst e7
        simp [siteRel, siteLookup, hashSys, Fields.fields, Fields.lookups, Fields.REL_TX, REL_BYTE] at hrel
      have := Fields.mult_vals fs hr' hk7
      simpa [siteMult, siteEval, siteLookup, hashSys, Fields.fields, hL 1 (by decide)] using this
    · simp [hashSys, Msg.msg, Msg.lookups] at hk'
      interval_cases k
      · have := Msg.bool_col ms (e := Msg.D) (by simp) hr'
        simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
          StarkedAir.Sha256.eval_col, wrap_zero hr']
        rcases this with h | h <;> simp [h]
      all_goals simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups, Fields.REL_TX, Msg.REL_MSGW,
        Msg.REL_MLEN, REL_BYTE] at hrel
    · simp [hashSys, Sha.sha, Sha.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
        Sha.REL_DIGEST, Sha.REL_NODE, REL_BYTE] at hrel
    · simp [hashSys, Merkle.merkle, Merkle.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Msg.REL_MSGW,
        Msg.REL_MLEN, Sha.REL_DIGEST, Sha.REL_NODE, REL_BYTE] at hrel
  have hcount : ((sites hashSys inst).filter fun s => s.1 ≠ 0 ∧ siteRel hashSys s = REL_BYTE).length < P := by
      have := List.length_filter_le (fun s : Site => decide (s.1 ≠ 0 ∧ siteRel hashSys s = REL_BYTE)) (sites hashSys inst)
      rw [hash_sites_len hL] at this
      have := hash_rows_lt_P hL hL25
      omega
  exact read_byte hsat.2 rfl hb0 hP huse hcount hs0 hi hrel hm hv

/-- **Fields reads are the block's bytes** (the read oracle `Fields.Reads` needs, for the hashing system). -/
theorem hash_fields_read (hL25 : L ≤ 25) : ∀ {r : ℕ}, r < 2 ^ L → ∀ {kk : ℕ}, kk < 7 →
    (Fields.lookups.getD kk ⟨0, .const 0, []⟩).mult.eval (2 ^ L) Fields.preCols pub (inst 1).main r = -1 →
    ∃ r0, r0 < (pub 0).val ∧
      ((Fields.lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) Fields.preCols pub (inst 1).main r)) =
        [(r0 : F), (inst 0).main BYTE r0] := by
  intro r hr kk hk hm
  have hs1 : ((1, r, kk) : Site) ∈ sites hashSys inst := by
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨1, by decide, r, by rw [hL 1 (by decide)]; exact hr, kk,
      by simp [hashSys, Fields.fields, Fields.lookups]; omega, rfl⟩
  have hrel : siteRel hashSys ((1, r, kk) : Site) = REL_BYTE := by
    simp only [siteRel, siteLookup, hashSys, Fields.fields]; interval_cases kk <;> rfl
  have hmult : siteMult hashSys inst pub ((1, r, kk) : Site) = -1 := by
    simpa [siteMult, siteEval, siteLookup, hashSys, Fields.fields, hL 1 (by decide)] using hm
  have e : siteVals hashSys inst pub ((1, r, kk) : Site) =
      (Fields.lookups.getD kk ⟨0, .const 0, []⟩).vals.map (Expr.eval (2 ^ L) Fields.preCols pub (inst 1).main r) := by
    simp [siteVals, siteEval, siteLookup, hashSys, Fields.fields, hL 1 (by decide)]
  obtain ⟨p, b, hpb⟩ : ∃ p b, siteVals hashSys inst pub ((1, r, kk) : Site) = [p, b] := by
    simp only [siteVals, siteLookup, hashSys, Fields.fields]
    interval_cases kk <;> exact ⟨_, _, rfl⟩
  obtain ⟨r0, hr0, hp, hb⟩ := hash_read hL hsat hL25 hs1 (by decide) hrel hmult hpb
  exact ⟨r0, hr0, by rw [← e, hpb, hp, hb]⟩

/-- **Message data bytes are the block's.** A message data row reads the block byte at its position. -/
theorem msg_read (hL25 : L ≤ 25) {r : ℕ} (hr : r < 2 ^ L) (hd : (inst 2).main Msg.D r = 1) :
    ∃ r0, r0 < (pub 0).val ∧ (inst 2).main Msg.POS r = (r0 : F) ∧
      (inst 2).main Msg.BYTE r = (inst 0).main BYTE r0 := by
  classical
  have hs0 : ((2, r, 0) : Site) ∈ sites hashSys inst := by
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨2, by decide, r, by rw [hL 2 (by decide)]; exact hr, 0, by simp [hashSys, Msg.msg, Msg.lookups], rfl⟩
  have hm : siteMult hashSys inst pub (2, r, 0) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr, hd]
  have hv : siteVals hashSys inst pub (2, r, 0) = [(inst 2).main Msg.POS r, (inst 2).main Msg.BYTE r] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Msg.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]
  exact hash_read hL hsat hL25 hs0 (by decide) (by simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups]) hm hv

/-- **A message's transaction tuple comes from the fields.** A non-header message start reads its
tuple `tx(i, a, seg, w, l)` from a fields row yielding it (lock-time row, multiplicity `K_LOCK · TXM`). -/
theorem msg_tuple_linked (hL25 : L ≤ 25) {r : ℕ} (hr : r < 2 ^ L) (hf : (inst 2).main Msg.FIRSTM r = 1)
    (hh : (inst 2).main Msg.HDR r = 0) :
    ∃ r' < 2 ^ L, siteMult hashSys inst pub (1, r', 7) ≠ 0 ∧
      siteVals hashSys inst pub (1, r', 7) = siteVals hashSys inst pub (2, r, 1) := by
  classical
  have mem : ∀ {i r k}, ((i, r, k) : Site) ∈ sites hashSys inst ↔
      i < 5 ∧ r < 2 ^ L ∧ k < (hashSys.comp i).lookups.length := by
    intro i r k
    simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
    constructor
    · rintro ⟨i', hi, r', hr', k', hk', rfl, rfl, rfl⟩
      exact ⟨hi, by rw [← hL i' hi]; exact hr', hk'⟩
    · rintro ⟨hi, hr', hk'⟩
      exact ⟨i, hi, r, by rw [hL i hi]; exact hr', k, hk', rfl, rfl, rfl⟩
  have ms := hash_msg_sat hL hsat
  have hs1 : ((2, r, 1) : Site) ∈ sites hashSys inst := mem.mpr ⟨by decide, hr, by simp [hashSys, Msg.msg, Msg.lookups]⟩
  have hm : siteMult hashSys inst pub (2, r, 1) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k, Msg.om,
      Msg.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr, hf, hh]
  have huse : ∀ s ∈ sites hashSys inst, (fun i k => i = 2 ∧ k = 1) s.1 s.2.2 →
      siteMult hashSys inst pub s = -1 ∨ siteMult hashSys inst pub s = 0 := by
    intro s hs hu
    obtain ⟨i, r', k⟩ := s
    obtain ⟨rfl, rfl⟩ := hu
    have hr' := (mem.mp hs).2.1
    have b1 := Msg.bool_col ms (e := Msg.FIRSTM) (by simp) hr'
    have b2 := Msg.bool_col ms (e := Msg.HDR) (by simp) hr'
    simp [siteMult, siteEval, siteLookup, hashSys, hL 2 (by decide), Msg.msg, Msg.lookups, Expr.eval, Msg.k, Msg.om,
      Msg.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr']
    rcases b1 with h1 | h1 <;> rcases b2 with h2 | h2 <;> simp [h1, h2]
  have hcount : ((sites hashSys inst).filter fun s => s.1 = 2 ∧ s.2.2 = 1).length + ([] : PubEntries).length < P := by
    have := List.length_filter_le (fun s : Site => decide (s.1 = 2 ∧ s.2.2 = 1)) (sites hashSys inst)
    rw [hash_sites_len hL] at this
    have := hash_rows_lt_P hL hL25
    simp only [List.length_nil, add_zero]; omega
  obtain ⟨s, hs, hnu, hsm, hsr, hsv⟩ := used_in_table_ext hsat.2 (use := fun i k => i = 2 ∧ k = 1) huse
    (by simp) hcount (Or.inl ⟨(2, r, 1), hs1, ⟨rfl, rfl⟩, hm, rfl, rfl⟩)
  obtain ⟨i, r', k⟩ := s
  obtain ⟨hi, hr', hk'⟩ := mem.mp hs
  have hrel : siteRel hashSys (i, r', k) = Fields.REL_TX := by
    rw [hsr]; simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups]
  have hik : i = 1 ∧ k = 7 := by
    interval_cases i
    · simp [hashSys, bytes] at hk'; subst hk'
      simp [siteRel, siteLookup, hashSys, bytes, REL_BYTE, Fields.REL_TX] at hrel
    · simp [hashSys, Fields.fields, Fields.lookups] at hk'
      interval_cases k <;> first | exact ⟨rfl, rfl⟩ | simp [siteRel, siteLookup, hashSys, Fields.fields,
        Fields.lookups, REL_BYTE, Fields.REL_TX] at hrel
    · simp [hashSys, Msg.msg, Msg.lookups] at hk'
      interval_cases k
      · simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups, REL_BYTE, Fields.REL_TX] at hrel
      · exact absurd ⟨rfl, rfl⟩ hnu
      all_goals simp [siteRel, siteLookup, hashSys, Msg.msg, Msg.lookups, Fields.REL_TX, Msg.REL_MSGW,
        Msg.REL_MLEN] at hrel
    · simp [hashSys, Sha.sha, Sha.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Sha.sha, Sha.lookups, Msg.REL_MSGW, Msg.REL_MLEN,
        Sha.REL_DIGEST, Sha.REL_NODE, Fields.REL_TX] at hrel
    · simp [hashSys, Merkle.merkle, Merkle.lookups] at hk'
      interval_cases k <;> simp [siteRel, siteLookup, hashSys, Merkle.merkle, Merkle.lookups, Msg.REL_MSGW,
        Msg.REL_MLEN, Sha.REL_DIGEST, Sha.REL_NODE, Fields.REL_TX] at hrel
  obtain ⟨rfl, rfl⟩ := hik
  exact ⟨r', hr', hsm, hsv⟩

/-- The tuple a non-header message start reads, from the fields' lock-time row of its transaction. -/
theorem msg_tuple_row (hL25 : L ≤ 25) {r : ℕ} (hr : r < 2 ^ L) (hf : (inst 2).main Msg.FIRSTM r = 1)
    (hh : (inst 2).main Msg.HDR r = 0) :
    ∃ ρ < 2 ^ L, (inst 1).main Fields.K_LOCK ρ = 1 ∧
      (inst 1).main Fields.TXI ρ = (inst 2).main Msg.TI r ∧ (inst 1).main Fields.TXA ρ = (inst 2).main Msg.TA r ∧
      (inst 1).main Fields.SEG ρ = (inst 2).main Msg.SEG r ∧ (inst 1).main Fields.WST ρ = (inst 2).main Msg.TW r ∧
      (inst 1).main Fields.START ρ = (inst 2).main Msg.TL r := by
  obtain ⟨ρ, hρ, hm, hv⟩ := msg_tuple_linked hL hsat hL25 hr hf hh
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
theorem mid_tuple (hL25 : L ≤ 25) {r0 r1 : ℕ} (h0 : r0 < 2 ^ L) (h1 : r1 < 2 ^ L)
    (f0 : (inst 2).main Msg.FIRSTM r0 = 1) (f1 : (inst 2).main Msg.FIRSTM r1 = 1)
    (hm : (inst 2).main Msg.MID r0 = (inst 2).main Msg.MID r1) :
    (inst 2).main Msg.HDR r0 = (inst 2).main Msg.HDR r1 ∧ (inst 2).main Msg.WTX r0 = (inst 2).main Msg.WTX r1 ∧
      (inst 2).main Msg.TA r0 = (inst 2).main Msg.TA r1 ∧ (inst 2).main Msg.TL r0 = (inst 2).main Msg.TL r1 ∧
      ((inst 2).main Msg.HDR r0 = 0 →
        (inst 2).main Msg.SEG r0 = (inst 2).main Msg.SEG r1 ∧ (inst 2).main Msg.TW r0 = (inst 2).main Msg.TW r1) := by
  have ms := hash_msg_sat hL hsat
  have fs := hash_fields_sat' hL hsat
  have hP : 2 ^ L < P := by have := hash_rows_lt_P hL hL25; omega
  have h25 : 2 ^ L ≤ 2 ^ 25 := Nat.pow_le_pow_right (by norm_num) hL25
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
    obtain ⟨ρ, hρ, hl, ti, ta, sg, tw, tl⟩ := msg_tuple_row hL hsat hL25 hr hf hh
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
theorem same_bytes (hL25 : L ≤ 25) {r0 r1 d0 d1 : ℕ} (h0 : r0 < 2 ^ L) (h1 : r1 < 2 ^ L)
    (f0 : (inst 2).main Msg.FIRSTM r0 = 1) (f1 : (inst 2).main Msg.FIRSTM r1 = 1)
    (hm : (inst 2).main Msg.MID r0 = (inst 2).main Msg.MID r1)
    (hc0 : ∀ j < d0, (inst 2).main Msg.CONT (r0 + j) = 1 ∨ (inst 2).main Msg.SW (r0 + j) = 1)
    (he0 : (inst 2).main Msg.ENDD (r0 + d0) = 1)
    (hc1 : ∀ j < d1, (inst 2).main Msg.CONT (r1 + j) = 1 ∨ (inst 2).main Msg.SW (r1 + j) = 1)
    (he1 : (inst 2).main Msg.ENDD (r1 + d1) = 1) :
    d0 = d1 ∧ ∀ j ≤ d0, (inst 2).main Msg.BYTE (r0 + j) = (inst 2).main Msg.BYTE (r1 + j) := by
  have ms := hash_msg_sat hL hsat
  obtain ⟨hh, hw, ta, tl, rest⟩ := mid_tuple hL hsat hL25 h0 h1 f0 f1 hm
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
  obtain ⟨ρ0, hρ0, p0, b0⟩ := msg_read hL hsat hL25 l0 dd0
  obtain ⟨ρ1, hρ1, p1, b1⟩ := msg_read hL hsat hL25 l1 dd1
  have hρ : ρ0 = ρ1 := by
    have := ZMod.val_lt (pub 0)
    exact natCast_inj_of_lt (by omega) (by omega) (p0.symm.trans ((hpos j hj).trans p1))
  rw [b0, b1, hρ]

end System

end StarkedAir.Block
