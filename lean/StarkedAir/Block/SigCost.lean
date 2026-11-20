/-
**The full sigop cost (CONNECT-RULES step 3), system level.** The walker's accurate spans are the
fields' requests (`aspan_sum`), a marked witness stack is an input's request (`wreq_sum`), a non-empty
scriptSig's row carries its walk (`sig_out`).
-/
import StarkedAir.Block.BlockSums
import StarkedAir.Block.CoinClaims
import StarkedAir.Block.CoinClass
import StarkedAir.Block.FieldsSig
import StarkedAir.Block.WalkAcc

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst)
open Fields (blockBytes slice toksFrom tokOf prefOf locks TxAt)
open StarkedAir.Spec.ConnectRules (sigOpsAccurate lastAcc pushOnly lastPush isP2SH isW p2shSigOps w20Of n32Of)

/-- The accurate-span relation's sites: the fields' two yields (lookups 42 and 43) and the walker's use. -/
def aspanOK : Bool :=
  (List.range 15).all fun i => (List.range (hashSys.comp i).lookups.length).all fun k =>
    relAt i k != 26 || (i == 1 && k == 42) || (i == 1 && k == 43) || (i == 6 && k == 5)

theorem aspanOK_true : aspanOK = true := by decide

theorem aspan_rel {i k : ℕ} (hi : i < 15) (hk : k < (hashSys.comp i).lookups.length) (h : relAt i k = 26) :
    (i = 1 ∧ k = 42) ∨ (i = 1 ∧ k = 43) ∨ (i = 6 ∧ k = 5) := by
  have hh := aspanOK_true
  simp only [aspanOK, List.all_eq_true, List.mem_range] at hh
  have := hh i hi k hk
  simp only [h, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  tauto

theorem wreq_only : onlyAt 27 1 44 1 45 = true := by decide

/-- A filtered sum splits along two exclusive cases. -/
theorem sum_filter_split {α : Type} (P P₁ P₂ : α → Prop) [DecidablePred P] [DecidablePred P₁] [DecidablePred P₂]
    (f : α → ℕ) : ∀ l : List α, (∀ s ∈ l, (P s ↔ P₁ s ∨ P₂ s)) → (∀ s ∈ l, ¬ (P₁ s ∧ P₂ s)) →
    ((l.filter P).map f).sum = ((l.filter P₁).map f).sum + ((l.filter P₂).map f).sum
  | [], _, _ => by simp
  | a :: l, h, hd => by
    have ih := sum_filter_split P P₁ P₂ f l (fun s hs => h s (List.mem_cons_of_mem _ hs))
      (fun s hs => hd s (List.mem_cons_of_mem _ hs))
    have ha := h a List.mem_cons_self
    have hda := hd a List.mem_cons_self
    by_cases h1 : P₁ a
    · have h2 : ¬ P₂ a := fun h2 => hda ⟨h1, h2⟩
      simp [List.filter_cons, ha.mpr (Or.inl h1), h1, h2, ih]; ring
    · by_cases h2 : P₂ a
      · simp [List.filter_cons, ha.mpr (Or.inr h2), h1, h2, ih]; ring
      · have : ¬ P a := fun hp => by rcases ha.mp hp with x | x <;> contradiction
        simp [List.filter_cons, this, h1, h2, ih]

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
include hL hsat hL24

omit hsat hL24 in
theorem aspan_sites1 {r : ℕ} (hr : r < 2 ^ Ls 1) :
    siteMult hashSys inst pub (1, r, 42) = (inst 1).main Fields.ARQ r ∧
    siteVals hashSys inst pub (1, r, 42) = [(inst 1).main Fields.SRS r, (inst 1).main Fields.SRL r, 1] ∧
    siteMult hashSys inst pub (1, r, 43) = (inst 1).main Fields.WQ r * (1 - (inst 1).main Fields.ZV r) ∧
    siteVals hashSys inst pub (1, r, 43) = [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r, 0] ∧
    siteMult hashSys inst pub (1, r, 44) = (inst 1).main Fields.N32 r * (inst 1).main Fields.SEG r ∧
    siteVals hashSys inst pub (1, r, 44) = [(inst 1).main Fields.TXI r, (inst 1).main Fields.INL r] ∧
    siteMult hashSys inst pub (1, r, 45) = -((inst 1).main Fields.K_WCNT r * (inst 1).main Fields.WS r) ∧
    siteVals hashSys inst pub (1, r, 45) = [(inst 1).main Fields.TXI r, (inst 1).main Fields.WINL r] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
      Fields.chkLookups, Fields.k, Fields.c, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
      wrap_zero hr]
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, Fields.oneMinus, Fields.one,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
      Fields.chkLookups, Fields.k, Fields.c, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
      wrap_zero hr]
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
      Fields.chkLookups, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col,
      wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
      Fields.chkLookups, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]

omit hsat hL24 in
theorem aspan_sites6 {r : ℕ} (hr : r < 2 ^ Ls 6) :
    siteMult hashSys inst pub (6, r, 5) = -((inst 6).main Walk.FS r * (inst 6).main Walk.AC r) ∧
    siteVals hashSys inst pub (6, r, 5) = [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r,
      (inst 6).main Walk.W4 r] := by
  refine ⟨?_, ?_⟩
  · simp [siteMult, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Expr.eval, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 6 (by decide), Walk.walk, Walk.lookups, Walk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]

/-- **A marked witness stack is an input's request**: for any `g`, summing over the inputs that request
their stack equals summing over the marked stack rows. -/
theorem wreq_sum (g : List F → ℕ) :
    ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => (inst 1).main Fields.N32 r * (inst 1).main Fields.SEG r = 1),
      g [(inst 1).main Fields.TXI r, (inst 1).main Fields.INL r] =
    ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => (inst 1).main Fields.K_WCNT r * (inst 1).main Fields.WS r = 1),
      g [(inst 1).main Fields.TXI r, (inst 1).main Fields.WINL r] :=
  pair_sum hL hsat hL24 wreq_only (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ _ (fun r hr => (aspan_sites1 hL hr).2.2.2.2.1) (fun r hr => (aspan_sites1 hL hr).2.2.2.2.2.2.1)
    (fun r hr => (Fields.req_bools (hash_fields_sat' hL hsat) hr).2.2.1)
    (fun r hr => (Fields.req_bools (hash_fields_sat' hL hsat) hr).2.2.2)
    _ _ (fun r hr => (aspan_sites1 hL hr).2.2.2.2.2.1) (fun r hr => (aspan_sites1 hL hr).2.2.2.2.2.2.2) g

/-- **The walker's accurate spans are the fields' requests**: for any `g`, summing over the walker's
accurate first rows equals summing over the requested redeem scripts plus the requested witness scripts. -/
theorem aspan_sum (g : List F → ℕ) :
    ∑ r ∈ (Finset.range (2 ^ Ls 6)).filter (fun r => (inst 6).main Walk.FS r * (inst 6).main Walk.AC r = 1),
      g [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r, (inst 6).main Walk.W4 r] =
    ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => (inst 1).main Fields.ARQ r = 1),
      g [(inst 1).main Fields.SRS r, (inst 1).main Fields.SRL r, 1] +
    ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter
        (fun r => (inst 1).main Fields.WQ r * (1 - (inst 1).main Fields.ZV r) = 1),
      g [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r, 0] := by
  classical
  have fs := hash_fields_sat' hL hsat
  have ws : ∀ r < 2 ^ Ls 6, ∀ c ∈ Walk.constraints, c.eval (2 ^ Ls 6) Walk.preCols pub (inst 6).main r = 0 := by
    have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this
  have n1 : (1 : F) ≠ -1 := by
    intro h
    have : (2 : F) = 0 := by linear_combination h
    have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num) (by simpa using this)
    omega
  have b6 : ∀ r < 2 ^ Ls 6, (inst 6).main Walk.FS r * (inst 6).main Walk.AC r = 0 ∨
      (inst 6).main Walk.FS r * (inst 6).main Walk.AC r = 1 := by
    intro r hr
    rcases Walk.bool ws (c := Walk.FS) (by simp [Walk.bools]) hr with a | a <;>
      rcases Walk.acc_bool ws (c := Walk.AC) (by simp [Walk.accC]) hr with b | b <;> simp [a, b]
  have rel26 : ∀ i r k, i < 15 → r < 2 ^ Ls i → k < (hashSys.comp i).lookups.length →
      siteRel hashSys (i, r, k) = 26 → (i = 1 ∧ k = 42) ∨ (i = 1 ∧ k = 43) ∨ (i = 6 ∧ k = 5) :=
    fun i r k hi _ hk h => aspan_rel hi hk h
  have hm : ∀ s ∈ sites hashSys inst, siteRel hashSys s = 26 →
      siteMult hashSys inst pub s = 0 ∨ siteMult hashSys inst pub s = 1 ∨ siteMult hashSys inst pub s = -1 := by
    rintro ⟨i, r, k⟩ hs h
    obtain ⟨hi, hr, hk⟩ := (mem_sites hL).mp hs
    rcases rel26 i r k hi hr hk h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [(aspan_sites1 hL hr).1]; rcases (Fields.req_bools fs hr).1 with e | e <;> simp [e]
    · rw [(aspan_sites1 hL hr).2.2.1]; rcases (Fields.req_bools fs hr).2.1 with e | e <;> simp [e]
    · rw [(aspan_sites6 hL hr).1]; rcases b6 r hr with e | e <;> simp [e]
  have hP : (sites hashSys inst).length < P := by rw [hash_sites_len hL]; exact hash_rows_lt_P hL24
  have heq := yields_eq_uses (balanced hL hsat hL24) hm hP
  have hsum := congrArg (fun M : Multiset (List F) => (M.map g).sum) heq
  simp only [tuplesWith, Multiset.map_coe, Multiset.sum_coe, List.map_map] at hsum
  -- the two kinds of yield
  rw [sum_filter_split (fun s : Site => siteRel hashSys s = 26 ∧ siteMult hashSys inst pub s = 1)
      (fun s : Site => (siteRel hashSys s = 26 ∧ siteMult hashSys inst pub s = 1) ∧ s.2.2 = 42)
      (fun s : Site => (siteRel hashSys s = 26 ∧ siteMult hashSys inst pub s = 1) ∧ s.2.2 = 43) _ _
      (by
        rintro ⟨i, r, k⟩ hs
        obtain ⟨hi, hr, hk⟩ := (mem_sites hL).mp hs
        constructor
        · intro hp
          rcases rel26 i r k hi hr hk hp.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact Or.inl ⟨hp, rfl⟩
          · exact Or.inr ⟨hp, rfl⟩
          · exfalso
            have := hp.2; rw [(aspan_sites6 hL hr).1] at this
            rcases b6 r hr with e | e <;> rw [e] at this
            · simp at this
            · exact n1 this.symm
        · rintro (h | h) <;> exact h.1)
      (by rintro ⟨i, r, k⟩ _ ⟨h1, h2⟩; have a := h1.2; have b := h2.2; simp only at a b; omega)] at hsum
  rw [filter_sites hL hsat hL24 (i0 := 1) (k0 := 42) (by decide) (fun i r k hi hr hk hp => by
      have hk42 : k = 42 := hp.2
      rcases rel26 i r k hi hr hk hp.1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · omega
      · omega)
    (by simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups])] at hsum
  rw [filter_sites hL hsat hL24 (i0 := 1) (k0 := 43) (by decide) (fun i r k hi hr hk hp => by
      have hk43 : k = 43 := hp.2
      rcases rel26 i r k hi hr hk hp.1.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · omega
      · exact ⟨rfl, rfl⟩
      · omega)
    (by simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups])] at hsum
  rw [filter_sites hL hsat hL24 (i0 := 6) (k0 := 5) (by decide) (fun i r k hi hr hk hp => by
      rcases rel26 i r k hi hr hk hp.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        have := hp.2; rw [(aspan_sites1 hL hr).1] at this
        rcases (Fields.req_bools fs hr).1 with e | e <;> rw [e] at this
        · have : (1 : F) = 0 := by linear_combination this
          exact one_ne_zero this
        · exact n1 this
      · exfalso
        have := hp.2; rw [(aspan_sites1 hL hr).2.2.1] at this
        rcases (Fields.req_bools fs hr).2.1 with e | e <;> rw [e] at this
        · have : (1 : F) = 0 := by linear_combination this
          exact one_ne_zero this
        · exact n1 this
      · exact ⟨rfl, rfl⟩)
    (by simp [hashSys, Walk.walk, Walk.lookups])] at hsum
  simp only [List.map_map] at hsum
  rw [list_sum_filter_range, list_sum_filter_range, list_sum_filter_range] at hsum
  simp only [Function.comp_def] at hsum
  have e1 : ∀ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => (siteRel hashSys (1, r, 42) = 26 ∧
      siteMult hashSys inst pub (1, r, 42) = 1) ∧ True),
      g (siteVals hashSys inst pub (1, r, 42)) =
        g [(inst 1).main Fields.SRS r, (inst 1).main Fields.SRL r, 1] := by
    intro r hr; rw [(aspan_sites1 hL (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)).2.1]
  have e2 : ∀ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => (siteRel hashSys (1, r, 43) = 26 ∧
      siteMult hashSys inst pub (1, r, 43) = 1) ∧ True),
      g (siteVals hashSys inst pub (1, r, 43)) =
        g [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r, 0] := by
    intro r hr; rw [(aspan_sites1 hL (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)).2.2.2.1]
  have e3 : ∀ r ∈ (Finset.range (2 ^ Ls 6)).filter (fun r => siteRel hashSys (6, r, 5) = 26 ∧
      siteMult hashSys inst pub (6, r, 5) = -1), g (siteVals hashSys inst pub (6, r, 5)) =
      g [(inst 6).main Walk.POS r, (inst 6).main Walk.REM r, (inst 6).main Walk.W4 r] := by
    intro r hr; rw [(aspan_sites6 hL (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)).2]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2, Finset.sum_congr rfl e3] at hsum
  have f1 : (Finset.range (2 ^ Ls 1)).filter (fun r => (siteRel hashSys (1, r, 42) = 26 ∧
      siteMult hashSys inst pub (1, r, 42) = 1) ∧ True) =
      (Finset.range (2 ^ Ls 1)).filter (fun r => (inst 1).main Fields.ARQ r = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, ⟨-, h⟩, -⟩; exact ⟨hr, by rw [← (aspan_sites1 hL hr).1]; exact h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, ⟨rfl, by rw [(aspan_sites1 hL hr).1]; exact h⟩, trivial⟩
  have f2 : (Finset.range (2 ^ Ls 1)).filter (fun r => (siteRel hashSys (1, r, 43) = 26 ∧
      siteMult hashSys inst pub (1, r, 43) = 1) ∧ True) =
      (Finset.range (2 ^ Ls 1)).filter
        (fun r => (inst 1).main Fields.WQ r * (1 - (inst 1).main Fields.ZV r) = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, ⟨-, h⟩, -⟩; exact ⟨hr, by rw [← (aspan_sites1 hL hr).2.2.1]; exact h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, ⟨rfl, by rw [(aspan_sites1 hL hr).2.2.1]; exact h⟩, trivial⟩
  have f3 : (Finset.range (2 ^ Ls 6)).filter (fun r => siteRel hashSys (6, r, 5) = 26 ∧
      siteMult hashSys inst pub (6, r, 5) = -1) =
      (Finset.range (2 ^ Ls 6)).filter (fun r => (inst 6).main Walk.FS r * (inst 6).main Walk.AC r = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, -, h⟩; rw [(aspan_sites6 hL hr).1, neg_inj] at h; exact ⟨hr, h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, rfl, by rw [(aspan_sites6 hL hr).1, h]⟩
  rw [f1, f2, f3] at hsum
  exact hsum.symm

end System

end StarkedAir.Block
