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

/-- The witness of the input of transaction `t` that has `v` inputs left (itself included). -/
def gW (b : Spec.Block.Blk) (t v : ℕ) : List Spec.Block.Bytes :=
  (b.txs[t]?.map fun tx => (tx.vin.map (·.witness)).getD (tx.vin.length - v) []).getD []

/-- A fields row's cost: its requested redeem script (weight 4), its 20-byte program flags, and, if it
requests its witness stack, the accurate count of the stack's last item. -/
noncomputable def rowCost (inst : ℕ → Inst) (pub : ℕ → F) (b : Spec.Block.Blk) (ρ : ℕ) : ℕ :=
  Fields.aN (inst 1).main (Rb inst pub) ρ +
    ((inst 1).main Fields.GIN ρ * (inst 1).main Fields.CW20 ρ + (inst 1).main Fields.RW20 ρ).val +
    (if (inst 1).main Fields.N32 ρ * (inst 1).main Fields.SEG ρ = 1 then
      lastAcc (gW b ((inst 1).main Fields.TXI ρ).val ((inst 1).main Fields.INL ρ).val) else 0)

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

/-- **A non-empty script's walk.** A fields row that yields its script is matched by a walker script
span with the same tuple, so `SPO` is `pushOnly` of the script and, for a push-only script, `SRL` is
its last push's length and `SRS + SRL` the script's end. -/
theorem sig_out (S : Setup inst pub (Ls 1)) {ρ : ℕ} (hρ : ρ < 2 ^ Ls 1) (hs : Fields.smult (inst 1).main ρ = 1) :
    (((inst 1).main Fields.SPO ρ = 1 ∧
        pushOnly (slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val ((inst 1).main Fields.VAL ρ).val) = true) ∨
      ((inst 1).main Fields.SPO ρ = 0 ∧
        pushOnly (slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val ((inst 1).main Fields.VAL ρ).val) = false)) ∧
    (pushOnly (slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val ((inst 1).main Fields.VAL ρ).val) = true →
      (inst 1).main Fields.SRL ρ = (((lastPush (slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val
        ((inst 1).main Fields.VAL ρ).val)).length : ℕ) : F) ∧
      ((lastPush (slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val ((inst 1).main Fields.VAL ρ).val)).length ≠ 0 →
        (inst 1).main Fields.SRS ρ + (((lastPush (slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val
          ((inst 1).main Fields.VAL ρ).val)).length : ℕ) : F) =
          (inst 1).main Fields.SSC ρ + (inst 1).main Fields.VAL ρ)) := by
  classical
  have ws : ∀ r < 2 ^ Ls 6, ∀ c ∈ Walk.constraints, c.eval (2 ^ Ls 6) Walk.preCols pub (inst 6).main r = 0 := by
    have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hlen := len_R hL hsat hL24 (inst := inst) (pub := pub)
  -- a walker script span with the same tuple
  have h := script_sum hL hsat hL24 (fun v => if v = [(inst 1).main Fields.SSC ρ, (inst 1).main Fields.VAL ρ,
    (inst 1).main Fields.SPO ρ, (inst 1).main Fields.SRS ρ, (inst 1).main Fields.SRL ρ] then 1 else 0)
  have hpos : 0 < ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => Fields.smult (inst 1).main r = 1),
      (if [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r, (inst 1).main Fields.SPO r,
        (inst 1).main Fields.SRS r, (inst 1).main Fields.SRL r] = [(inst 1).main Fields.SSC ρ,
        (inst 1).main Fields.VAL ρ, (inst 1).main Fields.SPO ρ, (inst 1).main Fields.SRS ρ,
        (inst 1).main Fields.SRL ρ] then 1 else 0) :=
    ind_sum_pos.mpr ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hρ, hs⟩, rfl⟩
  rw [h] at hpos
  obtain ⟨f, hf, he⟩ := ind_sum_pos.mp hpos
  obtain ⟨hfr, hwsm⟩ := Finset.mem_filter.mp hf
  have hfr' := Finset.mem_range.mp hfr
  simp only [List.cons.injEq, and_true] at he
  obtain ⟨e1, e2, e3, e4, e5⟩ := he
  have hfs : (inst 6).main Walk.FS f = 1 := by
    rcases Walk.bool ws (c := Walk.FS) (by simp [Walk.bools]) hfr' with a | a
    · rw [wsm, a, zero_mul] at hwsm; exact absurd hwsm zero_ne_one
    · exact a
  obtain ⟨h1, h25⟩ := walk_rem hL hsat hL24 S f hfr' hfs
  have so := Walk.span_out ws (walk_opc hL hsat hL24) (fun r hr ho => by
      obtain ⟨-, -, -, -, -, -, a7, a8, a9⟩ := walk_opc_all hL hsat hL24 r hr ho
      exact ⟨a7, a8, a9⟩) (walk_r8 hL hsat hL24) (Rb inst pub) (walk_read hL hsat hL24) (by omega) hfr' hfs rfl h1 h25
  rw [e1, e2, e3, e4, e5, ZMod.natCast_zmod_val] at so
  exact so

/-- **The redeem script's first two bytes**, read when its length is 22 or 34. -/
theorem rdf_read {ρ : ℕ} (hρ : ρ < 2 ^ Ls 1) (h : (inst 1).main Fields.RDF ρ = 1) :
    ((inst 1).main Fields.RB0 ρ).val = ((Rb inst pub).getD ((inst 1).main Fields.SRS ρ).val 0).toNat ∧
    ((inst 1).main Fields.RB1 ρ).val = ((Rb inst pub).getD (((inst 1).main Fields.SRS ρ).val + 1) 0).toNat := by
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hlen := len_R hL hsat hL24 (inst := inst) (pub := pub)
  have hs0 := site_mem hL (i := 1) (by decide) hρ (k := 40)
    (by simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups])
  have hs1 := site_mem hL (i := 1) (by decide) hρ (k := 41)
    (by simp [hashSys, Fields.fields, Fields.lookups, Fields.chkLookups])
  obtain ⟨p0, b0⟩ := byte_read_R hL hsat hL24 hs0 (by decide) rfl
    (p := (inst 1).main Fields.SRS ρ) (b := (inst 1).main Fields.RB0 ρ)
    (by
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
      simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col,
        wrap_zero hρ, h])
    (by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
        Fields.chkLookups, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hρ])
  obtain ⟨p1, b1⟩ := byte_read_R hL hsat hL24 hs1 (by decide) rfl
    (p := (inst 1).main Fields.SRS ρ + 1) (b := (inst 1).main Fields.RB1 ρ)
    (by
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
      simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col,
        wrap_zero hρ, h])
    (by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
        Fields.chkLookups, Fields.k, Fields.c, Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
        wrap_zero hρ])
  have hv : ((inst 1).main Fields.SRS ρ + 1).val = ((inst 1).main Fields.SRS ρ).val + 1 := by
    have e : (inst 1).main Fields.SRS ρ + 1 = ((((inst 1).main Fields.SRS ρ).val + 1 : ℕ) : F) := by
      push_cast; rw [ZMod.natCast_zmod_val]
    rw [e]; exact ZMod.val_natCast_of_lt (Fields.lt_P (by change _ < (Rb inst pub).length at p0; omega))
  rw [hv] at b1
  exact ⟨b0, b1⟩

/-- **The requested witness scripts are the requesting inputs' last witness items.** -/
theorem wq_total (S : Setup inst pub (Ls 1)) :
    ∑ r ∈ Finset.range S.m, Fields.qN (inst 1).main (Rb inst pub) r =
    ∑ ρ ∈ (Finset.range (2 ^ Ls 1)).filter
        (fun ρ => (inst 1).main Fields.N32 ρ * (inst 1).main Fields.SEG ρ = 1),
      lastAcc (gW S.b ((inst 1).main Fields.TXI ρ).val ((inst 1).main Fields.INL ρ).val) := by
  have fs := hash_fields_sat' hL hsat
  have hP : 2 ^ Ls 1 < P := rows_lt_P hL24 (by decide)
  have hmn := S.hmn
  -- a stack's items are its input's witness
  have key : ∀ c < S.m, (inst 1).main Fields.K_WCNT c = 1 →
      Fields.stackItems (inst 1).main (Rb inst pub) S.m c =
        gW S.b ((inst 1).main Fields.TXI c).val ((inst 1).main Fields.WINL c).val := by
    intro c hc hw
    obtain ⟨rh, ρ, tx, hρm, hl, hrc, hcρ, hat, nolock, -, -, hst⟩ :=
      Fields.wcnt_tx fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit S.hnp hc hw
    have htx := S.hidx ρ (by omega) hl tx hat
    have hlk : locks (inst 1).main ρ = locks (inst 1).main c :=
      Fields.locks_const (fun j a b => by rw [nolock j (by omega) b]; exact zero_ne_one) (by omega)
    rw [hst, gW, (Fields.txi_val fs hP (show c < 2 ^ Ls 1 by omega)).1, ← hlk, htx]; rfl
  have hwr := wreq_sum hL hsat hL24 (fun v => lastAcc (gW S.b (v.getD 0 0).val (v.getD 1 0).val))
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hwr
  rw [Fields.wq_sum fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit, hwr]
  rw [Finset.sum_filter, ← Finset.sum_range_add_sum_Ico _ (show S.m ≤ 2 ^ Ls 1 by omega)]
  have hz : ∑ r ∈ Finset.Ico S.m (2 ^ Ls 1), (if (inst 1).main Fields.K_WCNT r * (inst 1).main Fields.WS r = 1 then
      lastAcc (gW S.b ((inst 1).main Fields.TXI r).val ((inst 1).main Fields.WINL r).val) else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hr
    have := Fields.kinds_at fs h2 (a := Fields.K_PAD) (by simp [Fields.K_PAD]) (S.hpad r h2 h1) Fields.K_WCNT
      (by simp [Fields.K_WCNT])
    rw [if_neg]
    rw [this]; simp [Fields.K_WCNT, Fields.K_PAD]
  rw [hz, add_zero]
  refine Finset.sum_congr rfl (fun c hc => ?_)
  have hcm := Finset.mem_range.mp hc
  have hcn : c < 2 ^ Ls 1 := by omega
  rcases Fields.kind_bool fs (c := Fields.K_WCNT) (by simp [Fields.kinds, Fields.K_WCNT]) hcn with k0 | k1
  · rw [if_neg (by rw [k0]; simp), if_neg (by rw [k0]; simp)]
  · rw [k1, one_mul]
    by_cases hws : (inst 1).main Fields.WS c = 1
    · rw [if_pos ⟨rfl, hws⟩, if_pos hws, key c hcm k1]
    · rw [if_neg (fun h => hws h.2), if_neg hws]

/-- **The context's check, by rows.** With `s` the block's legacy sigops: `4·s` plus the costs of the
non-coinbase input rows, plus a slack, is 80,000. -/
theorem cost_rows (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) :
    ∃ D : ℕ, 4 * (S.b.txs.map Spec.Block.legacySigOps).sum +
      ∑ ρ ∈ (Finset.range (2 ^ Ls 1)).filter (fun ρ => (inst 1).main Fields.GIN ρ = 1), rowCost inst pub S.b ρ +
      D = 80000 := by
  classical
  obtain ⟨A, w, D, hsum, eA, ew⟩ := sigops_nat hL hsat hL24 hL8 S
  have fs := hash_fields_sat' hL hsat
  have ws : ∀ r < 2 ^ Ls 6, ∀ c ∈ Walk.constraints, c.eval (2 ^ Ls 6) Walk.preCols pub (inst 6).main r = 0 := by
    have := hsat.1 6 (by decide); rw [hL 6 (by decide)] at this; exact this
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hlen := len_R hL hsat hL24 (inst := inst) (pub := pub)
  have hP : P = 2147483647 := rfl
  have hmn := S.hmn
  -- the walker's total
  obtain ⟨hA1, hA2⟩ := Walk.total_acc_nat ws (walk_opc hL hsat hL24) (fun r hr ho => by
      obtain ⟨-, -, -, -, -, -, a7, a8, a9⟩ := walk_opc_all hL hsat hL24 r hr ho
      exact ⟨a7, a8, a9⟩) (walk_r8 hL hsat hL24) (Rb inst pub) (walk_read hL hsat hL24) (by omega)
    (walk_rem hL hsat hL24 S) (by positivity) rb6
  have hAA := natCast_inj_of_lt (by omega) (by omega) (eA.symm.trans hA1)
  -- as the fields' requests
  set g : List F → ℕ := fun v => (if v.getD 2 0 = 1 then 4 else 1) *
    sigOpsAccurate (slice (Rb inst pub) (v.getD 0 0).val (v.getD 1 0).val) with hg
  have step1 : ∑ f ∈ (Finset.range (2 ^ Ls 6)).filter (fun f => (inst 6).main Walk.FS f = 1),
      ((inst 6).main Walk.AC f + 3 * (inst 6).main Walk.W4 f).val *
        sigOpsAccurate (slice (Rb inst pub) ((inst 6).main Walk.POS f).val ((inst 6).main Walk.REM f).val) =
      ∑ f ∈ (Finset.range (2 ^ Ls 6)).filter (fun f => (inst 6).main Walk.FS f * (inst 6).main Walk.AC f = 1),
        g [(inst 6).main Walk.POS f, (inst 6).main Walk.REM f, (inst 6).main Walk.W4 f] := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun f hf => ?_)
    have hfr := Finset.mem_range.mp hf
    have c := Walk.sat ws (Walk.mem_acc (c := .mul (Walk.k Walk.W4) (Walk.om (Walk.k Walk.AC))) (by simp [Walk.accC])) hfr
    simp only [Expr.eval, Walk.ev_k hfr, Walk.om, Walk.one, StarkedAir.Sha256.eval_cst, Nat.cast_one] at c
    simp only [hg, List.getD_cons_zero, List.getD_cons_succ]
    rcases Walk.bool ws (c := Walk.FS) (by simp [Walk.bools]) hfr with a | a
    · simp [a]
    rcases Walk.acc_bool ws (c := Walk.AC) (by simp [Walk.accC]) hfr with b | b
    · have d : (inst 6).main Walk.W4 f = 0 := by rw [b] at c; simpa using c
      simp [a, b, d]
    rcases Walk.acc_bool ws (c := Walk.W4) (by simp [Walk.accC]) hfr with d | d
    · simp [a, b, d, ZMod.val_one]
    · have h4 : ((1 : F) + 3).val = 4 := by
        rw [show (1 : F) + 3 = ((4 : ℕ) : F) by norm_num, ZMod.val_natCast_of_lt (by unfold P; norm_num)]
      simp [a, b, d, h4]
  have step2 := aspan_sum hL hsat hL24 g
  have step3 : ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter (fun r => (inst 1).main Fields.ARQ r = 1),
      g [(inst 1).main Fields.SRS r, (inst 1).main Fields.SRL r, 1] =
      ∑ r ∈ Finset.range (2 ^ Ls 1), Fields.aN (inst 1).main (Rb inst pub) r := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp [hg, Fields.aN]
  have step4 : ∑ r ∈ (Finset.range (2 ^ Ls 1)).filter
        (fun r => (inst 1).main Fields.WQ r * (1 - (inst 1).main Fields.ZV r) = 1),
      g [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r, 0] =
      ∑ r ∈ Finset.range S.m, Fields.qN (inst 1).main (Rb inst pub) r := by
    rw [Finset.sum_filter, ← Finset.sum_range_add_sum_Ico _ (show S.m ≤ 2 ^ Ls 1 by omega)]
    have hz : ∑ r ∈ Finset.Ico S.m (2 ^ Ls 1), (if (inst 1).main Fields.WQ r * (1 - (inst 1).main Fields.ZV r) = 1
        then g [(inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r, 0] else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro r hr
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hr
      have hk := Fields.kinds_at fs h2 (a := Fields.K_PAD) (by simp [Fields.K_PAD]) (S.hpad r h2 h1) Fields.K_WITEM
        (by simp [Fields.K_WITEM])
      rw [if_neg]
      rw [Fields.wq_eq fs h2, hk]; simp [Fields.K_WITEM, Fields.K_PAD]
    rw [hz, add_zero]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp [hg, Fields.qN]
  -- the 20-byte program count
  have hn1 : 2 ^ Ls 1 - 1 < 2 ^ Ls 1 := Nat.sub_lt (by positivity) (by norm_num)
  have hw1 : (inst 1).main Fields.W20S (2 ^ Ls 1 - 1) = ((∑ j ∈ Finset.range (2 ^ Ls 1),
      ((inst 1).main Fields.GIN j * (inst 1).main Fields.CW20 j + (inst 1).main Fields.RW20 j).val : ℕ) : F) := by
    rw [Fields.w20_sum fs _ hn1, show 2 ^ Ls 1 - 1 + 1 = 2 ^ Ls 1 by omega]
    push_cast
    exact Finset.sum_congr rfl (fun j hj => (Fields.w20_term fs (Finset.mem_range.mp hj)).1)
  have hw2 : ∑ j ∈ Finset.range (2 ^ Ls 1),
      ((inst 1).main Fields.GIN j * (inst 1).main Fields.CW20 j + (inst 1).main Fields.RW20 j).val ≤ 2 * 2 ^ Ls 1 := by
    calc _ ≤ ∑ j ∈ Finset.range (2 ^ Ls 1), 2 :=
          Finset.sum_le_sum (fun j hj => (Fields.w20_term fs (Finset.mem_range.mp hj)).2)
      _ = 2 * 2 ^ Ls 1 := by simp [mul_comm]
  have hww := natCast_inj_of_lt (by omega) (by omega) (ew.symm.trans hw1)
  -- all together, row by row
  have hrows : A + w = ∑ ρ ∈ Finset.range (2 ^ Ls 1), rowCost inst pub S.b ρ := by
    rw [hAA, step1, step2, step3, step4, wq_total hL hsat hL24 S, hww, Finset.sum_filter]
    simp only [rowCost, Finset.sum_add_distrib]
    ring
  have hgin : ∑ ρ ∈ Finset.range (2 ^ Ls 1), rowCost inst pub S.b ρ =
      ∑ ρ ∈ (Finset.range (2 ^ Ls 1)).filter (fun ρ => (inst 1).main Fields.GIN ρ = 1), rowCost inst pub S.b ρ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ρ hρ => ?_)
    by_cases h : (inst 1).main Fields.GIN ρ = 1
    · rw [if_pos h]
    · rw [if_neg h]
      obtain ⟨a, b, c⟩ := Fields.nongin fs (Finset.mem_range.mp hρ) h
      simp [rowCost, Fields.aN, a, b, c]
  exact ⟨D, by rw [← hgin, ← hrows]; omega⟩

end System

end StarkedAir.Block
