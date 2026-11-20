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

/-- A strictly increasing map of `[0, n)` into itself is the identity. -/
theorem strict_mono_id {n : ℕ} (f : ℕ → ℕ) (hm : ∀ a b, a < b → b < n → f a < f b) (hb : ∀ a < n, f a < n) :
    ∀ a < n, f a = a := by
  have lo : ∀ a, a < n → a ≤ f a := by
    intro a
    induction a with
    | zero => intro _; omega
    | succ a ih => intro h; have := ih (by omega); have := hm a (a + 1) (by omega) h; omega
  have hi : ∀ d a, a + d + 1 = n → f a ≤ a := by
    intro d
    induction d with
    | zero => intro a h; have := hb a (by omega); omega
    | succ d ih => intro a h; have := ih (a + 1) (by omega); have := hm a (a + 1) (by omega) (by omega); omega
  intro a ha
  have := lo a ha; have := hi (n - a - 1) a (by omega); omega

theorem list_sum_getD (f : ℕ → ℕ) : ∀ l : List ℕ, (l.map f).sum = ∑ j ∈ Finset.range l.length, f (l.getD j 0)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, list_sum_getD f l, List.length_cons, Finset.sum_range_succ', add_comm]
    simp

theorem sum_zipIdx_nat {α : Type} (G : α × ℕ → ℕ) : ∀ (l : List α) (c : ℕ),
    ((l.zipIdx c).map G).sum = ∑ i ∈ Finset.range l.length, (l[i]?.map fun a => G (a, c + i)).getD 0
  | [], c => by simp
  | a :: l, c => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_nat G l (c + 1), List.length_cons,
      Finset.sum_range_succ', add_comm]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some, Option.getD_some, Nat.add_zero]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by rw [show c + 1 + i = c + (i + 1) by omega])

theorem sum_zip_range {α β : Type} (G : α × β → ℕ) (f : ℕ → β) (l : List α) :
    ((l.zip ((List.range l.length).map f)).map G).sum =
      ∑ k ∈ Finset.range l.length, (l[k]?.map fun a => G (a, f k)).getD 0 := by
  have e : (l.zip ((List.range l.length).map f)).map G =
      (List.range l.length).map (fun k => (l[k]?.map fun a => G (a, f k)).getD 0) := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    have hi : i < l.length := by simpa using h2
    simp [List.getElem?_eq_getElem hi]
  rw [e, Fields.list_sum_range]

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
    (walk_rem hL hsat hL24 S) (by positivity)
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

/-- **The inputs' rows.** For transaction `t ≥ 1`, the fields row of coin row `pre t + k` (`k` below the
input count) is input row `k` of the transaction: it carries input `k`, has `nIn − k` inputs left, the
transaction's index and segwit flag, and the coin row's tuple. -/
theorem in_rows (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {t : ℕ} {tx : Spec.Block.Tx} (htx : S.b.txs[t]? = some tx) (ht1 : 1 ≤ t) :
    ∀ k < tx.vin.length, ∃ inp, tx.vin[k]? = some inp ∧
      ((parts.take t).map List.length).sum + k < e ∧
      (inst 14).main Coin.KI (((parts.take t).map List.length).sum + k) = 1 ∧
      (ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0 < S.m ∧
      (inst 1).main Fields.K_IN ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) = 1 ∧
      (inst 1).main Fields.TXI ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) = (t : F) ∧
      cIn inst (((parts.take t).map List.length).sum + k) =
        fIn inst pub (Ls 1) ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) ∧
      Fields.InRow (inst 1).main (Rb inst pub) ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) inp ∧
      ((inst 1).main Fields.INL ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0)).val + k =
        tx.vin.length ∧
      ((inst 1).main Fields.SEG ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) = 1 ↔
        tx.hasWitness = true) := by
  classical
  have fs := hash_fields_sat' hL hsat
  have cs := coin_sat hL hsat hL24
  have hP : 2 ^ Ls 1 < P := rows_lt_P hL24 (by decide)
  have hmn := S.hmn
  set j0 := ((parts.take t).map List.length).sum with hj0
  set io := ioRows inst S.m with hio
  have hne : ∀ (t' : ℕ) (tx' : Spec.Block.Tx), S.b.txs[t']? = some tx' → tx'.vin ≠ [] ∧ tx'.vout ≠ [] := by
    intro t' tx' h
    have := txs_basic hL hsat hL24 S tx' (List.mem_of_getElem? h)
    exact ⟨this.1, this.2.1⟩
  obtain ⟨hrows, -, -, -, -⟩ := tx_rows hL hsat hL24 S he hon hlen hst hf htg hne htx ht1
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  -- the transaction's lock-time row and head
  have htN : t < S.b.txs.length := (List.getElem?_eq_some_iff.mp htx).1
  obtain ⟨ρl, tx', hρl, hl, hlk, hget, hat⟩ := S.hsurj t htN
  rw [htx, Option.some.injEq] at hget
  subst hget
  obtain ⟨rh, hrh, ht, hnt, htxT⟩ := hat
  have htxil : (inst 1).main Fields.TXI ρl = (t : F) := by
    rw [Fields.txi_count fs ρl (by omega), hlk]
  -- each of its input rows
  have stepA : ∀ k < tx.vin.length, ∃ i inp, i < tx.vin.length ∧ io.getD (j0 + k) 0 = rh + 1 + i ∧
      tx.vin[i]? = some inp ∧ j0 + k < e ∧ (inst 14).main Coin.KI (j0 + k) = 1 ∧ io.getD (j0 + k) 0 < S.m ∧
      (inst 1).main Fields.K_IN (io.getD (j0 + k) 0) = 1 ∧ (inst 1).main Fields.TXI (io.getD (j0 + k) 0) = (t : F) ∧
      cIn inst (j0 + k) = fIn inst pub (Ls 1) (io.getD (j0 + k) 0) ∧
      Fields.InRow (inst 1).main (Rb inst pub) (io.getD (j0 + k) 0) inp ∧
      ((inst 1).main Fields.INL (io.getD (j0 + k) 0)).val + i = tx.vin.length ∧
      ((inst 1).main Fields.SEG (io.getD (j0 + k) 0) = 1 ↔ tx.hasWitness = true) := by
    intro k hk
    obtain ⟨hje, hki, -⟩ := hrows k (by omega)
    have hki1 : (inst 14).main Coin.KI (j0 + k) = 1 := hki.mpr hk
    have hkc : (inst 14).main Coin.KI (j0 + k) + (inst 14).main Coin.CBI (j0 + k) = 1 := by
      rcases Coin.kinds cs (show j0 + k < 2 ^ Ls 14 by omega) with g | g | g | g
      · rw [g.2.1] at hki1; exact absurd hki1 zero_ne_one
      · rw [g.2.1, g.2.2.1]; simp
      · rw [g.2.1] at hki1; exact absurd hki1 zero_ne_one
      · rw [g.2.1] at hki1; exact absurd hki1 zero_ne_one
    obtain ⟨hkin, hTXI, hT⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hje).2 hkc
    obtain ⟨t0, q0, tx0, htx0, hT0, hjq0, hq0, -, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hje
    obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
    obtain ⟨rfl, -⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (show j0 + k = _ from hjq0)
    have hρ : io.getD (j0 + k) 0 ∈ io := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
    obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
    have htxi : (inst 1).main Fields.TXI (io.getD (j0 + k) 0) = (t : F) := by rw [← hTXI, hT0]
    obtain ⟨rh', ρ', tx'', i, inp, hpos, hρ'm, ht', hl', hlt, hat', nolock, notxh, hiv, hinp, hrow, hinl, hseg⟩ :=
      Fields.in_tx fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit S.hnp hρm hkin
    -- its lock-time row is the transaction's
    have hlk' : locks (inst 1).main ρ' = locks (inst 1).main (io.getD (j0 + k) 0) :=
      Fields.locks_const (fun j a b => by rw [nolock j (by omega) b]; exact zero_ne_one) (by omega)
    obtain rfl : ρ' = ρl := Fields.lock_unique fs hP (by omega) (by omega) hl' hl (by
      rw [htxil, Fields.txi_count fs ρ' (by omega), hlk', ← Fields.txi_count fs _ (by omega), htxi])
    obtain rfl : rh' = rh := by
      rcases lt_trichotomy rh' rh with h | h | h
      · have := notxh rh h (by omega); rw [ht] at this; exact absurd this one_ne_zero
      · exact h
      · have := hnt rh' h (by omega); rw [ht'] at this; exact absurd this one_ne_zero
    have htx'' := S.hidx ρ' (by omega) hl tx'' hat'
    rw [hlk, htx, Option.some.injEq] at htx''
    subst htx''
    exact ⟨i, inp, hiv, hpos, hinp, hje, hki1, hρm, hkin, htxi, hT, hrow, hinl, hseg⟩
  choose! fi finp hfi using stepA
  -- the rows are in order, so input row `k` is the `k`-th
  have hsort : io.Pairwise (· < ·) := ioRows_sorted S.m
  have hid := strict_mono_id (n := tx.vin.length) fi (fun a b hab hb => by
      have ha : a < tx.vin.length := by omega
      obtain ⟨-, pa, -, ja, -⟩ := hfi a ha
      obtain ⟨-, pb, -, jb, -⟩ := hfi b hb
      have := List.pairwise_iff_getElem.mp hsort (j0 + a) (j0 + b) (by omega) (by omega) (by omega)
      rw [← List.getD_eq_getElem _ 0, ← List.getD_eq_getElem _ 0, pa, pb] at this
      omega) (fun a ha => (hfi a ha).1)
  intro k hk
  obtain ⟨-, hpos, hinp, hje, hki1, hρm, hkin, htxi, hT, hrow, hinl, hseg⟩ := hfi k hk
  rw [hid k hk] at hinp hinl
  exact ⟨finp k hk, hinp, hje, hki1, hρm, hkin, htxi, hT, hrow, hinl, hseg⟩

omit hL24 in
/-- An input row of a transaction other than the first is a non-coinbase input row. -/
theorem gin_of_txi {ρ : ℕ} (hρ : ρ < 2 ^ Ls 1) (hk : (inst 1).main Fields.K_IN ρ = 1)
    (hne : (inst 1).main Fields.TXI ρ ≠ 0) : (inst 1).main Fields.GIN ρ = 1 := by
  have fs := hash_fields_sat' hL hsat
  have c := Fields.sat fs (Fields.mem_chk (c := .mul (Fields.k Fields.ZT) (Fields.k Fields.TXI))
    (by simp [Fields.chkC, Fields.prevoutC])) hρ
  simp only [Expr.eval, Fields.ev_k hρ] at c
  have hzt : (inst 1).main Fields.ZT ρ = 0 := by
    rcases mul_eq_zero.mp c with h | h
    · exact h
    · exact absurd h hne
  rw [Fields.chk_defn fs (a := Fields.GIN) (e := .mul (Fields.k Fields.K_IN) (Fields.oneMinus (Fields.k Fields.ZT)))
    (by simp [Fields.chkC, Fields.prevoutC]) hρ]
  simp [Expr.eval, Fields.ev_k hρ, Fields.oneMinus, Fields.one, StarkedAir.Sha256.eval_cst, hk, hzt]

/-- **An input's row cost is Core's.** For input `k` of transaction `t ≥ 1` whose claim is a real
output `o`: its fields row is a non-coinbase input row, and the row's cost is
`4 · p2shSigOps + countWitnessSigOps` of the spent script, the scriptSig and the witness. -/
theorem in_row_cost (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {t : ℕ} {tx : Spec.Block.Tx} (htx : S.b.txs[t]? = some tx) (ht1 : 1 ≤ t) {k : ℕ} (hk : k < tx.vin.length)
    {c : Spec.CoinEpoch.Claim} (hc : ClaimAt inst pub (Ls 13) (((parts.take t).map List.length).sum + k) c)
    {o : Spec.Block.TxOut} (ho : c.ser = Spec.Block.serTxOut o) :
    ∃ inp, tx.vin[k]? = some inp ∧
      (inst 1).main Fields.GIN ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) = 1 ∧
      rowCost inst pub S.b ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) =
        4 * p2shSigOps o.scriptPubKey inp.scriptSig +
          Spec.ConnectRules.countWitnessSigOps inp.scriptSig o.scriptPubKey inp.witness := by
  have fs := hash_fields_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hlenR := len_R hL hsat hL24 (inst := inst) (pub := pub)
  have hP : P = 2147483647 := rfl
  have hmn := S.hmn
  obtain ⟨inp, hinp, hje, hki, hρm, hkin, htxi, hT, hrow, hinl, hseg⟩ :=
    in_rows hL hsat hL24 S he hon hlen hst hf htg htx ht1 k hk
  set ρ := (ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0 with hρdef
  have hρn : ρ < 2 ^ Ls 1 := by omega
  have htN : t < S.b.txs.length := (List.getElem?_eq_some_iff.mp htx).1
  have htP : t < P := by have := S.hN25; omega
  have hgin : (inst 1).main Fields.GIN ρ = 1 := gin_of_txi hL hsat hρn hkin (by
    rw [htxi]; intro h0
    have := natCast_inj_of_lt (a := t) (b := 0) htP (by omega) (by simpa using h0)
    omega)
  refine ⟨inp, hinp, hgin, ?_⟩
  -- the spent script's class, through the coin row
  obtain ⟨c1, c2, c3⟩ := claim_class hL hsat hL24 (by omega) hc ho
  have e5 : (inst 1).main Fields.CP ρ = (inst 14).main Coin.UP (((parts.take t).map List.length).sum + k) := by
    have := congrArg (fun l => l.getD 5 0) hT; simpa [fIn, cIn] using this.symm
  have e6 : (inst 1).main Fields.CW20 ρ = (inst 14).main Coin.U20 (((parts.take t).map List.length).sum + k) := by
    have := congrArg (fun l => l.getD 6 0) hT; simpa [fIn, cIn] using this.symm
  have e7 : (inst 1).main Fields.CW32 ρ = (inst 14).main Coin.U32 (((parts.take t).map List.length).sum + k) := by
    have := congrArg (fun l => l.getD 7 0) hT; simpa [fIn, cIn] using this.symm
  rw [← e5] at c1; rw [← e6] at c2; rw [← e7] at c3
  -- the scriptSig's bytes
  have hssc := Fields.ssc_val fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hρm (a := Fields.K_IN) (Or.inl rfl) hkin
  rw [if_pos rfl] at hssc
  obtain ⟨hv, hlenρ, -, -, hfitρ⟩ := Fields.row_info fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hρm
    (a := Fields.K_IN) (by simp [Fields.K_IN]) hkin (by simp [Fields.K_IN, Fields.K_LOCK])
    (by simp [Fields.K_IN, Fields.K_PAD])
  simp only [Fields.lenN, Fields.K_IN, Fields.K_BLK, Fields.K_TXH, if_false, if_true,
    show (2 : ℕ) ≠ 0 by norm_num, show (2 : ℕ) ≠ 1 by norm_num] at hlenρ
  have hsig : slice (Rb inst pub) ((inst 1).main Fields.SSC ρ).val ((inst 1).main Fields.VAL ρ).val = inp.scriptSig := by
    rw [hssc, hrow.script]
  have hka := Fields.kinds_at fs hρn (a := Fields.K_IN) (by simp [Fields.K_IN]) hkin
  obtain ⟨E1, E2, E3⟩ := Fields.in_cost fs (Rb inst pub) hρn hgin o.scriptPubKey c1 c2 c3 (by omega) (by omega)
    (fun hz => sig_out hL hsat hL24 S hρn (by
      unfold Fields.smult
      rw [hkin, hka Fields.K_OUT (by simp [Fields.K_OUT]), hz]; simp [Fields.K_IN, Fields.K_OUT]))
    (fun hr => rdf_read hL hsat hL24 hρn hr)
  rw [hsig] at E1 E2 E3
  -- the input's witness
  have htv : ((inst 1).main Fields.TXI ρ).val = t := by rw [htxi]; exact ZMod.val_natCast_of_lt htP
  have hwit : gW S.b ((inst 1).main Fields.TXI ρ).val ((inst 1).main Fields.INL ρ).val = inp.witness := by
    rw [gW, htv, htx]
    simp only [Option.map_some, Option.getD_some]
    rw [show tx.vin.length - ((inst 1).main Fields.INL ρ).val = k by omega, List.getD_eq_getElem?_getD,
      List.getElem?_map, hinp]; rfl
  have hw20 := Spec.ConnectRules.w20Of_le inp.scriptSig o.scriptPubKey
  have hn32 := Spec.ConnectRules.n32Of_le inp.scriptSig o.scriptPubKey
  unfold rowCost
  rw [E1, E2, E3, hwit, ZMod.val_natCast_of_lt (by omega), Spec.ConnectRules.count_split]
  rcases Fields.seg_bool fs hρn with s0 | s1
  · -- no witness in the transaction
    have hw : tx.hasWitness = false := by
      rw [Bool.eq_false_iff]; intro h
      rw [hseg.mpr h] at s0; exact one_ne_zero s0
    have hwe : inp.witness = [] := by
      unfold Spec.Block.Tx.hasWitness at hw
      rw [List.any_eq_false] at hw
      have := hw inp (List.mem_of_getElem? hinp)
      simpa using this
    rw [s0, hwe]; simp [lastAcc]
  · rw [s1, mul_one]
    interval_cases hq : n32Of inp.scriptSig o.scriptPubKey
    · simp
    · simp; omega

omit hL24 in
/-- A row that is no input row, or an input row of the first transaction, is no non-coinbase input row. -/
theorem gin_zero {ρ : ℕ} (hρ : ρ < 2 ^ Ls 1)
    (h : (inst 1).main Fields.K_IN ρ ≠ 1 ∨ (inst 1).main Fields.TXI ρ = 0) : (inst 1).main Fields.GIN ρ ≠ 1 := by
  have fs := hash_fields_sat' hL hsat
  have hg := Fields.chk_defn fs (a := Fields.GIN)
    (e := .mul (Fields.k Fields.K_IN) (Fields.oneMinus (Fields.k Fields.ZT))) (by simp [Fields.chkC, Fields.prevoutC]) hρ
  simp only [Expr.eval, Fields.ev_k hρ, Fields.oneMinus, Fields.one, StarkedAir.Sha256.eval_cst, Nat.cast_one] at hg
  rcases h with h | h
  · rcases Fields.kind_bool fs (c := Fields.K_IN) (by simp [Fields.kinds, Fields.K_IN]) hρ with a | a
    · rw [hg, a]; simp
    · exact absurd a h
  · have c := Fields.sat fs (Fields.mem_chk (c := .mul (Fields.oneMinus (Fields.k Fields.ZT))
      (.sub (.mul (Fields.k Fields.TXI) (Fields.k Fields.INVT)) Fields.one)) (by simp [Fields.chkC, Fields.prevoutC])) hρ
    simp only [Expr.eval, Fields.ev_k hρ, Fields.oneMinus, Fields.one, StarkedAir.Sha256.eval_cst, Nat.cast_one, h,
      zero_mul, zero_sub, mul_neg, mul_one, neg_eq_zero] at c
    rw [hg, c, mul_zero]; exact zero_ne_one

/-- **The non-coinbase input rows, by transaction.** A sum over them is the sum, over the transactions
after the first and their inputs `k`, at the fields row of coin row `pre t + k`. -/
theorem gin_sum (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    (C : ℕ → ℕ) :
    ∑ ρ ∈ (Finset.range (2 ^ Ls 1)).filter (fun ρ => (inst 1).main Fields.GIN ρ = 1), C ρ =
    ∑ t ∈ Finset.range S.b.txs.length, (if 1 ≤ t then
      ∑ k ∈ Finset.range ((S.b.txs[t]?.map (·.vin.length)).getD 0),
        C ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) else 0) := by
  classical
  have fs := hash_fields_sat' hL hsat
  have cs := coin_sat hL hsat hL24
  have hmn := S.hmn
  set io := ioRows inst S.m with hio
  have hft := fields_tagged hL hsat hL24 S
  rw [htg] at hft
  have he' : e = (parts.map List.length).sum := by
    rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
  set Fn : ℕ → ℕ := fun ρ => if (inst 1).main Fields.GIN ρ = 1 then C ρ else 0 with hFn
  -- over the input and output rows
  have stepa : ∑ ρ ∈ (Finset.range (2 ^ Ls 1)).filter (fun ρ => (inst 1).main Fields.GIN ρ = 1), C ρ =
      ∑ ρ ∈ (Finset.range S.m).filter (fun r => (inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1),
        Fn ρ := by
    rw [Finset.sum_filter]
    symm
    apply Finset.sum_subset
    · intro x hx
      have := (Finset.mem_filter.mp hx).1
      exact Finset.mem_range.mpr (by have := Finset.mem_range.mp this; omega)
    · intro x hx hnx
      have hxn := Finset.mem_range.mp hx
      rw [hFn]; simp only
      rw [if_neg]
      apply gin_zero hL hsat hxn
      left
      intro hk
      apply hnx
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, Or.inr hk⟩
      by_contra hc
      have := Fields.kinds_at fs hxn (a := Fields.K_PAD) (by simp [Fields.K_PAD]) (S.hpad x hxn (by omega))
        Fields.K_IN (by simp [Fields.K_IN])
      rw [hk] at this; simp [Fields.K_IN, Fields.K_PAD] at this
  have stepb : ∑ ρ ∈ (Finset.range S.m).filter
        (fun r => (inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1), Fn ρ =
      ∑ j ∈ Finset.range io.length, Fn (io.getD j 0) := by
    rw [← list_sum_filter_range, ← list_sum_getD]; rfl
  rw [stepa, stepb, ← hlen, he', sum_by_parts, List.length_map, ← hf.length_eq]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have htN := Finset.mem_range.mp ht
  obtain ⟨tx, htx⟩ : ∃ tx, S.b.txs[t]? = some tx := ⟨_, List.getElem?_eq_getElem htN⟩
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  have hpre1 : ((parts.take (t + 1)).map List.length).sum = ((parts.take t).map List.length).sum +
      (tx.vin.length + tx.vout.length) := by rw [pre_succ parts hpl, hpe]
  have hle : ((parts.take (t + 1)).map List.length).sum ≤ e := by
    rw [he']
    have := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
    rwa [List.take_length] at this
  rw [htx, Option.map_some, Option.getD_some, ← List.map_take,
    show (parts.map List.length).getD t 0 = tx.vin.length + tx.vout.length by
      rw [← hpe]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hpl],
    Finset.sum_range_add]
  -- the outputs' rows add nothing
  have houts : ∑ x ∈ Finset.range tx.vout.length,
      Fn (io.getD (((parts.take t).map List.length).sum + (tx.vin.length + x)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hqv := Finset.mem_range.mp hq
    have hje : ((parts.take t).map List.length).sum + (tx.vin.length + q) < e := by omega
    have hko := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg hje htx rfl (by omega)).1.mpr (by omega)
    obtain ⟨hkout, -⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hje).1 hko
    have hρ : io.getD (((parts.take t).map List.length).sum + (tx.vin.length + q)) 0 < 2 ^ Ls 1 := by
      have : io.getD (((parts.take t).map List.length).sum + (tx.vin.length + q)) 0 ∈ io := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have := (mem_ioRows.mp this).1; omega
    rw [hFn]; simp only
    rw [if_neg]
    apply gin_zero hL hsat hρ
    left
    rw [Fields.kinds_at fs hρ (a := Fields.K_OUT) (by simp [Fields.K_OUT]) hkout Fields.K_IN (by simp [Fields.K_IN])]
    simp [Fields.K_IN, Fields.K_OUT]
  rw [houts, add_zero]
  by_cases ht1 : 1 ≤ t
  · rw [if_pos ht1]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    obtain ⟨inp, -, hje, -, hρm, hkin, htxi, -⟩ :=
      in_rows hL hsat hL24 S he hon hlen hst hf htg htx ht1 k (Finset.mem_range.mp hk)
    have htP : t < P := by
      have := S.hN25
      have : 2 ^ Ls 1 < P := rows_lt_P hL24 (by decide)
      omega
    rw [hFn]; simp only
    rw [if_pos (gin_of_txi hL hsat (by omega) hkin (by
      rw [htxi]; intro h0
      have := natCast_inj_of_lt (a := t) (b := 0) htP (by unfold P; norm_num) (by simpa using h0)
      omega))]
  · rw [if_neg ht1]
    have ht0 : t = 0 := by omega
    apply Finset.sum_eq_zero
    intro k hk
    have hkv := Finset.mem_range.mp hk
    have hje : ((parts.take t).map List.length).sum + k < e := by omega
    have hcbi := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg hje htx rfl (by omega)).2.2.mpr ⟨hkv, ht0⟩
    have hkc : (inst 14).main Coin.KI (((parts.take t).map List.length).sum + k) +
        (inst 14).main Coin.CBI (((parts.take t).map List.length).sum + k) = 1 := by
      rcases Coin.kinds cs (show ((parts.take t).map List.length).sum + k < 2 ^ Ls 14 by omega) with g | g | g | g
      · rw [g.2.2.1] at hcbi; exact absurd hcbi zero_ne_one
      · rw [g.2.2.1] at hcbi; exact absurd hcbi zero_ne_one
      · rw [g.2.1, g.2.2.1]; simp
      · rw [g.2.2.1] at hcbi; exact absurd hcbi zero_ne_one
    obtain ⟨hkin, hTXI, -⟩ := (coin_row_tok hL hsat hL24 S he hon hlen hst hje).2 hkc
    obtain ⟨t0, q0, tx0, htx0, hT0, hjq0, hq0, -, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hje
    obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
    obtain ⟨rfl, -⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega)
      (show ((parts.take t).map List.length).sum + k = _ from hjq0)
    have hρ : io.getD (((parts.take t).map List.length).sum + k) 0 < 2 ^ Ls 1 := by
      have : io.getD (((parts.take t).map List.length).sum + k) 0 ∈ io := by
        rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
      have := (mem_ioRows.mp this).1; omega
    rw [hFn]; simp only
    rw [if_neg]
    apply gin_zero hL hsat hρ
    right
    rw [← hTXI, hT0, ht0]; simp

/-- **The full sigop cost of a block** (`GetTransactionSigOpCost` summed, at most 80,000). For a block
whose non-coinbase inputs' claims (the undo records the coin component uses) are real outputs'
serializations: the legacy, P2SH and witness sigops of its transactions, with the claims' scripts as the
spent scripts, cost at most `MAX_BLOCK_SIGOPS_COST`. -/
theorem block_sigop_cost (hL8 : 8 ≤ Ls 7) (S : Setup inst pub (Ls 1)) {e : ℕ} (he : e < 2 ^ Ls 14)
    (hon : ∀ j < 2 ^ Ls 14, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    (claim : ℕ → ℕ → Spec.CoinEpoch.Claim)
    (hcl : ∀ (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t → ∀ k < tx.vin.length,
      ClaimAt inst pub (Ls 13) (((parts.take t).map List.length).sum + k) (claim t k))
    (hreal : ∀ (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t → ∀ k < tx.vin.length,
      ∃ o : Spec.Block.TxOut, (claim t k).ser = Spec.Block.serTxOut o) :
    Spec.ConnectRules.SigOpCostOK true ((S.b.txs.zipIdx).map fun p =>
      (p.1, if p.2 = 0 then [] else
        (List.range p.1.vin.length).map fun k => (Spec.CoinEpoch.decSer (claim p.2 k).ser).2)) := by
  obtain ⟨D, hD⟩ := cost_rows hL hsat hL24 hL8 S
  rw [gin_sum hL hsat hL24 S he hon hlen hst hf htg (rowCost inst pub S.b)] at hD
  unfold Spec.ConnectRules.SigOpCostOK
  rw [List.map_map, sum_zipIdx_nat]
  -- transaction by transaction
  have hper : ∀ t < S.b.txs.length,
      (S.b.txs[t]?.map fun a => ((fun p : Spec.Block.Tx × List Spec.Block.Bytes =>
        Spec.ConnectRules.txSigOpCost true p.1 p.2) ∘ fun p : Spec.Block.Tx × ℕ =>
        (p.1, if p.2 = 0 then [] else
          (List.range p.1.vin.length).map fun k => (Spec.CoinEpoch.decSer (claim p.2 k).ser).2)) (a, 0 + t)).getD 0 =
      4 * (S.b.txs[t]?.map Spec.Block.legacySigOps).getD 0 + (if 1 ≤ t then
        ∑ k ∈ Finset.range ((S.b.txs[t]?.map (·.vin.length)).getD 0),
          rowCost inst pub S.b ((ioRows inst S.m).getD (((parts.take t).map List.length).sum + k) 0) else 0) := by
    intro t htN
    obtain ⟨tx, htx⟩ : ∃ tx, S.b.txs[t]? = some tx := ⟨_, List.getElem?_eq_getElem htN⟩
    rw [htx]
    simp only [Option.map_some, Option.getD_some, Function.comp, Nat.zero_add]
    unfold Spec.ConnectRules.txSigOpCost
    by_cases ht1 : 1 ≤ t
    · have hcb : tx.isCoinbase = false :=
        Spec.Block.not_coinbase_of_inputs tx (txs_later hL hsat hL24 S ht1 htN htx)
      rw [if_pos ht1, hcb, if_neg (show ¬ t = 0 by omega)]
      simp only [Bool.not_true, Bool.or_self, Bool.false_eq_true, if_false]
      rw [sum_zip_range (fun p : Spec.Block.TxIn × Spec.Block.Bytes =>
        4 * p2shSigOps p.2 p.1.scriptSig + Spec.ConnectRules.countWitnessSigOps p.1.scriptSig p.2 p.1.witness)
        (fun k => (Spec.CoinEpoch.decSer (claim t k).ser).2) tx.vin]
      congr 1
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hkv := Finset.mem_range.mp hk
      obtain ⟨o, ho⟩ := hreal t tx htx ht1 k hkv
      obtain ⟨inp, hinp, -, hrc⟩ := in_row_cost hL hsat hL24 S he hon hlen hst hf htg htx ht1 hkv
        (hcl t tx htx ht1 k hkv) ho
      rw [hinp, hrc, ho, Spec.CoinEpoch.decSer_script]; rfl
    · have ht0 : t = 0 := by omega
      subst ht0
      simp
  rw [Finset.sum_congr rfl (fun t ht => hper t (Finset.mem_range.mp ht)), Finset.sum_add_distrib, ← Finset.mul_sum]
  have hleg : ∑ t ∈ Finset.range S.b.txs.length, (S.b.txs[t]?.map Spec.Block.legacySigOps).getD 0 =
      (S.b.txs.map Spec.Block.legacySigOps).sum := by
    have := sum_zipIdx_nat (fun p : Spec.Block.Tx × ℕ => Spec.Block.legacySigOps p.1) S.b.txs 0
    rw [← this]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  rw [hleg]
  unfold Spec.Block.MAX_BLOCK_SIGOPS_COST
  omega

end System

end StarkedAir.Block
