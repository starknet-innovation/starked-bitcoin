/-
**The coin component's links (M3b), system level: tokens.** The fields yield each output token's tuple
`(tx, start, length, script start, script length, value limbs)` (relation 24, lookup 34) and each
input token's `(tx, start)` (relation 25, lookup 35); the coin component uses them on its output rows
(lookup 0) and on its input and coinbase-input rows (lookup 1). Each relation has exactly these two
sites, with multiplicities in `{0, 1}` and `{0, −1}`, so balance makes the yielded and used tuples equal
as multisets:

- `pair_sum`: for a relation with one yield site `(i₁, k₁)` (multiplicity `f₁ ∈ {0, 1}`) and one use site
  `(i₂, k₂)` (multiplicity `−f₂`, `f₂ ∈ {0, 1}`), any function sums to the same total over the yield
  rows and over the use rows;
- `outt_sum`, `int_sum`: the instances. With the token starts distinct, every output (input) token is
  used by exactly one coin row, and every coin output (input) row is a token.
-/
import StarkedAir.Block.ScriptSum
import StarkedAir.Block.CoinSound
import StarkedAir.Block.ChkLink
import StarkedAir.Block.BlockSetup
import StarkedAir.Block.MerkleLink
import StarkedAir.Block.SysLink
import StarkedAir.Block.B2Link
import StarkedAir.Spec.BlockIo

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst outputAt)

/-- Relation `R` has exactly the sites `(i₁, k₁)` and `(i₂, k₂)`. -/
def onlyAt (R i₁ k₁ i₂ k₂ : ℕ) : Bool :=
  (List.range 15).all fun i => (List.range (hashSys.comp i).lookups.length).all fun k =>
    relAt i k != R || (i == i₁ && k == k₁) || (i == i₂ && k == k₂)

theorem outt_only : onlyAt 24 1 34 14 0 = true := by decide
theorem int_only : onlyAt 25 1 35 14 1 = true := by decide

theorem only_rel {R i₁ k₁ i₂ k₂ : ℕ} (h : onlyAt R i₁ k₁ i₂ k₂ = true) {i k : ℕ} (hi : i < 15)
    (hk : k < (hashSys.comp i).lookups.length) (hr : relAt i k = R) : (i = i₁ ∧ k = k₁) ∨ (i = i₂ ∧ k = k₂) := by
  simp only [onlyAt, List.all_eq_true, List.mem_range] at h
  have := h i hi k hk
  simp only [hr, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at this
  exact this

/-- **Two increasing enumerations of the same set agree.** -/
theorem enum_unique {a b : ℕ → ℕ} {na nb : ℕ} (ha : ∀ i j, i < j → j < na → a i < a j)
    (hb : ∀ i j, i < j → j < nb → b i < b j)
    (hset : ∀ x, (∃ i < na, a i = x) ↔ (∃ j < nb, b j = x)) : na = nb ∧ ∀ i < na, a i = b i := by
  have key : ∀ i, i < na → i < nb → a i = b i := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hia hib
      obtain ⟨j, hj, hbj⟩ := (hset (a i)).mp ⟨i, hia, rfl⟩
      obtain ⟨k, hk, hak⟩ := (hset (b i)).mpr ⟨i, hib, rfl⟩
      have h1 : i ≤ j := by
        by_contra hc; push Not at hc
        have := ih j hc (by omega) hj
        rw [hbj] at this
        have := ha j i hc hia; omega
      have h2 : i ≤ k := by
        by_contra hc; push Not at hc
        have := ih k hc hk (by omega)
        rw [hak] at this
        have := hb k i hc hib; omega
      have e1 : b i ≤ a i := by
        rcases Nat.eq_or_lt_of_le h1 with h | h
        · subst h; omega
        · have := hb i j h hj; omega
      have e2 : a i ≤ b i := by
        rcases Nat.eq_or_lt_of_le h2 with h | h
        · subst h; omega
        · have := ha i k h hk; omega
      omega
  have hlen : na = nb := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · obtain ⟨i, hi, hai⟩ := (hset (b na)).mpr ⟨na, h, rfl⟩
      have := key i hi (by omega)
      have := hb i na hi h; omega
    · obtain ⟨j, hj, hbj⟩ := (hset (a nb)).mp ⟨nb, h, rfl⟩
      have := key j (by omega) hj
      have := ha j nb hj h; omega
  exact ⟨hlen, fun i hi => key i hi (by omega)⟩

/-- An indicator sum is positive exactly when some row satisfies the indicator. -/
theorem ind_sum_pos {s : Finset ℕ} {p : ℕ → Prop} [DecidablePred p] :
    0 < ∑ r ∈ s, (if p r then 1 else 0) ↔ ∃ r ∈ s, p r := by
  constructor
  · intro h
    by_contra hc; push Not at hc
    rw [Finset.sum_eq_zero (fun r hr => if_neg (hc r hr))] at h; omega
  · rintro ⟨r, hr, hp⟩
    exact lt_of_lt_of_le (by simp [hp]) (Finset.single_le_sum (f := fun r => if p r then 1 else 0) (fun _ _ => Nat.zero_le _) hr)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **Two sites, one relation: yields and uses sum alike.** -/
theorem pair_sum {R i₁ k₁ i₂ k₂ : ℕ} (honly : onlyAt R i₁ k₁ i₂ k₂ = true) (hi₁ : i₁ < 15) (hi₂ : i₂ < 15)
    (hk₁ : k₁ < (hashSys.comp i₁).lookups.length) (hk₂ : k₂ < (hashSys.comp i₂).lookups.length)
    (hrel₁ : relAt i₁ k₁ = R) (hrel₂' : relAt i₂ k₂ = R)
    (f₁ f₂ : ℕ → F) (hm₁ : ∀ r < 2 ^ L, siteMult hashSys inst pub (i₁, r, k₁) = f₁ r)
    (hm₂ : ∀ r < 2 ^ L, siteMult hashSys inst pub (i₂, r, k₂) = -f₂ r)
    (hb₁ : ∀ r < 2 ^ L, f₁ r = 0 ∨ f₁ r = 1) (hb₂ : ∀ r < 2 ^ L, f₂ r = 0 ∨ f₂ r = 1)
    (v₁ v₂ : ℕ → List F) (hv₁ : ∀ r < 2 ^ L, siteVals hashSys inst pub (i₁, r, k₁) = v₁ r)
    (hv₂ : ∀ r < 2 ^ L, siteVals hashSys inst pub (i₂, r, k₂) = v₂ r) (g : List F → ℕ) :
    ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => f₁ r = 1), g (v₁ r) =
      ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => f₂ r = 1), g (v₂ r) := by
  classical
  have n1 : (1 : F) ≠ -1 := by
    intro h
    have : (2 : F) = 0 := by linear_combination h
    have := natCast_inj_of_lt (a := 2) (b := 0) (by unfold P; norm_num) (by unfold P; norm_num) (by simpa using this)
    omega
  have hsite : ∀ i r k, i < 15 → r < 2 ^ L → k < (hashSys.comp i).lookups.length → siteRel hashSys (i, r, k) = R →
      (i = i₁ ∧ k = k₁) ∨ (i = i₂ ∧ k = k₂) := fun i r k hi _ hk h => only_rel honly hi hk h
  have hm : ∀ s ∈ sites hashSys inst, siteRel hashSys s = R →
      siteMult hashSys inst pub s = 0 ∨ siteMult hashSys inst pub s = 1 ∨ siteMult hashSys inst pub s = -1 := by
    rintro ⟨i, r, k⟩ hs h
    obtain ⟨hi, hr, hk⟩ := (mem_sites hL).mp hs
    rcases hsite i r k hi hr hk h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hm₁ r hr]; rcases hb₁ r hr with e | e <;> simp [e]
    · rw [hm₂ r hr]; rcases hb₂ r hr with e | e <;> simp [e]
  have hP : (sites hashSys inst).length < P := by rw [hash_sites_len hL]; exact hash_rows_lt_P hL24
  have heq := yields_eq_uses (balanced hL hsat hL24) hm hP
  have hsum := congrArg (fun M : Multiset (List F) => (M.map g).sum) heq
  simp only [tuplesWith, Multiset.map_coe, Multiset.sum_coe, List.map_map] at hsum
  rw [filter_sites hL hsat hL24 (i0 := i₁) (k0 := k₁) hi₁ (fun i r k hi hr hk hp => by
      rcases hsite i r k hi hr hk hp.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
      · exfalso
        have := hp.2; rw [hm₂ r hr] at this
        rcases hb₂ r hr with e | e <;> rw [e] at this
        · simp at this
        · exact n1 this.symm) hk₁] at hsum
  rw [filter_sites hL hsat hL24 (i0 := i₂) (k0 := k₂) hi₂ (fun i r k hi hr hk hp => by
      rcases hsite i r k hi hr hk hp.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        have := hp.2; rw [hm₁ r hr] at this
        rcases hb₁ r hr with e | e <;> rw [e] at this
        · have : (1 : F) = 0 := by linear_combination this
          exact one_ne_zero this
        · exact n1 this
      · exact ⟨rfl, rfl⟩) hk₂] at hsum
  simp only [List.map_map] at hsum
  rw [list_sum_filter_range, list_sum_filter_range] at hsum
  simp only [Function.comp_def] at hsum
  have hrel₂ : ∀ r < 2 ^ L, siteRel hashSys (i₂, r, k₂) = R := fun _ _ => hrel₂'
  have e1 : ∀ r ∈ (Finset.range (2 ^ L)).filter (fun r => siteRel hashSys (i₁, r, k₁) = R ∧
      siteMult hashSys inst pub (i₁, r, k₁) = 1), g (siteVals hashSys inst pub (i₁, r, k₁)) = g (v₁ r) := by
    intro r hr; rw [hv₁ r (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)]
  have e2 : ∀ r ∈ (Finset.range (2 ^ L)).filter (fun r => siteRel hashSys (i₂, r, k₂) = R ∧
      siteMult hashSys inst pub (i₂, r, k₂) = -1), g (siteVals hashSys inst pub (i₂, r, k₂)) = g (v₂ r) := by
    intro r hr; rw [hv₂ r (Finset.mem_range.mp (Finset.mem_filter.mp hr).1)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl e2] at hsum
  have f1 : (Finset.range (2 ^ L)).filter (fun r => siteRel hashSys (i₁, r, k₁) = R ∧
      siteMult hashSys inst pub (i₁, r, k₁) = 1) = (Finset.range (2 ^ L)).filter (fun r => f₁ r = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, -, h⟩; exact ⟨hr, by rw [← hm₁ r hr]; exact h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, hrel₁, by rw [hm₁ r hr]; exact h⟩
  have f2 : (Finset.range (2 ^ L)).filter (fun r => siteRel hashSys (i₂, r, k₂) = R ∧
      siteMult hashSys inst pub (i₂, r, k₂) = -1) = (Finset.range (2 ^ L)).filter (fun r => f₂ r = 1) := by
    ext r; simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hr, -, h⟩; rw [hm₂ r hr, neg_inj] at h; exact ⟨hr, h⟩
    · rintro ⟨hr, h⟩; exact ⟨hr, hrel₂ r hr, by rw [hm₂ r hr, h]⟩
  rw [f1, f2] at hsum
  exact hsum

theorem coin_sat : ∀ r < 2 ^ L, ∀ c ∈ Coin.constraints, c.eval (2 ^ L) Coin.preCols pub (inst 14).main r = 0 :=
  hash_coin_sat hL hsat

/-- The output relation's sites: the fields' yield `K_OUT`, the coin use `−KO`. -/
theorem outt_sites {r : ℕ} (hr : r < 2 ^ L) :
    siteMult hashSys inst pub (1, r, 34) = (inst 1).main Fields.K_OUT r ∧
    siteMult hashSys inst pub (14, r, 0) = -(inst 14).main Coin.KO r ∧
    siteVals hashSys inst pub (1, r, 34) = [(inst 1).main Fields.TXI r, (inst 1).main Fields.START r,
      (inst 1).main Fields.LEN r, (inst 1).main Fields.SSC r, (inst 1).main Fields.VAL r,
      Fields.vlo.eval (2 ^ L) Fields.preCols pub (inst 1).main r, Fields.vhi.eval (2 ^ L) Fields.preCols pub (inst 1).main r] ∧
    siteVals hashSys inst pub (14, r, 0) = [(inst 14).main Coin.TXI r, (inst 14).main Coin.START r,
      (inst 14).main Coin.LEN r, (inst 14).main Coin.SSC r, (inst 14).main Coin.SVAL r,
      (inst 14).main Coin.VL r, (inst 14).main Coin.VH r] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide)]
    simp [Coin.coin, Coin.lookups, Expr.eval, Coin.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
      Fields.chkLookups, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]

/-- The input relation's sites: the fields' yield `K_IN`, the coin use `−(KI + CBI)`. -/
theorem int_sites {r : ℕ} (hr : r < 2 ^ L) :
    siteMult hashSys inst pub (1, r, 35) = (inst 1).main Fields.K_IN r ∧
    siteMult hashSys inst pub (14, r, 1) = -((inst 14).main Coin.KI r + (inst 14).main Coin.CBI r) ∧
    siteVals hashSys inst pub (1, r, 35) = [(inst 1).main Fields.TXI r, (inst 1).main Fields.START r] ∧
    siteVals hashSys inst pub (14, r, 1) = [(inst 14).main Coin.TXI r, (inst 14).main Coin.START r] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 1 (by decide)]
    simp [Fields.fields, Fields.lookups, Fields.chkLookups, Expr.eval, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide)]
    simp [Coin.coin, Coin.lookups, Expr.eval, Coin.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 1 (by decide), Fields.fields, Fields.lookups,
      Fields.chkLookups, Fields.k, StarkedAir.Sha256.eval_col, wrap_zero hr]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr]

theorem fields_sat' : ∀ r < 2 ^ L, ∀ c ∈ Fields.constraints, c.eval (2 ^ L) Fields.preCols pub (inst 1).main r = 0 :=
  hash_fields_sat' hL hsat

/-- **Output tokens are the coin output rows** (as multisets of tuples): any function sums alike. -/
theorem outt_sum (g : List F → ℕ) :
    ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 1).main Fields.K_OUT r = 1),
      g [(inst 1).main Fields.TXI r, (inst 1).main Fields.START r, (inst 1).main Fields.LEN r, (inst 1).main Fields.SSC r,
        (inst 1).main Fields.VAL r, Fields.vlo.eval (2 ^ L) Fields.preCols pub (inst 1).main r,
        Fields.vhi.eval (2 ^ L) Fields.preCols pub (inst 1).main r] =
    ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 14).main Coin.KO r = 1),
      g [(inst 14).main Coin.TXI r, (inst 14).main Coin.START r, (inst 14).main Coin.LEN r, (inst 14).main Coin.SSC r,
        (inst 14).main Coin.SVAL r, (inst 14).main Coin.VL r, (inst 14).main Coin.VH r] :=
  pair_sum hL hsat hL24 outt_only (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ _ (fun r hr => (outt_sites hL hsat hL24 hr).1) (fun r hr => (outt_sites hL hsat hL24 hr).2.1)
    (fun r hr => Fields.kind_bool (fields_sat' hL hsat hL24) (by simp [Fields.kinds]) hr)
    (fun r hr => Coin.bool_col (coin_sat hL hsat hL24) (by simp) hr)
    _ _ (fun r hr => (outt_sites hL hsat hL24 hr).2.2.1) (fun r hr => (outt_sites hL hsat hL24 hr).2.2.2) g

/-- **Input tokens are the coin input rows** (non-coinbase and coinbase), as multisets of `(tx, start)`. -/
theorem int_sum (g : List F → ℕ) :
    ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 1).main Fields.K_IN r = 1),
      g [(inst 1).main Fields.TXI r, (inst 1).main Fields.START r] =
    ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 14).main Coin.KI r + (inst 14).main Coin.CBI r = 1),
      g [(inst 14).main Coin.TXI r, (inst 14).main Coin.START r] :=
  pair_sum hL hsat hL24 int_only (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    _ _ (fun r hr => (int_sites hL hsat hL24 hr).1) (fun r hr => (int_sites hL hsat hL24 hr).2.1)
    (fun r hr => Fields.kind_bool (fields_sat' hL hsat hL24) (by simp [Fields.kinds]) hr)
    (fun r hr => by
      rcases Coin.kinds (coin_sat hL hsat hL24) hr with h | h | h | h <;> simp [h.2.1, h.2.2.1])
    _ _ (fun r hr => (int_sites hL hsat hL24 hr).2.2.1) (fun r hr => (int_sites hL hsat hL24 hr).2.2.2) g

/-- **A coin range check is a byte.** If the coin component's lookup `k` is `r8 (col c) mexp` and `mexp`
is 1 at row `r`, column `c` holds a byte there. -/
theorem coin_r8 {k c : ℕ} {mexp : Expr} (hk : k < 94) (hk4 : k ≠ 4)
    (hlk : Coin.lookups.getD k ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k c) mexp) {r : ℕ} (hr : r < 2 ^ L)
    (hm : mexp.eval (2 ^ L) Coin.preCols pub (inst 14).main r = 1) : ((inst 14).main c r).val < 256 := by
  have hlen : k < (hashSys.comp 14).lookups.length := by
    show k < Coin.lookups.length; rw [Coin.lookups_len]; exact hk
  have hs := site_mem hL (i := 14) (by decide) hr hlen
  have hsl : siteLookup hashSys ((14, r, k) : Site) = Coin.r8 (Coin.k c) mexp := hlk
  refine r8_lt hL hsat hL24 hs (by simp [isUse, hk4]) (by simp [siteRel, hsl, Coin.r8]) ?_ (v := (inst 14).main c r) ?_
  · show siteEval hashSys inst pub (14, r, k) (siteLookup hashSys (14, r, k)).mult = -1
    rw [hsl]
    have hpre : (hashSys.comp 14).air.pre = Coin.preCols := rfl
    simp only [siteEval, Coin.r8, Expr.eval, hpre, hL 14 (by decide), hm]
  · show (siteLookup hashSys (14, r, k)).vals.map (siteEval hashSys inst pub (14, r, k)) = _
    rw [hsl]
    have hpre : (hashSys.comp 14).air.pre = Coin.preCols := rfl
    simp [siteEval, Coin.r8, hpre, hL 14 (by decide), Coin.k, StarkedAir.Sha256.eval_col, wrap_zero hr]

/-- **The coin component's range facts**, by multiplicity. -/
theorem coin_bytes {r : ℕ} (hr : r < 2 ^ L) :
    let M := (inst 14).main
    (M Coin.MNB r = 1 → ∀ i < 3, (M (Coin.NB i) r).val < 256) ∧
    (M Coin.MC1 r = 1 → (∀ i < 3, (M (Coin.Q1 i) r).val < 256) ∧ (∀ i < 4, (M (Coin.H1 i) r).val < 256) ∧
      (M Coin.H1C r).val < 256 ∧ (∀ i < 3, (M (Coin.Q3 i) r).val < 256) ∧ (∀ i < 4, (M (Coin.H3 i) r).val < 256) ∧
      (M Coin.H3C r).val < 256) ∧
    (M Coin.MLO r = 1 → (∀ i < 3, (M (Coin.Q2 i) r).val < 256) ∧ (∀ i < 4, (M (Coin.H2 i) r).val < 256) ∧
      (M Coin.H2C r).val < 256) ∧
    (Coin.onV M r = 1 → ∀ i < 3, (M (Coin.FB i) r).val < 256) ∧
    (Coin.nf r * Coin.onV M r = 1 → ∀ i < 3, (M (Coin.D i) r).val < 256) := by
  intro M
  have f64 : ∀ i < 3, Coin.lookups.getD (64 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.NB i)) (Coin.k Coin.MNB) := by
    intro i hi; interval_cases i <;> rfl
  have f67 : ∀ i < 3, Coin.lookups.getD (67 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.Q1 i)) (Coin.k Coin.MC1) := by
    intro i hi; interval_cases i <;> rfl
  have f70 : ∀ i < 4, Coin.lookups.getD (70 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.H1 i)) (Coin.k Coin.MC1) := by
    intro i hi; interval_cases i <;> rfl
  have f86 : ∀ i < 3, Coin.lookups.getD (86 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.Q3 i)) (Coin.k Coin.MC1) := by
    intro i hi; interval_cases i <;> rfl
  have f89 : ∀ i < 4, Coin.lookups.getD (89 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.H3 i)) (Coin.k Coin.MC1) := by
    intro i hi; interval_cases i <;> rfl
  have f77 : ∀ i < 3, Coin.lookups.getD (77 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.Q2 i)) (Coin.k Coin.MLO) := by
    intro i hi; interval_cases i <;> rfl
  have f80 : ∀ i < 4, Coin.lookups.getD (80 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.H2 i)) (Coin.k Coin.MLO) := by
    intro i hi; interval_cases i <;> rfl
  have f74 : ∀ i < 3, Coin.lookups.getD (74 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.FB i)) (Coin.on) := by
    intro i hi; interval_cases i <;> rfl
  have f43 : ∀ i < 3, Coin.lookups.getD (43 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.D i)) (.mul Coin.notFirst Coin.on) := by
    intro i hi; interval_cases i <;> rfl
  have ek : ∀ c, (Coin.k c).eval (2 ^ L) Coin.preCols pub (inst 14).main r = M c r := fun c => Coin.ev_k hr
  refine ⟨fun h i hi => ?_, fun h => ⟨fun i hi => ?_, fun i hi => ?_, ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩,
    fun h => ⟨fun i hi => ?_, fun i hi => ?_, ?_⟩, fun h i hi => ?_, fun h i hi => ?_⟩
  · exact coin_r8 hL hsat hL24 (k := 64 + i) (by omega) (by omega) (f64 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 67 + i) (by omega) (by omega) (f67 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 70 + i) (by omega) (by omega) (f70 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 84) (by omega) (by omega) rfl hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 86 + i) (by omega) (by omega) (f86 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 89 + i) (by omega) (by omega) (f89 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 93) (by omega) (by omega) rfl hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 77 + i) (by omega) (by omega) (f77 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 80 + i) (by omega) (by omega) (f80 i hi) hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 85) (by omega) (by omega) rfl hr (by rw [ek]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 74 + i) (by omega) (by omega) (f74 i hi) hr
      (by rw [Coin.ev_on hr]; exact h)
  · exact coin_r8 hL hsat hL24 (k := 43 + i) (by omega) (by omega) (f43 i hi) hr
      (by simp only [Expr.eval, Coin.ev_on hr, Coin.ev_notFirst hr]; exact h)

/-! ### Fields' input and output tokens -/

/-- A fields row's kind is boolean and kinds exclude each other (padding rows have no other kind). -/
theorem fields_io_lt_m (S : Setup inst pub L) {r : ℕ} (hr : r < 2 ^ L)
    (hio : (inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1) : r < S.m := by
  have fs := fields_sat' hL hsat hL24
  rcases hio with h | h
  · exact Fields.lt_m fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr
      (Fields.kind_zero_of fs hr (a := Fields.K_OUT) (b := Fields.K_PAD) (by simp [Fields.K_OUT]) (by simp [Fields.K_PAD])
        (by simp [Fields.K_OUT, Fields.K_PAD]) (by rw [h]; exact one_ne_zero))
  · exact Fields.lt_m fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr
      (Fields.kind_zero_of fs hr (a := Fields.K_IN) (b := Fields.K_PAD) (by simp [Fields.K_IN]) (by simp [Fields.K_PAD])
        (by simp [Fields.K_IN, Fields.K_PAD]) (by rw [h]; exact one_ne_zero))

/-- An input or output token has positive length, so the next token starts later. -/
theorem fields_io_step (S : Setup inst pub L) {r : ℕ} (hr : r < S.m)
    (hio : (inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1) :
    ((inst 1).main Fields.START r).val < ((inst 1).main Fields.START (r + 1)).val := by
  have fs := fields_sat' hL hsat hL24
  have hr1 : r + 1 < 2 ^ L := by have := S.hmn; omega
  rw [Fields.start_val_succ fs (Rb inst pub) S.hcs (hmk_R hL hsat hL24) hr1]
  rcases hio with h | h
  · obtain ⟨-, hlen, -, -, -⟩ := Fields.row_info fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr (a := Fields.K_OUT)
      (by simp [Fields.K_OUT]) h (by simp [Fields.K_OUT, Fields.K_LOCK]) (by simp [Fields.K_OUT, Fields.K_PAD])
    rw [hlen]; simp [Fields.lenN, Fields.K_OUT, Fields.K_BLK, Fields.K_TXH, Fields.K_IN, Fields.K_NOUT]
  · obtain ⟨-, hlen, -, -, -⟩ := Fields.row_info fs (Rb inst pub) S.hcs S.hmn S.hpad S.hfit hr (a := Fields.K_IN)
      (by simp [Fields.K_IN]) h (by simp [Fields.K_IN, Fields.K_LOCK]) (by simp [Fields.K_IN, Fields.K_PAD])
    rw [hlen]; simp [Fields.lenN, Fields.K_IN, Fields.K_BLK, Fields.K_TXH]

/-- **Fields' input and output token starts strictly increase.** -/
theorem fields_io_strict (S : Setup inst pub L) {r s : ℕ} (hrs : r < s) (hs : s ≤ S.m)
    (hio : (inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1) :
    ((inst 1).main Fields.START r).val < ((inst 1).main Fields.START s).val :=
  lt_of_lt_of_le (fields_io_step hL hsat hL24 S (by omega) hio) (S.mono (r + 1) s (by omega) hs)

/-! ### Coin rows are tokens, and tokens are coin rows -/

/-- The fields' output tuple and the coin output tuple of a row. -/
noncomputable def fOut (inst : ℕ → Inst) (pub : ℕ → F) (L r : ℕ) : List F :=
  [(inst 1).main Fields.TXI r, (inst 1).main Fields.START r, (inst 1).main Fields.LEN r, (inst 1).main Fields.SSC r,
    (inst 1).main Fields.VAL r, Fields.vlo.eval (2 ^ L) Fields.preCols pub (inst 1).main r,
    Fields.vhi.eval (2 ^ L) Fields.preCols pub (inst 1).main r]
def cOut (inst : ℕ → Inst) (r : ℕ) : List F :=
  [(inst 14).main Coin.TXI r, (inst 14).main Coin.START r, (inst 14).main Coin.LEN r, (inst 14).main Coin.SSC r,
    (inst 14).main Coin.SVAL r, (inst 14).main Coin.VL r, (inst 14).main Coin.VH r]

theorem out_match_l {j : ℕ} (hj : j < 2 ^ L) (hko : (inst 14).main Coin.KO j = 1) :
    ∃ ρ < 2 ^ L, (inst 1).main Fields.K_OUT ρ = 1 ∧ fOut inst pub L ρ = cOut inst j := by
  classical
  have h := outt_sum hL hsat hL24 (fun v => if v = cOut inst j then 1 else 0)
  have hpos : 0 < ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 14).main Coin.KO r = 1),
      (if cOut inst r = cOut inst j then 1 else 0) :=
    ind_sum_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hko⟩, rfl⟩
  have hpos' := lt_of_lt_of_eq hpos h.symm
  obtain ⟨ρ, hρ, he⟩ := ind_sum_pos.mp hpos'
  obtain ⟨hρr, hk⟩ := Finset.mem_filter.mp hρ
  exact ⟨ρ, Finset.mem_range.mp hρr, hk, he⟩

theorem out_match_r {ρ : ℕ} (hρ : ρ < 2 ^ L) (hk : (inst 1).main Fields.K_OUT ρ = 1) :
    ∃ j < 2 ^ L, (inst 14).main Coin.KO j = 1 ∧ cOut inst j = fOut inst pub L ρ := by
  classical
  have h := outt_sum hL hsat hL24 (fun v => if v = fOut inst pub L ρ then 1 else 0)
  have hpos : 0 < ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 1).main Fields.K_OUT r = 1),
      (if fOut inst pub L r = fOut inst pub L ρ then 1 else 0) :=
    ind_sum_pos.mpr ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hρ, hk⟩, rfl⟩
  have hpos' := lt_of_lt_of_eq hpos h
  obtain ⟨j, hj, he⟩ := ind_sum_pos.mp hpos'
  obtain ⟨hjr, hko⟩ := Finset.mem_filter.mp hj
  exact ⟨j, Finset.mem_range.mp hjr, hko, he⟩

theorem in_match_l {j : ℕ} (hj : j < 2 ^ L) (hki : (inst 14).main Coin.KI j + (inst 14).main Coin.CBI j = 1) :
    ∃ ρ < 2 ^ L, (inst 1).main Fields.K_IN ρ = 1 ∧ (inst 1).main Fields.TXI ρ = (inst 14).main Coin.TXI j ∧
      (inst 1).main Fields.START ρ = (inst 14).main Coin.START j := by
  classical
  have h := int_sum hL hsat hL24 (fun v => if v = [(inst 14).main Coin.TXI j, (inst 14).main Coin.START j] then 1 else 0)
  have hpos : 0 < ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 14).main Coin.KI r + (inst 14).main Coin.CBI r = 1),
      (if [(inst 14).main Coin.TXI r, (inst 14).main Coin.START r] =
        [(inst 14).main Coin.TXI j, (inst 14).main Coin.START j] then 1 else 0) :=
    ind_sum_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hki⟩, rfl⟩
  rw [← h] at hpos
  obtain ⟨ρ, hρ, he⟩ := ind_sum_pos.mp hpos
  obtain ⟨hρr, hk⟩ := Finset.mem_filter.mp hρ
  simp only [List.cons.injEq, and_true] at he
  exact ⟨ρ, Finset.mem_range.mp hρr, hk, he.1, he.2⟩

theorem in_match_r {ρ : ℕ} (hρ : ρ < 2 ^ L) (hk : (inst 1).main Fields.K_IN ρ = 1) :
    ∃ j < 2 ^ L, (inst 14).main Coin.KI j + (inst 14).main Coin.CBI j = 1 ∧
      (inst 14).main Coin.TXI j = (inst 1).main Fields.TXI ρ ∧ (inst 14).main Coin.START j = (inst 1).main Fields.START ρ := by
  classical
  have h := int_sum hL hsat hL24 (fun v => if v = [(inst 1).main Fields.TXI ρ, (inst 1).main Fields.START ρ] then 1 else 0)
  have hpos : 0 < ∑ r ∈ (Finset.range (2 ^ L)).filter (fun r => (inst 1).main Fields.K_IN r = 1),
      (if [(inst 1).main Fields.TXI r, (inst 1).main Fields.START r] =
        [(inst 1).main Fields.TXI ρ, (inst 1).main Fields.START ρ] then 1 else 0) :=
    ind_sum_pos.mpr ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hρ, hk⟩, rfl⟩
  rw [h] at hpos
  obtain ⟨j, hj, he⟩ := ind_sum_pos.mp hpos
  obtain ⟨hjr, hki⟩ := Finset.mem_filter.mp hj
  simp only [List.cons.injEq, and_true] at he
  exact ⟨j, Finset.mem_range.mp hjr, hki, he.1, he.2⟩

/-! ### The alignment -/

/-- The fields' input and output token rows, in order. -/
def ioRows (inst : ℕ → Inst) (m : ℕ) : List ℕ :=
  (List.range m).filter fun r => decide ((inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1)

omit hL hsat hL24 in
theorem ioRows_sorted (m : ℕ) : (ioRows inst m).Pairwise (· < ·) :=
  (List.pairwise_lt_range).filter _

omit hL hsat hL24 in
theorem mem_ioRows {m r : ℕ} : r ∈ ioRows inst m ↔ r < m ∧ ((inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1) := by
  simp [ioRows]

/-- A coin row in use is a token: its start is a fields token's start, at most the block's length. -/
theorem coin_on_tok (S : Setup inst pub L) {j : ℕ} (hj : j < 2 ^ L) (hon : Coin.onV (inst 14).main j = 1) :
    ∃ ρ, ρ ∈ ioRows inst S.m ∧ (inst 1).main Fields.START ρ = (inst 14).main Coin.START j := by
  have cs := coin_sat hL hsat hL24
  rcases Coin.kinds cs hj with h | h | h | h
  · obtain ⟨ρ, hρ, hk, he⟩ := out_match_l hL hsat hL24 hj h.1
    have hst : (inst 1).main Fields.START ρ = (inst 14).main Coin.START j := by
      have := congrArg (fun l => l.getD 1 0) he; simpa [fOut, cOut] using this
    exact ⟨ρ, mem_ioRows.mpr ⟨fields_io_lt_m hL hsat hL24 S hρ (Or.inl hk), Or.inl hk⟩, hst⟩
  · obtain ⟨ρ, hρ, hk, -, hst⟩ := in_match_l hL hsat hL24 hj (by rw [h.2.1, h.2.2.1]; simp)
    exact ⟨ρ, mem_ioRows.mpr ⟨fields_io_lt_m hL hsat hL24 S hρ (Or.inr hk), Or.inr hk⟩, hst⟩
  · obtain ⟨ρ, hρ, hk, -, hst⟩ := in_match_l hL hsat hL24 hj (by rw [h.2.1, h.2.2.1]; simp)
    exact ⟨ρ, mem_ioRows.mpr ⟨fields_io_lt_m hL hsat hL24 S hρ (Or.inr hk), Or.inr hk⟩, hst⟩
  · rw [h.2.2.2] at hon; exact absurd hon zero_ne_one

/-- A token is a coin row in use. -/
theorem tok_coin_on {ρ : ℕ} (hρ : ρ < 2 ^ L)
    (hio : (inst 1).main Fields.K_OUT ρ = 1 ∨ (inst 1).main Fields.K_IN ρ = 1) :
    ∃ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ∧ (inst 14).main Coin.START j = (inst 1).main Fields.START ρ := by
  have cs := coin_sat hL hsat hL24
  rcases hio with hk | hk
  · obtain ⟨j, hj, hko, he⟩ := out_match_r hL hsat hL24 hρ hk
    have hst : (inst 14).main Coin.START j = (inst 1).main Fields.START ρ := by
      have := congrArg (fun l => l.getD 1 0) he; simpa [fOut, cOut] using this
    refine ⟨j, hj, ?_, hst⟩
    rcases Coin.kinds cs hj with h | h | h | h <;> simp_all
  · obtain ⟨j, hj, hki, -, hst⟩ := in_match_r hL hsat hL24 hρ hk
    refine ⟨j, hj, ?_, hst⟩
    rcases Coin.kinds cs hj with h | h | h | h
    · exact h.2.2.2
    · exact h.2.2.2
    · exact h.2.2.2
    · rw [h.2.1, h.2.2.1] at hki; simp at hki

/-- A coin row in use starts within the block. -/
theorem coin_start_le (S : Setup inst pub L) {j : ℕ} (hj : j < 2 ^ L) (hon : Coin.onV (inst 14).main j = 1) :
    ((inst 14).main Coin.START j).val ≤ 2 ^ L := by
  obtain ⟨ρ, hρ, hst⟩ := coin_on_tok hL hsat hL24 S hj hon
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have := S.hfit ρ hρm
  have := len_R hL hsat hL24
  rw [← hst]; omega

/-- **Coin rows in use have strictly increasing starts.** -/
theorem coin_start_strict (S : Setup inst pub L) {j : ℕ} (hj1 : j + 1 < 2 ^ L) (hon0 : Coin.onV (inst 14).main j = 1)
    (hon1 : Coin.onV (inst 14).main (j + 1) = 1) :
    ((inst 14).main Coin.START j).val < ((inst 14).main Coin.START (j + 1)).val := by
  have cs := coin_sat hL hsat hL24
  have hstep := Coin.start_step cs hj1 hon1
  have hD := (coin_bytes hL hsat hL24 hj1).2.2.2.2 (by simp [Coin.nf, hon1])
  have hb := Coin.b3N_lt hD
  have h0 := coin_start_le hL hsat hL24 S (by omega) hon0
  have h1 := coin_start_le hL hsat hL24 S hj1 hon1
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have e : ((inst 14).main Coin.START (j + 1)).val = ((inst 14).main Coin.START j).val + 1 + Coin.b3N (inst 14).main Coin.D (j + 1) := by
    apply Coin.lift _ (ZMod.val_lt _) (lt_of_lt_of_le (show ((inst 14).main Coin.START j).val + 1 +
      Coin.b3N (inst 14).main Coin.D (j + 1) < 2 ^ 25 by omega) (by unfold P; norm_num))
    rw [Coin.cast_val, hstep]; push_cast; rw [Coin.cast_val, Coin.b3V_eq]
  omega

/-- **The alignment.** The coin rows in use are `[0, e)` with `e` the number of fields input and output
tokens, and coin row `j` starts where the `j`-th such token does. -/
theorem coin_align (S : Setup inst pub L) :
    ∃ e, e < 2 ^ L ∧ (∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) ∧ e = (ioRows inst S.m).length ∧
      ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0) := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨e, he, hon⟩ := Coin.on_prefix cs (by positivity)
  set io := ioRows inst S.m with hio
  have hsort : io.Pairwise (· < ·) := ioRows_sorted S.m
  have hmem : ∀ i < io.length, io.getD i 0 ∈ io := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact List.getElem_mem hi
  have ha : ∀ i k, i < k → k < io.length →
      ((inst 1).main Fields.START (io.getD i 0)).val < ((inst 1).main Fields.START (io.getD k 0)).val := by
    intro i k hik hk
    have hlt : io.getD i 0 < io.getD k 0 := by
      rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
      exact List.pairwise_iff_getElem.mp hsort i k (by omega) hk hik
    obtain ⟨hkm, -⟩ := mem_ioRows.mp (hmem k hk)
    exact fields_io_strict hL hsat hL24 S hlt (le_of_lt hkm) (mem_ioRows.mp (hmem i (by omega))).2
  have hb : ∀ i k, i < k → k < e →
      ((inst 14).main Coin.START i).val < ((inst 14).main Coin.START k).val := by
    intro i k hik hk
    induction k with
    | zero => omega
    | succ k ih =>
      have s1 := coin_start_strict hL hsat hL24 S (j := k) (by omega) ((hon k (by omega)).mpr (by omega))
        ((hon (k + 1) (by omega)).mpr hk)
      rcases Nat.lt_or_ge i k with h | h
      · exact lt_trans (ih h (by omega)) s1
      · have : i = k := by omega
        subst this; exact s1
  have hset : ∀ x, (∃ i < io.length, ((inst 1).main Fields.START (io.getD i 0)).val = x) ↔
      (∃ j < e, ((inst 14).main Coin.START j).val = x) := by
    intro x
    constructor
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨hρm, hk⟩ := mem_ioRows.mp (hmem i hi)
      obtain ⟨j, hj, hjon, hst⟩ := tok_coin_on hL hsat hL24 (by have := S.hmn; omega) hk
      exact ⟨j, (hon j hj).mp hjon, by rw [hst]⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨ρ, hρ, hst⟩ := coin_on_tok hL hsat hL24 S (by omega) ((hon j (by omega)).mpr hj)
      obtain ⟨i, hi, hiρ⟩ := List.getElem_of_mem hρ
      exact ⟨i, hi, by rw [List.getD_eq_getElem _ _ hi, hiρ, hst]⟩
  obtain ⟨hlen, heq⟩ := enum_unique ha hb hset
  refine ⟨e, he, hon, hlen.symm, fun j hj => ?_⟩
  exact ZMod.val_injective _ (heq j (by omega)).symm

/-- Token starts identify input and output rows. -/
theorem io_start_inj (S : Setup inst pub L) {ρ ρ' : ℕ} (h1 : ρ ∈ ioRows inst S.m) (h2 : ρ' ∈ ioRows inst S.m)
    (he : (inst 1).main Fields.START ρ = (inst 1).main Fields.START ρ') : ρ = ρ' := by
  obtain ⟨m1, k1⟩ := mem_ioRows.mp h1
  obtain ⟨m2, k2⟩ := mem_ioRows.mp h2
  rcases Nat.lt_trichotomy ρ ρ' with h | h | h
  · have := fields_io_strict hL hsat hL24 S h (le_of_lt m2) k1; rw [he] at this; omega
  · exact h
  · have := fields_io_strict hL hsat hL24 S h (le_of_lt m1) k2; rw [he] at this; omega

/-- **Each coin row is its token.** For coin row `j < e` and the `j`-th token row `ρ`: an output row is an
output token with the same tuple; an input or coinbase-input row is an input token with the same
transaction. -/
theorem coin_row_tok (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {j : ℕ} (hj : j < e) :
    ((inst 14).main Coin.KO j = 1 → (inst 1).main Fields.K_OUT ((ioRows inst S.m).getD j 0) = 1 ∧
        cOut inst j = fOut inst pub L ((ioRows inst S.m).getD j 0)) ∧
      ((inst 14).main Coin.KI j + (inst 14).main Coin.CBI j = 1 →
        (inst 1).main Fields.K_IN ((ioRows inst S.m).getD j 0) = 1 ∧
          (inst 14).main Coin.TXI j = (inst 1).main Fields.TXI ((ioRows inst S.m).getD j 0)) := by
  set ρ := (ioRows inst S.m).getD j 0 with hρdef
  have hρ : ρ ∈ ioRows inst S.m := by
    rw [hρdef, List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  have hj2 : j < 2 ^ L := by omega
  refine ⟨fun hko => ?_, fun hki => ?_⟩
  · obtain ⟨ρ', hρ', hk, hT⟩ := out_match_l hL hsat hL24 hj2 hko
    have hs' : (inst 1).main Fields.START ρ' = (inst 1).main Fields.START ρ := by
      have h1 : (inst 1).main Fields.START ρ' = (inst 14).main Coin.START j := by
        have := congrArg (fun l => l.getD 1 0) hT; simpa [fOut, cOut] using this
      rw [h1]; exact hst j hj
    have hρ'io : ρ' ∈ ioRows inst S.m := mem_ioRows.mpr ⟨fields_io_lt_m hL hsat hL24 S hρ' (Or.inl hk), Or.inl hk⟩
    have := io_start_inj hL hsat hL24 S hρ'io hρ hs'
    subst this
    exact ⟨hk, hT.symm⟩
  · obtain ⟨ρ', hρ', hk, hT, hS⟩ := in_match_l hL hsat hL24 hj2 hki
    have hρ'io : ρ' ∈ ioRows inst S.m := mem_ioRows.mpr ⟨fields_io_lt_m hL hsat hL24 S hρ' (Or.inr hk), Or.inr hk⟩
    have := io_start_inj hL hsat hL24 S hρ'io hρ (by rw [hS]; exact hst j hj)
    subst this
    exact ⟨hk, hT.symm⟩

/-! ### Txids -/

/-- `pub 1` is the block's transaction count. -/
theorem pub1_N (S : Setup inst pub L) : pub 1 = (S.b.txs.length : F) := by
  have fs := fields_sat' hL hsat hL24
  have hn0 : 0 < 2 ^ L := by positivity
  have := fs 0 hn0 (.mul Fields.first (.sub (Fields.k Fields.VAL) (.pub 1))) (by simp [Fields.constraints, Fields.pubC])
  simp only [Expr.eval, Fields.ev_first hn0, if_true, one_mul, Fields.ev_k hn0, sub_eq_zero] at this
  rw [← this, S.hlenv, ZMod.natCast_zmod_val]

/-- **An output row's txid.** Its sixteen txid limbs are the 16-bit halves of a second-hash output that is
the txid of transaction `TXI`. -/
theorem coin_txid (S : Setup inst pub L) {j t : ℕ} (hj : j < 2 ^ L) (hko : (inst 14).main Coin.KO j = 1)
    (ht : (inst 14).main Coin.TXI j = (t : F)) (htN : t < S.b.txs.length) :
    ∃ q tx, 72 * q + 72 ≤ 2 ^ L ∧ S.b.txs[t]? = some tx ∧
      Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) = Spec.Block.txid tx ∧
      ∀ i < 16, (inst 14).main (Coin.TLB i) j =
        ((Sha256.half16 (Spec.Bitcoin.stateWord (outputAt (inst 3).main (72 * q)) (i / 2)) (i % 2) : ℕ) : F) := by
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have hN25 := S.hN25
  -- the coin's digest use: id `2·TXI + 1`, the txid limbs
  have hm : siteMult hashSys inst pub (14, j, 2) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hko]
  have hv : siteVals hashSys inst pub (14, j, 2) =
      (2 * (inst 14).main Coin.TXI j + 1) :: (List.range 16).map (fun i => (inst 14).main (Coin.TLB i) j) := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      Coin.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hj]
  have hid : ((2 * t + 1 : ℕ) : F) = 2 * (inst 14).main Coin.TXI j + 1 := by rw [ht]; push_cast; ring
  obtain ⟨q, hq, hd, hsv⟩ := digest_linked hL hsat hL24 (i := 14) (k := 2) (Or.inr (Or.inr ⟨rfl, rfl⟩)) hj hm (by
    intro v hv'
    rw [hv] at hv'
    simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hv'
    rw [← hv', ← hid, ZMod.val_natCast_of_lt (by unfold P; omega)]
    omega)
  rw [digest_vals hL hsat hq, hv] at hsv
  simp only [List.cons.injEq] at hsv
  obtain ⟨hmid, hlimbs⟩ := hsv
  obtain ⟨tx, htx⟩ : ∃ tx, S.b.txs[t]? = some tx := ⟨S.b.txs[t], List.getElem?_eq_getElem htN⟩
  have hdig := id_digest hL hsat hL24 S.hparse (pub1_N hL hsat hL24 S) S.hN1 S.hN25 0 (Or.inl rfl) t htN q hq hd
    (by rw [hmid, ← hid]; simp [Merkle.idOf]; ring)
  simp only [Spec.Block.lvs] at hdig
  rw [List.getD_eq_getElem _ _ (by simpa using htN), List.getElem_map] at hdig
  refine ⟨q, tx, hq, htx, by rw [hdig]; congr 1; simpa [List.getElem?_eq_getElem htN] using htx, fun i hi => ?_⟩
  have := congrArg (fun l => l[i]?) hlimbs
  simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at this
  exact this.symm

/-! ### Fingerprints -/

theorem fpwalk_sat' : ∀ r < 2 ^ L, ∀ c ∈ FpWalk.constraints, c.eval (2 ^ L) FpWalk.preCols pub (inst 12).main r = 0 :=
  hash_fpwalk_sat hL hsat

/-- **A fingerprint use is a segment's last row.** A use of relation 22 (`fp`) with multiplicity `−1` is
matched by the walker's yield at a row `r'` with `LST = 1` and the same tuple. -/
theorem fp_yield {i r k : ℕ} (hs : ((i, r, k) : Site) ∈ sites hashSys inst) (hu : isUse i k = true)
    (hrel : siteRel hashSys (i, r, k) = FpWalk.REL_FP) (hm : siteMult hashSys inst pub (i, r, k) = -1) :
    ∃ r' < 2 ^ L, (inst 12).main FpWalk.LST r' = 1 ∧
      [(inst 12).main FpWalk.STR r', (inst 12).main FpWalk.SID r', (inst 12).main FpWalk.LEN r',
        (inst 12).main FpWalk.H r', (inst 12).main (FpWalk.H + 1) r', (inst 12).main (FpWalk.H + 2) r',
        (inst 12).main (FpWalk.H + 3) r'] = siteVals hashSys inst pub (i, r, k) := by
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs hu hm
  rw [hrel, show FpWalk.REL_FP = 22 from rfl, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 12 ∧ k' = 3 := by omega
  have fw := fpwalk_sat' hL hsat hL24
  refine ⟨r', hr', ?_, ?_⟩
  · have hm' : (inst 12).main FpWalk.LST r' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, Expr.eval,
        FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
    rcases FpWalk.bool fw (c := FpWalk.LST) (by simp) hr' with h | h
    · exact absurd h hm'
    · exact h
  · rw [← hsv]
    simp [siteVals, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, FpWalk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hr']

/-- **A raw segment starts at its id.** The walker's first row of a raw segment (`STR = 0`) uses
`seg(0, SID, POS, REM)`, which only the coin's output rows yield, as `(0, START, START, LEN)`. -/
theorem seg_raw_start {s : ℕ} (hs : s < 2 ^ L) (hf : (inst 12).main FpWalk.FST s = 1)
    (hstr : (inst 12).main FpWalk.STR s = 0) :
    (inst 12).main FpWalk.POS s = (inst 12).main FpWalk.SID s := by
  have hsite := site_mem hL (i := 12) (by decide) hs (k := 2) (by simp [hashSys, FpWalk.fpwalk, FpWalk.lookups])
  have hm : siteMult hashSys inst pub (12, s, 2) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, Expr.eval,
      FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hs, hf]
  have hv : siteVals hashSys inst pub (12, s, 2) = [(inst 12).main FpWalk.STR s, (inst 12).main FpWalk.SID s,
      (inst 12).main FpWalk.POS s, (inst 12).main FpWalk.REM s] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, FpWalk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hs]
  obtain ⟨i', r', k', hr', hy, -, hsv⟩ := link hL hsat hL24 hsite rfl hm
  rw [show siteRel hashSys (12, s, 2) = 21 from rfl, yt] at hy
  rw [hv] at hsv
  rcases (by omega : (i' = 13 ∧ k' = 16) ∨ (i' = 14 ∧ k' = 4)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- an undo segment: stream 1, not 0
    exfalso
    have e : siteVals hashSys inst pub (13, r', 16) = [1, (inst 13).main URec.J r',
        (inst 13).main URec.S r' + 7, (inst 13).main URec.TL r'] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, URec.k, URec.HDR, Expr.eval,
        StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr']
    rw [e, hstr] at hsv
    simp at hsv
  · have e : siteVals hashSys inst pub (14, r', 4) = [0, (inst 14).main Coin.START r', (inst 14).main Coin.START r',
        (inst 14).main Coin.LEN r'] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k, Expr.eval,
        StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr']
    rw [e] at hsv
    simp only [List.cons.injEq] at hsv
    rw [← hsv.2.2.1, ← hsv.2.1]

/-- **A raw segment's bytes are the block's.** -/
theorem fp_byte {q : ℕ} (hq : q < 2 ^ L) (hon : (inst 12).main FpWalk.ON q = 1) (hstr : (inst 12).main FpWalk.STR q = 0) :
    ((inst 12).main FpWalk.POS q).val < (Rb inst pub).length ∧
      ((inst 12).main FpWalk.B q).val = ((Rb inst pub).getD ((inst 12).main FpWalk.POS q).val 0).toNat := by
  have hsite := site_mem hL (i := 12) (by decide) hq (k := 0) (by simp [hashSys, FpWalk.fpwalk, FpWalk.lookups])
  exact byte_read_R hL hsat hL24 hsite (by decide) rfl
    (by simp [siteMult, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, Expr.eval,
      FpWalk.k, FpWalk.om, FpWalk.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hq, hon, hstr])
    (by simp [siteVals, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, FpWalk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hq])

open StarkedAir.Spec.QM31 (QM toQ emb) in
/-- **An output's fingerprint** is the Horner fingerprint (at the public `γ`) of the block bytes
`[START, START + SLEN)`. -/
theorem coin_fp_out (S : Setup inst pub L) {j : ℕ} (hj : j < 2 ^ L) (hko : (inst 14).main Coin.KO j = 1) :
    ∃ len : ℕ, (inst 14).main Coin.SLEN j = (len : F) ∧ ((inst 14).main Coin.START j).val + len ≤ (Rb inst pub).length ∧
      toQ ⟨(inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
        (inst 14).main (Coin.FH + 3) j⟩ =
      FpWalk.horner (FpWalk.gQ pub) ((List.range len).map fun i =>
        emb ((((Rb inst pub).getD (((inst 14).main Coin.START j).val + i) 0).toNat : ℕ) : F)) := by
  have cs := coin_sat hL hsat hL24
  have fw := fpwalk_sat' hL hsat hL24
  have hki : (inst 14).main Coin.KI j = 0 := by
    rcases Coin.kinds cs hj with h | h | h | h <;> simp_all
  -- the coin's fingerprint use
  have hsite := site_mem hL (i := 14) (by decide) hj (k := 5) (by simp [hashSys, Coin.coin, Coin.lookups])
  have hm : siteMult hashSys inst pub (14, j, 5) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hko, hki]
  have hsidc := Coin.sidc_spec cs hj
  rw [hko, hki, one_mul, zero_mul, add_zero] at hsidc
  obtain ⟨r', hr', hl, htup⟩ := fp_yield hL hsat hL24 hsite rfl rfl hm
  have hv : siteVals hashSys inst pub (14, j, 5) = [0, (inst 14).main Coin.START j, (inst 14).main Coin.SLEN j,
      (inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
      (inst 14).main (Coin.FH + 3) j] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hki, hsidc]
  rw [hv] at htup
  simp only [List.cons.injEq, and_true] at htup
  obtain ⟨tstr, tsid, tlen, th0, th1, th2, th3⟩ := htup
  -- the walked segment
  obtain ⟨s0, hse, hfs, hrow, -, hlen, hh⟩ := FpWalk.seg_sound fw hr' hl
  set len := r' - s0 + 1 with hlendef
  have hstr0 : (inst 12).main FpWalk.STR s0 = 0 := by rw [(hrow s0 le_rfl hse).2.1, tstr]
  have hpos0 : (inst 12).main FpWalk.POS s0 = (inst 14).main Coin.START j := by
    rw [seg_raw_start hL hsat hL24 (by omega) hfs hstr0, (hrow s0 le_rfl hse).2.2.1, tsid]
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have hRl := len_R hL hsat hL24
  -- each byte
  have hbyte : ∀ i < len, ((inst 14).main Coin.START j).val + i < (Rb inst pub).length ∧
      (inst 12).main FpWalk.B (s0 + i) = ((((Rb inst pub).getD (((inst 14).main Coin.START j).val + i) 0).toNat : ℕ) : F) := by
    intro i hi
    have hq : s0 + i ≤ r' := by omega
    obtain ⟨hon, hstr, -, -, hpos⟩ := hrow (s0 + i) (by omega) hq
    rw [tstr] at hstr
    obtain ⟨hlt, hb⟩ := fp_byte hL hsat hL24 (q := s0 + i) (by omega) hon hstr
    have hst := coin_start_le hL hsat hL24 S hj (by rcases Coin.kinds cs hj with h | h | h | h <;> simp_all)
    have hlenb : len ≤ 2 ^ L := by omega
    have hpv : ((inst 12).main FpWalk.POS (s0 + i)).val = ((inst 14).main Coin.START j).val + i := by
      have e : (inst 12).main FpWalk.POS (s0 + i) = ((((inst 14).main Coin.START j).val + i : ℕ) : F) := by
        rw [hpos, hpos0, show s0 + i - s0 = i by omega]; push_cast; rw [Coin.cast_val]
      rw [e, ZMod.val_natCast_of_lt (lt_of_lt_of_le (show ((inst 14).main Coin.START j).val + i < 2 ^ 25 by omega)
        (by unfold P; norm_num))]
    rw [hpv] at hlt hb
    refine ⟨hlt, ?_⟩
    rw [← Coin.cast_val ((inst 12).main FpWalk.B (s0 + i)), hb]
  refine ⟨len, by rw [← tlen, hlen], ?_, ?_⟩
  · have := (hbyte (len - 1) (by omega)).1; omega
  · have e : toQ ⟨(inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
        (inst 14).main (Coin.FH + 3) j⟩ = FpWalk.hQ (inst 12).main r' := by
      simp only [FpWalk.hQ, th0, th1, th2, th3]
    rw [e, hh]
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [(hbyte i (List.mem_range.mp hi)).2]

/-! ### Claims: undo records -/

theorem urec_sat' : ∀ r < 2 ^ L, ∀ c ∈ URec.constraints, c.eval (2 ^ L) URec.preCols pub (inst 13).main r = 0 :=
  hash_urec_sat hL hsat

/-- **An input's claim is undo record `J`.** The coin's `urec(J, code, amount, index)` use is URec row `J`
(an on row, its `J` the row index), with the same code and amount limbs and creating-transaction index. -/
theorem coin_urec {j : ℕ} (hj : j < 2 ^ L) (hki : (inst 14).main Coin.KI j = 1) :
    ∃ rj < 2 ^ L, (inst 13).main URec.ON rj = 1 ∧ (inst 14).main Coin.J j = (inst 13).main URec.J rj ∧
      (inst 14).main Coin.CLO j = (inst 13).main (URec.C 0) rj + 256 * (inst 13).main (URec.C 1) rj ∧
      (inst 14).main Coin.CHI j = (inst 13).main (URec.C 2) rj + 256 * (inst 13).main (URec.C 3) rj ∧
      (inst 14).main Coin.VL j = (inst 13).main (URec.V 0) rj + 256 * (inst 13).main (URec.V 1) rj +
        65536 * (inst 13).main (URec.V 2) rj ∧
      (inst 14).main Coin.VH j = (inst 13).main (URec.V 3) rj + 256 * (inst 13).main (URec.V 4) rj +
        65536 * (inst 13).main (URec.V 5) rj + 16777216 * (inst 13).main (URec.V 6) rj ∧
      (inst 14).main Coin.CTX j = (inst 13).main (URec.X 0) rj + 256 * (inst 13).main (URec.X 1) rj +
        65536 * (inst 13).main (URec.X 2) rj := by
  have hsite := site_mem hL (i := 14) (by decide) hj (k := 3) (by simp [hashSys, Coin.coin, Coin.lookups])
  have hm : siteMult hashSys inst pub (14, j, 3) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hki]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hsite rfl hm
  rw [show siteRel hashSys (14, j, 3) = 23 from rfl, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 13 ∧ k' = 17 := by omega
  have us := urec_sat' hL hsat hL24
  refine ⟨r', hr', ?_, ?_⟩
  · have hm' : (inst 13).main URec.ON r' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, Expr.eval, URec.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
    rcases URec.on_bool us hr' with h | h
    · exact absurd h hm'
    · exact h
  have e1 : siteVals hashSys inst pub (13, r', 17) = [(inst 13).main URec.J r',
      (inst 13).main (URec.C 0) r' + 256 * (inst 13).main (URec.C 1) r',
      (inst 13).main (URec.C 2) r' + 256 * (inst 13).main (URec.C 3) r',
      (inst 13).main (URec.V 0) r' + 256 * (inst 13).main (URec.V 1) r' + 65536 * (inst 13).main (URec.V 2) r',
      (inst 13).main (URec.V 3) r' + 256 * (inst 13).main (URec.V 4) r' + 65536 * (inst 13).main (URec.V 5) r' +
        16777216 * (inst 13).main (URec.V 6) r',
      (inst 13).main (URec.X 0) r' + 256 * (inst 13).main (URec.X 1) r' + 65536 * (inst 13).main (URec.X 2) r'] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, URec.k, URec.limb,
      Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr']
  have e2 : siteVals hashSys inst pub (14, j, 3) = [(inst 14).main Coin.J j, (inst 14).main Coin.CLO j,
      (inst 14).main Coin.CHI j, (inst 14).main Coin.VL j, (inst 14).main Coin.VH j, (inst 14).main Coin.CTX j] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj]
  rw [e1, e2] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨a, b, c, d, e, g⟩ := hsv
  exact ⟨a.symm, b.symm, c.symm, d.symm, e.symm, g.symm⟩

/-- A URec on row's `J` is its index. -/
theorem urec_j {r : ℕ} (hr : r < 2 ^ L) (hon : (inst 13).main URec.ON r = 1) : (inst 13).main URec.J r = (r : F) := by
  obtain ⟨e, -, hon', hj, -⟩ := URec.rows_sound (urec_sat' hL hsat hL24) (n := 2 ^ L) (by positivity)
  exact hj r ((hon' r hr).mp hon)

/-- URec rows with the same `J` are the same row. -/
theorem urec_j_inj {r r' : ℕ} (hr : r < 2 ^ L) (hr' : r' < 2 ^ L) (h1 : (inst 13).main URec.ON r = 1)
    (h2 : (inst 13).main URec.ON r' = 1) (he : (inst 13).main URec.J r = (inst 13).main URec.J r') : r = r' := by
  rw [urec_j hL hsat hL24 hr h1, urec_j hL hsat hL24 hr' h2] at he
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  exact Coin.lift he (by unfold P; omega) (by unfold P; omega)

open StarkedAir.Spec.QM31 (QM toQ emb) in
/-- **An input's fingerprint** is the Horner fingerprint of undo record `J`'s `serTxOut` bytes:
the undo bytes from `S + 7`, `TL` of them, for the URec row of record `J`. -/
theorem coin_fp_in {j : ℕ} (hj : j < 2 ^ L) (hki : (inst 14).main Coin.KI j = 1) {rj : ℕ} (hrj : rj < 2 ^ L)
    (hon : (inst 13).main URec.ON rj = 1) (hJ : (inst 14).main Coin.J j = (inst 13).main URec.J rj) :
    ∃ len : ℕ, (inst 13).main URec.TL rj = (len : F) ∧ (inst 14).main Coin.SLEN j = (len : F) ∧
      ∃ u0 : ℕ, (inst 13).main URec.S rj + 7 = (u0 : F) ∧ u0 + len ≤ (pub 8).val ∧
      toQ ⟨(inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
        (inst 14).main (Coin.FH + 3) j⟩ =
      FpWalk.horner (FpWalk.gQ pub) ((List.range len).map fun i => emb ((((Ub inst pub).getD (u0 + i) 0).toNat : ℕ) : F)) := by
  have cs := coin_sat hL hsat hL24
  have fw := fpwalk_sat' hL hsat hL24
  have hko : (inst 14).main Coin.KO j = 0 := by
    rcases Coin.kinds cs hj with h | h | h | h <;> simp_all
  have hsite := site_mem hL (i := 14) (by decide) hj (k := 5) (by simp [hashSys, Coin.coin, Coin.lookups])
  have hm : siteMult hashSys inst pub (14, j, 5) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hko, hki]
  have hsidc := Coin.sidc_spec cs hj
  rw [hko, hki, one_mul, zero_mul, zero_add] at hsidc
  obtain ⟨r', hr', hl, htup⟩ := fp_yield hL hsat hL24 hsite rfl rfl hm
  have hv : siteVals hashSys inst pub (14, j, 5) = [1, (inst 14).main Coin.J j, (inst 14).main Coin.SLEN j,
      (inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
      (inst 14).main (Coin.FH + 3) j] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hki, hsidc]
  rw [hv] at htup
  simp only [List.cons.injEq, and_true] at htup
  obtain ⟨tstr, tsid, tlen, th0, th1, th2, th3⟩ := htup
  obtain ⟨s0, hse, hfs, hrow, hrem, hlen, hh⟩ := FpWalk.seg_sound fw hr' hl
  set len := r' - s0 + 1 with hlendef
  -- the segment's start: URec's yield `seg(1, J, S + 7, TL)` of the same record
  have hs0 : s0 < 2 ^ L := by omega
  have hsite2 := site_mem hL (i := 12) (by decide) hs0 (k := 2) (by simp [hashSys, FpWalk.fpwalk, FpWalk.lookups])
  have hm2 : siteMult hashSys inst pub (12, s0, 2) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, Expr.eval,
      FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hs0, hfs]
  have hv2 : siteVals hashSys inst pub (12, s0, 2) = [1, (inst 14).main Coin.J j, (inst 12).main FpWalk.POS s0,
      ((len : ℕ) : F)] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, FpWalk.k,
      StarkedAir.Sha256.eval_col, wrap_zero hs0, (hrow s0 le_rfl hse).2.1, (hrow s0 le_rfl hse).2.2.1, tstr, tsid, hrem]
  obtain ⟨i', r'', k', hr'', hy, hsm, hsv⟩ := link hL hsat hL24 hsite2 rfl hm2
  rw [show siteRel hashSys (12, s0, 2) = 21 from rfl, yt] at hy
  rw [hv2] at hsv
  rcases (by omega : (i' = 13 ∧ k' = 16) ∨ (i' = 14 ∧ k' = 4)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  swap
  · exfalso
    have e : siteVals hashSys inst pub (14, r'', 4) = [0, (inst 14).main Coin.START r'', (inst 14).main Coin.START r'',
        (inst 14).main Coin.LEN r''] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k, Expr.eval,
        StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr'']
    rw [e] at hsv; simp at hsv
  have e : siteVals hashSys inst pub (13, r'', 16) = [1, (inst 13).main URec.J r'', (inst 13).main URec.S r'' + 7,
      (inst 13).main URec.TL r''] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, URec.k, URec.HDR, Expr.eval,
      StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr'']
  rw [e] at hsv
  simp only [List.cons.injEq, and_true, true_and] at hsv
  obtain ⟨hJ'', hpos, htl⟩ := hsv
  have hon'' : (inst 13).main URec.ON r'' = 1 := by
    have hm' : (inst 13).main URec.ON r'' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, Expr.eval, URec.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr''] using hsm
    rcases URec.on_bool (urec_sat' hL hsat hL24) hr'' with h | h
    · exact absurd h hm'
    · exact h
  have hsame : r'' = rj := urec_j_inj hL hsat hL24 hr'' hrj hon'' hon (by rw [hJ'', hJ])
  subst hsame
  -- the bytes
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have hU := undo_len hL hsat hL24
  have hbyte : ∀ i < len, ∃ u : ℕ, u < (pub 8).val ∧ (inst 12).main FpWalk.POS (s0 + i) = (u : F) ∧
      (inst 12).main FpWalk.B (s0 + i) = ((((Ub inst pub).getD u 0).toNat : ℕ) : F) := by
    intro i hi
    obtain ⟨hon, hstr, -, -, -⟩ := hrow (s0 + i) (by omega) (by omega)
    rw [tstr] at hstr
    have hq : s0 + i < 2 ^ L := by omega
    have hsq := site_mem hL (i := 12) (by decide) hq (k := 1) (by simp [hashSys, FpWalk.fpwalk, FpWalk.lookups])
    obtain ⟨u, hu, hp, hb⟩ := undo_read hL hsat hL24 hsq rfl rfl (p := (inst 12).main FpWalk.POS (s0 + i))
      (b := (inst 12).main FpWalk.B (s0 + i))
      (by simp [siteMult, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, Expr.eval,
        FpWalk.k, StarkedAir.Sha256.eval_col, wrap_zero hq, hon, hstr])
      (by simp [siteVals, siteEval, siteLookup, hashSys, hL 12 (by decide), FpWalk.fpwalk, FpWalk.lookups, FpWalk.k,
        StarkedAir.Sha256.eval_col, wrap_zero hq])
    exact ⟨u, hu, hp, by rw [← Coin.cast_val ((inst 12).main FpWalk.B (s0 + i)), hb]⟩
  obtain ⟨u0, hu0, hp0, -⟩ := hbyte 0 (by omega)
  simp only [Nat.add_zero] at hp0
  -- positions are consecutive from u0
  have hposi : ∀ i < len, ∀ u : ℕ, (inst 12).main FpWalk.POS (s0 + i) = (u : F) → u < (pub 8).val → u = u0 + i := by
    intro i hi u hp hu
    have h1 := (hrow (s0 + i) (by omega) (by omega)).2.2.2.2
    rw [hp, show s0 + i - s0 = i by omega, hp0] at h1
    have := Coin.lift (a := u) (b := u0 + i) (by push_cast; exact h1) (by unfold P; omega) (by unfold P; omega)
    exact this
  refine ⟨len, by rw [← htl], by rw [← tlen, hlen], u0, hpos.trans hp0, ?_, ?_⟩
  · obtain ⟨u, hu, hp, -⟩ := hbyte (len - 1) (by omega)
    have := hposi (len - 1) (by omega) u hp hu
    omega
  · have e : toQ ⟨(inst 14).main Coin.FH j, (inst 14).main (Coin.FH + 1) j, (inst 14).main (Coin.FH + 2) j,
        (inst 14).main (Coin.FH + 3) j⟩ = FpWalk.hQ (inst 12).main r' := by
      simp only [FpWalk.hQ, th0, th1, th2, th3]
    rw [e, hh]
    congr 1
    apply List.map_congr_left
    intro i hi
    obtain ⟨u, hu, hp, hb⟩ := hbyte i (List.mem_range.mp hi)
    rw [hb, hposi i (List.mem_range.mp hi) u hp hu]

/-! ### Byte reads -/

omit hL hsat hL24 in
theorem prevout_lookup : ∀ i < 36, Coin.lookups.getD (7 + i) ⟨0, .const 0, []⟩ =
    ⟨REL_BYTE, .neg (Coin.k Coin.KI), [.add (Coin.k Coin.START) (cst i), Coin.k (Coin.PB i)]⟩ := by
  intro i hi; interval_cases i <;> rfl

/-- **An input's prevout bytes** are the block's 36 bytes from its start. -/
theorem coin_prevout {j : ℕ} (hj : j < 2 ^ L) (hki : (inst 14).main Coin.KI j = 1) {i : ℕ} (hi : i < 36) :
    ((inst 14).main Coin.START j + (i : F)).val < (Rb inst pub).length ∧
      ((inst 14).main (Coin.PB i) j).val = ((Rb inst pub).getD ((inst 14).main Coin.START j + (i : F)).val 0).toNat := by
  have hlen : 7 + i < (hashSys.comp 14).lookups.length := by
    show 7 + i < Coin.lookups.length; rw [Coin.lookups_len]; omega
  have hsite := site_mem hL (i := 14) (by decide) hj hlen
  have hsl : siteLookup hashSys ((14, j, 7 + i) : Site) =
      ⟨REL_BYTE, .neg (Coin.k Coin.KI), [.add (Coin.k Coin.START) (cst i), Coin.k (Coin.PB i)]⟩ := prevout_lookup i hi
  have hpre : (hashSys.comp 14).air.pre = Coin.preCols := rfl
  refine byte_read_R hL hsat hL24 hsite (by decide) (by simp [siteRel, hsl]) ?_ ?_
  · show siteEval hashSys inst pub (14, j, 7 + i) (siteLookup hashSys (14, j, 7 + i)).mult = -1
    rw [hsl]
    simp [siteEval, hpre, hL 14 (by decide), Expr.eval, Coin.k, StarkedAir.Sha256.eval_col, wrap_zero hj, hki]
  · show (siteLookup hashSys (14, j, 7 + i)).vals.map (siteEval hashSys inst pub (14, j, 7 + i)) = _
    rw [hsl]
    simp [siteEval, hpre, hL 14 (by decide), Expr.eval, Coin.k, StarkedAir.Sha256.eval_col,
      StarkedAir.Sha256.eval_cst, wrap_zero hj]

/-- **An output's first script byte** (nonempty script) is the block's byte at the script's start. -/
theorem coin_script_byte {j : ℕ} (hj : j < 2 ^ L) (hko : (inst 14).main Coin.KO j = 1)
    (hzs : (inst 14).main Coin.ZS j = 0) :
    ((inst 14).main Coin.SSC j).val < (Rb inst pub).length ∧
      ((inst 14).main Coin.SB j).val = ((Rb inst pub).getD ((inst 14).main Coin.SSC j).val 0).toNat := by
  have hsite := site_mem hL (i := 14) (by decide) hj (k := 6) (by simp [hashSys, Coin.coin, Coin.lookups])
  refine byte_read_R hL hsat hL24 hsite (by decide) rfl ?_ ?_
  · simp [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      Coin.om, Coin.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hj, hko, hzs]
  · simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj]

omit hL hsat hL24 in
theorem urec_code_lookup : ∀ i < 4, URec.lookups.getD (1 + i) ⟨0, .const 0, []⟩ =
    ⟨Undo.REL_UBYTE, .neg (URec.k URec.ON), [.add (URec.k URec.S) (cst i), URec.k (URec.C i)]⟩ := by
  intro i hi; interval_cases i <;> rfl

omit hL hsat hL24 in
theorem urec_val_lookup : ∀ i < 8, URec.lookups.getD (5 + i) ⟨0, .const 0, []⟩ =
    ⟨Undo.REL_UBYTE, .neg (URec.k URec.ON), [.add (URec.k URec.S) (cst (URec.HDR + i)), URec.k (URec.V i)]⟩ := by
  intro i hi; interval_cases i <;> rfl

omit hL hsat hL24 in
theorem urec_idx_lookup : ∀ i < 3, URec.lookups.getD (13 + i) ⟨0, .const 0, []⟩ =
    ⟨Undo.REL_UBYTE, .neg (URec.k URec.ON), [.add (URec.k URec.S) (cst (4 + i)), URec.k (URec.X i)]⟩ := by
  intro i hi; interval_cases i <;> rfl

omit hL hsat hL24 in
theorem urec_byte_lookup : ∀ c < 15, URec.lookups.getD (URec.uidx c) ⟨0, .const 0, []⟩ =
    ⟨Undo.REL_UBYTE, .neg (URec.k URec.ON), [.add (URec.k URec.S) (cst c), URec.k (URec.ucol c)]⟩ := by
  intro c hc
  unfold URec.uidx URec.ucol
  by_cases h4 : c < 4
  · simp only [if_pos h4]; exact urec_code_lookup c h4
  by_cases h7 : c < 7
  · simp only [if_neg h4, if_pos h7]
    have := urec_idx_lookup (c - 4) (by omega)
    rwa [show 4 + (c - 4) = c by omega] at this
  · simp only [if_neg h4, if_neg h7]
    have := urec_val_lookup (c - 7) (by omega)
    rwa [show URec.HDR + (c - 7) = c by unfold URec.HDR; omega] at this

omit hL hsat hL24 in
theorem urec_uidx_lt : ∀ c < 15, URec.uidx c < URec.lookups.length := by
  intro c hc; unfold URec.uidx; simp [URec.lookups]; split_ifs <;> omega

/-- **An undo record's bytes.** On URec row `r`, header and amount byte `c` (code `0–3`, creating
transaction index `4–6`, amount `7–14`) is the undo byte at `S + c` (positions inside the undo stream). -/
theorem urec_bytes {r : ℕ} (hr : r < 2 ^ L) (hon : (inst 13).main URec.ON r = 1) {c : ℕ} (hc : c < 15) :
    ∃ u, u < (pub 8).val ∧ (inst 13).main URec.S r + (c : F) = (u : F) ∧
      ((inst 13).main (URec.ucol c) r).val = ((Ub inst pub).getD u 0).toNat := by
  have hpre : (hashSys.comp 13).air.pre = URec.preCols := rfl
  have hlen : URec.uidx c < (hashSys.comp 13).lookups.length := urec_uidx_lt c hc
  have hsite := site_mem hL (i := 13) (by decide) hr hlen
  have hsl : siteLookup hashSys ((13, r, URec.uidx c) : Site) =
      ⟨Undo.REL_UBYTE, .neg (URec.k URec.ON), [.add (URec.k URec.S) (cst c), URec.k (URec.ucol c)]⟩ :=
    urec_byte_lookup c hc
  have huse : isUse 13 (URec.uidx c) = true := by
    unfold URec.uidx; simp only [isUse]; split_ifs <;> simp <;> omega
  obtain ⟨u, hu, hp, hb⟩ := undo_read hL hsat hL24 hsite huse (by simp [siteRel, hsl])
    (p := (inst 13).main URec.S r + (c : F)) (b := (inst 13).main (URec.ucol c) r)
    (by
      show siteEval hashSys inst pub (13, r, URec.uidx c) (siteLookup hashSys (13, r, URec.uidx c)).mult = -1
      rw [hsl]
      simp [siteEval, hpre, hL 13 (by decide), Expr.eval, URec.k, StarkedAir.Sha256.eval_col, wrap_zero hr, hon])
    (by
      show (siteLookup hashSys (13, r, URec.uidx c)).vals.map (siteEval hashSys inst pub (13, r, URec.uidx c)) = _
      rw [hsl]
      simp [siteEval, hpre, hL 13 (by decide), Expr.eval, URec.k, StarkedAir.Sha256.eval_col,
        StarkedAir.Sha256.eval_cst, wrap_zero hr])
  exact ⟨u, hu, hp, hb⟩

/-! ### Tokens and transactions -/

/-- A row before the padding is an input or output token exactly when it is of kind `K_IN` or `K_OUT`,
and a lock-time token exactly when it is of kind `K_LOCK`. -/
theorem tok_kinds (S : Setup inst pub L) {r : ℕ} (hr : r < S.m) :
    ((Fields.tokOf (inst 1).main (Rb inst pub) r).isIo = true ↔
      ((inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1)) ∧
    ((Fields.tokOf (inst 1).main (Rb inst pub) r).isLock = true ↔ (inst 1).main Fields.K_LOCK r = 1) := by
  have fs := fields_sat' hL hsat hL24
  have hrn : r < 2 ^ L := by have := S.hmn; omega
  obtain ⟨a, ha, h1⟩ := Fields.kind_exists fs hrn
  have kat := Fields.kinds_at fs hrn ha h1
  have hpad := S.hnp r hr
  have hne : a ≠ Fields.K_PAD := by intro e; subst e; rw [hpad] at h1; exact zero_ne_one h1
  have one0 : (1 : F) ≠ 0 := one_ne_zero
  simp only [Fields.K_PAD] at hne
  interval_cases a <;>
    simp_all [Fields.tokOf, Fields.K_BLK, Fields.K_TXH, Fields.K_IN, Fields.K_NOUT, Fields.K_OUT, Fields.K_WCNT,
      Fields.K_WITEM, Fields.K_LOCK, Spec.Block.Tok.isIo, Spec.Block.Tok.isLock]

/-- **The fields' tagged tokens**: each input or output row with its lock-time count (its `TXI`). -/
theorem fields_tagged (S : Setup inst pub L) :
    Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) =
      (ioRows inst S.m).map fun ρ => (Fields.locks (inst 1).main ρ, Fields.tokOf (inst 1).main (Rb inst pub) ρ) := by
  have e : Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0 = (List.range S.m).map (Fields.tokOf (inst 1).main (Rb inst pub)) := by
    simp [Fields.toksFrom]
  rw [e, Spec.Block.tagged_range]
  have hf : ((List.range S.m).filter fun r => (Fields.tokOf (inst 1).main (Rb inst pub) r).isIo) = ioRows inst S.m := by
    unfold ioRows
    apply List.filter_congr
    intro r hr
    have := (tok_kinds hL hsat hL24 S (List.mem_range.mp hr)).1
    by_cases h : (Fields.tokOf (inst 1).main (Rb inst pub) r).isIo = true
    · simp [h, this.mp h]
    · have : ¬((inst 1).main Fields.K_OUT r = 1 ∨ (inst 1).main Fields.K_IN r = 1) := fun hh => h (this.mpr hh)
      simp only [Bool.not_eq_true] at h
      simp [h, this]
  rw [hf]
  apply List.map_congr_left
  intro ρ hρ
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  simp only [Nat.zero_add, Prod.mk.injEq, and_true]
  unfold Fields.locks
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro r hr
  have hk := (tok_kinds hL hsat hL24 S (r := r) (by have := List.mem_range.mp hr; omega)).2
  by_cases h : (Fields.tokOf (inst 1).main (Rb inst pub) r).isLock = true
  · simp [Function.comp, h, hk.mp h]
  · have : ¬ (inst 1).main Fields.K_LOCK r = 1 := fun hh => h (hk.mpr hh)
    simp only [Bool.not_eq_true] at h
    simp [Function.comp, h, this]

/-- **A coin row's transaction and position.** Coin row `j` (in use) is token `q` of transaction `t`'s
input/output tokens, with `TXI = t`: an output row's token describes output `q − |vin|`, an input row's
token input `q`. -/
theorem coin_row_tx (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {j : ℕ} (hj : j < e) :
    ∃ (t q : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx ∧
      (inst 14).main Coin.TXI j = (t : F) ∧
      j = ((parts.take t).map List.length).sum + q ∧ q < tx.vin.length + tx.vout.length ∧
      ((inst 14).main Coin.KO j = 1 → tx.vin.length ≤ q ∧ ∃ o, tx.vout[q - tx.vin.length]? = some o ∧
        Spec.Block.OutTok o (Fields.tokOf (inst 1).main (Rb inst pub) ((ioRows inst S.m).getD j 0))) ∧
      ((inst 14).main Coin.KI j + (inst 14).main Coin.CBI j = 1 → q < tx.vin.length ∧ ∃ i, tx.vin[q]? = some i ∧
        Spec.Block.InTok i (Fields.tokOf (inst 1).main (Rb inst pub) ((ioRows inst S.m).getD j 0))) := by
  have cs := coin_sat hL hsat hL24
  have fs := fields_sat' hL hsat hL24
  have hft := fields_tagged hL hsat hL24 S
  rw [htg] at hft
  set io := ioRows inst S.m with hio
  have hjl : j < (Spec.Block.tagParts 0 parts).length := by
    rw [hft, List.length_map]; omega
  obtain ⟨t, q, ht, hq, hget, hidx⟩ := Spec.Block.tagParts_get 0 parts j hjl
  have hpair : (Fields.locks (inst 1).main (io.getD j 0), Fields.tokOf (inst 1).main (Rb inst pub) (io.getD j 0)) =
      (0 + t, (parts.getD t []).getD q (.lock [])) := by
    have := congrArg (fun l => l[j]?) hft
    rw [hget, List.getElem?_map, List.getElem?_eq_getElem (by omega), Option.map_some, Option.some.injEq] at this
    rw [List.getD_eq_getElem _ _ (by omega)]; exact this.symm
  simp only [Prod.mk.injEq, Nat.zero_add] at hpair
  obtain ⟨hlocks, htok⟩ := hpair
  -- the transaction
  have hlenp := hf.length_eq
  obtain ⟨tx, htx⟩ : ∃ tx, S.b.txs[t]? = some tx := ⟨S.b.txs[t], List.getElem?_eq_getElem (by omega)⟩
  have hpt : List.Forall₂ Spec.Block.IoTx [tx] [parts.getD t []] := by
    have := List.forall₂_iff_get.mp hf
    refine List.Forall₂.cons ?_ List.Forall₂.nil
    have h2 := this.2 t (by omega) (by omega)
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at htx
    simpa [← htx] using h2
  obtain ⟨li, lo, hlilo, hfi, hfo⟩ : Spec.Block.IoTx tx (parts.getD t []) := by
    cases hpt with | cons h _ => exact h
  have hli := hfi.length_eq
  have hlo := hfo.length_eq
  -- the coin row's TXI is its token's lock count
  have hρ : io.getD j 0 ∈ io := by rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _
  obtain ⟨hρm, -⟩ := mem_ioRows.mp hρ
  have hρn : io.getD j 0 < 2 ^ L := by have := S.hmn; omega
  have htxi : (inst 1).main Fields.TXI (io.getD j 0) = (t : F) := by
    rw [Fields.txi_count fs _ hρn, hlocks]
  have htxi' : (inst 1).main Fields.TXI ((ioRows inst S.m)[j]?.getD 0) = (t : F) := by
    rw [← List.getD_eq_getElem?_getD]; exact htxi
  have hrt := coin_row_tok hL hsat hL24 S he hon hlen hst hj
  have hj2 : j < 2 ^ L := by omega
  have hcoinTXI : (inst 14).main Coin.TXI j = (t : F) := by
    have cs' := cs
    rcases Coin.kinds cs hj2 with h | h | h | h
    · obtain ⟨-, hT⟩ := hrt.1 h.1
      have := congrArg (fun l => l.getD 0 0) hT
      simp only [cOut, fOut] at this
      simpa [htxi'] using this
    · obtain ⟨-, hT⟩ := hrt.2 (by rw [h.2.1, h.2.2.1]; simp)
      rw [hT, htxi]
    · obtain ⟨-, hT⟩ := hrt.2 (by rw [h.2.1, h.2.2.1]; simp)
      rw [hT, htxi]
    · exact absurd ((hon j hj2).mpr hj) (by rw [h.2.2.2]; exact zero_ne_one)
  refine ⟨t, q, tx, htx, hcoinTXI, hidx, by rw [hlilo] at hq; simp at hq; omega, fun hko => ?_, fun hki => ?_⟩
  · obtain ⟨hk, -⟩ := hrt.1 hko
    -- an output token: not among the inputs' tokens
    have hout : ∃ v s, Fields.tokOf (inst 1).main (Rb inst pub) (io.getD j 0) = .out v s := by
      have kat := Fields.kinds_at fs hρn (a := Fields.K_OUT) (by decide) hk
      unfold Fields.tokOf
      rw [if_neg (by rw [kat Fields.K_BLK (by decide)]; simp [Fields.K_BLK, Fields.K_OUT]),
        if_neg (by rw [kat Fields.K_TXH (by decide)]; simp [Fields.K_TXH, Fields.K_OUT]),
        if_neg (by rw [kat Fields.K_IN (by decide)]; simp [Fields.K_IN, Fields.K_OUT]),
        if_neg (by rw [kat Fields.K_NOUT (by decide)]; simp [Fields.K_NOUT, Fields.K_OUT]), if_pos hk]
      exact ⟨_, _, rfl⟩
    obtain ⟨v, s, hvs⟩ := hout
    have hqge : li.length ≤ q := by
      by_contra hc; push Not at hc
      have hin := List.forall₂_iff_get.mp hfi
      have h2 := hin.2 q (by omega) hc
      simp only [List.get_eq_getElem] at h2
      have : (parts.getD t []).getD q (.lock []) = li[q] := by
        rw [hlilo, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hc]
      rw [← this, ← htok, hvs] at h2
      simp [Spec.Block.InTok] at h2
    refine ⟨by omega, ?_⟩
    have hout2 := List.forall₂_iff_get.mp hfo
    have hq2 : q - li.length < lo.length := by rw [hlilo] at hq; simp at hq; omega
    refine ⟨tx.vout[q - li.length], by rw [hli]; exact List.getElem?_eq_getElem (by omega), ?_⟩
    have h2 := hout2.2 (q - li.length) (by omega) hq2
    simp only [List.get_eq_getElem] at h2
    have : (parts.getD t []).getD q (.lock []) = lo[q - li.length] := by
      rw [hlilo, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right hqge]
    rw [htok, this]
    simpa [hli] using h2
  · obtain ⟨hk, -⟩ := hrt.2 hki
    have hinp : ∃ a b c d, Fields.tokOf (inst 1).main (Rb inst pub) (io.getD j 0) = .inp a b c d := by
      have kat := Fields.kinds_at fs hρn (a := Fields.K_IN) (by decide) hk
      unfold Fields.tokOf
      rw [if_neg (by rw [kat Fields.K_BLK (by decide)]; simp [Fields.K_BLK, Fields.K_IN]),
        if_neg (by rw [kat Fields.K_TXH (by decide)]; simp [Fields.K_TXH, Fields.K_IN]), if_pos hk]
      exact ⟨_, _, _, _, rfl⟩
    obtain ⟨a, b, c, d, hab⟩ := hinp
    have hqlt : q < li.length := by
      by_contra hc; push Not at hc
      have hout2 := List.forall₂_iff_get.mp hfo
      have hq2 : q - li.length < lo.length := by rw [hlilo] at hq; simp at hq; omega
      have h2 := hout2.2 (q - li.length) (by omega) hq2
      simp only [List.get_eq_getElem] at h2
      have : (parts.getD t []).getD q (.lock []) = lo[q - li.length] := by
        rw [hlilo, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right hc]
      rw [← this, ← htok, hab] at h2
      simp [Spec.Block.OutTok] at h2
    refine ⟨by omega, tx.vin[q], List.getElem?_eq_getElem (by omega), ?_⟩
    have hin := List.forall₂_iff_get.mp hfi
    have h2 := hin.2 q (by omega) hqlt
    simp only [List.get_eq_getElem] at h2
    have : (parts.getD t []).getD q (.lock []) = li[q] := by
      rw [hlilo, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left hqlt]
    rw [htok, this]
    simpa using h2

/-! ### Output indices -/

omit hL hsat hL24 in
/-- The earlier parts' total length. -/
theorem pre_succ (parts : List (List Spec.Block.Tok)) {t : ℕ} (ht : t < parts.length) :
    ((parts.take (t + 1)).map List.length).sum = ((parts.take t).map List.length).sum + (parts.getD t []).length := by
  rw [List.take_succ, List.map_append, List.sum_append, List.getElem?_eq_getElem ht, List.getD_eq_getElem _ _ ht]
  simp

omit hL hsat hL24 in
theorem pre_mono (parts : List (List Spec.Block.Tok)) : ∀ {t t' : ℕ}, t ≤ t' → t' ≤ parts.length →
    ((parts.take t).map List.length).sum ≤ ((parts.take t').map List.length).sum := by
  intro t t' h _
  have := List.take_prefix_take_left (l := parts) h
  exact List.Sublist.sum_le_sum ((this.sublist).map _) (fun _ _ => Nat.zero_le _)

omit hL hsat hL24 in
/-- **Positions decompose uniquely.** -/
theorem decomp_unique (parts : List (List Spec.Block.Tok)) {t q t' q' : ℕ} (ht : t < parts.length)
    (ht' : t' < parts.length) (hq : q < (parts.getD t []).length) (hq' : q' < (parts.getD t' []).length)
    (he : ((parts.take t).map List.length).sum + q = ((parts.take t').map List.length).sum + q') : t = t' ∧ q = q' := by
  rcases Nat.lt_trichotomy t t' with h | h | h
  · exfalso
    have h1 := pre_succ parts ht
    have h2 := pre_mono parts (t := t + 1) (t' := t') (by omega) (by omega)
    omega
  · subst h; exact ⟨rfl, by omega⟩
  · exfalso
    have h1 := pre_succ parts ht'
    have h2 := pre_mono parts (t := t' + 1) (t' := t) (by omega) (by omega)
    omega

omit hL hsat hL24 in
theorem part_len {txs : List Spec.Block.Tx} {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx txs parts)
    {t : ℕ} {tx : Spec.Block.Tx} (htx : txs[t]? = some tx) :
    t < parts.length ∧ (parts.getD t []).length = tx.vin.length + tx.vout.length := by
  have hl := hf.length_eq
  have htl : t < txs.length := (List.getElem?_eq_some_iff.mp htx).1
  refine ⟨by omega, ?_⟩
  have h2 := (List.forall₂_iff_get.mp hf).2 t htl (by omega)
  simp only [List.get_eq_getElem] at h2
  rw [List.getElem?_eq_getElem htl, Option.some.injEq] at htx
  subst htx
  obtain ⟨li, lo, he, hi, ho⟩ := h2
  rw [List.getD_eq_getElem _ _ (by omega), he, List.length_append, hi.length_eq, ho.length_eq]

/-- Every transaction has an input. -/
theorem vin_pos (S : Setup inst pub L) {t : ℕ} {tx : Spec.Block.Tx} (htx : S.b.txs[t]? = some tx) :
    1 ≤ tx.vin.length := by
  have hwf := (Spec.Block.toksBlock_sound S.htok).1.2.2 tx (List.mem_of_getElem? htx)
  have := hwf.2.2.1
  exact List.length_pos_of_ne_nil this

/-- **An output row's index** is the output's index in its transaction. -/
theorem coin_vout (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts) :
    ∀ j < e, (inst 14).main Coin.KO j = 1 → ∀ t q tx, S.b.txs[t]? = some tx →
      j = ((parts.take t).map List.length).sum + q → q < tx.vin.length + tx.vout.length →
      (inst 14).main Coin.VOUT j = ((q - tx.vin.length : ℕ) : F) := by
  have cs := coin_sat hL hsat hL24
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hko t q tx htx hjq hq
    have hrow := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
    obtain ⟨t0, q0, tx0, htx0, -, hjq0, hq0, hko0, -⟩ := hrow
    obtain ⟨hpl, hpe⟩ := part_len hf htx
    obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
    obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
    rw [htx] at htx0; obtain rfl := Option.some.inj htx0
    have hvq := (hko0 hko).1
    have hv1 := vin_pos hL hsat hL24 S htx
    -- the previous row
    have hj1 : 1 ≤ j := by
      by_contra hc; push Not at hc
      have : ((parts.take t).map List.length).sum = 0 := by omega
      omega
    obtain ⟨p, rfl⟩ : ∃ p, j = p + 1 := ⟨j - 1, by omega⟩
    have hp : p < e := by omega
    have hvs := (Coin.vout_spec cs (r := p) (by omega) hko).1
    obtain ⟨t1, q1, tx1, htx1, -, hjq1, hq1, hko1, hki1⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hp
    obtain ⟨hpl1, hpe1⟩ := part_len hf htx1
    have hE : ((parts.take t).map List.length).sum + (q - 1) = ((parts.take t1).map List.length).sum + q1 := by
      omega
    obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl1 (q := q - 1) (by omega) (by omega) hE
    rw [htx] at htx1; obtain rfl := Option.some.inj htx1
    have hpon : Coin.onV (inst 14).main p = 1 := (hon p (by omega)).mpr hp
    rcases Nat.eq_or_lt_of_le hvq with heq | hlt
    · -- the transaction's first output: the previous row is an input
      have hko0' : (inst 14).main Coin.KO p = 0 := by
        rcases Coin.kinds cs (show p < 2 ^ L by omega) with h | h | h | h
        · exact absurd (hko1 h.1).1 (by omega)
        · exact h.1
        · exact h.1
        · rw [h.2.2.2] at hpon; exact absurd hpon zero_ne_one
      rw [hvs, hko0', zero_mul, ← heq, Nat.sub_self, Nat.cast_zero]
    · -- a later output: the previous row is the previous output
      have hkop : (inst 14).main Coin.KO p = 1 := by
        rcases Coin.kinds cs (show p < 2 ^ L by omega) with h | h | h | h
        · exact h.1
        · exact absurd (hki1 (by rw [h.2.1, h.2.2.1]; simp)).1 (by omega)
        · exact absurd (hki1 (by rw [h.2.1, h.2.2.1]; simp)).1 (by omega)
        · rw [h.2.2.2] at hpon; exact absurd hpon zero_ne_one
      rw [hvs, hkop, one_mul, ih p (by omega) hp hkop t (q - 1) tx htx (by omega) (by omega)]
      rw [show q - tx.vin.length = (q - 1 - tx.vin.length) + 1 by omega]
      push_cast; ring

/-- **A coin row's kind is its position's**: an output iff `q ≥ |vin|`; a non-coinbase input iff `q < |vin|`
in a transaction `t ≥ 1`; the coinbase input iff `q < |vin|` in transaction 0. -/
theorem coin_kind_pos (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {j t q : ℕ} {tx : Spec.Block.Tx} (hj : j < e) (htx : S.b.txs[t]? = some tx)
    (hjq : j = ((parts.take t).map List.length).sum + q) (hq : q < tx.vin.length + tx.vout.length) :
    ((inst 14).main Coin.KO j = 1 ↔ tx.vin.length ≤ q) ∧
      ((inst 14).main Coin.KI j = 1 ↔ q < tx.vin.length ∧ 1 ≤ t) ∧
      ((inst 14).main Coin.CBI j = 1 ↔ q < tx.vin.length ∧ t = 0) := by
  have cs := coin_sat hL hsat hL24
  have hj2 : j < 2 ^ L := by omega
  obtain ⟨t0, q0, tx0, htx0, htxi, hjq0, hq0, hko, hki⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
  obtain ⟨hpl, hpe⟩ := part_len hf htx
  obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
  obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjq.symm.trans hjq0)
  rw [htx] at htx0; obtain rfl := Option.some.inj htx0
  have htN : t < 2 ^ L := by have := (List.getElem?_eq_some_iff.mp htx).1; have := S.hN25; omega
  have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
  have ht0 : (t : F) = 0 ↔ t = 0 := by
    constructor
    · intro h; exact Coin.lift (a := t) (b := 0) (by simpa using h) (by unfold P; omega) (by unfold P; norm_num)
    · intro h; simp [h]
  have hcbo := Coin.cbo_spec cs hj2
  rw [htxi, ht0] at hcbo
  have hon' := (hon j hj2).mpr hj
  rcases Coin.kinds cs hj2 with h | h | h | h
  · have := (hko h.1).1
    refine ⟨⟨fun _ => this, fun _ => h.1⟩, ⟨fun e => by rw [h.2.1] at e; exact absurd e zero_ne_one, fun e => by omega⟩,
      ⟨fun e => by rw [h.2.2.1] at e; exact absurd e zero_ne_one, fun e => by omega⟩⟩
  · have hq' := (hki (by rw [h.2.1, h.2.2.1]; simp)).1
    have hcb0 := hcbo.2.2.2 h.2.1
    have ht1 : 1 ≤ t := by
      by_contra hc; have : t = 0 := by omega
      rw [hcbo.1.mpr this] at hcb0; exact one_ne_zero hcb0
    refine ⟨⟨fun e => by rw [h.1] at e; exact absurd e zero_ne_one, fun e => by omega⟩, ⟨fun _ => ⟨hq', ht1⟩, fun _ => h.2.1⟩,
      ⟨fun e => by rw [h.2.2.1] at e; exact absurd e zero_ne_one, fun e => by omega⟩⟩
  · have hq' := (hki (by rw [h.2.1, h.2.2.1]; simp)).1
    have hcb1 := hcbo.2.2.1 h.2.2.1
    have ht0' : t = 0 := hcbo.1.mp hcb1
    refine ⟨⟨fun e => by rw [h.1] at e; exact absurd e zero_ne_one, fun e => by omega⟩,
      ⟨fun e => by rw [h.2.1] at e; exact absurd e zero_ne_one, fun e => by omega⟩, ⟨fun _ => ⟨hq', ht0'⟩, fun _ => h.2.2.1⟩⟩
  · rw [h.2.2.2] at hon'; exact absurd hon' zero_ne_one

omit hL hsat hL24 in
theorem exists_get {α : Type} {l : List α} {i : ℕ} (h : i < l.length) : ∃ x, l[i]? = some x :=
  ⟨l[i], List.getElem?_eq_getElem h⟩

omit hL hsat hL24 in
/-- The non-coinbase inputs before position `(t, q)`: all of transactions `1 … t − 1`, and `min q |vin|`
of transaction `t` if `t ≥ 1`. -/
def vinLen (txs : List Spec.Block.Tx) (t : ℕ) : ℕ := (txs[t]?.map (·.vin.length)).getD 0

def inBefore (txs : List Spec.Block.Tx) (t q : ℕ) : ℕ :=
  ((List.range t).map fun t' => if 1 ≤ t' then vinLen txs t' else 0).sum + (if 1 ≤ t then min q (vinLen txs t) else 0)

/-- **An input row's record index** is the number of non-coinbase inputs before it. -/
theorem coin_J (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts) :
    ∀ j < e, ∀ t q tx, S.b.txs[t]? = some tx → j = ((parts.take t).map List.length).sum + q →
      q < tx.vin.length + tx.vout.length → (inst 14).main Coin.J j = ((inBefore S.b.txs t q : ℕ) : F) := by
  have cs := coin_sat hL hsat hL24
  have hjs := Coin.j_spec cs
  intro j
  induction j with
  | zero =>
    intro hj t q tx htx hjq hq
    have h0 := hjs 0 (by omega)
    simp only [Finset.range_zero, Finset.sum_empty] at h0
    rw [h0]
    -- position 0 is transaction 0's first token
    have ht0 : t = 0 := by
      by_contra hc
      obtain ⟨hpl, -⟩ := part_len hf htx
      have h1 := pre_mono parts (t := 1) (t' := t) (by omega) (by omega)
      have hl0 : 0 < S.b.txs.length := by have := (List.getElem?_eq_some_iff.mp htx).1; omega
      obtain ⟨tx0, htx0⟩ := exists_get hl0
      have h2 := pre_succ parts (t := 0) (part_len hf htx0).1
      have := (part_len hf htx0).2
      have := vin_pos hL hsat hL24 S htx0
      have h0 : ((parts.take 0).map List.length).sum = 0 := by simp
      rw [Nat.zero_add] at h2
      omega
    subst ht0
    have : q = 0 := by simp at hjq; omega
    subst this
    simp [inBefore]
  | succ p ih =>
    intro hj t q tx htx hjq hq
    have hJ1 : (inst 14).main Coin.J (p + 1) = (inst 14).main Coin.J p + (inst 14).main Coin.KI p := by
      rw [hjs (p + 1) (by omega), hjs p (by omega), Finset.sum_range_succ]
    obtain ⟨hpl, hpe⟩ := part_len hf htx
    rcases Nat.eq_zero_or_pos q with hq0 | hq1
    · -- the transaction's first token: the previous row is transaction `t − 1`'s last
      subst hq0
      have ht1 : 1 ≤ t := by
        by_contra hc; have : t = 0 := by omega
        subst this; simp at hjq
      have hl1 : t - 1 < S.b.txs.length := by have := (List.getElem?_eq_some_iff.mp htx).1; omega
      obtain ⟨tx', htx'⟩ := exists_get hl1
      obtain ⟨hpl', hpe'⟩ := part_len hf htx'
      have hv' := vin_pos hL hsat hL24 S htx'
      have hps := pre_succ parts (t := t - 1) hpl'
      rw [show t - 1 + 1 = t by omega] at hps
      have hpq : p = ((parts.take (t - 1)).map List.length).sum + (tx'.vin.length + tx'.vout.length - 1) := by omega
      have ihp := ih (by omega) (t - 1) _ tx' htx' hpq (by omega)
      have hk := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (by omega) htx' hpq (by omega)).2.1
      rw [hJ1, ihp]
      have hvl : vinLen S.b.txs (t - 1) = tx'.vin.length := by simp [vinLen, htx']
      have hsplit : ((List.range t).map fun t' => if 1 ≤ t' then vinLen S.b.txs t' else 0).sum =
          ((List.range (t - 1)).map fun t' => if 1 ≤ t' then vinLen S.b.txs t' else 0).sum +
            (if 1 ≤ t - 1 then vinLen S.b.txs (t - 1) else 0) := by
        conv_lhs => rw [show t = t - 1 + 1 by omega, List.range_succ]
        simp
      by_cases hki : (inst 14).main Coin.KI p = 1
      · obtain ⟨hql, ht2⟩ := hk.mp hki
        rw [hki]
        have hn : inBefore S.b.txs t 0 = inBefore S.b.txs (t - 1) (tx'.vin.length + tx'.vout.length - 1) + 1 := by
          simp only [inBefore, if_pos ht1, if_pos ht2, Nat.zero_min, add_zero, hsplit, hvl]
          rw [min_eq_left (by omega)]; omega
        rw [hn]; push_cast; ring
      · have hki0 : (inst 14).main Coin.KI p = 0 := by
          rcases Coin.bool_col cs (c := Coin.KI) (by simp) (show p < 2 ^ L by omega) with h | h
          · exact h
          · exact absurd h hki
        rw [hki0, add_zero]
        simp only [inBefore, if_pos ht1, Nat.zero_min, add_zero, hsplit, hvl]
        congr 1
        by_cases ht2 : 1 ≤ t - 1
        · have : ¬ (tx'.vin.length + tx'.vout.length - 1 < tx'.vin.length) := fun hh => hki (hk.mpr ⟨hh, ht2⟩)
          rw [if_pos ht2, if_pos ht2, min_eq_right (by omega)]
        · rw [if_neg ht2, if_neg ht2]
    · -- a later token of the same transaction
      have hpq : p = ((parts.take t).map List.length).sum + (q - 1) := by omega
      have ihp := ih (by omega) t (q - 1) tx htx hpq (by omega)
      have hk := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg (by omega) htx hpq (by omega)).2.1
      have hvl : vinLen S.b.txs t = tx.vin.length := by simp [vinLen, htx]
      rw [hJ1, ihp]
      by_cases hki : (inst 14).main Coin.KI p = 1
      · obtain ⟨hql, ht1⟩ := hk.mp hki
        rw [hki]
        have hn : inBefore S.b.txs t q = inBefore S.b.txs t (q - 1) + 1 := by
          simp only [inBefore, if_pos ht1, hvl]
          rw [min_eq_left (by omega), min_eq_left (by omega)]; omega
        rw [hn]; push_cast; ring
      · have hki0 : (inst 14).main Coin.KI p = 0 := by
          rcases Coin.bool_col cs (c := Coin.KI) (by simp) (show p < 2 ^ L by omega) with h | h
          · exact h
          · exact absurd h hki
        rw [hki0, add_zero]
        simp only [inBefore, hvl]
        congr 1
        by_cases ht1 : 1 ≤ t
        · have : ¬ (q - 1 < tx.vin.length) := fun hh => hki (hk.mpr ⟨hh, ht1⟩)
          rw [if_pos ht1, if_pos ht1, min_eq_right (by omega), min_eq_right (by omega)]
        · rw [if_neg ht1, if_neg ht1]

end System

end StarkedAir.Block
