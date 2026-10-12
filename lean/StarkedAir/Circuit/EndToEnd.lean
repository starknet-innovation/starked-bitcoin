/-
**The plain verifier, end to end (VL-E2E).** The pieces proven separately (the composition check
`sys_sound`, the LogUp balance check `balance_sound`, LogUp's telescoping `logup_sum`, the
Schwartz–Zippel step `logup_sz`) composed into one statement: if the leaf circuit's composition and
balance programs hold, then — under the STARK soundness assumption (`StarkSound`, stated, not proven)
— the committed traces satisfy every component's AIR, and, for challenges `(α, z)` outside the
`logup_sz` bad set of those traces' entries (`SZGood`), the system balances with the public entries:
`sys.SatisfiedExt`. For the header-chain leaf this gives `leaf_valid_T` (`plain_leaf_valid`).

**What is assumed, and where.**
- `StarkSound` (row form of STARK soundness: FRI, DEEP-ALI, Merkle commitments in the random-oracle
  model). For the terms the composition check combines (`terms`: each component's constraints and
  LogUp batch terms, as polynomial expressions of its columns), if their Horner combination with the
  random coefficient at the OODS samples, times `1/Z(oods)`, equals the composition polynomial's
  sampled value `C`, then base-field columns exist on which every term vanishes at every row.
  Except with the configuration's soundness error, this holds for the columns committed in the
  proof, and they are what the samples are values of. What makes the assumption's premises hold in
  the circuit is proven elsewhere: the DEEP responses are the mixed samples (`deep_sound`), the
  Merkle leaves and paths hash to the committed roots (`leaf_sound`, `path_check_sound`), every
  challenge is drawn after what it binds (`Transcript.lean`, `Channel.lean`). FRI itself is inside
  stwo-zig (VL-FRI).
- `SZGood` for the extracted traces' entries at the circuit's `(α, z)`: `logup_sz` proves the pairs
  failing it number at most `(N²·L + 2N)·|QM31|` out of `|QM31|²`; the challenges are drawn after the
  main commitment (`elements_bound`), so in the random-oracle model they fail it with probability at
  most `(N²·L + 2N)/|QM31|`.

Everything else is proven here: the composition value is that Horner combination for `sys`'s exported
constraints and lookups (`partTerms_eq`, `sys_sound`), vanishing rows give the AIR (`row_constraints`)
and each component's fractions summing to its claimed sum (`comp_frac_sum`, via `logup_sum`), the
balance check makes all fractions sum to zero (`fracSum_zero`), and `logup_sz`'s conclusion gives
`BalancedExt` (`balancedExt_of_poly`).
-/
import StarkedAir.Circuit.Balance
import StarkedAir.Circuit.CompositionSound
import StarkedAir.LogUp
import StarkedAir.LogUpSZ
import StarkedAir.Gadgets.AggregateTree

namespace StarkedAir.Circuit.EndToEnd

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.Composition StarkedAir.LogUpSZ Polynomial
open StarkedAir.Spec.QM31 (QM toQ emb emb_inj)

/-! ### Terms as functions of a valuation -/

/-- A component's values at one point (the OODS point, or a trace row): its preprocessed and main
columns by offset, and its interaction base columns by offset. -/
structure Val where
  leaf : Tree → ℕ → ℤ → QM
  inter : ℕ → ℤ → QM

/-- **A component's terms** at a valuation: its constraints, then (with lookups) its LogUp batch
terms. `share` is the claimed sum's share per row (`claimed / 2^L`). These are the polynomial
identities the composition check combines. -/
noncomputable def terms (c : Comp) (α z share : QM) (pub : ℕ → QM) (v : Val) : List QM :=
  c.air.constraints.map (fun e => e.evalR cstQ v.leaf pub) ++
  if c.lookups.isEmpty then [] else
    (List.range ((c.lookups.length + 1) / 2)).map (batchTerm (fun j => (lk c j).mult.evalR cstQ v.leaf pub)
      (fun j => fingerprint α (emb ((lk c j).rel : F)) ((lk c j).vals.map (·.evalR cstQ v.leaf pub)) - z)
      (fun b => secureVal fun k => v.inter (4 * b + k) 0)
      (secureVal fun k => v.inter (4 * ((c.lookups.length + 1) / 2 - 1) + k) (-1))
      share c.lookups.length ((c.lookups.length + 1) / 2))

/-- The circuit's valuation of a component at the OODS point: the sample registers. The last batch
column has two samples (index 0 at offset −1, index 1 at offset 0); the others one. -/
noncomputable def oodsVal (ρ : ℕ → Q) (c : Comp) (pr : PartRegs) : Val :=
  ⟨leafQ ρ pr.ci, fun k off =>
    val ρ (pr.inter k (if off = -1 then 0 else if 4 * (pB c - 1) ≤ k then 1 else 0))⟩

/-- **The composition terms are `terms` at the OODS samples.** -/
theorem partTerms_eq (ρ : ℕ → Q) (c : Comp) (pr : PartRegs) (sh : Shared) :
    partTerms ρ c pr sh = terms c (val ρ sh.alpha) (val ρ sh.z) (val ρ pr.claimed * emb (ninv sh.logSize : F))
      (pubQ ρ pr.ci) (oodsVal ρ c pr) := by
  unfold partTerms terms
  refine congrArg₂ (· ++ ·) (List.map_congr_left fun _ _ => rfl) ?_
  by_cases hE : c.lookups.isEmpty
  · simp [hE]
  simp only [hE, if_false, Bool.false_eq_true]
  apply List.map_congr_left
  intro b hb
  have hbB : b < (c.lookups.length + 1) / 2 := List.mem_range.mp hb
  have hS : ∀ i < (c.lookups.length + 1) / 2,
      (secureVal fun k => val ρ (pr.inter (4 * i + k) (if i + 1 = (c.lookups.length + 1) / 2 then 1 else 0))) =
      (secureVal fun k => (oodsVal ρ c pr).inter (4 * i + k) 0) := by
    intro i hi
    unfold secureVal oodsVal
    simp only [show (0 : ℤ) ≠ -1 by decide, if_false]
    have key : ∀ k < 4, (if 4 * (pB c - 1) ≤ 4 * i + k then 1 else 0) =
        (if i + 1 = (c.lookups.length + 1) / 2 then 1 else 0) := by
      intro k hk
      unfold pB pL
      by_cases h : i + 1 = (c.lookups.length + 1) / 2
      · rw [if_pos h, if_pos (by omega)]
      · rw [if_neg h, if_neg (by omega)]
    rw [key 0 (by norm_num), key 1 (by norm_num), key 2 (by norm_num), key 3 (by norm_num)]
  refine batchTerm_congr hbB rfl (fun _ _ => rfl) (fun _ _ => rfl) hS ?_ rfl
  unfold secureVal oodsVal
  simp

/-! ### Rows -/

/-- A component's valuation at row `r` of an `n`-row trace with base-field main columns `main` and
interaction base columns `I`. -/
noncomputable def rowVal (n : ℕ) (pre : List PreCol) (main I : ℕ → ℕ → F) (r : ℕ) : Val :=
  ⟨fun t j off => emb (match t with
      | .pre => (pre.getD j (.periodic [0])).eval n (wrap n r off)
      | .main => main j (wrap n r off)),
   fun k off => emb (I k (wrap n r off))⟩

/-- `evalR` commutes with a ring hom. -/
theorem evalR_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (cst : ℕ → R)
    (leaf : Tree → ℕ → ℤ → R) (pub : ℕ → R) (e : Expr) :
    f (e.evalR cst leaf pub) = e.evalR (fun v => f (cst v)) (fun t i o => f (leaf t i o)) (fun i => f (pub i)) := by
  induction e with
  | col t i off => rfl
  | const v => rfl
  | add a b iha ihb => simp [Expr.evalR, iha, ihb]
  | sub a b iha ihb => simp [Expr.evalR, iha, ihb]
  | mul a b iha ihb => simp [Expr.evalR, iha, ihb]
  | neg a iha => simp [Expr.evalR, iha]
  | pub i => rfl

/-- `emb` as a ring hom. -/
noncomputable def embHom : F →+* QM := algebraMap F QM

theorem embHom_apply (x : F) : embHom x = emb x := rfl

/-- **At a row, `evalR` is the embedded trace value.** -/
theorem evalR_row (n : ℕ) (pre : List PreCol) (pub : ℕ → F) (main I : ℕ → ℕ → F) (r : ℕ) (e : Expr) :
    e.evalR cstQ (rowVal n pre main I r).leaf (fun j => emb (pub j)) = emb (e.eval n pre pub main r) := by
  rw [eval_eq_evalR, ← embHom_apply, evalR_map]
  congr 1

/-- The previous row, as `wrap` computes it. -/
theorem wrap_neg_one {n r : ℕ} (hr : r < n) : wrap n r (-1) = LogUp.prev n r := by
  unfold wrap LogUp.prev
  have e : (r : ℤ) + -1 = ((r + n - 1 : ℕ) : ℤ) + (-1) * (n : ℤ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [e, Int.add_mul_emod_self_right, ← Int.natCast_mod, Int.toNat_natCast]


/-! ### One component's LogUp sum -/

/-- Pairing: summing over batches of two is summing over lookups. -/
theorem pair_sum (f : ℕ → QM) (L : ℕ) :
    ∑ b ∈ Finset.range ((L + 1) / 2), (f (2 * b) + if 2 * b + 1 < L then f (2 * b + 1) else 0) =
      ∑ j ∈ Finset.range L, f j := by
  set h : ℕ → QM := fun j => if j < L then f j else 0 with hh
  have h2 : ∀ B, ∑ j ∈ Finset.range (2 * B), h j = ∑ b ∈ Finset.range B, (h (2 * b) + h (2 * b + 1)) := by
    intro B
    induction B with
    | zero => simp
    | succ B ih =>
      rw [show 2 * (B + 1) = 2 * B + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ, add_assoc]
  have hL : ∑ j ∈ Finset.range L, f j = ∑ j ∈ Finset.range (2 * ((L + 1) / 2)), h j := by
    obtain ⟨e, he⟩ : ∃ e, 2 * ((L + 1) / 2) = L + e ∧ e ≤ 1 := ⟨2 * ((L + 1) / 2) - L, by omega, by omega⟩
    rw [he.1, Finset.sum_range_add]
    have z : ∑ x ∈ Finset.range e, h (L + x) = 0 :=
      Finset.sum_eq_zero fun x _ => by simp [hh]
    rw [z, add_zero]
    exact Finset.sum_congr rfl fun j hj => by simp [hh, Finset.mem_range.mp hj]
  rw [hL, h2]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_range.mp hb
  simp only [hh, if_pos (show 2 * b < L by omega)]

/-- A batch's numerator and denominator, as `batchTerm` forms them. -/
noncomputable def bN (m d : ℕ → QM) (L b : ℕ) : QM :=
  if 2 * b + 1 < L then m (2 * b) * d (2 * b + 1) + m (2 * b + 1) * d (2 * b) else m (2 * b)
noncomputable def bD (d : ℕ → QM) (L b : ℕ) : QM :=
  if 2 * b + 1 < L then d (2 * b) * d (2 * b + 1) else d (2 * b)

theorem bN_div_bD (m d : ℕ → QM) (L b : ℕ) (hd0 : d (2 * b) ≠ 0) (hd1 : 2 * b + 1 < L → d (2 * b + 1) ≠ 0) :
    bN m d L b / bD d L b = m (2 * b) / d (2 * b) + if 2 * b + 1 < L then m (2 * b + 1) / d (2 * b + 1) else 0 := by
  unfold bN bD
  split
  · rename_i h; rw [LogUp.pair_frac hd0 (hd1 h)]
  · simp

theorem bD_ne (d : ℕ → QM) (L b : ℕ) (hd0 : d (2 * b) ≠ 0) (hd1 : 2 * b + 1 < L → d (2 * b + 1) ≠ 0) :
    bD d L b ≠ 0 := by
  unfold bD; split
  · rename_i h; exact mul_ne_zero hd0 (hd1 h)
  · exact hd0

theorem two_pow_ne (L : ℕ) : ((2 ^ L : ℕ) : QM) ≠ 0 := by
  rw [← map_natCast embHom]
  intro h
  have h' : embHom ((2 ^ L : ℕ) : F) = embHom 0 := h.trans (map_zero embHom).symm
  have := emb_inj h'
  push_cast at this
  exact pow_ne_zero L (by decide : (2 : F) ≠ 0) this

theorem ninv_share (L : ℕ) (c : QM) : c * emb (ninv L : F) = c / ((2 ^ L : ℕ) : QM) := by
  rw [div_eq_mul_inv]; congr 1
  rw [ninv, ZMod.natCast_zmod_val, ← embHom_apply, map_inv₀, map_pow]
  push_cast; rfl

section Comp

variable (c : Comp) (L : ℕ) (pre : List PreCol) (pub : ℕ → F) (main I : ℕ → ℕ → F) (α z claimed : QM)

/-- Lookup `j`'s multiplicity at row `r`. -/
noncomputable def rM (r j : ℕ) : QM := emb ((lk c j).mult.eval (2 ^ L) pre pub main r)
/-- Lookup `j`'s denominator at row `r`. -/
noncomputable def rD (r j : ℕ) : QM :=
  fingerprint α (emb ((lk c j).rel : F)) (((lk c j).vals.map (·.eval (2 ^ L) pre pub main r)).map emb) - z
/-- Secure column `b` at row `r`. -/
noncomputable def rS (b r : ℕ) : QM := secureVal fun k => emb (I (4 * b + k) r)

/-- The batch term at a row is `batchTerm` of the row's multiplicities, denominators and sums. -/
theorem row_batch {r : ℕ} (hr : r < 2 ^ L) (b : ℕ) :
    batchTerm (fun j => (lk c j).mult.evalR cstQ (rowVal (2 ^ L) pre main I r).leaf (fun j => emb (pub j)))
      (fun j => fingerprint α (emb ((lk c j).rel : F))
        ((lk c j).vals.map (·.evalR cstQ (rowVal (2 ^ L) pre main I r).leaf (fun j => emb (pub j)))) - z)
      (fun b => secureVal fun k => (rowVal (2 ^ L) pre main I r).inter (4 * b + k) 0)
      (secureVal fun k => (rowVal (2 ^ L) pre main I r).inter (4 * ((c.lookups.length + 1) / 2 - 1) + k) (-1))
      (claimed * emb (ninv L : F)) c.lookups.length ((c.lookups.length + 1) / 2) b =
    (let B := (c.lookups.length + 1) / 2
     (if b + 1 < B then rS I b r - (if b = 0 then 0 else rS I (b - 1) r)
      else rS I b r - rS I (B - 1) (LogUp.prev (2 ^ L) r) - (if B = 1 then 0 else rS I (B - 2) r) +
        claimed / ((2 ^ L : ℕ) : QM)) * bD (rD c L pre pub main α z r) c.lookups.length b -
      bN (rM c L pre pub main r) (rD c L pre pub main α z r) c.lookups.length b) := by
  have hw0 : wrap (2 ^ L) r 0 = r := wrap_zero hr
  have hm : ∀ j, (lk c j).mult.evalR cstQ (rowVal (2 ^ L) pre main I r).leaf (fun j => emb (pub j)) =
      rM c L pre pub main r j := fun j => evalR_row _ _ _ _ _ _ _
  have hd : ∀ j, fingerprint α (emb ((lk c j).rel : F))
      ((lk c j).vals.map (·.evalR cstQ (rowVal (2 ^ L) pre main I r).leaf (fun j => emb (pub j)))) - z =
      rD c L pre pub main α z r j := by
    intro j; unfold rD; rw [List.map_map]; congr 3
    funext e; exact evalR_row _ _ _ _ _ _ _
  simp only [hm, hd]
  simp only [batchTerm, rowVal, hw0, wrap_neg_one hr, ninv_share, rS, bN, bD]

/-- **A component's fractions sum to its claimed sum.** If every term vanishes at every row and every
denominator is nonzero, the multiplicity-over-denominator fractions of all its lookups at all its
rows sum to `claimed` (`logup_sum`, with the batch pairing). -/
theorem comp_frac_sum (hne : c.lookups ≠ [])
    (hrows : ∀ r < 2 ^ L, ∀ t ∈ terms c α z (claimed * emb (ninv L : F)) (fun j => emb (pub j))
      (rowVal (2 ^ L) pre main I r), t = 0)
    (hd : ∀ r < 2 ^ L, ∀ j < c.lookups.length, rD c L pre pub main α z r j ≠ 0) :
    ∑ r ∈ Finset.range (2 ^ L), ∑ j ∈ Finset.range c.lookups.length,
      rM c L pre pub main r j / rD c L pre pub main α z r j = claimed := by
  set Lk := c.lookups.length with hLk
  have hLk0 : 0 < Lk := List.length_pos_iff.mpr hne
  have hE : c.lookups.isEmpty = false := by
    rcases h : c.lookups with _ | ⟨x, xs⟩
    · exact absurd h hne
    · rfl
  have hterm : ∀ r < 2 ^ L, ∀ b < (Lk + 1) / 2,
      (let B := (Lk + 1) / 2
       (if b + 1 < B then rS I b r - (if b = 0 then 0 else rS I (b - 1) r)
        else rS I b r - rS I (B - 1) (LogUp.prev (2 ^ L) r) - (if B = 1 then 0 else rS I (B - 2) r) +
          claimed / ((2 ^ L : ℕ) : QM)) * bD (rD c L pre pub main α z r) Lk b -
        bN (rM c L pre pub main r) (rD c L pre pub main α z r) Lk b) = 0 := by
    intro r hr b hb
    rw [← row_batch c L pre pub main I α z claimed hr b]
    apply hrows r hr
    unfold terms
    rw [hE, if_neg (by decide)]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩)
  have hdb : ∀ r < 2 ^ L, ∀ b < (Lk + 1) / 2, rD c L pre pub main α z r (2 * b) ≠ 0 ∧
      (2 * b + 1 < Lk → rD c L pre pub main α z r (2 * b + 1) ≠ 0) :=
    fun r hr b hb => ⟨hd r hr _ (by omega), fun h => hd r hr _ h⟩
  have hsum := LogUp.logup_sum (K := QM) (2 ^ L) ((Lk + 1) / 2) (by positivity) (two_pow_ne L) (by omega)
    (fun b r => rS I b r) (fun b r => bN (rM c L pre pub main r) (rD c L pre pub main α z r) Lk b)
    (fun b r => bD (rD c L pre pub main α z r) Lk b) claimed
    (fun b hb r hr => bD_ne _ _ _ (hdb r hr b hb).1 (hdb r hr b hb).2)
    (fun b hb r hr => by
      have := hterm r hr b (by omega)
      simp only [if_pos hb] at this
      exact sub_eq_zero.mp this)
    (fun r hr => by
      have := hterm r hr ((Lk + 1) / 2 - 1) (by omega)
      simp only [if_neg (show ¬ ((Lk + 1) / 2 - 1 + 1 < (Lk + 1) / 2) by omega)] at this
      exact sub_eq_zero.mp this)
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' := Finset.mem_range.mp hr
  rw [← pair_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hb' := Finset.mem_range.mp hb
  rw [bN_div_bD _ _ _ _ (hdb r hr' b hb').1 (hdb r hr' b hb').2]

end Comp

/-! ### Fingerprints are tuple polynomials -/

theorem tuplePoly_cons' (a : F) (t : List F) :
    tuplePoly (K := QM) (a :: t) = C (algebraMap F QM a) + X * tuplePoly t := by
  ext n
  cases n with
  | zero => simp [coeff_tuplePoly]
  | succ n => simp [coeff_tuplePoly, coeff_X_mul]

theorem horner_rev (α : QM) : ∀ vs : List F,
    horner α 0 ((vs.map emb).reverse) = (tuplePoly (K := QM) vs).eval α
  | [] => by simp [horner, tuplePoly]
  | v :: vs => by
    rw [List.map_cons, List.reverse_cons, horner_append, horner_rev α vs, tuplePoly_cons']
    simp only [eval_add, eval_C, eval_mul, eval_X]
    rw [mul_comm, add_comm]; rfl

/-- **The circuit's fingerprint is the tuple polynomial at `α`.** -/
theorem fingerprint_poly (α : QM) (rel : ℕ) (vs : List F) :
    fingerprint α (emb (rel : F)) (vs.map emb) = (tuplePoly (K := QM) ((rel : F) :: vs)).eval α := by
  rw [fingerprint, horner_append, horner_rev, tuplePoly_cons']
  simp only [eval_add, eval_C, eval_mul, eval_X]
  rw [mul_comm, add_comm]; rfl

/-! ### The system -/

/-- Component traces of one log size. -/
def instOf (L : ℕ) (main : ℕ → ℕ → ℕ → F) : ℕ → Inst := fun i => ⟨L, main i⟩

theorem list_sum_range (f : ℕ → QM) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f n, Finset.sum_range_succ]; simp

theorem sum_flatMap_range {β : Type} (g : β → QM) (f : ℕ → List β) : ∀ n,
    (((List.range n).flatMap f).map g).sum = ∑ i ∈ Finset.range n, ((f i).map g).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.flatMap_append, List.map_append, List.sum_append, sum_flatMap_range g f n,
      Finset.sum_range_succ]; simp

/-- `SZGood`: the conclusion of `logup_sz` at one challenge pair (all denominators nonzero; fractions
summing to zero balance per fingerprint). `sz_good_bound`: it fails on few pairs. -/
def SZGood [DecidableEq QM] (es : List (Entry QM)) (α z : QM) : Prop :=
  (∀ e ∈ es, e.2.eval α ≠ z) ∧ (fracSum es α z = 0 → PolyBalanced es)

theorem sz_good_bound [DecidableEq QM] (es : List (Entry QM)) (W : ℕ) (hdeg : ∀ e ∈ es, e.2.natDegree < W) :
    ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys es).card ^ 2 * W + 2 * (polys es).card) * Fintype.card QM ∧
      ∀ az ∉ Bad, SZGood es az.1 az.2 :=
  logup_sz es W hdeg

section Sys

variable (sys : System) (L : ℕ) (pub : ℕ → F) (main : ℕ → ℕ → ℕ → F) (α z : QM)

/-- **The sites' fractions, component by component.** -/
theorem fracSum_sites :
    fracSum ((siteRaw sys (instOf L main) pub).map (toEntry (K := QM))) α z =
      ∑ i ∈ Finset.range sys.m, ∑ r ∈ Finset.range (2 ^ L), ∑ j ∈ Finset.range (sys.comp i).lookups.length,
        rM (sys.comp i) L (sys.comp i).air.pre pub (main i) r j / rD (sys.comp i) L (sys.comp i).air.pre pub (main i) α z r j := by
  unfold fracSum siteRaw sites
  rw [List.map_map, List.map_map, sum_flatMap_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_flatMap_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [List.map_map, list_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp, toEntry, rM, rD, siteRel, siteVals, siteMult, siteEval, siteLookup, instOf, lk]
  rw [fingerprint_poly]
  rfl

end Sys

/-! ### The STARK assumption, the public entries, static shapes -/

/-- **STARK soundness, row form (assumed).** For components `cs` (each with its claimed sum's share
and its OODS valuation): if the Horner combination with `coeff` of their terms at the OODS samples,
times `invZ = 1/Z(oods)`, equals the composition polynomial's sampled value `C`, then there are
base-field main and interaction columns on which every term vanishes at every row of the `2^L`-row
trace. This is the FRI + DEEP-ALI soundness of Stwo for the leaf's configuration, in the
random-oracle model, except with the configuration's soundness error; it is not proven here. -/
def StarkSound (L : ℕ) (pub : ℕ → F) (α z coeff invZ C : QM) (cs : List (Comp × QM × Val)) : Prop :=
  horner coeff 0 (cs.flatMap fun x => terms x.1 α z x.2.1 (fun j => emb (pub j)) x.2.2) * invZ = C →
  ∃ main I : ℕ → ℕ → ℕ → F, ∀ i (hi : i < cs.length), ∀ r < 2 ^ L,
    ∀ t ∈ terms cs[i].1 α z cs[i].2.1 (fun j => emb (pub j)) (rowVal (2 ^ L) cs[i].1.air.pre (main i) (I i) r),
      t = 0

/-- The public entries as the system's `PubEntries`: relation, the values' base coordinates,
multiplicity. -/
def extRaw (ρ : ℕ → Q) (xs : List ExtE) : PubEntries :=
  xs.map fun e => (e.rel, e.vals.map fun r => (ρ r).a, (e.mult : F))

theorem fracSum_ext [DecidableEq QM] (ρ : ℕ → Q) (xs : List ExtE) (zr ar : ℕ)
    (hxb : ∀ e ∈ xs, ∀ r ∈ e.vals, val ρ r = emb (ρ r).a) :
    fracSum ((extRaw ρ xs).map (toEntry (K := QM))) (val ρ ar) (val ρ zr) = (xs.map (entryFrac ρ zr ar)).sum := by
  unfold fracSum extRaw
  rw [List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro e he
  simp only [Function.comp, toEntry, entryFrac]
  rw [div_eq_mul_inv]
  have hv : e.vals.map (val ρ) = (e.vals.map fun r => (ρ r).a).map emb := by
    rw [List.map_map]; exact List.map_congr_left fun r hr => hxb e he r hr
  rw [hv, fingerprint_poly]
  rfl

theorem fracSum_append (a b : List (Entry QM)) (α z : QM) : fracSum (a ++ b) α z = fracSum a α z + fracSum b α z := by
  simp [fracSum]

/-- Every entry's shape is one of the system's shapes, so `StaticOk` gives one arity per relation. -/
theorem static_ext {sys : System} (h : StaticOk sys = true) {inst : ℕ → Inst} {pub : ℕ → F} {ext : PubEntries}
    (hx : ∀ e ∈ ext, (e.1, e.2.1.length) ∈ shapes sys) :
    (∀ e ∈ siteRaw sys inst pub ++ ext, ∀ e' ∈ siteRaw sys inst pub ++ ext, e.1 = e'.1 → e.2.1.length = e'.2.1.length) ∧
    (∀ e ∈ siteRaw sys inst pub ++ ext, e.1 < P) := by
  have hs : ∀ e ∈ siteRaw sys inst pub ++ ext, (e.1, e.2.1.length) ∈ shapes sys := by
    intro e he
    rcases List.mem_append.mp he with h1 | h1
    · exact siteRaw_shape h1
    · exact hx e h1
  simp only [StaticOk, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, bne_iff_ne,
    ne_eq, beq_iff_eq] at h
  refine ⟨fun e he e' he' hr => ?_, fun e he => (h _ (hs e he)).1⟩
  rcases (h _ (hs e he)).2 _ (hs e' he') with h1 | h1
  · exact absurd hr h1
  · exact h1

/-! ### The end-to-end theorem -/

theorem flatMap_map' {α β γ : Type*} (l : List α) (f : α → β) (g : β → List γ) :
    (l.map f).flatMap g = l.flatMap fun a => g (f a) := by
  induction l <;> simp [*]

theorem flatMap_congr' {α β : Type*} (l : List α) (f g : α → List β) (h : ∀ a ∈ l, f a = g a) :
    l.flatMap f = l.flatMap g := by
  induction l <;> simp_all

theorem list_sum_getD (l : List QM) : l.sum = ∑ i ∈ Finset.range l.length, l.getD i 0 := by
  induction l with
  | nil => simp
  | cons a l ih => rw [List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']; simp [add_comm]

theorem rD_site (sys : System) (L : ℕ) (pub : ℕ → F) (main : ℕ → ℕ → ℕ → F) (α z : QM) (i r j : ℕ) :
    rD (sys.comp i) L (sys.comp i).air.pre pub (main i) α z r j =
      (toEntry (K := QM) (siteRel sys (i, r, j), siteVals sys (instOf L main) pub (i, r, j),
        siteMult sys (instOf L main) pub (i, r, j))).2.eval α - z := by
  simp only [toEntry, rD, siteRel, siteVals, siteLookup, lk]
  rw [fingerprint_poly]
  rfl

/-! ### Per-component trace sizes (D-045) -/

/-- Component traces of per-component log sizes: component `i` has `2^(Ls i)` rows. -/
def instOfV (Ls : ℕ → ℕ) (main : ℕ → ℕ → ℕ → F) : ℕ → Inst := fun i => ⟨Ls i, main i⟩

theorem instOfV_const (L : ℕ) (main : ℕ → ℕ → ℕ → F) : instOfV (fun _ => L) main = instOf L main := rfl

/-- **STARK soundness with lifted components, row form (assumed).** As `StarkSound`, with component `i`'s
terms vanishing at every row of its own `2^(Ls i)`-row trace (its valuation at that size).

This stands for stwo's soundness for a proof whose trees are committed at the largest size `N` with
component `i`'s columns lifted (`f ∘ π^(N − Ls i)`, `π` the circle doubling; `vcs_lifted`): the
composition's quotient by `Z_N` is low-degree only if each component's terms, evaluated on the lifted
columns, vanish on the size-`2^N` domain; `π^(N − Ls i)` maps that domain onto component `i`'s own
size-`2^(Ls i)` domain (`Z_(Ls i)(π^k p) = Z_N(p)`, mask offsets at `g_N` map to offsets at `g_(Ls i)`),
so the terms vanish at every row of component `i`'s trace. It also covers the samples' points (OODS,
shifts at `g_N`, periodicity points `pt + 2^(Ls i)·g_N` for two-sample columns), as `StarkSound` does
for its points. Like `StarkSound` it is not proven here, and it **needs review against stwo's lifting
soundness argument before anything relies on it**. At one size it is `StarkSound` (`starkSoundV_const`). -/
def StarkSoundV (Ls : ℕ → ℕ) (pub : ℕ → F) (α z coeff invZ C : QM) (cs : List (Comp × QM × Val)) : Prop :=
  horner coeff 0 (cs.flatMap fun x => terms x.1 α z x.2.1 (fun j => emb (pub j)) x.2.2) * invZ = C →
  ∃ main I : ℕ → ℕ → ℕ → F, ∀ i (hi : i < cs.length), ∀ r < 2 ^ Ls i,
    ∀ t ∈ terms cs[i].1 α z cs[i].2.1 (fun j => emb (pub j)) (rowVal (2 ^ Ls i) cs[i].1.air.pre (main i) (I i) r),
      t = 0

/-- **At one size, `StarkSoundV` is `StarkSound`.** -/
theorem starkSoundV_const (L : ℕ) (pub : ℕ → F) (α z coeff invZ C : QM) (cs : List (Comp × QM × Val)) :
    StarkSoundV (fun _ => L) pub α z coeff invZ C cs ↔ StarkSound L pub α z coeff invZ C cs := Iff.rfl

theorem fracSum_sitesV (sys : System) (Ls : ℕ → ℕ) (pub : ℕ → F) (main : ℕ → ℕ → ℕ → F) (α z : QM) :
    fracSum ((siteRaw sys (instOfV Ls main) pub).map (toEntry (K := QM))) α z =
      ∑ i ∈ Finset.range sys.m, ∑ r ∈ Finset.range (2 ^ Ls i), ∑ j ∈ Finset.range (sys.comp i).lookups.length,
        rM (sys.comp i) (Ls i) (sys.comp i).air.pre pub (main i) r j /
          rD (sys.comp i) (Ls i) (sys.comp i).air.pre pub (main i) α z r j := by
  unfold fracSum siteRaw sites
  rw [List.map_map, List.map_map, sum_flatMap_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_flatMap_range]
  apply Finset.sum_congr rfl
  intro r _
  rw [List.map_map, list_sum_range]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Function.comp, toEntry, rM, rD, siteRel, siteVals, siteMult, siteEval, siteLookup, instOfV, lk]
  rw [fingerprint_poly]
  rfl

theorem rD_siteV (sys : System) (Ls : ℕ → ℕ) (pub : ℕ → F) (main : ℕ → ℕ → ℕ → F) (α z : QM) (i r j : ℕ) :
    rD (sys.comp i) (Ls i) (sys.comp i).air.pre pub (main i) α z r j =
      (toEntry (K := QM) (siteRel sys (i, r, j), siteVals sys (instOfV Ls main) pub (i, r, j),
        siteMult sys (instOfV Ls main) pub (i, r, j))).2.eval α - z := by
  simp only [toEntry, rD, siteRel, siteVals, siteLookup, lk]
  rw [fingerprint_poly]
  rfl

theorem flatMap_mapIdx {α β γ : Type} (l : List α) (g : ℕ → α → β) (h : β → List γ) :
    (l.mapIdx g).flatMap h = (l.mapIdx fun i a => h (g i a)).flatten := by
  rw [List.flatMap_def]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp [List.getElem_mapIdx]

theorem flatten_mapIdx_congr {α β : Type} (l : List α) (f g : ℕ → α → List β)
    (h : ∀ i (hi : i < l.length), f i l[i] = g i l[i]) : (l.mapIdx f).flatten = (l.mapIdx g).flatten := by
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_mapIdx]
  exact h i (by simpa using h1)

/-- The components' STARK inputs, part `i` sharing its claimed sum over `2^(Ls i)` rows. -/
noncomputable def starkParts (ρ : ℕ → Q) (Ls : ℕ → ℕ) (parts : List (Comp × PartRegs)) : List (Comp × QM × Val) :=
  parts.mapIdx fun i p => (p.1, val ρ p.2.claimed * emb (ninv (Ls i) : F), oodsVal ρ p.1 p.2)

theorem starkParts_const (ρ : ℕ → Q) (L : ℕ) (parts : List (Comp × PartRegs)) :
    starkParts ρ (fun _ => L) parts = parts.map fun p => (p.1, val ρ p.2.claimed * emb (ninv L : F), oodsVal ρ p.1 p.2) :=
  Composition.mapIdx_const _ parts

variable {ρ : ℕ → Q}

/-- **The plain verifier, end to end, per-component sizes.** As `plain_sound`, for a proof whose
component `i` has `2^(Ls i)` rows: the host's hook 2 gives part `i` the share `1/2^(Ls i)` (`HookOk`),
and under `StarkSoundV` there are main columns on which component `i`'s AIR holds at size `Ls i`; for
good `(α, z)` the system with those per-component sizes is satisfied with the public entries. -/
theorem plain_soundV [DecidableEq QM] (sys : System) (parts : List (Comp × PartRegs)) (sh : Shared) (Ls : ℕ → ℕ)
    (nIn oodsX nB : ℕ) (xs : List ExtE) (pub : ℕ → F) (C : QM)
    (hm : parts.length = sys.m) (hcomp : ∀ i (hi : i < parts.length), parts[i].1 = sys.comp i)
    (hlk : ∀ i < sys.m, (sys.comp i).lookups ≠ [])
    (hstatic : StaticOk sys = true) (hshape : ∀ e ∈ extRaw ρ xs, (e.1, e.2.1.length) ∈ shapes sys)
    (hpub : ∀ p ∈ parts, ∀ j, val ρ (p.2.ci.pub j) = emb (pub j))
    (hxb : ∀ e ∈ xs, ∀ r ∈ e.vals, val ρ r = emb (ρ r).a)
    (hw : ∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size)
    (hk : HookOk ρ sh Ls parts ([], nIn, nIn + 1))
    (hsys : Holds ρ (sysProg parts sh nIn oodsX).1)
    (hoods : val ρ (sysProg parts sh nIn oodsX).2 = C)
    (hbal : Holds ρ (balanceProg nB (parts.map (·.2.claimed)) xs sh.z sh.alpha))
    (hstark : StarkSoundV Ls pub (val ρ sh.alpha) (val ρ sh.z) (val ρ sh.coeff)
      (val ρ (partFold sh parts ([], nIn, nIn + 1)).2.2) C (starkParts ρ Ls parts)) :
    ∃ main : ℕ → ℕ → ℕ → F,
      (∀ i < sys.m, (sys.comp i).air.Satisfied (Ls i) pub (main i)) ∧
      (SZGood ((siteRaw sys (instOfV Ls main) pub ++ extRaw ρ xs).map (toEntry (K := QM)))
          (val ρ sh.alpha) (val ρ sh.z) →
        sys.SatisfiedExt (instOfV Ls main) pub (extRaw ρ xs)) := by
  -- The composition value is the Horner combination of `terms` at the OODS samples.
  have hcomb : horner (val ρ sh.coeff) 0 ((starkParts ρ Ls parts).flatMap
        fun x => terms x.1 (val ρ sh.alpha) (val ρ sh.z) x.2.1 (fun j => emb (pub j)) x.2.2) *
      val ρ (partFold sh parts ([], nIn, nIn + 1)).2.2 = C := by
    rw [← hoods, sys_soundV Ls hw hk hsys, starkParts, flatMap_mapIdx, termsV]
    congr 2
    apply flatten_mapIdx_congr
    intro i hi
    rw [partTerms_eq]
    have : pubQ ρ parts[i].2.ci = fun j => emb (pub j) := funext (hpub _ (List.getElem_mem hi))
    rw [this]; rfl
  obtain ⟨main, I, hrows⟩ := hstark hcomb
  have hrow : ∀ i (hi : i < parts.length), ∀ r < 2 ^ Ls i, ∀ t ∈ terms (sys.comp i) (val ρ sh.alpha) (val ρ sh.z)
      (val ρ parts[i].2.claimed * emb (ninv (Ls i) : F)) (fun j => emb (pub j))
      (rowVal (2 ^ Ls i) (sys.comp i).air.pre (main i) (I i) r), t = 0 := by
    intro i hi r hr t ht
    have := hrows i (by simpa [starkParts] using hi) r hr t
    simp only [starkParts, List.getElem_mapIdx] at this
    rw [hcomp i hi] at this
    exact this ht
  -- Constraints.
  have hair : ∀ i < sys.m, (sys.comp i).air.Satisfied (Ls i) pub (main i) := by
    intro i hi r hr e he
    have h0 := hrow i (by omega) r hr _ (by
      unfold terms
      exact List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))
    rw [evalR_row] at h0
    exact emb_inj (h0.trans (map_zero embHom).symm)
  refine ⟨main, hair, fun hsz => ⟨fun i hi => hair i hi, ?_⟩⟩
  -- Denominators.
  have hd : ∀ i < sys.m, ∀ r < 2 ^ Ls i, ∀ j < (sys.comp i).lookups.length,
      rD (sys.comp i) (Ls i) (sys.comp i).air.pre pub (main i) (val ρ sh.alpha) (val ρ sh.z) r j ≠ 0 := by
    intro i hi r hr j hj h
    rw [rD_siteV] at h
    apply hsz.1 _ (List.mem_map.mpr ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨(i, r, j), ?_, rfl⟩), rfl⟩)
    · exact sub_eq_zero.mp h
    · simp only [sites, List.mem_flatMap, List.mem_range, List.mem_map, instOfV]
      exact ⟨i, hi, r, hr, j, hj, rfl⟩
  -- Each component's fractions sum to its claimed sum.
  have hsites : fracSum ((siteRaw sys (instOfV Ls main) pub).map (toEntry (K := QM))) (val ρ sh.alpha) (val ρ sh.z) =
      ((parts.map (·.2.claimed)).map (val ρ)).sum := by
    rw [fracSum_sitesV, list_sum_getD, List.length_map, List.length_map, hm]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i < parts.length := by rw [hm]; exact Finset.mem_range.mp hi
    rw [List.getD_eq_getElem _ _ (by simpa using hi'), List.getElem_map, List.getElem_map]
    exact comp_frac_sum (sys.comp i) (Ls i) (sys.comp i).air.pre pub (main i) (I i) _ _ _
      (hlk i (by omega)) (hrow i hi') (hd i (by omega))
  -- The balance check closes the sum.
  have htot : fracSum ((siteRaw sys (instOfV Ls main) pub ++ extRaw ρ xs).map (toEntry (K := QM)))
      (val ρ sh.alpha) (val ρ sh.z) = 0 := by
    rw [List.map_append, fracSum_append, hsites, fracSum_ext ρ xs sh.z sh.alpha hxb]
    exact balance_sound hbal
  obtain ⟨har, hrs⟩ := static_ext (inst := instOfV Ls main) (pub := pub) hstatic hshape
  exact balancedExt_of_poly sys (instOfV Ls main) pub (extRaw ρ xs) har hrs (hsz.2 htot)

/-- **The plain verifier, end to end.** Suppose the leaf circuit's composition program (`sysProg`, over
the components `parts` of `sys`, in order, each with lookups) and its balance program (the claimed
sums in component order, the public entries `xs`) hold; the public-input registers hold `pub`; and the
composition value equals the sampled composition value `C`. Then, under `StarkSound`, there are main
columns on which every component's AIR holds; and if the circuit's `(α, z)` is good for those traces'
entries (`SZGood`, failing on few pairs by `sz_good_bound`), the system is satisfied with the public
entries: `sys.SatisfiedExt`. -/
theorem plain_sound [DecidableEq QM] (sys : System) (parts : List (Comp × PartRegs)) (sh : Shared)
    (nIn oodsX nB : ℕ) (xs : List ExtE) (pub : ℕ → F) (C : QM)
    (hm : parts.length = sys.m) (hcomp : ∀ i (hi : i < parts.length), parts[i].1 = sys.comp i)
    (hlk : ∀ i < sys.m, (sys.comp i).lookups ≠ [])
    (hstatic : StaticOk sys = true) (hshape : ∀ e ∈ extRaw ρ xs, (e.1, e.2.1.length) ∈ shapes sys)
    (hpub : ∀ p ∈ parts, ∀ j, val ρ (p.2.ci.pub j) = emb (pub j))
    (hxb : ∀ e ∈ xs, ∀ r ∈ e.vals, val ρ r = emb (ρ r).a)
    (hw : ∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size)
    (hninv : ∀ q, Op.hook 2 [] [q] ∈ (sysProg parts sh nIn oodsX).1 → val ρ q = emb (ninv sh.logSize : F))
    (hsys : Holds ρ (sysProg parts sh nIn oodsX).1)
    (hoods : val ρ (sysProg parts sh nIn oodsX).2 = C)
    (hbal : Holds ρ (balanceProg nB (parts.map (·.2.claimed)) xs sh.z sh.alpha))
    (hstark : StarkSound sh.logSize pub (val ρ sh.alpha) (val ρ sh.z) (val ρ sh.coeff)
      (val ρ (partFold sh parts ([], nIn, nIn + 1)).2.2) C
      (parts.map fun p => (p.1, val ρ p.2.claimed * emb (ninv sh.logSize : F), oodsVal ρ p.1 p.2))) :
    ∃ main : ℕ → ℕ → ℕ → F,
      (∀ i < sys.m, (sys.comp i).air.Satisfied sh.logSize pub (main i)) ∧
      (SZGood ((siteRaw sys (instOf sh.logSize main) pub ++ extRaw ρ xs).map (toEntry (K := QM)))
          (val ρ sh.alpha) (val ρ sh.z) →
        sys.SatisfiedExt (instOf sh.logSize main) pub (extRaw ρ xs)) := by
  -- One size: `plain_soundV` at the constant vector.
  have hk : HookOk ρ sh (fun _ => sh.logSize) parts ([], nIn, nIn + 1) :=
    hookOk_of_const sh parts _ (fun q hq => hninv q (List.mem_append_left _ (List.mem_append_right _ hq)))
  exact plain_soundV sys parts sh (fun _ => sh.logSize) nIn oodsX nB xs pub C hm hcomp hlk hstatic hshape hpub hxb hw
    hk hsys hoods hbal (by rw [starkParts_const]; exact hstark)

/-! ### The header-chain leaf -/

theorem headerTree_shape : (HeaderTree.REL_NODE, 18) ∈ shapes HeaderTree.sys := by decide

theorem headerTree_static' : StaticOk HeaderTree.sys = true := by decide

/-- **The header-chain leaf, end to end.** For the (headers, tree) system with `2^L` rows, the leaf
circuit's composition and balance programs holding, the balance check's one public entry being the
tree root `node(L − 8, 0, pubT pub)` with multiplicity `−1` (as `verifyPlain` wires it for this
system), and under `StarkSound`: there are traces on which both AIRs hold, and for `(α, z)` good for
their entries, the public inputs are proven (`PubValidT`, the leaves' guarantee the aggregation
composes, `chain_from_genesis_T`). -/
theorem plain_leaf_valid [DecidableEq QM] (parts : List (Comp × PartRegs)) (sh : Shared)
    (nIn oodsX nB : ℕ) (xs : List ExtE) (pub : ℕ → F) (C : QM)
    (hm : parts.length = 2) (hcomp : ∀ i (hi : i < parts.length), parts[i].1 = HeaderTree.sys.comp i)
    (hL8 : 8 ≤ sh.logSize) (hL28 : sh.logSize ≤ 28)
    (hext : extRaw ρ xs = [(HeaderTree.REL_NODE, ((sh.logSize - 8 : ℕ) : F) :: 0 :: HeaderTree.pubT pub, -1)])
    (hpub : ∀ p ∈ parts, ∀ j, val ρ (p.2.ci.pub j) = emb (pub j))
    (hxb : ∀ e ∈ xs, ∀ r ∈ e.vals, val ρ r = emb (ρ r).a)
    (hw : ∀ p ∈ parts, WF (pNodes p.1) ∧ ∀ id ∈ pIds p.1, id < (pNodes p.1).size)
    (hninv : ∀ q, Op.hook 2 [] [q] ∈ (sysProg parts sh nIn oodsX).1 → val ρ q = emb (ninv sh.logSize : F))
    (hsys : Holds ρ (sysProg parts sh nIn oodsX).1)
    (hoods : val ρ (sysProg parts sh nIn oodsX).2 = C)
    (hbal : Holds ρ (balanceProg nB (parts.map (·.2.claimed)) xs sh.z sh.alpha))
    (hstark : StarkSound sh.logSize pub (val ρ sh.alpha) (val ρ sh.z) (val ρ sh.coeff)
      (val ρ (partFold sh parts ([], nIn, nIn + 1)).2.2) C
      (parts.map fun p => (p.1, val ρ p.2.claimed * emb (ninv sh.logSize : F), oodsVal ρ p.1 p.2))) :
    ∃ main : ℕ → ℕ → ℕ → F,
      SZGood ((siteRaw HeaderTree.sys (instOf sh.logSize main) pub ++ extRaw ρ xs).map (toEntry (K := QM)))
          (val ρ sh.alpha) (val ρ sh.z) →
        HeaderTree.PubValidT pub := by
  have hshape : ∀ e ∈ extRaw ρ xs, (e.1, e.2.1.length) ∈ shapes HeaderTree.sys := by
    rw [hext]
    intro e he
    rw [List.mem_singleton.mp he]
    simp only [List.length_cons, HeaderTree.pubT, List.length_map, List.length_range]
    exact headerTree_shape
  obtain ⟨main, -, hsat⟩ := plain_sound HeaderTree.sys parts sh nIn oodsX nB xs pub C hm hcomp
    (fun i hi => by
      rcases (show i = 0 ∨ i = 1 by have : HeaderTree.sys.m = 2 := rfl; omega) with rfl | rfl <;> decide)
    headerTree_static' hshape hpub hxb hw hninv hsys hoods hbal hstark
  refine ⟨main, fun hsz => ?_⟩
  have h := hsat hsz
  rw [hext] at h
  exact HeaderTree.leaf_valid_T rfl rfl hL8 hL28 h

end StarkedAir.Circuit.EndToEnd
