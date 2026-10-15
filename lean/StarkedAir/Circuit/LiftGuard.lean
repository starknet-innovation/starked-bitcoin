/-
**(W) for components with guarded wrapped reads.** `liftOK_of_offsets` proves (W) when every main
column is read at no more than two offsets. This file proves it for some components that read a column
at three or more offsets, when every wrapped read of such a column is harmless.

**The own-size trace.** Columns with at most two offsets are built as in `liftOK_of_offsets`; a column
with three or more offsets is the window `T j` itself. At own row `r`, a read at offset `off` agrees
with the big trace unless it wraps around the own size (`r + off ∉ [0, 2^L)`); this happens only in
the first and last `K` rows, where `K` bounds the offsets.

**The check (`guardOk`).** In those boundary rows, written as relative rows `ρ ∈ [−K, K)` (`ρ < 0` is
row `2^L + ρ`), every expression of the component must not depend on a wrapped read (`dep`). The value
of a subexpression can be known without the main trace (`kv`), which removes its reads:
- preprocessed reads have known values at a relative row, for every size `2^L ≥ 2^L0` (`preSym`);
- a *cell fact* `(j, σ)`: column `j` vanishes at every big row congruent to `σ` modulo `2^L`. It is
  justified by a constraint `a · col j o` whose factor `a` is a known nonzero constant at relative row
  `σ − o`, using the lifted preprocessed columns (`cellOk`);
- a *row fact* `(ρ, g, side)`: a constraint `g = a · b` with `a` a known nonzero constant at row `ρ`
  and `b` independent of wrapped reads there, so `b` vanishes at row `ρ` in both traces (`rowOk`).

`liftOK_of_guard`: `guardOk` gives (W) at every own size `L ≥ L0`. The check is decidable, so a
component is handled by `decide +kernel` with a certificate (the bound `K`, the cell and row facts).
-/
import StarkedAir.Circuit.Lift

namespace StarkedAir.Circuit.Lift

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.Composition StarkedAir.Circuit.EndToEnd StarkedAir.LogUpSZ
open StarkedAir.Spec.QM31 (QM emb emb_add emb_sub emb_mul emb_zero)

/-! ### Known values and dependence on chosen reads -/

/-- The value of `e` when it is known without the main trace: from the preprocessed values `pv`, the
constants, and the subexpressions `zx` marks as zero, folded through the arithmetic. -/
def kv (pv : ℕ → ℤ → Option F) (zx : Expr → Bool) (e : Expr) : Option F :=
  if zx e then some 0 else
  match e with
  | .col .pre j off => pv j off
  | .col .main _ _ => none
  | .const v => some (v : F)
  | .pub _ => none
  | .add a b => match kv pv zx a, kv pv zx b with
    | some x, some y => some (x + y)
    | _, _ => none
  | .sub a b => match kv pv zx a, kv pv zx b with
    | some x, some y => some (x - y)
    | _, _ => none
  | .mul a b => match kv pv zx a, kv pv zx b with
    | some x, some y => some (x * y)
    | some x, none => if x = 0 then some 0 else none
    | none, some y => if y = 0 then some 0 else none
    | none, none => none
  | .neg a => (kv pv zx a).map (- ·)
termination_by structural e

/-- Whether `e` may depend on a main read `W` marks, once known subexpressions are folded. -/
def dep (pv : ℕ → ℤ → Option F) (zx : Expr → Bool) (W : ℕ → ℤ → Bool) (e : Expr) : Bool :=
  if (kv pv zx e).isSome then false else
  match e with
  | .col .main j off => W j off
  | .col .pre _ _ => false
  | .const _ => false
  | .pub _ => false
  | .add a b => dep pv zx W a || dep pv zx W b
  | .sub a b => dep pv zx W a || dep pv zx W b
  | .mul a b => dep pv zx W a || dep pv zx W b
  | .neg a => dep pv zx W a
termination_by structural e

theorem emb_neg' (x : F) : emb (-x) = -emb x := by simp [emb]

section Sound

variable {pv : ℕ → ℤ → Option F} {zx : Expr → Bool} {pub : ℕ → QM}

theorem kv_sound {l : Tree → ℕ → ℤ → QM}
    (hpv : ∀ j off x, pv j off = some x → l .pre j off = emb x)
    (hzx : ∀ e, zx e = true → e.evalR cstQ l pub = 0) :
    ∀ e x, kv pv zx e = some x → e.evalR cstQ l pub = emb x := by
  intro e
  induction e with
  | col t j off =>
    intro x h
    cases t <;> rw [kv] at h <;> split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · exact hpv j off x h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · cases h
  | const v =>
    intro x h
    rw [kv] at h
    split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · cases h; rfl
  | pub i =>
    intro x h
    rw [kv] at h
    split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · cases h
  | neg a iha =>
    intro x h
    rw [kv] at h
    split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · obtain ⟨x1, h1, rfl⟩ := Option.map_eq_some_iff.mp h
      simp only [Expr.evalR, iha x1 h1, emb_neg']
  | add a b iha ihb =>
    intro x h
    rw [kv] at h
    split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · rcases ha : kv pv zx a with _ | x1 <;> rcases hb : kv pv zx b with _ | y1 <;> simp only [ha, hb] at h <;>
        try cases h
      simp only [Expr.evalR, iha x1 ha, ihb y1 hb, emb_add]
  | sub a b iha ihb =>
    intro x h
    rw [kv] at h
    split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · rcases ha : kv pv zx a with _ | x1 <;> rcases hb : kv pv zx b with _ | y1 <;> simp only [ha, hb] at h <;>
        try cases h
      simp only [Expr.evalR, iha x1 ha, ihb y1 hb, emb_sub]
  | mul a b iha ihb =>
    intro x h
    rw [kv] at h
    split at h
    · rename_i hz; cases h; rw [hzx _ hz, emb_zero]
    · rcases ha : kv pv zx a with _ | x1 <;> rcases hb : kv pv zx b with _ | y1 <;> simp only [ha, hb] at h
      · cases h
      · split_ifs at h with hy; cases h; subst hy
        simp only [Expr.evalR, ihb 0 hb, emb_zero, mul_zero]
      · split_ifs at h with hx; cases h; subst hx
        simp only [Expr.evalR, iha 0 ha, emb_zero, zero_mul]
      · cases h; simp only [Expr.evalR, iha x1 ha, ihb y1 hb, emb_mul]

/-- **Independence.** Two valuations that agree on preprocessed reads and on every main read of `e`
outside `W`, and on which `pv` and `zx` are sound, give `e` the same value when `dep` is false. -/
theorem dep_sound {W : ℕ → ℤ → Bool} {l l' : Tree → ℕ → ℤ → QM}
    (hpre : ∀ j off, l .pre j off = l' .pre j off)
    (hpv : ∀ j off x, pv j off = some x → l .pre j off = emb x)
    (hzx : ∀ e, zx e = true → e.evalR cstQ l pub = 0)
    (hzx' : ∀ e, zx e = true → e.evalR cstQ l' pub = 0) :
    ∀ e, (∀ j off, (j, off) ∈ mainReads e → W j off = false → l .main j off = l' .main j off) →
      dep pv zx W e = false → e.evalR cstQ l pub = e.evalR cstQ l' pub := by
  have hpv' : ∀ j off x, pv j off = some x → l' .pre j off = emb x := fun j off x h => by
    rw [← hpre]; exact hpv j off x h
  intro e hm hd
  rcases hk : kv pv zx e with _ | x
  · induction e with
    | col t j off =>
      cases t
      · exact hpre j off
      · simp only [dep, hk, Option.isSome_none, Bool.false_eq_true, if_false] at hd
        exact hm j off (by simp [mainReads]) hd
    | const v => rfl
    | pub i => rfl
    | neg a iha =>
      simp only [dep, hk, Option.isSome_none, Bool.false_eq_true, if_false] at hd
      simp only [Expr.evalR]
      congr 1
      rcases ha : kv pv zx a with _ | x
      · exact iha (fun j o h => hm j o (by simpa [mainReads] using h)) hd ha
      · rw [kv_sound hpv hzx a x ha, kv_sound hpv' hzx' a x ha]
    | add a b iha ihb =>
      simp only [dep, hk, Option.isSome_none, Bool.false_eq_true, if_false, Bool.or_eq_false_iff] at hd
      simp only [Expr.evalR]
      congr 1
      · rcases ha : kv pv zx a with _ | x
        · exact iha (fun j o h => hm j o (by simp [mainReads, h])) hd.1 ha
        · rw [kv_sound hpv hzx a x ha, kv_sound hpv' hzx' a x ha]
      · rcases hb : kv pv zx b with _ | x
        · exact ihb (fun j o h => hm j o (by simp [mainReads, h])) hd.2 hb
        · rw [kv_sound hpv hzx b x hb, kv_sound hpv' hzx' b x hb]
    | sub a b iha ihb =>
      simp only [dep, hk, Option.isSome_none, Bool.false_eq_true, if_false, Bool.or_eq_false_iff] at hd
      simp only [Expr.evalR]
      congr 1
      · rcases ha : kv pv zx a with _ | x
        · exact iha (fun j o h => hm j o (by simp [mainReads, h])) hd.1 ha
        · rw [kv_sound hpv hzx a x ha, kv_sound hpv' hzx' a x ha]
      · rcases hb : kv pv zx b with _ | x
        · exact ihb (fun j o h => hm j o (by simp [mainReads, h])) hd.2 hb
        · rw [kv_sound hpv hzx b x hb, kv_sound hpv' hzx' b x hb]
    | mul a b iha ihb =>
      simp only [dep, hk, Option.isSome_none, Bool.false_eq_true, if_false, Bool.or_eq_false_iff] at hd
      simp only [Expr.evalR]
      congr 1
      · rcases ha : kv pv zx a with _ | x
        · exact iha (fun j o h => hm j o (by simp [mainReads, h])) hd.1 ha
        · rw [kv_sound hpv hzx a x ha, kv_sound hpv' hzx' a x ha]
      · rcases hb : kv pv zx b with _ | x
        · exact ihb (fun j o h => hm j o (by simp [mainReads, h])) hd.2 hb
        · rw [kv_sound hpv hzx b x hb, kv_sound hpv' hzx' b x hb]
  · rw [kv_sound hpv hzx e x hk, kv_sound hpv' hzx' e x hk]

end Sound

/-! ### Relative rows -/

/-- Relative row `τ` of an `n`-row trace is `wrap n 0 τ`: row `τ` if `τ ≥ 0`, row `n + τ` if not. -/
theorem wrap0_of_nonneg {n : ℕ} {τ : ℤ} (h0 : 0 ≤ τ) (h1 : τ < n) : (wrap n 0 τ : ℤ) = τ := by
  rw [wrap_cast _ _ _ (by omega), Nat.cast_zero, zero_add, Int.emod_eq_of_lt h0 h1]

theorem wrap0_of_neg {n : ℕ} {τ : ℤ} (h0 : τ < 0) (h1 : -τ ≤ n) : (wrap n 0 τ : ℤ) = n + τ := by
  have hn : 0 < n := by omega
  rw [wrap_cast _ _ _ hn, Nat.cast_zero, zero_add, ← Int.add_emod_right, add_comm,
    Int.emod_eq_of_lt (by omega) (by omega)]

/-- Reads from a row congruent to relative row `ρ`. -/
theorem wrap_rel {n R : ℕ} (hn : 0 < n) {ρ : ℤ} (h : (R : ℤ) % n = ρ % n) (off : ℤ) :
    wrap n R off = wrap n 0 (ρ + off) := by
  apply Int.ofNat.inj
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, wrap_cast _ _ _ hn, wrap_cast _ _ _ hn, Nat.cast_zero, zero_add,
    ← Int.emod_add_emod, h, Int.emod_add_emod]

/-! ### Preprocessed columns at relative rows -/

/-- The bound a preprocessed column's parameter must respect. -/
def preParam : PreCol → ℕ
  | .rowLt m => m
  | .rowGeEnd m => m
  | _ => 0

/-- A preprocessed column's value at relative row `τ`, valid for every size `2^L` with `L ≥ L0` large
enough (`preSym_sound`). A periodic column is known at negative rows only when its period divides
`2^L0`. -/
def preSym (L0 : ℕ) : PreCol → ℤ → Option F
  | .isFirst, τ => some (if τ = 0 then 1 else 0)
  | .notLast, τ => some (if τ = -1 then 0 else 1)
  | .rowLt m, τ => some (if 0 ≤ τ ∧ τ < m then 1 else 0)
  | .rowGeEnd m, τ => some (if τ < 0 ∧ -τ ≤ m then 1 else 0)
  | .periodic vs, τ =>
    if 0 ≤ τ ∨ vs.length ∣ 2 ^ L0 then some ((vs.getD (τ % (vs.length : ℤ)).toNat 0 : ℕ) : F) else none

theorem preSym_sound {L0 n K : ℕ} (hn : 8 * K + 8 < n) (hdiv : 2 ^ L0 ∣ n) {p : PreCol} (hp : preParam p ≤ K)
    {τ : ℤ} (hτ : |τ| ≤ 4 * K) {x : F} (h : preSym L0 p τ = some x) : p.eval n (wrap n 0 τ) = x := by
  have hτ' := abs_le.mp hτ
  rcases le_or_gt 0 τ with h0 | h0
  · have hw : wrap n 0 τ = τ.toNat := by have := wrap0_of_nonneg (n := n) h0 (by omega); omega
    cases p with
    | isFirst =>
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      by_cases hz : τ = 0
      · rw [if_pos (by omega), if_pos hz]
      · rw [if_neg (by omega), if_neg hz]
    | notLast =>
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      rw [if_pos (by omega), if_neg (by omega)]
    | rowLt m =>
      simp only [preParam] at hp
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      by_cases hm : τ < m
      · rw [if_pos (by omega), if_pos ⟨h0, hm⟩]
      · rw [if_neg (by omega), if_neg (by omega)]
    | rowGeEnd m =>
      simp only [preParam] at hp
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      rw [if_neg (by omega), if_neg (by omega)]
    | periodic vs =>
      simp only [preSym, if_pos (Or.inl h0), Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      rw [Int.toNat_emod h0 (by omega), Int.toNat_natCast]
  · have hw : wrap n 0 τ = (n + τ).toNat := by have := wrap0_of_neg (n := n) h0 (by omega); omega
    cases p with
    | isFirst =>
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      rw [if_neg (by omega), if_neg (by omega)]
    | notLast =>
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      by_cases hz : τ = -1
      · rw [if_neg (by omega), if_pos hz]
      · rw [if_pos (by omega), if_neg hz]
    | rowLt m =>
      simp only [preParam] at hp
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      rw [if_neg (by omega), if_neg (by omega)]
    | rowGeEnd m =>
      simp only [preParam] at hp
      simp only [preSym, Option.some.injEq] at h; subst h
      simp only [PreCol.eval, hw]
      by_cases hm : -τ ≤ m
      · rw [if_pos (by omega), if_pos ⟨h0, hm⟩]
      · rw [if_neg (by omega), if_neg (by omega)]
    | periodic vs =>
      simp only [preSym, show ¬ (0 ≤ τ) by omega, false_or] at h
      split_ifs at h with hd
      cases h
      simp only [PreCol.eval, hw]
      have hlen : (vs.length : ℤ) ∣ n := by exact_mod_cast hd.trans hdiv
      rw [← Int.toNat_natCast vs.length, ← Int.toNat_emod (by omega) (by omega), Int.toNat_natCast,
        Int.add_emod, Int.emod_eq_zero_of_dvd hlen, zero_add,
        Int.emod_emod_of_dvd _ (dvd_refl _)]

/-! ### The check -/

/-- Whether a read at offset `off` from relative row `ρ` wraps around the own size. -/
def wraps (ρ off : ℤ) : Bool := if 0 ≤ ρ then decide (ρ + off < 0) else decide (0 ≤ ρ + off)

/-- Main column `j` is read at three or more offsets. -/
def big (c : Comp) (j : ℕ) : Bool := decide (3 ≤ (mainOffs c j).length)

/-- Preprocessed values at relative row `ρ`, known within `4K` of the boundary. -/
def pvAt (c : Comp) (L0 K : ℕ) (ρ : ℤ) (j : ℕ) (off : ℤ) : Option F :=
  if |ρ + off| ≤ 4 * K then preSym L0 (c.air.pre.getD j (.periodic [0])) (ρ + off) else none

/-- The wrapped reads at relative row `ρ`: reads of a three-offset column that wrap. -/
def WAt (c : Comp) (ρ : ℤ) (j : ℕ) (off : ℤ) : Bool := big c j && wraps ρ off

/-- Cell facts: a read from relative row `ρ` lands on a cell listed in `cells`. -/
def zc (c : Comp) (cells : List (ℕ × ℤ)) (ρ : ℤ) : Expr → Bool
  | .col .main j off => big c j && cells.contains (j, ρ + off)
  | _ => false

/-- A product constraint split as (guard, factor). -/
def partsOf (g : Expr) (side : Bool) : Option (Expr × Expr) :=
  match g with
  | .mul a b => some (if side then (a, b) else (b, a))
  | _ => none

/-- Constraint `f.1` split at side `f.2`. -/
def factOf (c : Comp) (f : ℕ × Bool) : Option (Expr × Expr) := (c.air.constraints[f.1]?).bind (partsOf · f.2)

/-- All known zeros at relative row `ρ`: cell facts, and the factors of the row facts at `ρ`. -/
def zx (c : Comp) (cells : List (ℕ × ℤ)) (rf : List (ℤ × ℕ × Bool)) (ρ : ℤ) (e : Expr) : Bool :=
  zc c cells ρ e || rf.any fun f => f.1 == ρ && (factOf c f.2).any fun p => p.2 == e

/-- A cell fact `(j, σ)` is justified by a constraint `a · col j o` with `a` a known nonzero constant at
relative row `σ − o`. -/
def cellOk (c : Comp) (L0 K : ℕ) (f : ℕ × ℤ) : Bool :=
  c.air.constraints.any fun g => [true, false].any fun side =>
    match partsOf g side with
    | some (a, .col .main j o) => j == f.1 && (kv (pvAt c L0 K (f.2 - o)) (fun _ => false) a).any (· != 0)
    | _ => false

/-- A row fact `(ρ, g, side)`: the guard is a known nonzero constant at `ρ`, and the factor does not
depend on wrapped reads there. -/
def rowOk (c : Comp) (L0 K : ℕ) (cells : List (ℕ × ℤ)) (f : ℤ × ℕ × Bool) : Bool :=
  match factOf c f.2 with
  | some (a, b) => (kv (pvAt c L0 K f.1) (zc c cells f.1) a).any (· != 0) &&
      !dep (pvAt c L0 K f.1) (zc c cells f.1) (WAt c f.1) b
  | none => false

/-- Every offset an expression reads at. -/
def offsAll : Expr → List ℤ
  | .col _ _ off => [off]
  | .const _ => []
  | .pub _ => []
  | .add a b => offsAll a ++ offsAll b
  | .sub a b => offsAll a ++ offsAll b
  | .mul a b => offsAll a ++ offsAll b
  | .neg a => offsAll a

/-- Offsets and preprocessed parameters are bounded by `K`. -/
def bndOk (c : Comp) (K : ℕ) : Bool :=
  (exprs c).all (fun e => (offsAll e).all fun o => decide (|o| ≤ K)) &&
    c.air.pre.all fun p => decide (preParam p ≤ K)

/-- **The check.** Sizes, bounds, the facts, and: at every relative row `ρ ∈ [−K, K)`, no expression
depends on a wrapped read. -/
def guardOk (c : Comp) (L0 K : ℕ) (cells : List (ℕ × ℤ)) (rf : List (ℤ × ℕ × Bool)) : Bool :=
  decide (8 * K + 8 < 2 ^ L0) && bndOk c K && cells.all (cellOk c L0 K) && rf.all (rowOk c L0 K cells) &&
  (List.range (2 * K)).all fun i => (exprs c).all fun e =>
    !dep (pvAt c L0 K ((i : ℤ) - K)) (zx c cells rf ((i : ℤ) - K)) (WAt c ((i : ℤ) - K)) e

/-! ### Soundness -/

/-- The own-size columns: as in `liftOK_of_offsets` for columns with at most two offsets, the window
for the others. -/
noncomputable def ownG (c : Comp) (N L : ℕ) (T : ℕ → ℕ → F) (j : ℕ) : ℕ → F :=
  if (mainOffs c j).length ≤ 2 then ownCol N L (mainOffs c j) (T j) else T j

theorem wrap_eq_of_mem {n r : ℕ} {off : ℤ} (h0 : 0 ≤ (r : ℤ) + off) (h1 : (r : ℤ) + off < n) :
    (wrap n r off : ℤ) = r + off := by
  rw [wrap_cast _ _ _ (by omega), Int.emod_eq_of_lt h0 h1]

theorem wrap_modL {L N : ℕ} (hLN : L ≤ N) (R : ℕ) (off : ℤ) :
    ((wrap (2 ^ N) R off : ℕ) : ℤ) % 2 ^ L = ((R : ℤ) + off) % 2 ^ L := by
  have hdvd : (2 : ℤ) ^ L ∣ 2 ^ N := pow_dvd_pow _ hLN
  rw [wrap_cast _ _ _ (pow_pos (by norm_num) _)]
  push_cast
  exact Int.emod_emod_of_dvd _ hdvd

section
variable {c : Comp} {N L L0 K : ℕ} {T S : ℕ → ℕ → F}

theorem ownG_read (hLN : L ≤ N) (hper : PeriodicCols c N L T S) {r : ℕ} (hr : r < 2 ^ L) {j : ℕ} {off : ℤ}
    (hoff : off ∈ mainOffs c j)
    (h : (mainOffs c j).length ≤ 2 ∨ (0 ≤ (r : ℤ) + off ∧ (r : ℤ) + off < 2 ^ L)) :
    ownG c N L T j (wrap (2 ^ L) r off) = T j (wrap (2 ^ N) r off) := by
  have hN : 0 < 2 ^ N := pow_pos (by norm_num) _
  have hL : 0 < 2 ^ L := pow_pos (by norm_num) _
  unfold ownG
  split_ifs with h2
  · unfold ownCol
    split_ifs with h3
    · rw [hper.1 j h3 _ (wrap_lt _ _ _ hN), wrap_mod_pow hLN]
    · have h1 : (mainOffs c j).length = 1 := by
        have hpos := List.length_pos_of_mem hoff
        omega
      obtain ⟨o, ho⟩ := List.length_eq_one_iff.mp h1
      rw [ho] at hoff ⊢
      have : off = o := List.mem_singleton.mp hoff
      subst this
      simp only [List.headD_cons]
      rw [wrap_wrap hL, add_neg_cancel, wrap_zero hr]
  · obtain ⟨h0, h1⟩ := h.resolve_left h2
    have hLN' : (2 : ℤ) ^ L ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hLN
    congr 1
    apply Int.ofNat.inj
    rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, wrap_eq_of_mem h0 (by exact_mod_cast h1),
      wrap_eq_of_mem h0 (by push_cast; omega)]

theorem pvAt_sound (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true) {R : ℕ} {ρ : ℤ}
    (hR : (R : ℤ) % 2 ^ L = ρ % 2 ^ L) {j : ℕ} {off : ℤ} {x : F} (h : pvAt c L0 K ρ j off = some x) :
    (c.air.pre.getD j (.periodic [0])).eval (2 ^ L) (wrap (2 ^ L) R off) = x := by
  unfold pvAt at h
  split_ifs at h with hτ
  have hL : 0 < 2 ^ L := pow_pos (by norm_num) _
  have hle : 2 ^ L0 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL0
  have hp : preParam (c.air.pre.getD j (.periodic [0])) ≤ K := by
    have := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hb).2
    by_cases hj : j < c.air.pre.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact of_decide_eq_true (this _ (List.getElem_mem hj))
    · rw [List.getD_eq_default _ _ (by omega)]; simp [preParam]
  rw [wrap_rel hL (by exact_mod_cast hR)]
  exact preSym_sound (by omega) (pow_dvd_pow _ hL0) hp hτ h

end


theorem partsOf_eval {g : Expr} {side : Bool} {a b : Expr} (h : partsOf g side = some (a, b))
    (l : Tree → ℕ → ℤ → QM) (pub : ℕ → QM) :
    g.evalR cstQ l pub = a.evalR cstQ l pub * b.evalR cstQ l pub := by
  cases g <;> simp only [partsOf, reduceCtorEq] at h
  rename_i x y
  cases side <;> simp only [Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true, if_false, if_true] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp only [Expr.evalR, mul_comm]

theorem partsOf_reads {g : Expr} {side : Bool} {a b : Expr} (h : partsOf g side = some (a, b)) {p : ℕ × ℤ}
    (hp : p ∈ mainReads b) : p ∈ mainReads g := by
  cases g <;> simp only [partsOf, reduceCtorEq] at h
  rename_i x y
  cases side <;> simp only [Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true, if_false, if_true] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [mainReads, hp]

theorem partsOf_offs {g : Expr} {side : Bool} {a b : Expr} (h : partsOf g side = some (a, b)) {o : ℤ}
    (hp : o ∈ offsAll b) : o ∈ offsAll g := by
  cases g <;> simp only [partsOf, reduceCtorEq] at h
  rename_i x y
  cases side <;> simp only [Option.some.injEq, Prod.mk.injEq, Bool.false_eq_true, if_false, if_true] at h <;>
    obtain ⟨rfl, rfl⟩ := h <;> simp [offsAll, hp]

theorem emb_ne_zero {y : F} (hy : y ≠ 0) : emb y ≠ 0 := fun h =>
  hy (StarkedAir.Spec.QM31.emb_inj (h.trans emb_zero.symm))

section
variable {c : Comp} {N L L0 K : ℕ} {α z share : QM} {pub : ℕ → QM} {T S : ℕ → ℕ → F}

theorem constraint_zero (hbig : BigOK c N L α z share pub T S) {R : ℕ} (hR : R < 2 ^ N) {g : Expr}
    (hg : g ∈ c.air.constraints) : g.evalR cstQ (liftVal N L c.air.pre T S R).leaf pub = 0 :=
  hbig R hR _ (List.mem_append_left _ (List.mem_map_of_mem hg))

/-- A guard that is a known nonzero constant forces its factor to vanish. -/
theorem factor_zero {pv : ℕ → ℤ → Option F} {zx : Expr → Bool} {l : Tree → ℕ → ℤ → QM}
    (hpv : ∀ j off x, pv j off = some x → l .pre j off = emb x)
    (hzx : ∀ e, zx e = true → e.evalR cstQ l pub = 0) {g a b : Expr} {side : Bool}
    (hp : partsOf g side = some (a, b)) (hg : g.evalR cstQ l pub = 0) {y : F} (hka : kv pv zx a = some y)
    (hy : y ≠ 0) : b.evalR cstQ l pub = 0 := by
  rw [partsOf_eval hp, kv_sound hpv hzx a y hka] at hg
  exact (mul_eq_zero.mp hg).resolve_left (emb_ne_zero hy)

theorem hpv_big (hLN : L ≤ N) (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true) {R : ℕ} {ρ : ℤ}
    (hR : (R : ℤ) % 2 ^ L = ρ % 2 ^ L) :
    ∀ j off x, pvAt c L0 K ρ j off = some x → (liftVal N L c.air.pre T S R).leaf .pre j off = emb x := by
  intro j off x h
  simp only [liftVal]
  rw [wrap_mod_pow hLN, pvAt_sound hL0 hK hb hR h]

theorem hpv_own (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true) {main : ℕ → ℕ → F} {r : ℕ}
    {ρ : ℤ} (hr : (r : ℤ) % 2 ^ L = ρ % 2 ^ L) :
    ∀ j off x, pvAt c L0 K ρ j off = some x → (rowVal (2 ^ L) c.air.pre main S r).leaf .pre j off = emb x := by
  intro j off x h
  simp only [rowVal]
  rw [pvAt_sound hL0 hK hb hr h]

theorem modL_shift {L : ℕ} {X : ℕ} {R : ℕ} {ρ : ℤ} (off : ℤ) (hR : (R : ℤ) % 2 ^ L = ρ % 2 ^ L)
    (hX : (X : ℤ) % 2 ^ L = ((R : ℤ) + off) % 2 ^ L) : (X : ℤ) % 2 ^ L = (ρ + off) % 2 ^ L := by
  rw [hX, ← Int.emod_add_emod, hR, Int.emod_add_emod]

/-- **Cell facts hold at every congruent big row.** -/
theorem cell_zero (hLN : L ≤ N) (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true)
    (hbig : BigOK c N L α z share pub T S) {f : ℕ × ℤ} (hf : cellOk c L0 K f = true) {X : ℕ} (hX : X < 2 ^ N)
    (hXm : (X : ℤ) % 2 ^ L = f.2 % 2 ^ L) : T f.1 X = 0 := by
  have hN : 0 < 2 ^ N := pow_pos (by norm_num) _
  obtain ⟨g, hg, hside⟩ := List.any_eq_true.mp hf
  obtain ⟨side, -, hm⟩ := List.any_eq_true.mp hside
  rcases hp : partsOf g side with _ | ⟨a, b⟩
  · rw [hp] at hm; cases hm
  rw [hp] at hm
  rcases b with ⟨_ | _, j, o⟩ | _ | _ | _ | _ | _ | _ <;> simp only [reduceCtorEq] at hm
  simp only [Bool.and_eq_true, beq_iff_eq] at hm
  obtain ⟨rfl, hka⟩ := hm
  rcases hk : kv (pvAt c L0 K (f.2 - o)) (fun _ => false) a with _ | y
  · rw [hk] at hka; cases hka
  rw [hk] at hka
  have hy : y ≠ 0 := by simpa using hka
  set R' := wrap (2 ^ N) X (-o) with hR'
  have hR'm : (R' : ℤ) % 2 ^ L = (f.2 - o) % 2 ^ L := by
    rw [hR', sub_eq_add_neg, wrap_modL hLN X (-o), ← Int.emod_add_emod, hXm, Int.emod_add_emod]
  have h0 := factor_zero (hpv_big hLN hL0 hK hb (T := T) (S := S) hR'm) (fun _ h => by cases h) hp
    (constraint_zero hbig (wrap_lt _ _ _ hN) hg) hk hy
  simp only [Expr.evalR, liftVal] at h0
  rw [hR', wrap_wrap hN, neg_add_cancel, wrap_zero hX] at h0
  exact StarkedAir.Spec.QM31.emb_inj (h0.trans emb_zero.symm)

end


theorem mainReads_offs {e : Expr} {j : ℕ} {off : ℤ} (h : (j, off) ∈ mainReads e) : off ∈ offsAll e := by
  induction e with
  | col t i o => cases t <;> simp_all [mainReads, offsAll]
  | const v => simp [mainReads] at h
  | pub i => simp [mainReads] at h
  | add a b iha ihb =>
    simp only [mainReads, List.mem_append] at h
    simp only [offsAll, List.mem_append]; exact h.imp iha ihb
  | sub a b iha ihb =>
    simp only [mainReads, List.mem_append] at h
    simp only [offsAll, List.mem_append]; exact h.imp iha ihb
  | mul a b iha ihb =>
    simp only [mainReads, List.mem_append] at h
    simp only [offsAll, List.mem_append]; exact h.imp iha ihb
  | neg a iha => exact iha h

section
variable {c : Comp} {N L L0 K : ℕ} {α z share : QM} {pub : ℕ → QM} {T S : ℕ → ℕ → F}
  {cells : List (ℕ × ℤ)} {rf : List (ℤ × ℕ × Bool)}

theorem zc_big (hLN : L ≤ N) (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true)
    (hbig : BigOK c N L α z share pub T S) (hcells : cells.all (cellOk c L0 K) = true) {R : ℕ}
    {ρ : ℤ} (hRρ : (R : ℤ) % 2 ^ L = ρ % 2 ^ L) :
    ∀ e, zc c cells ρ e = true → e.evalR cstQ (liftVal N L c.air.pre T S R).leaf pub = 0 := by
  have hN : 0 < 2 ^ N := pow_pos (by norm_num) _
  intro e he
  rcases e with ⟨_ | _, j, off⟩ | _ | _ | _ | _ | _ | _ <;> simp only [zc, reduceCtorEq] at he
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he
  have := cell_zero hLN hL0 hK hb hbig (List.all_eq_true.mp hcells _ he.2) (wrap_lt _ _ _ hN)
    (modL_shift off hRρ (wrap_modL hLN R off))
  simp only [Expr.evalR, liftVal]
  rw [this, emb_zero]

theorem zc_own (hLN : L ≤ N) (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true)
    (hbig : BigOK c N L α z share pub T S) (hcells : cells.all (cellOk c L0 K) = true) {r : ℕ}
    {ρ : ℤ} (hrρ : (r : ℤ) % 2 ^ L = ρ % 2 ^ L) :
    ∀ e, zc c cells ρ e = true → e.evalR cstQ (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf pub = 0 := by
  have hL : 0 < 2 ^ L := pow_pos (by norm_num) _
  intro e he
  rcases e with ⟨_ | _, j, off⟩ | _ | _ | _ | _ | _ | _ <;> simp only [zc, reduceCtorEq] at he
  simp only [Bool.and_eq_true, List.contains_iff_mem] at he
  have h3 : ¬ (mainOffs c j).length ≤ 2 := by have := of_decide_eq_true he.1; omega
  have := cell_zero hLN hL0 hK hb hbig (List.all_eq_true.mp hcells _ he.2)
    (wrap_small hLN (wrap_lt _ _ _ hL)) (modL_shift off hrρ (wrap_modL le_rfl r off))
  simp only [Expr.evalR, rowVal, ownG, h3, if_false]
  rw [this, emb_zero]

theorem pre_agree (hLN : L ≤ N) (main : ℕ → ℕ → F) (r j : ℕ) (off : ℤ) :
    (rowVal (2 ^ L) c.air.pre main S r).leaf .pre j off = (liftVal N L c.air.pre T S r).leaf .pre j off := by
  simp only [rowVal, liftVal]
  rw [wrap_mod_pow hLN]

/-- **Known zeros are sound** at own row `r`, relative row `ρ`, in both traces, given that reads outside
`W` agree. -/
theorem zx_sound (hLN : L ≤ N) (hL0 : L0 ≤ L) (hK : 8 * K + 8 < 2 ^ L0) (hb : bndOk c K = true)
    (hbig : BigOK c N L α z share pub T S) (hcells : cells.all (cellOk c L0 K) = true)
    (hrf : rf.all (rowOk c L0 K cells) = true) {r : ℕ} (hr : r < 2 ^ L) {ρ : ℤ}
    (hrρ : (r : ℤ) % 2 ^ L = ρ % 2 ^ L)
    (hag : ∀ j off, (∃ e ∈ exprs c, (j, off) ∈ mainReads e) → WAt c ρ j off = false →
      (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf .main j off = (liftVal N L c.air.pre T S r).leaf .main j off) :
    (∀ e, zx c cells rf ρ e = true → e.evalR cstQ (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf pub = 0) ∧
    (∀ e, zx c cells rf ρ e = true → e.evalR cstQ (liftVal N L c.air.pre T S r).leaf pub = 0) := by
  have hrN := wrap_small hLN hr
  have hzo := zc_own (pub := pub) hLN hL0 hK hb hbig hcells hrρ
  have hzb := zc_big (pub := pub) hLN hL0 hK hb hbig hcells hrρ
  have hpo := hpv_own (main := ownG c N L T) (S := S) hL0 hK hb hrρ
  have hpb := hpv_big (T := T) (S := S) hLN hL0 hK hb hrρ
  -- a row fact's factor vanishes in both traces
  have hfact : ∀ f ∈ rf, f.1 = ρ → ∀ a b, factOf c f.2 = some (a, b) →
      b.evalR cstQ (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf pub = 0 ∧
      b.evalR cstQ (liftVal N L c.air.pre T S r).leaf pub = 0 := by
    intro f hf hfρ a b hab
    have hok := List.all_eq_true.mp hrf f hf
    unfold rowOk at hok
    rw [hab] at hok
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hok
    obtain ⟨hka, hd⟩ := hok
    rw [hfρ] at hka hd
    rcases hk : kv (pvAt c L0 K ρ) (zc c cells ρ) a with _ | y
    · rw [hk] at hka; cases hka
    rw [hk] at hka
    have hy : y ≠ 0 := by simpa using hka
    obtain ⟨g, hg, hp⟩ : ∃ g, c.air.constraints[f.2.1]? = some g ∧ partsOf g f.2.2 = some (a, b) := by
      unfold factOf at hab
      rcases hgi : c.air.constraints[f.2.1]? with _ | g
      · rw [hgi] at hab; cases hab
      · rw [hgi] at hab; exact ⟨g, rfl, hab⟩
    have hgm : g ∈ c.air.constraints := List.mem_of_getElem? hg
    have hbig0 := factor_zero hpb hzb hp (constraint_zero hbig hrN hgm) hk hy
    refine ⟨?_, hbig0⟩
    rw [dep_sound (pre_agree hLN _ r) hpo hzo hzb b (fun j off hjo hW => hag j off
      ⟨g, List.mem_append_left _ hgm, partsOf_reads hp hjo⟩ hW) hd]
    exact hbig0
  have hsplit : ∀ e, zx c cells rf ρ e = true → zc c cells ρ e = true ∨
      ∃ f ∈ rf, f.1 = ρ ∧ ∃ a, factOf c f.2 = some (a, e) := by
    intro e he
    unfold zx at he
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at he
    refine he.imp id fun ⟨f, hf, hfρ, hp⟩ => ⟨f, hf, hfρ, ?_⟩
    rcases hq : factOf c f.2 with _ | ⟨a, b⟩
    · rw [hq] at hp; cases hp
    · rw [hq] at hp
      simp only [Option.any_some, beq_iff_eq] at hp
      exact ⟨a, hp ▸ rfl⟩
  constructor
  · intro e he
    rcases hsplit e he with h | ⟨f, hf, hfρ, a, hab⟩
    · exact hzo e h
    · exact (hfact f hf hfρ a e hab).1
  · intro e he
    rcases hsplit e he with h | ⟨f, hf, hfρ, a, hab⟩
    · exact hzb e h
    · exact (hfact f hf hfρ a e hab).2

end


/-- **(W) from the check**, at every own size `L ≥ L0`. -/
theorem liftOK_of_guard {c : Comp} {N L L0 K : ℕ} {cells : List (ℕ × ℤ)} {rf : List (ℤ × ℕ × Bool)}
    (hL0 : L0 ≤ L) (hLN : L ≤ N) (h : guardOk c L0 K cells rf = true) : LiftOK c N L := by
  unfold guardOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hK, hb⟩, hcells⟩, hrf⟩, hrows⟩ := h
  intro α z share pub T S hbig hper
  have hN : 0 < 2 ^ N := pow_pos (by norm_num) _
  have hL : 0 < 2 ^ L := pow_pos (by norm_num) _
  have hKL : 8 * K + 8 < 2 ^ L := lt_of_lt_of_le hK (Nat.pow_le_pow_right (by norm_num) hL0)
  have hcL : ((2 ^ L : ℕ) : ℤ) = (2 : ℤ) ^ L := by push_cast; rfl
  refine ⟨ownG c N L T, S, fun r hr t ht => ?_⟩
  have hrN := wrap_small hLN hr
  apply hbig r hrN
  -- reads of the component: bounded offsets, in `mainOffs`
  have hoffs : ∀ e ∈ exprs c, ∀ j off, (j, off) ∈ mainReads e → |off| ≤ K ∧ off ∈ mainOffs c j := by
    intro e he j off hjo
    have h1 := List.all_eq_true.mp ((Bool.and_eq_true _ _).mp hb).1 e he
    exact ⟨of_decide_eq_true (List.all_eq_true.mp h1 off (mainReads_offs hjo)), mem_mainOffs he hjo⟩
  have hread : ∀ j off, off ∈ mainOffs c j →
      ((mainOffs c j).length ≤ 2 ∨ (0 ≤ (r : ℤ) + off ∧ (r : ℤ) + off < 2 ^ L)) →
      (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf .main j off = (liftVal N L c.air.pre T S r).leaf .main j off := by
    intro j off hm hc
    simp only [rowVal, liftVal]
    rw [ownG_read hLN hper hr hm hc]
  have hE : ∀ e ∈ exprs c, e.evalR cstQ (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf pub =
      e.evalR cstQ (liftVal N L c.air.pre T S r).leaf pub := by
    intro e he
    by_cases hmid : K ≤ r ∧ r + K < 2 ^ L
    · refine evalR_congr _ _ _ _ (pre_agree hLN _ r) e fun j off hjo => ?_
      obtain ⟨hK', hm⟩ := hoffs e he j off hjo
      have := abs_le.mp hK'
      exact hread j off hm (Or.inr ⟨by omega, by omega⟩)
    -- a boundary row, at relative row `ρ`
    obtain ⟨ρ, hρ1, hρ2, hrρ, hρa, hρb⟩ : ∃ ρ : ℤ, -(K : ℤ) ≤ ρ ∧ ρ < K ∧ (r : ℤ) % 2 ^ L = ρ % 2 ^ L ∧
        (r < K → ρ = r) ∧ (¬ r < K → ρ = r - 2 ^ L) := by
      by_cases h1 : r < K
      · exact ⟨r, by omega, by omega, rfl, fun _ => rfl, fun h => absurd h1 h⟩
      · refine ⟨r - 2 ^ L, by omega, by omega, ?_, fun h => absurd h h1, fun _ => rfl⟩
        rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ (dvd_refl _)]
    have hag : ∀ j off, (∃ e ∈ exprs c, (j, off) ∈ mainReads e) → WAt c ρ j off = false →
        (rowVal (2 ^ L) c.air.pre (ownG c N L T) S r).leaf .main j off =
          (liftVal N L c.air.pre T S r).leaf .main j off := by
      rintro j off ⟨e', he', hjo⟩ hW
      obtain ⟨hK', hm⟩ := hoffs e' he' j off hjo
      have := abs_le.mp hK'
      unfold WAt at hW
      rcases hbj : big c j
      · exact hread j off hm (Or.inl (by unfold big at hbj; have := of_decide_eq_false hbj; omega))
      · rw [hbj, Bool.true_and] at hW
        refine hread j off hm (Or.inr ?_)
        unfold wraps at hW
        by_cases h1 : r < K
        · rw [hρa h1] at hW
          simp only [Nat.cast_nonneg, if_true, decide_eq_false_iff_not, not_lt] at hW
          constructor <;> omega
        · rw [hρb h1, if_neg (by omega), decide_eq_false_iff_not] at hW
          constructor <;> omega
    have hd : dep (pvAt c L0 K ρ) (zx c cells rf ρ) (WAt c ρ) e = false := by
      have hi : (ρ + K).toNat < 2 * K := by omega
      have := List.all_eq_true.mp (List.all_eq_true.mp hrows _ (List.mem_range.mpr hi)) e he
      rwa [show (((ρ + K).toNat : ℕ) : ℤ) - K = ρ by omega, Bool.not_eq_true'] at this
    obtain ⟨hzo, hzb⟩ := zx_sound hLN hL0 hK hb hbig hcells hrf hr hrρ hag
    exact dep_sound (pre_agree hLN _ r) (hpv_own hL0 hK hb hrρ) hzo hzb e
      (fun j off hjo hW => hag j off ⟨e, he, hjo⟩ hW) hd
  rwa [← terms_congr_exprs c α z share pub _ _ hE]
  · intro k
    simp only [rowVal, liftVal, wrap_zero hr, wrap_zero hrN]
  · intro hne k hk
    simp only [rowVal, liftVal]
    rw [hper.2 hne k hk _ (wrap_lt _ _ _ hN), wrap_mod_pow hLN]

end StarkedAir.Circuit.Lift
