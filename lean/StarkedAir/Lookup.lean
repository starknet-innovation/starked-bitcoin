/-
**Lookups (IR v2, roadmap IR-LOGUP): semantics.** A *system* is several components, each an AIR
plus lookup declarations. At every row of its trace, a lookup emits an entry: a relation id, a
tuple of field elements and a multiplicity. A system is satisfied when every component's AIR is
satisfied and every relation is *balanced*: for each tuple, the multiplicities of all its
entries, over all components and rows, sum to zero.

Tables emit their rows with a prover-chosen multiplicity; users emit with multiplicity `−1`.
`used_in_table` turns balance into membership: every used tuple is emitted by a table, as long
as the number of uses stays below the field size.

How balance is enforced (LogUp: interaction columns, random challenges, claimed sums) is a
separate layer; its deterministic part is proven in `LogUp.lean`, and the random-challenge step
(Schwartz–Zippel over QM31) is trusted with Stwo.
-/
import StarkedAir.IR

namespace StarkedAir

structure Lookup where
  rel : ℕ
  mult : Expr
  vals : List Expr
  deriving Repr

structure Comp where
  air : Air
  lookups : List Lookup

structure System where
  /-- Number of components. -/
  m : ℕ
  comp : ℕ → Comp

/-- One component's trace: its log size and main columns. -/
structure Inst where
  logSize : ℕ
  main : ℕ → ℕ → F

/-- A lookup site: component `i`, row `r`, lookup `k`. -/
abbrev Site := ℕ × ℕ × ℕ

/-- All sites of a system instance. -/
def sites (sys : System) (inst : ℕ → Inst) : List Site :=
  (List.range sys.m).flatMap fun i =>
    (List.range (2 ^ (inst i).logSize)).flatMap fun r =>
      (List.range (sys.comp i).lookups.length).map fun k => (i, r, k)

section
variable (sys : System) (inst : ℕ → Inst) (pub : ℕ → F)

def siteLookup (s : Site) : Lookup := (sys.comp s.1).lookups.getD s.2.2 ⟨0, .const 0, []⟩

def siteEval (s : Site) (e : Expr) : F :=
  e.eval (2 ^ (inst s.1).logSize) (sys.comp s.1).air.pre pub (inst s.1).main s.2.1

def siteRel (s : Site) : ℕ := (siteLookup sys s).rel
def siteVals (s : Site) : List F := (siteLookup sys s).vals.map (siteEval sys inst pub s)
def siteMult (s : Site) : F := siteEval sys inst pub s (siteLookup sys s).mult

/-- Total multiplicity of tuple `v` in relation `R`. -/
def total (R : ℕ) (v : List F) : F :=
  (((sites sys inst).filter fun s => siteRel sys s = R ∧ siteVals sys inst pub s = v).map
    (siteMult sys inst pub)).sum

def Balanced : Prop := ∀ R v, total sys inst pub R v = 0

/-- **System satisfaction**: every component's AIR holds and every relation is balanced. -/
def System.Satisfied : Prop :=
  (∀ i < sys.m, (sys.comp i).air.Satisfied (inst i).logSize pub (inst i).main) ∧ Balanced sys inst pub
end

theorem sum_neg_one {α : Type} (l : List α) (f : α → F) (h : ∀ a ∈ l, f a = -1) :
    (l.map f).sum = -(l.length : F) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    rw [h a (List.mem_cons_self ..), ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    ring

/-- **Balance gives membership.** Classify each lookup `(i, k)` as a use (`use i k`) whose
multiplicity is `−1` at every row, or a table. If there are fewer than `P` use sites in all, then
every emitted tuple (in particular every used one) is emitted, in the same relation, by some
table site. -/
theorem used_in_table {sys : System} {inst : ℕ → Inst} {pub : ℕ → F} (hb : Balanced sys inst pub)
    (use : ℕ → ℕ → Prop) [DecidablePred fun s : Site => use s.1 s.2.2]
    (huse : ∀ s ∈ sites sys inst, use s.1 s.2.2 → siteMult sys inst pub s = -1)
    (hcount : ((sites sys inst).filter fun s => use s.1 s.2.2).length < P)
    {s0 : Site} (hs0 : s0 ∈ sites sys inst) :
    ∃ s ∈ sites sys inst, ¬ use s.1 s.2.2 ∧ siteRel sys s = siteRel sys s0 ∧
      siteVals sys inst pub s = siteVals sys inst pub s0 := by
  by_contra hne
  push Not at hne
  set R := siteRel sys s0
  set v := siteVals sys inst pub s0
  obtain ⟨L, hL⟩ : ∃ L, L = (sites sys inst).filter fun s => siteRel sys s = R ∧ siteVals sys inst pub s = v :=
    ⟨_, rfl⟩
  have hall : ∀ s ∈ L, use s.1 s.2.2 := by
    intro s hs
    rw [hL, List.mem_filter] at hs
    by_contra hn
    have h2 : siteRel sys s = R ∧ siteVals sys inst pub s = v := by simpa using hs.2
    exact hne s hs.1 hn h2.1 h2.2
  have htot : total sys inst pub R v = -(L.length : F) := by
    unfold total; rw [← hL]
    exact sum_neg_one L _ (fun s hs => huse s (List.mem_filter.mp (hL ▸ hs)).1 (hall s hs))
  have hpos : 0 < L.length := List.length_pos_of_mem (hL ▸ List.mem_filter.mpr ⟨hs0, by simp [R, v]⟩)
  have hle : L.length ≤ ((sites sys inst).filter fun s => use s.1 s.2.2).length := by
    have e : L = L.filter fun s => decide (use s.1 s.2.2) :=
      (List.filter_eq_self.mpr fun s hs => by simpa using hall s hs).symm
    rw [e, hL, List.filter_filter]
    apply List.Sublist.length_le
    apply List.monotone_filter_right
    intro a h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
    exact h.1
  have h0 := hb R v
  rw [htot, neg_eq_zero] at h0
  have := natCast_inj_of_lt (a := L.length) (b := 0) (by omega) (by unfold P; norm_num) (by simpa using h0)
  omega

/-! ### Public entries and selector-gated uses -/

/-- Entries the verifier contributes: `(relation, tuple, multiplicity)`. -/
abbrev Ext := List (ℕ × List F × F)

def extTotal (ext : Ext) (R : ℕ) (v : List F) : F :=
  ((ext.filter fun e => e.1 = R ∧ e.2.1 = v).map (·.2.2)).sum

section
variable (sys : System) (inst : ℕ → Inst) (pub : ℕ → F)

/-- Balance including public entries. -/
def BalancedExt (ext : Ext) : Prop := ∀ R v, total sys inst pub R v + extTotal ext R v = 0

def System.SatisfiedExt (ext : Ext) : Prop :=
  (∀ i < sys.m, (sys.comp i).air.Satisfied (inst i).logSize pub (inst i).main) ∧ BalancedExt sys inst pub ext
end

theorem sum_neg_one_or_zero {α : Type} (l : List α) (f : α → F) (h : ∀ a ∈ l, f a = -1 ∨ f a = 0) :
    (l.map f).sum = -(((l.filter fun a => f a = -1).length : ℕ) : F) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, List.filter_cons]
    rw [ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]
    rcases h a (List.mem_cons_self ..) with ha | ha
    · simp only [ha, if_true, decide_true, List.length_cons, Nat.cast_succ]; ring
    · have : ¬ (0 : F) = -1 := fun h0 => one_ne_zero (neg_eq_zero.mp h0.symm)
      simp [ha, this]

/-- **Balance gives membership**, with public entries and selector-gated uses. Use sites
(`use i k`) have multiplicity `−1` or `0` at every row; public entries have multiplicity `−1`. If
fewer than `P` use sites and public entries take part, every tuple that a use site (with
multiplicity `−1`) or a public entry looks up is emitted by some table site. -/
theorem used_in_table_ext {sys : System} {inst : ℕ → Inst} {pub : ℕ → F} {ext : Ext}
    (hb : BalancedExt sys inst pub ext)
    (use : ℕ → ℕ → Prop) [DecidablePred fun s : Site => use s.1 s.2.2]
    (huse : ∀ s ∈ sites sys inst, use s.1 s.2.2 → siteMult sys inst pub s = -1 ∨ siteMult sys inst pub s = 0)
    (hext : ∀ e ∈ ext, e.2.2 = -1)
    (hcount : ((sites sys inst).filter fun s => use s.1 s.2.2).length + ext.length < P)
    {R : ℕ} {v : List F}
    (h0 : (∃ s ∈ sites sys inst, use s.1 s.2.2 ∧ siteMult sys inst pub s = -1 ∧ siteRel sys s = R ∧
        siteVals sys inst pub s = v) ∨ (R, v, -1) ∈ ext) :
    ∃ s ∈ sites sys inst, ¬ use s.1 s.2.2 ∧ siteRel sys s = R ∧ siteVals sys inst pub s = v := by
  by_contra hne
  push Not at hne
  obtain ⟨L, hL⟩ : ∃ L, L = (sites sys inst).filter fun s => siteRel sys s = R ∧ siteVals sys inst pub s = v :=
    ⟨_, rfl⟩
  have hall : ∀ s ∈ L, use s.1 s.2.2 := by
    intro s hs
    rw [hL, List.mem_filter] at hs
    by_contra hn
    have h2 : siteRel sys s = R ∧ siteVals sys inst pub s = v := by simpa using hs.2
    exact hne s hs.1 hn h2.1 h2.2
  have hsub : ∀ s ∈ L, siteMult sys inst pub s = -1 ∨ siteMult sys inst pub s = 0 :=
    fun s hs => huse s (List.mem_filter.mp (hL ▸ hs)).1 (hall s hs)
  set E := ext.filter fun e => e.1 = R ∧ e.2.1 = v
  have htot : total sys inst pub R v = -(((L.filter fun s => siteMult sys inst pub s = -1).length : ℕ) : F) := by
    unfold total; rw [← hL]; exact sum_neg_one_or_zero L _ hsub
  have hext' : extTotal ext R v = -((E.length : ℕ) : F) := by
    unfold extTotal
    exact sum_neg_one (E) _ (fun e he => hext e (List.mem_filter.mp he).1)
  set a := (L.filter fun s => siteMult sys inst pub s = -1).length
  have hpos : 0 < a + E.length := by
    rcases h0 with ⟨s, hs, hu, hm, hr, hv⟩ | he
    · have : s ∈ L.filter fun s => siteMult sys inst pub s = -1 :=
        List.mem_filter.mpr ⟨hL ▸ List.mem_filter.mpr ⟨hs, by simp [hr, hv]⟩, by simp [hm]⟩
      have := List.length_pos_of_mem this; omega
    · have : (R, v, (-1 : F)) ∈ E := List.mem_filter.mpr ⟨he, by simp⟩
      have := List.length_pos_of_mem this; omega
  have hle : a ≤ ((sites sys inst).filter fun s => use s.1 s.2.2).length := by
    calc a ≤ L.length := List.length_filter_le _ _
      _ ≤ _ := by
        have e : L = L.filter fun s => decide (use s.1 s.2.2) :=
          (List.filter_eq_self.mpr fun s hs => by simpa using hall s hs).symm
        rw [e, hL, List.filter_filter]
        apply List.Sublist.length_le
        apply List.monotone_filter_right
        intro x hx
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hx ⊢
        exact hx.1
  have hEle : E.length ≤ ext.length := List.length_filter_le _ _
  have h0' := hb R v
  rw [htot, hext', ← neg_add, neg_eq_zero, ← Nat.cast_add] at h0'
  have := natCast_inj_of_lt (a := a + E.length) (b := 0) (by omega) (by unfold P; norm_num) (by simpa using h0')
  omega

end StarkedAir
