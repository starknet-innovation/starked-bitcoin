/-
**The UTXO multiset argument (M3b, D-040), at the spec level.** Core keeps the coins view as a map from
outpoints to coins and connects transactions in order: each input must find its coin, which is removed,
then each output is added (and may not overwrite an unspent coin, BIP30).

M3b does not run that map in the proof. Instead every created coin and every spent coin is a tuple
`(key, value, creation index)`; a spent coin's tuple is what the prover claims (the undo record), with a
creation index before the spending transaction's. Over an epoch the created tuples must equal, as
multisets, the spent ones plus the final set.

**`run_of_balance`**: if creation keys are unique and every claimed creation index is earlier, a balance
`created = spent + final` implies Core's sequential update succeeds, every input reads exactly the coin
it claims (so the undo records are the removed coins, D-029), no outpoint is spent twice (D-031), and
the final view is the final set.
-/
import Mathlib

namespace StarkedAir.Spec.Utxo

variable {K V : Type} [DecidableEq K] [DecidableEq V]

/-- A coin tuple: outpoint, coin data, creation index (the creating transaction's position). -/
abbrev Ev (K V : Type) := K × V × ℕ

/-- A transaction's coin events: its inputs as claimed tuples, its outputs. -/
structure Tx (K V : Type) where
  ins : List (Ev K V)
  outs : List (K × V)

/-- The coins view: outpoint ↦ (coin, creation index). -/
abbrev View (K V : Type) := K → Option (V × ℕ)

/-- Spend: the outpoint must hold exactly the claimed coin; it is removed. -/
def spendOne (m : View K V) (e : Ev K V) : Option (View K V) :=
  if m e.1 = some (e.2.1, e.2.2) then some (Function.update m e.1 none) else none

/-- Add an output of transaction `i`; it may not overwrite a coin. -/
def addOne (i : ℕ) (m : View K V) (o : K × V) : Option (View K V) :=
  if m o.1 = none then some (Function.update m o.1 (some (o.2, i))) else none

/-- Connect transaction `i`: inputs, then outputs. -/
def applyTx (i : ℕ) (m : View K V) (t : Tx K V) : Option (View K V) :=
  (t.ins.foldlM spendOne m) >>= fun m' => t.outs.foldlM (addOne i) m'

/-- Connect transactions `i, i + 1, …` in order. -/
def run : ℕ → View K V → List (Tx K V) → Option (View K V)
  | _, m, [] => some m
  | i, m, t :: ts => (applyTx i m t) >>= fun m' => run (i + 1) m' ts

/-- Transaction `i`'s created tuples. -/
def outsT (i : ℕ) (t : Tx K V) : Multiset (Ev K V) := ((t.outs.map fun o => (o.1, o.2, i) : List (Ev K V)) : Multiset _)

def created : ℕ → List (Tx K V) → Multiset (Ev K V)
  | _, [] => 0
  | i, t :: ts => outsT i t + created (i + 1) ts

def spent : List (Tx K V) → Multiset (Ev K V)
  | [] => 0
  | t :: ts => (t.ins : Multiset (Ev K V)) + spent ts

/-- Every claimed creation index is before the spending transaction (`i` the first one's index). -/
def Ordered : ℕ → List (Tx K V) → Prop
  | _, [] => True
  | i, t :: ts => (∀ e ∈ t.ins, e.2.2 < i) ∧ Ordered (i + 1) ts

/-- The view `m` holds exactly the tuples of `R`, whose keys are distinct. -/
def Rep (m : View K V) (R : Multiset (Ev K V)) : Prop :=
  (R.map Prod.fst).Nodup ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ R

theorem nodup_keys_le {R S : Multiset (Ev K V)} (h : R ≤ S) (hs : (S.map Prod.fst).Nodup) : (R.map Prod.fst).Nodup :=
  Multiset.nodup_of_le (Multiset.map_le_map h) hs

theorem rep_spend {m : View K V} {R : Multiset (Ev K V)} (hr : Rep m R) {e : Ev K V} (he : e ∈ R) :
    ∃ m', spendOne m e = some m' ∧ Rep m' (R.erase e) := by
  obtain ⟨hnd, hiff⟩ := hr
  have hm : m e.1 = some (e.2.1, e.2.2) := (hiff e.1 e.2.1 e.2.2).mpr (by simpa using he)
  refine ⟨Function.update m e.1 none, by simp [spendOne, hm], nodup_keys_le (Multiset.erase_le e R) hnd, ?_⟩
  intro k v j
  have hR : R = e ::ₘ R.erase e := (Multiset.cons_erase he).symm
  by_cases hk : k = e.1
  · subst hk
    simp only [Function.update_self, reduceCtorEq, false_iff]
    intro hmem
    rw [hR, Multiset.map_cons, Multiset.nodup_cons] at hnd
    exact hnd.1 (Multiset.mem_map.mpr ⟨_, hmem, rfl⟩)
  · rw [Function.update_of_ne hk, hiff]
    have hne : (k, v, j) ≠ e := fun h => hk (by rw [← h])
    exact (Multiset.mem_erase_of_ne hne).symm

theorem rep_add {m : View K V} {R : Multiset (Ev K V)} (hr : Rep m R) (i : ℕ) {o : K × V}
    (hnd : (((o.1, o.2, i) ::ₘ R).map Prod.fst).Nodup) :
    ∃ m', addOne i m o = some m' ∧ Rep m' ((o.1, o.2, i) ::ₘ R) := by
  obtain ⟨-, hiff⟩ := hr
  have hnot : o.1 ∉ R.map Prod.fst := by
    rw [Multiset.map_cons, Multiset.nodup_cons] at hnd; exact hnd.1
  have hm : m o.1 = none := by
    by_contra h
    obtain ⟨⟨v, j⟩, hx⟩ := Option.ne_none_iff_exists'.mp h
    exact hnot (Multiset.mem_map.mpr ⟨(o.1, v, j), (hiff _ _ _).mp hx, rfl⟩)
  refine ⟨Function.update m o.1 (some (o.2, i)), by simp [addOne, hm], hnd, ?_⟩
  intro k v j
  by_cases hk : k = o.1
  · subst hk
    rw [Function.update_self, Multiset.mem_cons]
    constructor
    · intro h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      left; rw [← h.1, ← h.2]
    · rintro (h | h)
      · have h2 := congrArg (fun x => x.2) h
        simp only [Prod.mk.injEq] at h2
        rw [h2.1, h2.2]
      · exact absurd (Multiset.mem_map.mpr ⟨_, h, rfl⟩) hnot
  · rw [Function.update_of_ne hk, hiff, Multiset.mem_cons]
    constructor
    · exact Or.inr
    · rintro (h | h)
      · exact absurd (congrArg Prod.fst h) hk
      · exact h

theorem spend_all : ∀ (ins : List (Ev K V)) (m : View K V) (R : Multiset (Ev K V)), Rep m R →
    (ins : Multiset (Ev K V)) ≤ R → ∃ m', ins.foldlM spendOne m = some m' ∧ Rep m' (R - ins)
  | [], m, R, hr, _ => ⟨m, rfl, by simpa using hr⟩
  | e :: rest, m, R, hr, hle => by
    have he : e ∈ R := Multiset.mem_of_le hle (by simp)
    obtain ⟨m1, h1, hr1⟩ := rep_spend hr he
    have hle' : (rest : Multiset (Ev K V)) ≤ R.erase e := by
      have := Multiset.erase_le_erase e hle
      simpa using this
    obtain ⟨m', h', hr'⟩ := spend_all rest m1 (R.erase e) hr1 hle'
    refine ⟨m', by simp [List.foldlM_cons, h1, h'], ?_⟩
    rw [← Multiset.cons_coe, Multiset.sub_cons]
    exact hr'

theorem add_all (i : ℕ) : ∀ (outs : List (K × V)) (m : View K V) (R : Multiset (Ev K V)), Rep m R →
    ((((outs.map fun o => (o.1, o.2, i) : List (Ev K V)) : Multiset (Ev K V)) + R).map Prod.fst).Nodup →
    ∃ m', outs.foldlM (addOne i) m = some m' ∧
      Rep m' (((outs.map fun o => (o.1, o.2, i) : List (Ev K V)) : Multiset (Ev K V)) + R)
  | [], m, R, hr, _ => ⟨m, rfl, by simpa using hr⟩
  | o :: rest, m, R, hr, hnd => by
    have hnd1 : (((o.1, o.2, i) ::ₘ R).map Prod.fst).Nodup := by
      refine nodup_keys_le ?_ hnd
      simp only [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add]
      exact Multiset.cons_le_cons _ (Multiset.le_add_left _ _)
    obtain ⟨m1, h1, hr1⟩ := rep_add hr i hnd1
    have hnd2 : ((((rest.map fun o => (o.1, o.2, i) : List (Ev K V)) : Multiset (Ev K V)) + (o.1, o.2, i) ::ₘ R).map
        Prod.fst).Nodup := by
      simpa [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons] using hnd
    obtain ⟨m', h', hr'⟩ := add_all i rest m1 _ hr1 hnd2
    refine ⟨m', by simp [List.foldlM_cons, h1, h'], ?_⟩
    simpa [List.map_cons, ← Multiset.cons_coe, Multiset.cons_add, Multiset.add_cons] using hr'

/-- A tuple created by transactions from `i` on has index at least `i`. -/
theorem created_idx : ∀ (ts : List (Tx K V)) (i : ℕ), ∀ e ∈ created i ts, i ≤ e.2.2
  | [], _, e, he => by simp [created] at he
  | t :: ts, i, e, he => by
    simp only [created, Multiset.mem_add, outsT, Multiset.mem_coe, List.mem_map] at he
    rcases he with ⟨o, _, rfl⟩ | he
    · exact le_rfl
    · have := created_idx ts (i + 1) e he; omega

theorem count_created_zero (ts : List (Tx K V)) (i : ℕ) {e : Ev K V} (he : e.2.2 < i) :
    Multiset.count e (created i ts) = 0 :=
  Multiset.count_eq_zero.mpr fun h => absurd (created_idx ts i e h) (by omega)

/-- **The induction.** From a view holding `R` (indices below `i`), connecting `ts` succeeds and holds
`R + created − spent`, given distinct keys, earlier claims, and spends covered by what exists. -/
theorem run_rep : ∀ (ts : List (Tx K V)) (i : ℕ) (m : View K V) (R : Multiset (Ev K V)), Rep m R →
    (∀ e ∈ R, e.2.2 < i) → Ordered i ts → ((R + created i ts).map Prod.fst).Nodup →
    spent ts ≤ R + created i ts →
    ∃ m', run i m ts = some m' ∧ Rep m' (R + created i ts - spent ts)
  | [], i, m, R, hr, _, _, _, _ => ⟨m, rfl, by simpa [created, spent] using hr⟩
  | t :: ts, i, m, R, hr, hidx, hord, hnd, hle => by
    obtain ⟨hin, hord'⟩ := hord
    simp only [created, spent] at hnd hle
    -- the inputs are covered by `R`: their indices are below `i`
    have hinR : (t.ins : Multiset (Ev K V)) ≤ R := by
      rw [Multiset.le_iff_count]
      intro e
      by_cases hmem : e ∈ (t.ins : Multiset (Ev K V))
      · have hlt : e.2.2 < i := hin e (by simpa using hmem)
        have h1 := Multiset.le_iff_count.mp hle e
        simp only [Multiset.count_add] at h1
        have c1 := count_created_zero ts (i + 1) (e := e) (by omega)
        have c2 : Multiset.count e (outsT i t) = 0 := Multiset.count_eq_zero.mpr fun h => by
          simp only [outsT, Multiset.mem_coe, List.mem_map] at h
          obtain ⟨o, _, rfl⟩ := h; simp at hlt
        rw [c1, c2] at h1
        omega
      · rw [Multiset.count_eq_zero.mpr hmem]; exact Nat.zero_le _
    obtain ⟨m1, h1, hr1⟩ := spend_all t.ins m R hr hinR
    have hsub : outsT i t + (R - t.ins) ≤ R + (outsT i t + created (i + 1) ts) := by
      calc outsT i t + (R - t.ins) ≤ outsT i t + R := add_le_add (le_refl _) tsub_le_self
        _ = R + outsT i t := add_comm _ _
        _ ≤ R + (outsT i t + created (i + 1) ts) := add_le_add (le_refl _) (Multiset.le_add_right _ _)
    obtain ⟨m2, h2, hr2⟩ := add_all i t.outs m1 (R - t.ins) hr1 (nodup_keys_le hsub hnd)
    -- the rest, from `R' = outs + (R − ins)`
    set R' := outsT i t + (R - t.ins) with hR'
    have hidx' : ∀ e ∈ R', e.2.2 < i + 1 := by
      intro e he
      rcases Multiset.mem_add.mp he with h | h
      · simp only [outsT, Multiset.mem_coe, List.mem_map] at h
        obtain ⟨o, _, rfl⟩ := h; simp
      · have := hidx e (Multiset.mem_of_le tsub_le_self h); omega
    have heq : R' + created (i + 1) ts = R + (outsT i t + created (i + 1) ts) - t.ins := by
      rw [← tsub_add_eq_add_tsub hinR, hR']; ac_rfl
    have hnd' : ((R' + created (i + 1) ts).map Prod.fst).Nodup := by
      rw [heq]; exact nodup_keys_le tsub_le_self hnd
    have hle' : spent ts ≤ R' + created (i + 1) ts := by
      rw [heq]
      exact (le_tsub_iff_left (le_trans hinR (Multiset.le_add_right _ _))).mpr hle
    obtain ⟨m', h', hr'⟩ := run_rep ts (i + 1) m2 R' hr2 hidx' hord' hnd' hle'
    refine ⟨m', ?_, ?_⟩
    · simp [run, applyTx, h1, h2, h']
    · rw [heq] at hr'
      simp only [created, spent]
      rw [tsub_add_eq_tsub_tsub]; exact hr'

/-- **The multiset argument is sound.** Over transactions `0, 1, …`: if every claimed creation index is
earlier, the created tuples' keys are distinct, and `created = spent + final`, then Core's sequential
update from the empty view succeeds (every input finds exactly the coin it claims) and ends holding
exactly `final`. -/
theorem run_of_balance (ts : List (Tx K V)) (fin : Multiset (Ev K V)) (hord : Ordered 0 ts)
    (hnd : ((created 0 ts).map Prod.fst).Nodup) (hbal : created 0 ts = spent ts + fin) :
    ∃ m, run 0 (fun _ => none) ts = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  have hr0 : Rep (fun _ => (none : Option (V × ℕ))) (0 : Multiset (Ev K V)) := by
    refine ⟨by simp, fun k v j => by simp⟩
  obtain ⟨m, hm, hr⟩ := run_rep ts 0 _ 0 hr0 (by simp) hord (by simpa using hnd)
    (by rw [zero_add, hbal]; exact Multiset.le_add_right _ _)
  refine ⟨m, hm, fun k v j => ?_⟩
  rw [hr.2, zero_add, hbal, add_tsub_cancel_left]

end StarkedAir.Spec.Utxo
