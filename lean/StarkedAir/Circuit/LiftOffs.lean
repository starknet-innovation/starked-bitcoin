/-
**`mainOffs` is the verifier's offset set.** `PeriodicCols` decides which main columns are two-sample
from `Lift.mainOffs`, read off the component's expressions. The verifier's layout (`compShape`) reads
them off the emitted DAG instead (`Composition.mainOffsets (pNodes c)`). This file proves the two agree:
- `mem_mainOffsets_iff`: same members, for every column;
- `mainOffsets_perm`: the lists are permutations of each other, so they have the same length, and a
  column is two-sample for `PeriodicCols` exactly when the verifier samples it at two offsets
  (`mainOffs_length_eq_shape`).

The proof tracks, through the hash-consing emitter, which `(column, offset)` leaves the node array
holds: emitting `e` adds exactly `e`'s main reads (`emitN_cols`), using the invariant that every
shared key's reads are already emitted (`KeyOK`).
-/
import StarkedAir.Circuit.Lift

namespace StarkedAir.Circuit.Lift

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.Composition

/-- The node array holds the main leaf `(j, off)`. -/
def HasCol (out : Array Node) (j : ℕ) (off : ℤ) : Prop := Node.col .main j off ∈ out.toList

/-- Every shared key's main reads are already emitted. -/
def KeyOK (s : DagState) : Prop :=
  ∀ e id, s.ids[e]? = some id → ∀ p ∈ mainReads e, HasCol s.out p.1 p.2

theorem hasCol_push {out : Array Node} {nd : Node} {j : ℕ} {off : ℤ} :
    HasCol (out.push nd) j off ↔ HasCol out j off ∨ nd = .col .main j off := by
  unfold HasCol
  rw [Array.toList_push, List.mem_append, List.mem_singleton, eq_comm (a := Node.col .main j off)]

theorem keyOK_push {s : DagState} (hs : KeyOK s) (e : Expr) (nd : Node)
    (hreads : ∀ p ∈ mainReads e, HasCol (s.out.push nd) p.1 p.2) :
    KeyOK { ids := s.ids.insert e s.out.size, out := s.out.push nd } := by
  intro e' id h p hp
  simp only [Std.HashMap.getElem?_insert] at h
  split at h
  · rename_i heq
    have : e = e' := by simpa using heq
    subst this
    exact hreads p hp
  · exact hasCol_push.mpr (Or.inl (hs e' id h p hp))

/-- **Emitting `e` adds exactly its main reads** to the node array. -/
theorem emitN_cols (e : Expr) : ∀ s, KeyOK s →
    KeyOK (emitN e s).2 ∧
      ∀ j off, HasCol (emitN e s).2.out j off ↔ HasCol s.out j off ∨ (j, off) ∈ mainReads e := by
  induction e with
  | col t i o =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · refine ⟨keyOK_push hs _ _ fun p hp => ?_, fun j off => ?_⟩
      · cases t <;> simp [mainReads] at hp
        subst hp; exact hasCol_push.mpr (Or.inr rfl)
      · rw [hasCol_push]
        cases t <;> simp [mainReads]
        aesop
  | const v =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · exact ⟨keyOK_push hs _ _ fun p hp => by simp [mainReads] at hp,
        fun j off => by rw [hasCol_push]; simp [mainReads]⟩
  | pub i =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · exact ⟨keyOK_push hs _ _ fun p hp => by simp [mainReads] at hp,
        fun j off => by rw [hasCol_push]; simp [mainReads]⟩
  | neg a iha =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · obtain ⟨k1, c1⟩ := iha s hs
      refine ⟨keyOK_push k1 _ _ fun p hp => ?_, fun j off => ?_⟩
      · exact hasCol_push.mpr (Or.inl ((c1 p.1 p.2).mpr (Or.inr (by simpa [mainReads] using hp))))
      · rw [hasCol_push, c1]; simp [mainReads]
  | add a b iha ihb =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · obtain ⟨k1, c1⟩ := iha s hs
      obtain ⟨k2, c2⟩ := ihb _ k1
      refine ⟨keyOK_push k2 _ _ fun p hp => ?_, fun j off => ?_⟩
      · refine hasCol_push.mpr (Or.inl ((c2 p.1 p.2).mpr ?_))
        rcases List.mem_append.mp (by simpa [mainReads] using hp) with h | h
        · exact Or.inl ((c1 p.1 p.2).mpr (Or.inr h))
        · exact Or.inr h
      · rw [hasCol_push, c2, c1]; simp [mainReads, or_assoc]
  | sub a b iha ihb =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · obtain ⟨k1, c1⟩ := iha s hs
      obtain ⟨k2, c2⟩ := ihb _ k1
      refine ⟨keyOK_push k2 _ _ fun p hp => ?_, fun j off => ?_⟩
      · refine hasCol_push.mpr (Or.inl ((c2 p.1 p.2).mpr ?_))
        rcases List.mem_append.mp (by simpa [mainReads] using hp) with h | h
        · exact Or.inl ((c1 p.1 p.2).mpr (Or.inr h))
        · exact Or.inr h
      · rw [hasCol_push, c2, c1]; simp [mainReads, or_assoc]
  | mul a b iha ihb =>
    intro s hs
    unfold emitN
    split
    · rename_i id h
      exact ⟨hs, fun j off => ⟨Or.inl, fun h' => h'.elim (fun x => x) fun hr => hs _ id h _ hr⟩⟩
    · obtain ⟨k1, c1⟩ := iha s hs
      obtain ⟨k2, c2⟩ := ihb _ k1
      refine ⟨keyOK_push k2 _ _ fun p hp => ?_, fun j off => ?_⟩
      · refine hasCol_push.mpr (Or.inl ((c2 p.1 p.2).mpr ?_))
        rcases List.mem_append.mp (by simpa [mainReads] using hp) with h | h
        · exact Or.inl ((c1 p.1 p.2).mpr (Or.inr h))
        · exact Or.inr h
      · rw [hasCol_push, c2, c1]; simp [mainReads, or_assoc]

theorem emitAll_cols : ∀ (es : List Expr) (s : DagState), KeyOK s →
    KeyOK (emitAll es s).2 ∧
      ∀ j off, HasCol (emitAll es s).2.out j off ↔ HasCol s.out j off ∨ ∃ e ∈ es, (j, off) ∈ mainReads e
  | [], s, hs => ⟨hs, fun j off => by simp [emitAll]⟩
  | e :: es, s, hs => by
    obtain ⟨k1, c1⟩ := emitN_cols e s hs
    obtain ⟨k2, c2⟩ := emitAll_cols es _ k1
    refine ⟨k2, fun j off => ?_⟩
    change HasCol (emitAll es (emitN e s).2).2.out j off ↔ _
    rw [c2, c1]
    simp [or_assoc]

/-- The emitted DAG of `c` holds exactly the main leaves its expressions read. -/
theorem hasCol_pNodes (c : Comp) (j : ℕ) (off : ℤ) :
    HasCol (pNodes c) j off ↔ ∃ e ∈ exprs c, (j, off) ∈ mainReads e := by
  have h0 : KeyOK ({} : DagState) := fun e id h => by simp at h
  have := (emitAll_cols (compRoots c) {} h0).2 j off
  simp only [HasCol, List.not_mem_nil, false_or] at this
  simpa [HasCol, pNodes, compDag, exprs, compRoots] using this

theorem mem_mainOffsets_nodes (nodes : Array Node) (j : ℕ) (off : ℤ) :
    off ∈ mainOffsets nodes j ↔ Node.col .main j off ∈ nodes.toList := by
  unfold mainOffsets
  rw [List.mem_mergeSort, List.mem_dedup, List.mem_filterMap]
  constructor
  · rintro ⟨nd, hnd, h⟩
    rcases nd with ⟨_ | _, i, o⟩ | _ | _ | _ | _ | _ | _ <;> simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact hnd
  · intro h
    exact ⟨_, h, by simp⟩

/-- **The verifier's offsets are `mainOffs`**, as sets. -/
theorem mem_mainOffsets_iff (c : Comp) (j : ℕ) (off : ℤ) :
    off ∈ mainOffsets (pNodes c) j ↔ off ∈ mainOffs c j := by
  rw [mem_mainOffsets_nodes]
  have h := hasCol_pNodes c j off
  simp only [HasCol] at h
  rw [h]
  unfold mainOffs
  rw [List.mem_dedup, List.mem_flatMap]
  constructor
  · rintro ⟨e, he, hr⟩; exact ⟨e, he, List.mem_filterMap.mpr ⟨(j, off), hr, by simp⟩⟩
  · rintro ⟨e, he, hr⟩
    obtain ⟨⟨j', o⟩, hp, hs⟩ := List.mem_filterMap.mp hr
    by_cases hj : j' = j
    · subst hj; simp at hs; subst hs; exact ⟨e, he, hp⟩
    · simp [hj] at hs

/-- **…and as lists up to order.** Both are duplicate-free. -/
theorem mainOffsets_perm (c : Comp) (j : ℕ) : (mainOffsets (pNodes c) j).Perm (mainOffs c j) := by
  have n1 : (mainOffsets (pNodes c) j).Nodup := by
    unfold mainOffsets
    exact (List.mergeSort_perm _ _).symm.nodup_iff.mp (List.nodup_dedup _)
  have n2 : (mainOffs c j).Nodup := List.nodup_dedup _
  exact (List.perm_ext_iff_of_nodup n1 n2).mpr fun off => mem_mainOffsets_iff c j off

/-- **Two-sample columns are the verifier's.** For every main column of the layout (`compShape`), the
number of offsets the verifier samples is `(mainOffs c j).length`; in particular `PeriodicCols`
requires periodicity exactly of the columns the verifier samples at two offsets. -/
theorem mainOffs_length_eq_shape (c : Comp) (nPub : ℕ) {j : ℕ} (hj : j < c.air.nMain) :
    ((compShape c nPub).offs.getD j []).length = (mainOffs c j).length := by
  have : (compShape c nPub).offs.getD j [] = mainOffsets (pNodes c) j := by
    simp [compShape, pNodes, hj]
  rw [this]
  exact (mainOffsets_perm c j).length_eq

/-- Every main read of `c` is of a layout column (`j < nMain`). -/
def colsOk (c : Comp) : Bool := (exprs c).all fun e => (mainReads e).all fun p => decide (p.1 < c.air.nMain)

/-- **Every column `PeriodicCols` constrains is in the layout.** With `colsOk`, a column with any
offset is below `nMain`, so `mainOffs_length_eq_shape` covers it. -/
theorem lt_nMain_of_mem_mainOffs {c : Comp} (h : colsOk c = true) {j : ℕ} {off : ℤ} (hoff : off ∈ mainOffs c j) :
    j < c.air.nMain := by
  unfold mainOffs at hoff
  rw [List.mem_dedup, List.mem_flatMap] at hoff
  obtain ⟨e, he, hp⟩ := hoff
  obtain ⟨p, hp, hpe⟩ := List.mem_filterMap.mp hp
  have hpj : p.1 = j := by by_contra hne; simp [hne] at hpe
  have := of_decide_eq_true (List.all_eq_true.mp (List.all_eq_true.mp h e he) p hp)
  rwa [hpj] at this

end StarkedAir.Circuit.Lift
