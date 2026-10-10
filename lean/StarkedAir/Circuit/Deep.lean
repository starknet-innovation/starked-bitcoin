/-
**The DEEP response list, Lean-first (VERIFIER-LEAN step 4b).** After the OODS samples are mixed into
the channel (`verifyPlain`, `src/recursion/plain_verifier.zig`), the DEEP quotients take a list of
responses: (tree, column, point, value). Each value must be a sample that was mixed, and its point must
be the OODS point shifted by that sample's mask offset; otherwise the quotients would bind the
committed columns to values the transcript never saw.

`samples` labels the mixed values in mixing order: preprocessed (offset 0), main (column by column, its
sorted offsets), interaction (a part's last four columns at `−1, 0`, the others at `0`), composition.
`deepList` is the response table in stwo's order (tree, column, mask; a two-sample column is preceded by
its periodicity sample, the last one). Each entry names its value by index into the mixed list, so the
circuit uses the very variables that were mixed.

- `deep_sound`: every response's index is in range, and its label is the response's
  (tree, column, offset).
- `deep_complete`: every mixed sample is used by some response.

The order itself is stwo's (checked by verifying real proofs).
-/
import StarkedAir.Circuit.CompositionLogUp

namespace StarkedAir.Circuit.Deep

open StarkedAir.Circuit.Composition (PartShape)

/-- A sample's label: tree (0 pre, 1 main, 2 interaction, 3 composition), global column, offset. -/
abbrev Label := ℕ × ℕ × ℤ

/-- A response: its label and the index of its value in the mixed list. -/
structure Resp where
  tree : ℕ
  col : ℕ
  off : ℤ
  idx : ℕ
deriving DecidableEq

def Resp.label (r : Resp) : Label := (r.tree, r.col, r.off)

/-- The interaction offsets of column `c` of a part with `n` interaction columns. -/
def interOffs (n c : ℕ) : List ℤ := if c + 4 ≥ n then [-1, 0] else [0]

/-- Per tree, its columns' offsets, in order (global across parts). -/
def treeCols (shapes : List PartShape) (anyLookups : Bool) : List (ℕ × List (List ℤ)) :=
  [(0, (List.range (shapes.map (·.nPre)).sum).map fun _ => [0]),
   (1, shapes.flatMap (·.offs)),
   (2, if anyLookups then shapes.flatMap (fun s => (List.range s.nInter).map (interOffs s.nInter)) else []),
   (3, (List.range 8).map fun _ => [0])]

/-- The labels of one tree's samples. -/
def treeLabels (t : ℕ) (cols : List (List ℤ)) : List Label :=
  (cols.zipIdx).flatMap fun (offs, c) => offs.map fun o => (t, c, o)

/-- The mixed samples, labelled, in mixing order. -/
def samples (tc : List (ℕ × List (List ℤ))) : List Label := tc.flatMap fun (t, cols) => treeLabels t cols

/-- One column's responses, its samples starting at index `base`: the periodicity sample first for a
two-sample column. -/
def colResps (t c base : ℕ) (offs : List ℤ) : List Resp :=
  let rs := (offs.zipIdx).map fun (o, k) => (⟨t, c, o, base + k⟩ : Resp)
  if offs.length = 2 then rs.getLast?.toList ++ rs else rs

/-- One tree's responses, its samples starting at `base`. -/
def treeResps (t : ℕ) : List (List ℤ) → ℕ → ℕ → List Resp
  | [], _, _ => []
  | offs :: cols, c, base => colResps t c base offs ++ treeResps t cols (c + 1) (base + offs.length)

def deepFrom : List (ℕ × List (List ℤ)) → ℕ → List Resp
  | [], _ => []
  | (t, cols) :: rest, base => treeResps t cols 0 base ++ deepFrom rest (base + (cols.map List.length).sum)

/-- The response table. -/
def deepList (tc : List (ℕ × List (List ℤ))) : List Resp := deepFrom tc 0

/-! ### Soundness: indices point at matching labels -/

theorem treeLabels_cons (t : ℕ) (offs : List ℤ) (cols : List (List ℤ)) (c : ℕ) :
    ((offs :: cols).zipIdx c).flatMap (fun (p : List ℤ × ℕ) => p.1.map fun o => ((t, p.2, o) : Label)) =
      offs.map (fun o => ((t, c, o) : Label)) ++
        (cols.zipIdx (c + 1)).flatMap (fun (p : List ℤ × ℕ) => p.1.map fun o => ((t, p.2, o) : Label)) := by
  simp [List.zipIdx_cons]

/-- The labels of a tree's columns from column `c`. -/
def labelsFrom (t : ℕ) (cols : List (List ℤ)) (c : ℕ) : List Label :=
  (cols.zipIdx c).flatMap fun (p : List ℤ × ℕ) => p.1.map fun o => ((t, p.2, o) : Label)

theorem labelsFrom_length (t : ℕ) : ∀ (cols : List (List ℤ)) (c : ℕ),
    (labelsFrom t cols c).length = (cols.map List.length).sum
  | [], _ => by simp [labelsFrom]
  | offs :: cols, c => by
    have := labelsFrom_length t cols (c + 1)
    simp only [labelsFrom] at this ⊢
    rw [treeLabels_cons, List.length_append, this]; simp

theorem colResps_sound {t c base : ℕ} {offs : List ℤ} {L : List Label}
    (hL : ∀ k (h : k < offs.length), L[base + k]? = some (t, c, offs[k])) :
    ∀ r ∈ colResps t c base offs, L[r.idx]? = some r.label := by
  have hrs : ∀ r ∈ (offs.zipIdx).map (fun (p : ℤ × ℕ) => (⟨t, c, p.1, base + p.2⟩ : Resp)),
      L[r.idx]? = some r.label := by
    intro r hr
    obtain ⟨⟨o, k⟩, hm, rfl⟩ := List.mem_map.mp hr
    have hk := List.mem_zipIdx hm
    simp only [Resp.label]
    rw [hL k (by simpa using hk.2.1)]
    obtain ⟨-, -, ho⟩ := hk
    simp [ho]
  intro r hr
  simp only [colResps] at hr
  split at hr
  · rcases List.mem_append.mp hr with h | h
    · exact hrs r (List.mem_of_mem_getLast? (by simpa using h))
    · exact hrs r h
  · exact hrs r hr

theorem treeResps_sound (t : ℕ) {L : List Label} : ∀ (cols : List (List ℤ)) (c base : ℕ),
    (∀ i (h : i < (labelsFrom t cols c).length), L[base + i]? = some (labelsFrom t cols c)[i]) →
    ∀ r ∈ treeResps t cols c base, L[r.idx]? = some r.label
  | [], _, _, _ => by simp [treeResps]
  | offs :: cols, c, base, hL => by
    have hsplit : labelsFrom t (offs :: cols) c = offs.map (fun o => ((t, c, o) : Label)) ++ labelsFrom t cols (c + 1) := by
      simp only [labelsFrom]; exact treeLabels_cons t offs cols c
    intro r hr
    simp only [treeResps] at hr
    rcases List.mem_append.mp hr with h | h
    · refine colResps_sound (fun k hk => ?_) r h
      have hi : k < (labelsFrom t (offs :: cols) c).length := by rw [hsplit]; simp; omega
      rw [hL k hi]; congr 1
      simp only [hsplit]
      rw [List.getElem_append_left (by simpa using hk), List.getElem_map]
    · refine treeResps_sound t cols (c + 1) (base + offs.length) (fun i hi => ?_) r h
      have hi' : offs.length + i < (labelsFrom t (offs :: cols) c).length := by rw [hsplit]; simp; omega
      rw [Nat.add_assoc, hL _ hi']; congr 1
      simp only [hsplit]
      rw [List.getElem_append_right (by simp)]
      simp

theorem samples_cons (t : ℕ) (cols : List (List ℤ)) (rest : List (ℕ × List (List ℤ))) :
    samples ((t, cols) :: rest) = labelsFrom t cols 0 ++ samples rest := by
  simp [samples, treeLabels, labelsFrom]

theorem deepFrom_sound {L : List Label} : ∀ (tc : List (ℕ × List (List ℤ))) (base : ℕ),
    (∀ i (h : i < (samples tc).length), L[base + i]? = some (samples tc)[i]) →
    ∀ r ∈ deepFrom tc base, L[r.idx]? = some r.label
  | [], _, _ => by simp [deepFrom]
  | (t, cols) :: rest, base, hL => by
    intro r hr
    simp only [deepFrom] at hr
    rcases List.mem_append.mp hr with h | h
    · refine treeResps_sound t cols 0 base (fun i hi => ?_) r h
      have hi' : i < (samples ((t, cols) :: rest)).length := by rw [samples_cons]; simp; omega
      rw [hL i hi']; congr 1
      simp only [samples_cons]; rw [List.getElem_append_left hi]
    · refine deepFrom_sound rest _ (fun i hi => ?_) r h
      have hlen := labelsFrom_length t cols 0
      have hi' : (cols.map List.length).sum + i < (samples ((t, cols) :: rest)).length := by
        rw [samples_cons]; simp only [List.length_append]; omega
      rw [Nat.add_assoc, hL _ hi']; congr 1
      simp only [samples_cons]
      rw [List.getElem_append_right (by omega)]
      congr 1; omega

/-- **The responses are sound.** Each response's value is the mixed sample with the response's label:
same tree, column and offset (so its point is the OODS point shifted by that offset). -/
theorem deep_sound (tc : List (ℕ × List (List ℤ))) :
    ∀ r ∈ deepList tc, (samples tc)[r.idx]? = some r.label :=
  deepFrom_sound tc 0 (fun i h => by simp [List.getElem?_eq_getElem h])

/-! ### Completeness: every mixed sample is used -/

theorem colResps_complete {t c base : ℕ} {offs : List ℤ} :
    ∀ k < offs.length, ∃ r ∈ colResps t c base offs, r.idx = base + k ∧ r.label = (t, c, offs[k]!) := by
  intro k hk
  have hm : (⟨t, c, offs[k], base + k⟩ : Resp) ∈ (offs.zipIdx).map (fun (p : ℤ × ℕ) => (⟨t, c, p.1, base + p.2⟩ : Resp)) :=
    List.mem_map.mpr ⟨(offs[k], k), List.mem_zipIdx_iff_getElem?.mpr (by simp [List.getElem?_eq_getElem hk]), rfl⟩
  refine ⟨⟨t, c, offs[k], base + k⟩, ?_, rfl, by simp [Resp.label, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hk]⟩
  simp only [colResps]
  split
  · exact List.mem_append_right _ hm
  · exact hm

theorem treeResps_complete (t : ℕ) : ∀ (cols : List (List ℤ)) (c base : ℕ),
    ∀ i < (labelsFrom t cols c).length, ∃ r ∈ treeResps t cols c base, r.idx = base + i
  | [], _, _ => by simp [labelsFrom]
  | offs :: cols, c, base => by
    intro i hi
    have hlen : (labelsFrom t (offs :: cols) c).length = offs.length + (labelsFrom t cols (c + 1)).length := by
      simp only [labelsFrom]; rw [treeLabels_cons]; simp
    simp only [treeResps]
    by_cases hk : i < offs.length
    · obtain ⟨r, hr, hi, -⟩ := colResps_complete (t := t) (c := c) (base := base) i hk
      exact ⟨r, List.mem_append_left _ hr, hi⟩
    · obtain ⟨r, hr, hi⟩ := treeResps_complete t cols (c + 1) (base + offs.length) (i - offs.length) (by omega)
      exact ⟨r, List.mem_append_right _ hr, by omega⟩

theorem deepFrom_complete : ∀ (tc : List (ℕ × List (List ℤ))) (base : ℕ),
    ∀ i < (samples tc).length, ∃ r ∈ deepFrom tc base, r.idx = base + i
  | [], _ => by simp [samples]
  | (t, cols) :: rest, base => by
    intro i hi
    rw [samples_cons, List.length_append] at hi
    simp only [deepFrom]
    by_cases hk : i < (labelsFrom t cols 0).length
    · obtain ⟨r, hr, h⟩ := treeResps_complete t cols 0 base i hk
      exact ⟨r, List.mem_append_left _ hr, h⟩
    · have hlen := labelsFrom_length t cols 0
      obtain ⟨r, hr, h⟩ := deepFrom_complete rest (base + (cols.map List.length).sum) (i - (cols.map List.length).sum) (by omega)
      exact ⟨r, List.mem_append_right _ hr, by omega⟩

/-- **The responses are complete.** Every mixed sample is some response's value. -/
theorem deep_complete (tc : List (ℕ × List (List ℤ))) :
    ∀ i < (samples tc).length, ∃ r ∈ deepList tc, r.idx = i := by
  intro i hi
  obtain ⟨r, hr, h⟩ := deepFrom_complete tc 0 i hi
  exact ⟨r, hr, by omega⟩

/-! ### Export -/

def deepJson (shapes : List PartShape) : String :=
  let tc := treeCols shapes (shapes.any (·.lookups))
  let rs := (deepList tc).map fun r => s!"[{r.tree},{r.col},{r.off},{r.idx}]"
  s!"\{\"schema\":\"starked-deep-v1\",\"n_samples\":{(samples tc).length},\"responses\":[{",".intercalate rs}]}"

end StarkedAir.Circuit.Deep
