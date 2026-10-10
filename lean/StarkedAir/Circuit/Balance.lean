/-
**The LogUp balance check, Lean-first (VERIFIER-LEAN step 3a).** In `verifyPlain`
(`src/recursion/plain_verifier.zig`), after drawing the lookup elements `(z, α)`, the circuit checks that
the components' claimed sums and the public entries' fractions add to zero:
`total = Σ claimed + Σₑ multₑ · 1/(fingerprint(eₑ) − z)`, then `total = 0`.

`balanceProg` emits those builder calls in order; `balance_sound`: if its ops hold, the sum is zero in
QM31, each public entry's denominator being nonzero (the `inv` op proves it).
-/
import StarkedAir.Circuit.CompositionLogUp

namespace StarkedAir.Circuit.Composition

open StarkedAir StarkedAir.Circuit
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

variable {ρ : ℕ → Q}

/-- A public entry: relation, value registers, multiplicity (a canonical M31). -/
structure ExtE where
  rel : ℕ
  vals : List ℕ
  mult : ℕ

/-- One entry's ops from `n`: its denominator, the multiplicity constant, the inverse, the product, and
the sum into `acc`. -/
def entryOps (n acc z alpha : ℕ) (e : ExtE) : Out ℕ :=
  let d := denOps n e.rel z alpha e.vals
  let m := d.next
  ⟨d.ops ++ [.const m e.mult 0 0 0, .inv (m + 1) d.res, .mul (m + 2) m (m + 1), .add (m + 3) acc (m + 2)], m + 3, m + 4⟩

/-- The balance program: `total ← 0`, plus each claimed sum, plus each entry's fraction, then `total = 0`. -/
def balanceProg (n : ℕ) (claimed : List ℕ) (ext : List ExtE) (z alpha : ℕ) : List Op :=
  let sums := (List.range claimed.length).map fun k => Op.add (n + 1 + k) (if k = 0 then n else n + k) (claimed.getD k 0)
  let t1 := if claimed.length = 0 then n else n + claimed.length
  let ents := ext.foldl (fun (acc : List Op × ℕ × ℕ) e =>
    let o := entryOps acc.2.2 acc.2.1 z alpha e; (acc.1 ++ o.ops, o.res, o.next)) ([], t1, n + 1 + claimed.length)
  [.zero n] ++ sums ++ ents.1 ++ [.zero ents.2.2, .eq ents.2.1 ents.2.2]

/-- The entries' fold. -/
def entFold (z alpha : ℕ) (ext : List ExtE) (s : List Op × ℕ × ℕ) : List Op × ℕ × ℕ :=
  ext.foldl (fun (acc : List Op × ℕ × ℕ) e => let o := entryOps acc.2.2 acc.2.1 z alpha e; (acc.1 ++ o.ops, o.res, o.next)) s

/-- An entry's fraction over QM31. -/
noncomputable def entryFrac (ρ : ℕ → Q) (z alpha : ℕ) (e : ExtE) : QM :=
  emb (e.mult : F) * (fingerprint (val ρ alpha) (emb (e.rel : F)) (e.vals.map (val ρ)) - val ρ z)⁻¹

theorem entry_sound {n acc z alpha : ℕ} {e : ExtE} (h : Holds ρ (entryOps n acc z alpha e).ops) :
    val ρ (entryOps n acc z alpha e).res = val ρ acc + entryFrac ρ z alpha e ∧
      fingerprint (val ρ alpha) (emb (e.rel : F)) (e.vals.map (val ρ)) - val ρ z ≠ 0 := by
  simp only [entryOps] at h ⊢
  rw [holds_append] at h
  obtain ⟨hd, ht⟩ := h
  have hden := den_sound hd
  have c1 := ht (.const (denOps n e.rel z alpha e.vals).next e.mult 0 0 0) (by simp)
  have i1 := ht (.inv ((denOps n e.rel z alpha e.vals).next + 1) (denOps n e.rel z alpha e.vals).res) (by simp)
  have m1 := ht (.mul ((denOps n e.rel z alpha e.vals).next + 2) (denOps n e.rel z alpha e.vals).next
    ((denOps n e.rel z alpha e.vals).next + 1)) (by simp)
  have a1 := ht (.add ((denOps n e.rel z alpha e.vals).next + 3) acc ((denOps n e.rel z alpha e.vals).next + 2)) (by simp)
  simp only [Op.holds] at c1 i1 m1 a1
  have hinv : val ρ (denOps n e.rel z alpha e.vals).res * val ρ ((denOps n e.rel z alpha e.vals).next + 1) = 1 := by
    simp only [val]; rw [← toQ_mul, i1, toQ_lit1]
  have hne : val ρ (denOps n e.rel z alpha e.vals).res ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hinv; exact zero_ne_one hinv
  rw [hden] at hinv hne
  refine ⟨?_, hne⟩
  simp only [val] at hinv ⊢
  rw [a1, toQ_add, m1, toQ_mul, c1, toQ_lit, entryFrac, val]
  congr 2
  exact (eq_inv_of_mul_eq_one_right hinv)

theorem entFold_prefix {z alpha : ℕ} : ∀ (ext : List ExtE) (t : List Op × ℕ × ℕ), ∃ rest, (entFold z alpha ext t).1 = t.1 ++ rest
  | [], t => ⟨[], by simp [entFold]⟩
  | e :: es, t => by
    obtain ⟨r, hr⟩ := entFold_prefix (z := z) (alpha := alpha) es (t.1 ++ (entryOps t.2.2 t.2.1 z alpha e).ops,
      (entryOps t.2.2 t.2.1 z alpha e).res, (entryOps t.2.2 t.2.1 z alpha e).next)
    exact ⟨(entryOps t.2.2 t.2.1 z alpha e).ops ++ r, by simp only [entFold, List.foldl_cons] at hr ⊢; rw [hr, List.append_assoc]⟩

theorem entFold_sound {z alpha : ℕ} : ∀ (ext : List ExtE) (s : List Op × ℕ × ℕ), Holds ρ (entFold z alpha ext s).1 →
    val ρ (entFold z alpha ext s).2.1 = val ρ s.2.1 + (ext.map (entryFrac ρ z alpha)).sum
  | [], s, _ => by simp [entFold]
  | e :: es, s, h => by
    set o := entryOps s.2.2 s.2.1 z alpha e with ho
    have eq1 : entFold z alpha (e :: es) s = entFold z alpha es (s.1 ++ o.ops, o.res, o.next) := by simp [entFold, ho]
    rw [eq1] at h ⊢
    obtain ⟨rest, hr⟩ := entFold_prefix (z := z) (alpha := alpha) es (s.1 ++ o.ops, o.res, o.next)
    have hops : Holds ρ o.ops := by
      rw [hr] at h; simp only at h; rw [holds_append, holds_append] at h; exact h.1.2
    rw [entFold_sound es _ h]
    simp only
    rw [(entry_sound hops).1, List.map_cons, List.sum_cons, add_assoc]

theorem balance_eq (n : ℕ) (claimed : List ℕ) (ext : List ExtE) (z alpha : ℕ) :
    balanceProg n claimed ext z alpha =
      [.zero n] ++ (List.range claimed.length).map (fun k => Op.add (n + 1 + k) (if k = 0 then n else n + k) (claimed.getD k 0)) ++
      (entFold z alpha ext ([], if claimed.length = 0 then n else n + claimed.length, n + 1 + claimed.length)).1 ++
      [.zero (entFold z alpha ext ([], if claimed.length = 0 then n else n + claimed.length, n + 1 + claimed.length)).2.2,
       .eq (entFold z alpha ext ([], if claimed.length = 0 then n else n + claimed.length, n + 1 + claimed.length)).2.1
         (entFold z alpha ext ([], if claimed.length = 0 then n else n + claimed.length, n + 1 + claimed.length)).2.2] := rfl

/-- **The balance check is sound.** If its ops hold, the claimed sums and the public entries' fractions
add to zero over QM31 (and every entry's denominator is nonzero). -/
theorem balance_sound {n : ℕ} {claimed : List ℕ} {ext : List ExtE} {z alpha : ℕ}
    (h : Holds ρ (balanceProg n claimed ext z alpha)) :
    (claimed.map (val ρ)).sum + (ext.map (entryFrac ρ z alpha)).sum = 0 := by
  rw [balance_eq, holds_append, holds_append, holds_append] at h
  obtain ⟨⟨⟨h0, hs⟩, he⟩, hf⟩ := h
  have hz : val ρ n = 0 := by
    have := h0 (.zero n) (by simp); simp only [Op.holds] at this; rw [val, this, toQ_lit0]
  -- the running sum of the claimed sums
  have run : ∀ k ≤ claimed.length, val ρ (if k = 0 then n else n + k) = ((claimed.take k).map (val ρ)).sum := by
    intro k
    induction k with
    | zero => intro _; simp [hz]
    | succ k ih =>
      intro hk
      have ha := hs (Op.add (n + 1 + k) (if k = 0 then n else n + k) (claimed.getD k 0)) (by
        simp only [List.mem_map, List.mem_range]; exact ⟨k, by omega, rfl⟩)
      simp only [Op.holds] at ha
      rw [if_neg (by omega), show n + (k + 1) = n + 1 + k by omega]
      simp only [val] at ih ⊢
      rw [ha, toQ_add, ih (by omega), List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
        List.map_append, List.sum_append, List.map_singleton, List.sum_singleton, List.getD_eq_getElem _ _ (by omega)]
  have hsum := entFold_sound ext _ he
  simp only at hsum
  have hfin := hf _ (List.Mem.tail _ (List.Mem.head _))
  have hzero := hf _ (List.Mem.head _)
  simp only [Op.holds] at hfin hzero
  have hv : val ρ (entFold z alpha ext ([], if claimed.length = 0 then n else n + claimed.length, n + 1 + claimed.length)).2.1 = 0 := by
    simp only [val]; rw [hfin, hzero, toQ_lit0]
  rw [hsum, run claimed.length le_rfl, List.take_of_length_le le_rfl] at hv
  exact hv

end StarkedAir.Circuit.Composition

namespace StarkedAir.Circuit.Composition

/-- The exported balance program: hook 0 binds the claimed sums, the entries' values, `z`, `α`. -/
def balanceJson (nClaimed : ℕ) (entries : List (ℕ × ℕ × ℕ)) : String :=
  let nVals := (entries.map fun e => e.2.1).sum
  let nIn := nClaimed + nVals + 2
  let z := nClaimed + nVals
  let alpha := z + 1
  let ext := (entries.foldl (fun (acc : List ExtE × ℕ) e =>
    (acc.1 ++ [⟨e.1, (List.range e.2.1).map (acc.2 + ·), e.2.2⟩], acc.2 + e.2.1)) ([], nClaimed)).1
  let ops := [Op.hook 0 [] (List.range nIn)] ++ balanceProg nIn (List.range nClaimed) ext z alpha
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[]}"

end StarkedAir.Circuit.Composition
