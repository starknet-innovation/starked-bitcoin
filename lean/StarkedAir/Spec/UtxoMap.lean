/-
**Runs survive a map of the values (M3b).** The epoch argument runs over the circuit's values (a coin's
code and serialized output); Core's view holds decoded coins. A successful run maps to a successful run
over any map of the values: each spend's check is an equality, which a map preserves, and the keys and
creation indices are unchanged. No injectivity is needed for this direction.

- `run_map`: `run i m ts = some m'` gives `run i (vmap g m) (ts.map (tmap g)) = some (vmap g m')`.
-/
import StarkedAir.Spec.UtxoMultiset

namespace StarkedAir.Spec.Utxo

variable {K V W : Type} [DecidableEq K] [DecidableEq V] [DecidableEq W] (g : V → W)

def vmap (m : View K V) : View K W := fun k => (m k).map fun p => (g p.1, p.2)

def emap (e : Ev K V) : Ev K W := (e.1, g e.2.1, e.2.2)

def tmap (t : Tx K V) : Tx K W := ⟨t.ins.map (emap g), t.outs.map fun o => (o.1, g o.2)⟩

theorem vmap_update (m : View K V) (k : K) (o : Option (V × ℕ)) :
    vmap g (Function.update m k o) = Function.update (vmap g m) k (o.map fun p => (g p.1, p.2)) := by
  funext j; by_cases h : j = k
  · subst h; simp [vmap]
  · simp [vmap, Function.update_of_ne h]

theorem spendOne_map {m m' : View K V} {e : Ev K V} (h : spendOne m e = some m') :
    spendOne (vmap g m) (emap g e) = some (vmap g m') := by
  unfold spendOne at h ⊢
  split_ifs at h with he
  obtain rfl := Option.some.inj h.symm
  have : vmap g m (emap g e).1 = some ((emap g e).2.1, (emap g e).2.2) := by simp [vmap, emap, he]
  rw [if_pos this, vmap_update]; rfl

theorem addOne_map (i : ℕ) {m m' : View K V} {o : K × V} (h : addOne i m o = some m') :
    addOne i (vmap g m) (o.1, g o.2) = some (vmap g m') := by
  unfold addOne at h ⊢
  split_ifs at h with he
  obtain rfl := Option.some.inj h.symm
  have : vmap g m o.1 = none := by simp [vmap, he]
  rw [if_pos this, vmap_update]; rfl

theorem spends_map : ∀ (es : List (Ev K V)) (m m' : View K V), es.foldlM spendOne m = some m' →
    (es.map (emap g)).foldlM spendOne (vmap g m) = some (vmap g m')
  | [], m, m', h => by simp at h; subst h; rfl
  | e :: es, m, m', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.map_cons, List.foldlM_cons, spendOne_map g h1]
    exact spends_map es m1 m' h2

theorem adds_map (i : ℕ) : ∀ (os : List (K × V)) (m m' : View K V), os.foldlM (addOne i) m = some m' →
    (os.map fun o => (o.1, g o.2)).foldlM (addOne i) (vmap g m) = some (vmap g m')
  | [], m, m', h => by simp at h; subst h; rfl
  | o :: os, m, m', h => by
    simp only [List.foldlM_cons] at h
    obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    simp only [List.map_cons, List.foldlM_cons, addOne_map g i h1]
    exact adds_map i os m1 m' h2

/-- **A run maps to a run.** -/
theorem run_map : ∀ (i : ℕ) (m m' : View K V) (ts : List (Tx K V)), run i m ts = some m' →
    run i (vmap g m) (ts.map (tmap g)) = some (vmap g m')
  | _, m, m', [], h => by simp [run] at h; subst h; rfl
  | i, m, m', t :: ts, h => by
    simp only [run] at h
    obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
    unfold applyTx at h1
    obtain ⟨m0, h0, h01⟩ := Option.bind_eq_some_iff.mp h1
    have ha : applyTx i (vmap g m) (tmap g t) = some (vmap g m1) := by
      unfold applyTx tmap
      rw [spends_map g _ _ _ h0]
      exact adds_map g i _ _ _ h01
    simp only [List.map_cons, run, ha]
    exact run_map (i + 1) m1 m' ts h2

end StarkedAir.Spec.Utxo
