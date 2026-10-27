/-
**A segment's pass, in one go.** Folding `step` over a nonempty segment: the count grows by its length,
both hashes are fed its bytes at once (`b2Feed_append`, `shaFeed_append`), the sums, amount and highest
height grow by its records', the last record is its last, and the checks hold iff they held before, every
record is well formed and the records are sorted after the carried last one (`chainOk`).
-/
import StarkedAir.SetPass.B2Spec
import StarkedAir.SetPass.ShaSpec

namespace StarkedAir.Spec.SetFile

open StarkedAir.Spec.Block StarkedAir.Spec.CoinEpoch

/-- Absorbing in two steps is absorbing the concatenation. -/
theorem shaAbsorb_append (H : Sha256.State) (b : Bytes) :
    ∀ y, shaAbsorb H (b ++ y) = shaAbsorb (shaAbsorb H b).1 ((shaAbsorb H b).2 ++ y) := by
  induction H, b using shaAbsorb.induct with
  | case1 H b hb ih =>
    intro y
    have hl : 64 ≤ (b ++ y).length := by rw [List.length_append]; omega
    rw [shaAbsorb_pos hl, shaAbsorb_pos hb, List.take_append_of_le_length hb, List.drop_append_of_le_length hb, ih y]
  | case2 H b hb => intro y; rw [shaAbsorb_neg hb]

/-- **Feeding is associative.** -/
theorem shaFeed_append (s : Sha) (x y : Bytes) : shaFeed (shaFeed s x) y = shaFeed s (x ++ y) := by
  unfold shaFeed
  simp only [List.length_append, Nat.add_assoc, ← List.append_assoc]
  rw [← shaAbsorb_append]

/-- The records are sorted, after the carried last one. -/
def chainOk (last : Option CEv) : List CEv → Bool
  | [] => true
  | e :: es => sortedAfter last e && chainOk (some e) es

theorem chainOk_none : ∀ (es : List CEv), chainOk none es = true ↔ Sorted es
  | [] => by simp [chainOk, Sorted]
  | e :: es => by
    simp only [chainOk, sortedAfter, Bool.true_and]
    induction es generalizing e with
    | nil => simp [chainOk, Sorted]
    | cons e' es ih =>
      simp only [chainOk, sortedAfter, Bool.and_eq_true, Sorted, List.isChain_cons_cons]
      have := ih e'
      simp only [chainOk, Bool.and_eq_true, Sorted] at this
      rw [this]

theorem chainOk_some (p : CEv) (es : List CEv) :
    chainOk (some p) es = true ↔ Sorted (p :: es) := by
  rw [← chainOk_none]; simp [chainOk, sortedAfter]

theorem zipWith_zipWith {α β : Type} (g h : α → β → α) :
    ∀ (l : List α) (fr : List β), List.zipWith g (List.zipWith h l fr) fr = List.zipWith (fun a f => g (h a f) f) l fr
  | [], _ => rfl
  | _ :: _, [] => rfl
  | a :: l, f :: fr => by simp [zipWith_zipWith g h l fr]

variable {𝕂 : Type} [AddCommMonoid 𝕂]

/-- **A nonempty segment's pass.** -/
theorem fold_step (fr : List (CEv → 𝕂)) : ∀ (seg : List CEv) (s : St 𝕂), seg ≠ [] →
    (seg.foldl (step fr) s).n = s.n ∧ (seg.foldl (step fr) s).i = s.i + seg.length ∧
    (seg.foldl (step fr) s).b2 = b2Feed s.b2 (seg.flatMap encRec) ∧
    (seg.foldl (step fr) s).sha = shaFeed s.sha (seg.flatMap txOutSer) ∧
    (seg.foldl (step fr) s).sums = List.zipWith (fun a f => a + (seg.map f).sum) s.sums fr ∧
    (seg.foldl (step fr) s).amount = s.amount + (seg.map amountOf).sum ∧
    (seg.foldl (step fr) s).maxHeight = (seg.map fun e => code e / 2).foldl max s.maxHeight ∧
    (seg.foldl (step fr) s).last = seg.getLast? ∧
    ((seg.foldl (step fr) s).ok = true ↔ s.ok = true ∧ (∀ e ∈ seg, RecOk e) ∧ chainOk s.last seg = true)
  | [], _, h => absurd rfl h
  | [e], s, _ => by
    refine ⟨rfl, rfl, by simp [step], by simp [step], ?_, by simp [step], by simp [step], by simp [step], ?_⟩
    · simp only [List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
    · simp [step, chainOk, Bool.and_assoc]
  | e :: e' :: es, s, _ => by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := fold_step fr (e' :: es) (step fr s e) (by simp)
    rw [List.foldl_cons]
    refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h2]; simp [step]; ring
    · rw [h3]; simp only [step]; rw [b2Feed_append]; simp
    · rw [h4]; simp only [step]; rw [shaFeed_append]; simp
    · rw [h5]; simp only [step]; rw [zipWith_zipWith]
      congr 1; funext a f; simp [add_assoc]
    · rw [h6]; simp [step, add_assoc]
    · rw [h7]; simp [step]
    · rw [h8]; simp
    · rw [h9]
      simp only [step, chainOk, Bool.and_eq_true, decide_eq_true_eq, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩
        exact ⟨h1, ⟨h2, h4, h5⟩, h3, h6⟩
      · rintro ⟨h1, ⟨h2, h4, h5⟩, h3, h6⟩
        exact ⟨⟨⟨h1, h2⟩, h3⟩, ⟨h4, h5⟩, h6⟩

end StarkedAir.Spec.SetFile
