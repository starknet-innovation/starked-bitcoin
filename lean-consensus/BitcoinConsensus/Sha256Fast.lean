/-
**Fast SHA-256 compression, proven equal to the reference.** `schedule` (Spec/Sha256.lean) is
written for proofs and recomputes earlier words, which is exponential when executed. Here the
schedule is built once as a list, and `compress_eq_fast` proves the result equal; `@[csimp]`
makes compiled and interpreted code use `compressFast` wherever `compress` is called, so the
specification is unchanged and execution is linear.
-/
import BitcoinConsensus.Sha256

namespace BitcoinConsensus.Sha256

/-- Schedule words `0 .. 16 + k - 1`, built front to back. -/
def schedList (M : ℕ → Word) : ℕ → List Word
  | 0 => (List.range 16).map M
  | k + 1 =>
    let w := schedList M k
    let t := 16 + k
    w ++ [ssig1 (w.getD (t - 2) 0) + w.getD (t - 7) 0 + ssig0 (w.getD (t - 15) 0) + w.getD (t - 16) 0]

theorem schedList_length (M : ℕ → Word) : ∀ k, (schedList M k).length = 16 + k
  | 0 => by simp [schedList]
  | k + 1 => by simp [schedList, schedList_length M k]; omega

theorem schedList_get (M : ℕ → Word) : ∀ k, ∀ i < 16 + k, (schedList M k).getD i 0 = schedule M i
  | 0 => fun i hi => by
    simp only [schedList, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega : i < 16),
      Option.map_some, Option.getD_some]
    rw [schedule, dif_pos (by omega)]
  | k + 1 => fun i hi => by
    have ih := schedList_get M k
    have hl := schedList_length M k
    simp only [schedList]
    by_cases h : i < 16 + k
    · rw [List.getD_append _ _ _ _ (by omega)]; exact ih i h
    · have hi' : i = 16 + k := by omega
      subst hi'
      rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
      simp only [List.getD_cons_zero]
      rw [ih _ (by omega), ih _ (by omega), ih _ (by omega), ih _ (by omega)]
      conv_rhs => rw [schedule, dif_neg (by omega)]

/-- `compress` with the schedule computed once. -/
def compressFast (H : State) (M : ℕ → Word) : State :=
  let w := schedList M 48
  let s := (List.range 64).foldl (fun s t => round s (K t) (w.getD t 0)) H
  ⟨H.a + s.a, H.b + s.b, H.c + s.c, H.d + s.d, H.e + s.e, H.f + s.f, H.g + s.g, H.h + s.h⟩

theorem rounds_foldl (H : State) (M : ℕ → Word) :
    ∀ n, rounds H M n = (List.range n).foldl (fun s t => round s (K t) (schedule M t)) H
  | 0 => rfl
  | n + 1 => by rw [rounds, rounds_foldl H M n, List.range_succ, List.foldl_append]; rfl

theorem foldl_congr_mem {α β : Type} (f g : α → β → α) :
    ∀ (l : List β) (a : α), (∀ s, ∀ t ∈ l, f s t = g s t) → l.foldl f a = l.foldl g a
  | [], _, _ => rfl
  | t :: l, a, h => by
    simp only [List.foldl_cons]
    rw [h a t (List.mem_cons_self ..)]
    exact foldl_congr_mem f g l _ (fun s u hu => h s u (List.mem_cons_of_mem _ hu))

theorem compress_eq_fast : @compress = @compressFast := by
  funext H M
  have e : (List.range 64).foldl (fun s t => round s (K t) ((schedList M 48).getD t 0)) H =
      (List.range 64).foldl (fun s t => round s (K t) (schedule M t)) H := by
    apply foldl_congr_mem
    intro s t ht
    rw [List.mem_range] at ht
    rw [schedList_get M 48 t (by omega)]
  simp only [compress, compressFast, rounds_foldl, e]

attribute [csimp] compress_eq_fast

end BitcoinConsensus.Sha256
