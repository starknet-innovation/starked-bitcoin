/-
**Merkle leaf compressions, soundness (D-050).** `set_lc` is `block_b2s` (same columns, preprocessed
columns and constraints) plus the record index `RI`, constant down a period and equal across a chain. So
every `block_b2s` period lemma (`B2s.period_compress`, `h_first`, `h_chain`, `tf`, `msg_word`, …) holds
for a satisfied `set_lc` trace (`b2s_sat`).
-/
import StarkedAir.SetPass.LC
import StarkedAir.Block.B2sSound

namespace StarkedAir.SetPass.LC

open StarkedAir

theorem preCols_eq : preCols = Block.B2s.preCols := rfl

theorem flagC_sub : ∀ c ∈ Block.B2s.flagC, c ∈ flagC := by
  intro c hc
  simp only [Block.B2s.flagC, List.mem_append, List.mem_map] at hc
  simp only [flagC, List.mem_append, List.mem_map, perConst]
  rcases hc with (⟨x, hx, rfl⟩ | h) | ⟨x, hx, rfl⟩
  · exact Or.inl (Or.inl ⟨x, hx, rfl⟩)
  · exact Or.inl (Or.inr h)
  · refine Or.inr ⟨x, ?_, rfl⟩
    simp only [Block.B2s.perConst, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
    rcases hx with h | h | h | h | h <;> simp [h, BLKI, FST, NIL, LASTF, T, Block.B2s.BLKI, Block.B2s.FST,
      Block.B2s.NIL, Block.B2s.LASTF, Block.B2s.T]

theorem chainC_sub : ∀ c ∈ Block.B2s.chainC, c ∈ chainC := by
  intro c hc
  simp only [Block.B2s.chainC, List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [chainC, List.mem_cons, List.not_mem_nil, or_false]
  rcases hc with h | h | h | h <;> subst h
  · exact Or.inl rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem initC_eq : initC = Block.B2s.initC := rfl
theorem tfC_eq : tfC = Block.B2s.tfC := rfl
theorem wordC_eq : wordC = Block.B2s.wordC := rfl

/-- `block_b2s`'s constraints are `set_lc`'s. -/
theorem sub : ∀ c ∈ Block.B2s.constraints, c ∈ constraints := by
  intro c hc
  simp only [Block.B2s.constraints, List.mem_append] at hc
  simp only [constraints, List.mem_append, initC_eq, tfC_eq, wordC_eq]
  rcases hc with ((((h | h) | h) | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h))))
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (flagC_sub c h)))))
  · exact Or.inl (Or.inl (Or.inl (Or.inr (chainC_sub c h))))
  · exact Or.inl (Or.inl (Or.inr h))
  · exact Or.inl (Or.inr h)
  · exact Or.inr h

/-- **A satisfied `set_lc` trace satisfies `block_b2s`.** -/
theorem b2s_sat {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
    (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) :
    ∀ r < n, ∀ c ∈ Block.B2s.constraints, c.eval n Block.B2s.preCols pub M r = 0 :=
  fun r hr c hc => hsat r hr c (sub c hc)

end StarkedAir.SetPass.LC
