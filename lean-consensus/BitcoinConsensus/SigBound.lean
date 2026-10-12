/-
**Sigop bounds.** A script's legacy sigops are at most 20 per byte, so a block's sigop sum stays far
below the field size.
-/
import BitcoinConsensus.TokSums
import BitcoinConsensus.BlockFlat

namespace BitcoinConsensus.Block

theorem len_aux {o : UInt8} {c : Prop} [Decidable c] {X r : Bytes} (hX : (ops X).length ≤ X.length)
    (hXr : X.length ≤ r.length) : (if c then [] else o :: ops X).length ≤ (o :: r).length := by
  split <;> simp <;> omega

theorem ops_length_le : ∀ n (s : Bytes), s.length = n → (ops s).length ≤ s.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro s hs
    match s with
    | [] => simp [ops]
    | o :: r =>
      unfold ops
      simp only
      have key : ∀ d : Bytes, d.length ≤ r.length → (ops d).length ≤ d.length := fun d hd =>
        ih d.length (by simp at hs; omega) d rfl
      split
      · simp
      · refine len_aux (key _ ?_) ?_ <;> simp <;> omega

theorem sigOps_le (s : Bytes) : sigOps s ≤ 20 * s.length := by
  rw [sigOps_eq]
  have h1 := ops_length_le _ s rfl
  have : ((ops s).map sigW).sum ≤ 20 * (ops s).length := by
    have := List.sum_le_card_nsmul ((ops s).map sigW) 20 (by
      intro x hx
      obtain ⟨o, -, rfl⟩ := List.mem_map.mp hx
      unfold sigW; split_ifs <;> omega)
    simpa [mul_comm] using this
  omega

theorem tokSig_le (t : Tok) : tokSig t ≤ 20 * (Tok.bytes t).length := by
  cases t with
  | inp h i s q => have := sigOps_le s; simp [tokSig, Tok.bytes, serVarBytes]; omega
  | out v s => have := sigOps_le s; simp [tokSig, Tok.bytes, serVarBytes]; omega
  | _ => simp [tokSig]

theorem sumSig_le (ts : List Tok) : sumSig ts ≤ 20 * (toksBytes ts).length := by
  induction ts with
  | nil => simp [sumSig, toksBytes]
  | cons t ts ih =>
    rw [sumSig_cons]
    have := tokSig_le t
    simp only [toksBytes, List.flatMap_cons, List.length_append] at ih ⊢
    omega

end BitcoinConsensus.Block
