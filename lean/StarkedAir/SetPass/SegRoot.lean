/-
**A segment's public root is the Merkle root of its records (D-050).** `set_seg_root`: a sound segment
(`set_seg_sound`) also has its public `ROOT` limbs equal to `Spec.SetMerkle.segRoot HALF s.last seg`: the
heap tree over `2·HALF` slots of its records' leaves `Blake2s-256(key(previous) ‖ encRec)`, the previous
key before the first record being the incoming state's last record's (36 zero bytes when there is none).
-/
import StarkedAir.SetPass.MTTree
import StarkedAir.SetPass.LeafLink
import StarkedAir.Spec.SetMerkle

namespace StarkedAir.SetPass

open StarkedAir
open StarkedAir.Sha256 (half16)
open StarkedAir.Spec.CoinEpoch (CEv)
open StarkedAir.Spec.QM31 (QM)

/-- A record's key bytes are its spec key. -/
theorem key_bytes {x : CEv} (hx : (Spec.SetFile.txid x).length = 32) :
    (List.range 36).map (fun j => UInt8.ofNat (Rec.keyB x j)) = Spec.SetMerkle.key x := by
  apply List.ext_getElem (by simp [Spec.SetMerkle.key, Spec.Block.beBytes, hx])
  intro j h1 h2
  have hj : j < 36 := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, Rec.keyB, Spec.SetMerkle.key]
  by_cases h32 : j < 32
  · rw [if_pos h32, List.getElem_append_left (by omega), List.getD_eq_getElem _ _ (by omega)]
    simp
  · rw [if_neg h32, List.getElem_append_right (by omega)]
    simp only [Spec.Block.beBytes, List.getElem_map, List.getElem_reverse, List.getElem_range, List.length_range, hx]
    rw [show 256 ^ (35 - j) = 2 ^ (8 * (4 - 1 - (j - 32))) by interval_cases j <;> norm_num]
    apply UInt8.toNat.inj
    simp

/-- The leaves of `n` records given by `f`, after `last`. -/
theorem leaves_map : ∀ (n : ℕ) (f : ℕ → CEv) (last : Option CEv),
    Spec.SetMerkle.leaves last ((List.range n).map f) = (List.range n).map (fun ρ =>
      Spec.SetMerkle.leafHash (Spec.SetMerkle.prevKey (if ρ = 0 then last else some (f (ρ - 1))) ++
        Spec.SetFile.encRec (f ρ)))
  | 0, _, _ => rfl
  | n + 1, f, last => by
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Spec.SetMerkle.leaves,
      show f ∘ Nat.succ = fun ρ => f (ρ + 1) from rfl, leaves_map n (fun ρ => f (ρ + 1)) (some (f 0)),
      List.map_cons, List.map_map]
    simp only [if_true]
    congr 1
    apply List.map_congr_left
    intro ρ _
    cases ρ with
    | zero => rfl
    | succ ρ => simp

section Seg

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 12, (inst i).logSize = Ls i) (hsat : segSys.SatisfiedExt inst pub []) (hsz : SegSizeOk Ls)
include hL hsat hsz

/-- **The segment's root.** A sound segment's public root limbs are those of the heap tree over its records'
leaves. -/
theorem set_seg_root (s : Spec.SetFile.St QM) (hin : EncIn pub s) :
    ∃ seg : List CEv, seg ≠ [] ∧ seg.flatMap Spec.SetFile.encRec = segBytes inst pub ∧
      (∀ x ∈ seg, Spec.SetFile.RecOk x) ∧
      EncOut pub (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s) ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s).n = s.n ∧
      (seg.foldl (Spec.SetFile.step [Rec.frac pub]) s).ok = s.ok ∧
      ∀ i < 16, pub (PUB_ROOT i) =
        (StarkedAir.HeaderTree.limbsOf (Spec.SetMerkle.segRoot (pub PUB_HALF).val s.last seg)).getD i 0 := by
  have hHL : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1 := by
    rcases hin.last with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨seg, hne, hb, hok, hout, hn, hk, e, E, hidx, hcnt, hseg, H⟩ := set_seg_sound hL hsat hsz s hin
  refine ⟨seg, hne, hb, hok, hout, hn, hk, ?_⟩
  have he24 : e ≤ 2 ^ 24 := by
    have := E.lt; have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (hsz.1 3 (by decide)); omega
  obtain ⟨hhalf, h1, h24, hc⟩ := half_facts hL hsat hHL hsz hcnt he24
  set MR := (inst 3).main with hMR
  set S := Sb inst pub with hS
  have hleaf := fun r k (hr : r < 2 ^ Ls 10) (h2 : 2 ≤ k) (h10 : k < 10) hm =>
    leaf_yield hL hsat hHL hsz E hidx H (r := r) (k := k) hr h2 h10 hm
  have hroot := root_ok hL hsat hHL hsz hhalf h24 hcnt hc (lf := fun ρ => Spec.SetMerkle.leafHash (leafMsg pub MR S ρ))
    hleaf h1
  -- the circuit's leaves are the spec's
  have hrs := rec_sat hL hsat
  have hmsg : ∀ ρ < e, leafMsg pub MR S ρ = Spec.SetMerkle.prevKey (if ρ = 0 then s.last else
      some (Rec.recR MR S (ρ - 1))) ++ Spec.SetFile.encRec (Rec.recR MR S ρ) := by
    intro ρ hρ
    unfold leafMsg
    congr 1
    by_cases h0 : ρ = 0
    · subst h0
      simp only [Rec.prevKey, if_true]
      rcases hin.last with ⟨-, hn, hz⟩ | ⟨-, p, hp, hpok, hpk⟩
      · rw [hn, Spec.SetMerkle.prevKey]
        apply List.ext_getElem (by simp)
        intro j h1 _
        have hj : j < 36 := by simpa using h1
        simp only [List.getElem_map, List.getElem_range, hz j hj, ZMod.val_zero, List.getElem_replicate]
        rfl
      · rw [hp, Spec.SetMerkle.prevKey, ← key_bytes hpok.1]
        apply List.map_congr_left
        intro j hj
        rw [hpk j (by simpa using hj)]
    · simp only [Rec.prevKey, if_neg h0, Spec.SetMerkle.prevKey]
      have hr : Rec.recR MR S (ρ - 1) ∈ seg := by
        rw [hseg, Rec.recs]; exact List.mem_map.mpr ⟨ρ - 1, List.mem_range.mpr (by omega), rfl⟩
      exact key_bytes (hok _ hr).1
  have hls : (List.range e).map (fun ρ => Spec.SetMerkle.leafHash (leafMsg pub MR S ρ)) =
      Spec.SetMerkle.leaves s.last seg := by
    rw [hseg, Rec.recs, leaves_map]
    apply List.map_congr_left
    intro ρ hρ
    rw [hmsg ρ (List.mem_range.mp hρ)]
  intro i hi
  rw [hroot i hi, StarkedAir.HeaderTree.limbsOf_get hi, Spec.SetMerkle.segRoot, ← hls]

end Seg

end StarkedAir.SetPass
