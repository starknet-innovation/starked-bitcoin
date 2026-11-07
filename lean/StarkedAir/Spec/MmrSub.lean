/-
**Subtree inclusion in the header MMR (SEAL-T-LEAN, D-052).** The seal checks each epoch child's
block-hash root, the root of the perfect tree over the child's `2^k` block hashes, against the
header chain's root `T` with a path from that subtree's root, not from a leaf: the verifier takes
leaf `pos`'s sides (`HTree.sides`, Zig `HT.inclusionSides`), checks the first `k` (leaf end) are
`false` and drops them (`chain_seal.pathPubs`).

`sub_inclusionC`: a path whose root-first sides lead to a node `u` of `t` (`HTree.sub?`) and whose
recomputed root is `t`'s proves `u.root` is the path's start, or two of the compared inputs collide
(`subPairs`, named as in `pathPairsRev`).

`mmr_sub`: in the canonical MMR over `L`, a block of `2^k` leaves at a position `pos` divisible by
`2^k` with `pos + 2^k ≤ |L|` is such a node: leaf `pos`'s root-first sides are `ps ++ k × false`
and the node at `ps` is `bal k` over the block. `mmr_subC` combines the two in the verifier's terms.
-/
import StarkedAir.Spec.Mmr

namespace StarkedAir.Spec.Mmr

open StarkedAir.Spec.Sha256 (State)
open StarkedAir.Spec.HeaderTree (HTree hnode)

/-- The node reached from the root by root-first sides (`false`: left child). -/
def _root_.StarkedAir.Spec.HeaderTree.HTree.sub? : HTree → List Bool → Option HTree
  | t, [] => some t
  | .node l _, false :: ps => l.sub? ps
  | .node _ r, true :: ps => r.sub? ps
  | .leaf _, _ :: _ => none

theorem sub?_nil (t : HTree) : t.sub? [] = some t := by cases t <;> rfl

/-- The inputs a root-first path to a node compares: at each node, the recomputed (child, sibling)
in the step's order against the tree's children's roots. -/
def subPairs : HTree → State → List Step → List ((State × State) × (State × State))
  | .node l r, x, s :: rest =>
    if s.left then ((s.sibling, pathRootRev x rest), (l.root, r.root)) :: subPairs r x rest
    else ((pathRootRev x rest, s.sibling), (l.root, r.root)) :: subPairs l x rest
  | _, _, _ => []

/-- **Inclusion of a node, with a named collision** (root-first form). -/
theorem sub_inclusion_revC : ∀ (t : HTree) (x : State) (rs : List Step) (u : HTree),
    t.sub? (rs.map Step.left) = some u → pathRootRev x rs = t.root →
    u.root = x ∨ CollidesIn (subPairs t x rs)
  | t, x, [], u, hs, hr => by
    simp only [List.map_nil, sub?_nil, Option.some.injEq] at hs
    subst hs; exact Or.inl hr.symm
  | .leaf _, x, s :: rest, u, hs, _ => by simp [HTree.sub?] at hs
  | .node l r, x, s :: rest, u, hs, hr => by
    simp only [pathRootRev, HTree.root, Step.up] at hr
    cases hb : s.left
    · simp only [List.map_cons, hb, HTree.sub?] at hs
      simp only [hb, Bool.false_eq_true, ite_false] at hr
      simp only [subPairs, hb, Bool.false_eq_true, ite_false]
      by_cases he : (pathRootRev x rest, s.sibling) = (l.root, r.root)
      · simp only [Prod.mk.injEq] at he
        rcases sub_inclusion_revC l x rest u hs he.1 with h1 | ⟨pq, hm, hc⟩
        · exact Or.inl h1
        · exact Or.inr ⟨pq, List.mem_cons_of_mem _ hm, hc⟩
      · exact Or.inr ⟨_, List.mem_cons_self .., he, hr⟩
    · simp only [List.map_cons, hb, HTree.sub?] at hs
      simp only [hb, ite_true] at hr
      simp only [subPairs, hb, ite_true]
      by_cases he : (s.sibling, pathRootRev x rest) = (l.root, r.root)
      · simp only [Prod.mk.injEq] at he
        rcases sub_inclusion_revC r x rest u hs he.2 with h1 | ⟨pq, hm, hc⟩
        · exact Or.inl h1
        · exact Or.inr ⟨pq, List.mem_cons_of_mem _ hm, hc⟩
      · exact Or.inr ⟨_, List.mem_cons_self .., he, hr⟩

/-- **Inclusion of a node, with a named collision**: a path (start to root) whose reversed sides
lead to `u` in `t` and whose recomputed root is `t`'s proves `u.root` is its start. -/
theorem sub_inclusionC (t : HTree) (x : State) (steps : List Step) (u : HTree)
    (hs : t.sub? (steps.reverse.map Step.left) = some u) (hr : pathRoot x steps = t.root) :
    u.root = x ∨ CollidesIn (subPairs t x steps.reverse) := by
  rw [pathRoot_rev] at hr
  exact sub_inclusion_revC t x steps.reverse u hs hr

/-! ### Aligned blocks of the canonical MMR -/

theorem bal_size (k : ℕ) (L : List State) (h : L.length = 2 ^ k) : (bal k L).size = 2 ^ k := by
  rw [HTree.size, bal_leaves k L h, h]

/-- Leaf 0 of a perfect tree of height `k` is `k` steps down the left. -/
theorem bal_sidesRev_zero : ∀ (k : ℕ) (L : List State), L.length = 2 ^ k →
    (bal k L).sidesRev 0 = List.replicate k false
  | 0, L, _ => rfl
  | k + 1, L, h => by
    have hl : (L.take (2 ^ k)).length = 2 ^ k := by rw [List.length_take, h, pow_succ]; omega
    simp only [bal, HTree.sidesRev, bal_size k _ hl, Nat.two_pow_pos, ite_true, List.replicate_succ]
    rw [bal_sidesRev_zero k _ hl]

/-- A block of `2^k` leaves aligned in a perfect tree is a node of it. -/
theorem bal_sub : ∀ (j k pos : ℕ) (A : List State), A.length = 2 ^ j → 2 ^ k ∣ pos → pos + 2 ^ k ≤ 2 ^ j →
    ∃ ps, (bal j A).sidesRev pos = ps ++ List.replicate k false ∧
      (bal j A).sub? ps = some (bal k ((A.drop pos).take (2 ^ k)))
  | j, k, pos, A, hA, hd, hle => by
    have hkj : k ≤ j := by
      by_contra hc
      have : 2 ^ (j + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ] at this; have := Nat.two_pow_pos j; omega
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · -- the whole tree
      have hp : pos = 0 := by have := Nat.two_pow_pos k; omega
      subst hp
      refine ⟨[], by rw [bal_sidesRev_zero k A hA, List.nil_append], ?_⟩
      rw [List.drop_zero, List.take_of_length_le (by rw [hA]), sub?_nil]
    · obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have hl : (A.take (2 ^ j)).length = 2 ^ j := by rw [List.length_take, hA, pow_succ]; omega
      have hr : (A.drop (2 ^ j)).length = 2 ^ j := by rw [List.length_drop, hA, pow_succ]; omega
      have hkj' : 2 ^ k ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
      simp only [bal, HTree.sidesRev, bal_size j _ hl]
      by_cases hpos : pos < 2 ^ j
      · have hle' : pos + 2 ^ k ≤ 2 ^ j := by
          obtain ⟨a, rfl⟩ := hd; obtain ⟨b, hb⟩ := hkj'
          rw [hb] at hpos ⊢
          have := Nat.two_pow_pos k
          have : a < b := by by_contra hc; have : 2 ^ k * b ≤ 2 ^ k * a := Nat.mul_le_mul_left _ (by omega); omega
          nlinarith
        obtain ⟨ps, h1, h2⟩ := bal_sub j k pos _ hl hd hle'
        refine ⟨false :: ps, by rw [if_pos hpos, h1, List.cons_append], ?_⟩
        have e : List.take (2 ^ k) (List.drop pos (List.take (2 ^ j) A)) = List.take (2 ^ k) (List.drop pos A) := by
          rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
        simp only [HTree.sub?, h2, e]
      · have hge : 2 ^ j ≤ pos := by omega
        obtain ⟨ps, h1, h2⟩ := bal_sub j k (pos - 2 ^ j) _ hr (Nat.dvd_sub hd hkj')
          (by rw [pow_succ] at hle; omega)
        refine ⟨true :: ps, by rw [if_neg hpos, h1, List.cons_append], ?_⟩
        simp only [HTree.sub?, h2, List.drop_drop]
        congr 4
        omega

/-- **An aligned block of the canonical MMR is a node of it**: for non-empty `L`, `2^k ∣ pos` and
`pos + 2^k ≤ |L|`, leaf `pos`'s root-first sides are `ps ++ k × false` and the node at `ps` is the
perfect tree over the block. -/
theorem mmr_sub (L : List State) (hL : L ≠ []) (k pos : ℕ) (hd : 2 ^ k ∣ pos) (hle : pos + 2 ^ k ≤ L.length) :
    ∃ ps, (mmr L).sidesRev pos = ps ++ List.replicate k false ∧
      (mmr L).sub? ps = some (bal k ((L.drop pos).take (2 ^ k))) := by
  induction L using WellFounded.induction (InvImage.wf List.length Nat.lt_wfRel.wf) generalizing pos with
  | _ L ih =>
    unfold mmr
    split
    · rename_i h1
      have h2k : 2 ^ k ≤ 1 := by omega
      have hk : k = 0 := by
        rcases k with _ | k
        · rfl
        · rw [pow_succ] at h2k; have := Nat.two_pow_pos k; omega
      subst hk
      have hp : pos = 0 := by rw [pow_zero] at hle; omega
      subst hp
      refine ⟨[], rfl, ?_⟩
      match L, hL with
      | [x], _ => rfl
      | _ :: _ :: _, _ => simp at h1
    · rename_i h1
      have hn : 2 ≤ L.length := by omega
      set K := Nat.log 2 L.length with hK
      have hle2 : 2 ^ K ≤ L.length := Nat.pow_log_le_self 2 (by omega)
      have hlt : L.length < 2 ^ (K + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
      have hkK : k ≤ K := by
        by_contra hc
        have : 2 ^ (K + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      simp only
      split
      · rename_i heq
        exact bal_sub K k pos L heq hd (by omega)
      · rename_i hne
        have htl : (L.take (2 ^ K)).length = 2 ^ K := by rw [List.length_take]; omega
        have hkK' : 2 ^ k ∣ 2 ^ K := Nat.pow_dvd_pow 2 hkK
        simp only [HTree.sidesRev, bal_size K _ htl]
        by_cases hpos : pos < 2 ^ K
        · have hle' : pos + 2 ^ k ≤ 2 ^ K := by
            obtain ⟨a, rfl⟩ := hd; obtain ⟨b, hb⟩ := hkK'
            rw [hb] at hpos ⊢
            have := Nat.two_pow_pos k
            have : a < b := by by_contra hc; have : 2 ^ k * b ≤ 2 ^ k * a := Nat.mul_le_mul_left _ (by omega); omega
            nlinarith
          obtain ⟨ps, h1, h2⟩ := bal_sub K k pos _ htl hd hle'
          refine ⟨false :: ps, by rw [if_pos hpos, h1, List.cons_append], ?_⟩
          have e : List.take (2 ^ k) (List.drop pos (List.take (2 ^ K) L)) = List.take (2 ^ k) (List.drop pos L) := by
            rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]
          simp only [HTree.sub?, h2, e]
        · have hge : 2 ^ K ≤ pos := by omega
          have hdl : (L.drop (2 ^ K)).length = L.length - 2 ^ K := List.length_drop ..
          obtain ⟨ps, h1, h2⟩ := ih (L.drop (2 ^ K))
            (by simp only [InvImage, hdl]; have := Nat.two_pow_pos K; show _ < _; omega)
            (by intro h; simp [List.drop_eq_nil_iff] at h; omega) (pos - 2 ^ K)
            (Nat.dvd_sub hd hkK') (by rw [hdl]; omega)
          refine ⟨true :: ps, by rw [if_neg hpos, h1, List.cons_append], ?_⟩
          simp only [HTree.sub?, h2, List.drop_drop]
          congr 4
          omega

/-- **The seal's subtree check, with a named collision.** In the canonical MMR over non-empty `L`,
for an aligned block (`2^k ∣ pos`, `pos + 2^k ≤ |L|`): a path whose sides are leaf `pos`'s with the
first `k` (`false`) dropped, and whose recomputed root is the MMR's, proves its start is the root of
the perfect tree over the block, or two of the inputs it compares collide. -/
theorem mmr_subC (L : List State) (hL : L ≠ []) (k pos : ℕ) (hd : 2 ^ k ∣ pos) (hle : pos + 2 ^ k ≤ L.length)
    (x : State) (steps : List Step)
    (hs : (mmr L).sides pos = List.replicate k false ++ steps.map Step.left)
    (hr : pathRoot x steps = (mmr L).root) :
    (bal k ((L.drop pos).take (2 ^ k))).root = x ∨ CollidesIn (subPairs (mmr L) x steps.reverse) := by
  obtain ⟨ps, h1, h2⟩ := mmr_sub L hL k pos hd hle
  have e : (mmr L).sidesRev pos = (steps.map Step.left).reverse ++ List.replicate k false := by
    have := congrArg List.reverse hs
    rw [HTree.sides, List.reverse_reverse, List.reverse_append, List.reverse_replicate] at this
    exact this
  rw [e] at h1
  have hps : ps = (steps.map Step.left).reverse := (List.append_inj_left' h1.symm rfl)
  rw [hps, ← List.map_reverse] at h2
  exact sub_inclusionC _ x steps _ h2 hr

/-! ### The sides depend on the leaf count only -/

theorem bal_sidesRev_len : ∀ (k : ℕ) (A B : List State) (pos : ℕ), A.length = 2 ^ k → B.length = 2 ^ k →
    (bal k A).sidesRev pos = (bal k B).sidesRev pos
  | 0, _, _, _, _, _ => rfl
  | k + 1, A, B, pos, hA, hB => by
    have hlA : (A.take (2 ^ k)).length = 2 ^ k := by rw [List.length_take, hA, pow_succ]; omega
    have hlB : (B.take (2 ^ k)).length = 2 ^ k := by rw [List.length_take, hB, pow_succ]; omega
    have hrA : (A.drop (2 ^ k)).length = 2 ^ k := by rw [List.length_drop, hA, pow_succ]; omega
    have hrB : (B.drop (2 ^ k)).length = 2 ^ k := by rw [List.length_drop, hB, pow_succ]; omega
    simp only [bal, HTree.sidesRev, bal_size k _ hlA, bal_size k _ hlB]
    split
    · rw [bal_sidesRev_len k _ _ pos hlA hlB]
    · rw [bal_sidesRev_len k _ _ _ hrA hrB]

/-- **The MMR's sides depend on the leaf count only** (what the verifier computes from `n`). -/
theorem mmr_sidesRev_len (L M : List State) (h : L.length = M.length) (pos : ℕ) :
    (mmr L).sidesRev pos = (mmr M).sidesRev pos := by
  induction L using WellFounded.induction (InvImage.wf List.length Nat.lt_wfRel.wf) generalizing M pos with
  | _ L ih =>
    rw [mmr, mmr]
    by_cases h1 : L.length ≤ 1
    · rw [dif_pos h1, dif_pos (h ▸ h1)]; rfl
    · rw [dif_neg h1, dif_neg (h ▸ h1)]
      simp only [← h]
      have hle2 : 2 ^ Nat.log 2 L.length ≤ L.length := Nat.pow_log_le_self 2 (by omega)
      split
      · rename_i heq; exact bal_sidesRev_len _ _ _ pos heq (h ▸ heq)
      · have htL : (L.take (2 ^ Nat.log 2 L.length)).length = 2 ^ Nat.log 2 L.length := by rw [List.length_take]; omega
        have htM : (M.take (2 ^ Nat.log 2 L.length)).length = 2 ^ Nat.log 2 L.length := by rw [List.length_take]; omega
        simp only [HTree.sidesRev, bal_size _ _ htL, bal_size _ _ htM]
        split
        · rw [bal_sidesRev_len _ _ _ pos htL htM]
        · rw [ih (L.drop _) (by simp only [InvImage, List.length_drop]; have := Nat.two_pow_pos (Nat.log 2 L.length); show _ < _; omega)
            (M.drop (2 ^ Nat.log 2 L.length)) (by simp [h])]

theorem mmr_sides_len (L M : List State) (h : L.length = M.length) (pos : ℕ) :
    (mmr L).sides pos = (mmr M).sides pos := by
  rw [HTree.sides, HTree.sides, mmr_sidesRev_len L M h]

/-- The sides of leaf `pos` among `n` leaves (`header_tree.inclusionSides`), leaf to root. -/
def mmrSides (n pos : ℕ) : List Bool := (mmr (List.replicate n zeroState)).sides pos

theorem mmr_sides_eq (L : List State) (pos : ℕ) : (mmr L).sides pos = mmrSides L.length pos :=
  mmr_sides_len L _ (by simp) pos

end StarkedAir.Spec.Mmr
