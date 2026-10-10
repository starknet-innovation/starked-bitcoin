/-
**Merkle path verification, Lean-first (VERIFIER-LEAN step 5).** stwo-zig's `verifyMerklePath`
(`stark_verifier/merkle.zig`): from the leaf, each level flips (node, sibling) by the query bit
(`condFlipU32`: `d = bit·(sib − node)`, left `node + d`, right `sib − d`), hashes `left ‖ right` with
Blake2s (64 bytes), and finally requires the recomputed root to equal the committed one word for word.

`pathCheck` emits those builder calls in order. `path_sound`: if its ops hold and every bit is 0 or 1,
the committed root is `specRoot` of the leaf and the authentication path, i.e. the Blake2s Merkle root
(`left ‖ right`, the bit saying whether the current node is the right child).
-/
import StarkedAir.Circuit.BlakeSound

namespace StarkedAir.Circuit.Merkle

open StarkedAir StarkedAir.Circuit Spec.Blake2s Q

/-! ### Spec -/

/-- A parent: Blake2s of `left ‖ right` (64 bytes); `bit` says the current node is the right child. -/
def specNode (cur sib : List Word) (bit : Bool) : List Word :=
  let lr := if bit then sib ++ cur else cur ++ sib
  (List.range 8).map (blake2sWords lr 64)

/-- The root from a leaf and its authentication path (bit, sibling), leaf level first. -/
def specRoot (cur : List Word) : List (Bool × List Word) → List Word
  | [] => cur
  | (b, s) :: rest => specRoot (specNode cur s b) rest

/-! ### Program -/

/-- `condFlip` of one word pair from register `n`: `b − a`, `bit·(b − a)`, `a + d`, `b − d`. -/
def flipOps (n bit a b : ℕ) : List Op := [.sub n b a, .mul (n + 1) bit n, .add (n + 2) a (n + 1), .sub (n + 3) b (n + 1)]

/-- `merkleNode`: the eight word flips, then `hashNode(left, right)`. -/
def node (n : ℕ) (cur sib : List ℕ) (bit : ℕ) : Out (List ℕ) :=
  let flips := (List.range 8).flatMap fun k => flipOps (n + 4 * k) bit (cur.getD k 0) (sib.getD k 0)
  let msg := (List.range 8).map (fun k => n + 4 * k + 2) ++ (List.range 8).map (fun k => n + 4 * k + 3)
  let h := blake2s (n + 32) msg 64
  ⟨flips ++ h.ops, h.res, h.next⟩

/-- The levels, leaf first. -/
def path : ℕ → List ℕ → List (ℕ × List ℕ) → Out (List ℕ)
  | n, cur, [] => ⟨[], cur, n⟩
  | n, cur, (bit, sib) :: rest =>
    let o := node n cur sib bit
    let r := path o.next o.res rest
    ⟨o.ops ++ r.ops, r.res, r.next⟩

/-- `verifyMerklePath`: the levels, then the recomputed root equals `root`, word by word. -/
def pathCheck (n : ℕ) (leaf : List ℕ) (levels : List (ℕ × List ℕ)) (root : List ℕ) : Out Unit :=
  let p := path n leaf levels
  ⟨p.ops ++ (List.range 8).map (fun k => .eq (p.res.getD k 0) (root.getD k 0)), (), p.next⟩

/-! ### Soundness -/

variable {ρ : ℕ → Q}

theorem lit0_mul (x : Q) : lit 0 0 0 0 * x = ⟨0, 0, 0, 0⟩ := by
  show (⟨_, _, _, _⟩ : Q) = _
  simp [lit, cmul]

theorem lit1_mul (x : Q) : lit 1 0 0 0 * x = x := by
  show (⟨_, _, _, _⟩ : Q) = _
  ext <;> simp [lit, cmul]

/-- A Boolean wire. -/
def bitQ (b : Bool) : Q := if b then lit 1 0 0 0 else lit 0 0 0 0

theorem flip_sound {n bit a b : ℕ} {β : Bool} (h : Holds ρ (flipOps n bit a b)) (hb : ρ bit = bitQ β) :
    ρ (n + 2) = (if β then ρ b else ρ a) ∧ ρ (n + 3) = (if β then ρ a else ρ b) := by
  have h0 := h _ (by simp [flipOps] : Op.sub n b a ∈ _)
  have h1 := h _ (by simp [flipOps] : Op.mul (n + 1) bit n ∈ _)
  have h2 := h _ (by simp [flipOps] : Op.add (n + 2) a (n + 1) ∈ _)
  have h3 := h _ (by simp [flipOps] : Op.sub (n + 3) b (n + 1) ∈ _)
  simp only [Op.holds] at h0 h1 h2 h3
  rw [h2, h3, h1, h0, hb]
  cases β
  · rw [show bitQ false = lit 0 0 0 0 from rfl, lit0_mul]; constructor <;> ext <;> simp
  · rw [show bitQ true = lit 1 0 0 0 from rfl, lit1_mul]; constructor <;> ext <;> simp

theorem node_sound {n : ℕ} {cur sib : List ℕ} {bit : ℕ} {β : Bool} (hc : cur.length = 8) (hs : sib.length = 8)
    (h : Holds ρ (node n cur sib bit).ops) (hb : ρ bit = bitQ β) :
    (node n cur sib bit).res.map (word ∘ ρ) = specNode (cur.map (word ∘ ρ)) (sib.map (word ∘ ρ)) β := by
  simp only [node] at h ⊢
  rw [holds_append] at h
  obtain ⟨hf, hh⟩ := h
  have hfl : ∀ k < 8, ρ (n + 4 * k + 2) = (if β then ρ (sib.getD k 0) else ρ (cur.getD k 0)) ∧
      ρ (n + 4 * k + 3) = (if β then ρ (cur.getD k 0) else ρ (sib.getD k 0)) := by
    intro k hk
    exact flip_sound (fun op hop => hf op (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hop⟩)) hb
  have hw := blake2s_words hh (by norm_num)
  have hlen : (blake2s (n + 32) ((List.range 8).map (fun k => n + 4 * k + 2) ++ (List.range 8).map (fun k => n + 4 * k + 3)) 64).res.length = 8 := by
    simp [blake2s]
  apply List.ext_getElem (by simp [hlen, specNode])
  intro i h1 h2
  have hi : i < 8 := by simpa [hlen] using h1
  simp only [List.getElem_map, Function.comp, specNode, List.getElem_range]
  rw [← List.getD_eq_getElem _ 0 (by omega), hw i hi]
  congr 1
  have hmsg : ∀ k < 8, (word ∘ ρ) (n + 4 * k + 2) = (if β then sib.map (word ∘ ρ) else cur.map (word ∘ ρ)).getD k 0 ∧
      (word ∘ ρ) (n + 4 * k + 3) = (if β then cur.map (word ∘ ρ) else sib.map (word ∘ ρ)).getD k 0 := by
    intro k hk
    obtain ⟨e2, e3⟩ := hfl k hk
    simp only [Function.comp, e2, e3]
    have gc : (cur.map (word ∘ ρ)).getD k 0 = word (ρ (cur.getD k 0)) := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]; simp
    have gs : (sib.map (word ∘ ρ)).getD k 0 = word (ρ (sib.getD k 0)) := by
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by omega)]; simp
    cases β <;> simp only [Bool.false_eq_true, if_false, if_true] <;>
      first | exact ⟨gc.symm, gs.symm⟩ | exact ⟨gs.symm, gc.symm⟩
  have half : ∀ (c : ℕ) (L : List ℕ), L.length = 8 →
      (∀ k < 8, (word ∘ ρ) (n + 4 * k + c) = (L.map (word ∘ ρ)).getD k 0) →
      ((List.range 8).map (fun k => n + 4 * k + c)).map (word ∘ ρ) = L.map (word ∘ ρ) := by
    intro c L hL hk
    apply List.ext_getElem (by simp [hL])
    intro j g1 g2
    have hj : j < 8 := by simpa using g1
    rw [← List.getD_eq_getElem _ 0 g2, ← hk j hj]
    simp
  rw [List.map_append]
  cases β
  · rw [half 2 cur hc (fun k hk => by simpa using (hmsg k hk).1), half 3 sib hs (fun k hk => by simpa using (hmsg k hk).2)]
    rfl
  · rw [half 2 sib hs (fun k hk => by simpa using (hmsg k hk).1), half 3 cur hc (fun k hk => by simpa using (hmsg k hk).2)]
    rfl

theorem node_len (n : ℕ) (cur sib : List ℕ) (bit : ℕ) : (node n cur sib bit).res.length = 8 := by
  simp [node, blake2s]

theorem path_sound (β : ℕ → Bool) : ∀ (n : ℕ) (cur : List ℕ) (levels : List (ℕ × List ℕ)), cur.length = 8 →
    (∀ p ∈ levels, p.2.length = 8 ∧ ρ p.1 = bitQ (β p.1)) → Holds ρ (path n cur levels).ops →
    (path n cur levels).res.map (word ∘ ρ) =
      specRoot (cur.map (word ∘ ρ)) (levels.map fun p => (β p.1, p.2.map (word ∘ ρ)))
  | _, _, [], _, _, _ => rfl
  | n, cur, (bit, sib) :: rest, hc, hl, h => by
    simp only [path] at h ⊢
    rw [holds_append] at h
    have hp := hl (bit, sib) List.mem_cons_self
    rw [path_sound β _ _ rest (node_len n cur sib bit) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) h.2,
      node_sound hc hp.1 h.1 hp.2]
    rfl

/-- **Merkle path verification is sound.** If the ops hold and each level's bit is Boolean, the
committed root is the Blake2s Merkle root of the leaf along the authentication path. -/
theorem path_check_sound (β : ℕ → Bool) {n : ℕ} {leaf root : List ℕ} {levels : List (ℕ × List ℕ)}
    (hc : leaf.length = 8) (hr : root.length = 8)
    (hl : ∀ p ∈ levels, p.2.length = 8 ∧ ρ p.1 = bitQ (β p.1)) (h : Holds ρ (pathCheck n leaf levels root).ops) :
    root.map (word ∘ ρ) = specRoot (leaf.map (word ∘ ρ)) (levels.map fun p => (β p.1, p.2.map (word ∘ ρ))) := by
  simp only [pathCheck] at h
  rw [holds_append] at h
  have hres := path_sound β n leaf levels hc hl h.1
  rw [← hres]
  have hlen : (path n leaf levels).res.length = 8 := by
    cases levels with
    | nil => simpa [path] using hc
    | cons p rest =>
      have : ∀ (m : ℕ) (c : List ℕ) (ls : List (ℕ × List ℕ)), c.length = 8 → (path m c ls).res.length = 8 := by
        intro m c ls
        induction ls generalizing m c with
        | nil => intro hc; simpa [path] using hc
        | cons q qs ih => intro _; simp only [path]; exact ih _ _ (node_len _ _ _ _)
      exact this _ _ _ hc
  apply List.ext_getElem (by simp [hr, hlen])
  intro k g1 g2
  have hk : k < 8 := by simpa [hr] using g1
  have he := h.2 (.eq ((path n leaf levels).res.getD k 0) (root.getD k 0)) (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
  simp only [Op.holds] at he
  simp only [List.getElem_map, Function.comp]
  rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at he
  rw [he]

end StarkedAir.Circuit.Merkle

namespace StarkedAir.Circuit.Merkle

/-- The exported check of a depth-`d` path: hook 0 binds the leaf (8), the root (8), and per level
the bit and the sibling (8). -/
def pathJson (d : ℕ) : String :=
  let nIn := 16 + 9 * d
  let levels := (List.range d).map fun l => (16 + 9 * l, (List.range 8).map (16 + 9 * l + 1 + ·))
  let o := pathCheck nIn (List.range 8) levels ((List.range 8).map (8 + ·))
  let ops := [Op.hook 0 [] (List.range nIn)] ++ o.ops
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[]}"

/-- The exported level: hook 0 binds the current node (8 words), the sibling (8), the bit. -/
def nodeJson : String :=
  let o := node 17 (List.range 8) ((List.range 8).map (8 + ·)) 16
  let ops := [Op.hook 0 [] (List.range 17)] ++ o.ops
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[{",".intercalate (o.res.map toString)}]}"

end StarkedAir.Circuit.Merkle
