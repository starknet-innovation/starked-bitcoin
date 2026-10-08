/-
**Header commitment tree (HC-HASHTREE, D-033): spec.** Block hashes (SHA-256 states) are the
leaves; an internal node is the Blake2s compression of its children's 16 words (`t = 64`, final,
the standard parameter block). `rootAt f ℓ p` is the root of the perfect subtree at level `ℓ`,
position `p` over leaves `f` (leaf `h` at position `h`). A segment of `2^K` headers starting at
`h₀ = 2^K · p` commits to `rootAt hash K p`. Above segments, the recursion builds an MMR:
`HTree` is any binary tree over consecutive leaves; its shape is fixed by the verifier.
-/
import StarkedAir.Spec.Sha256
import StarkedAir.Spec.Blake2s

namespace StarkedAir.Spec.HeaderTree

open StarkedAir.Spec.Sha256 (State)

/-- The 8 words of a state, as message words. -/
def stWord (s : State) : ℕ → Spec.Blake2s.Word
  | 0 => s.a | 1 => s.b | 2 => s.c | 3 => s.d | 4 => s.e | 5 => s.f | 6 => s.g | _ => s.h

def toState (w : ℕ → Spec.Blake2s.Word) : State := ⟨w 0, w 1, w 2, w 3, w 4, w 5, w 6, w 7⟩

/-- An internal node: Blake2s of `l ‖ r` (one 64-byte block, final). -/
def hnode (l r : State) : State :=
  toState (Spec.Blake2s.compress Spec.Blake2s.h0 (fun k => if k < 8 then stWord l k else stWord r (k - 8)) 64 true)

-- Blake2s of the 64 bytes `1..8 ‖ 9..16` (little-endian words), from Python's hashlib.
#guard hnode ⟨1, 2, 3, 4, 5, 6, 7, 8⟩ ⟨9, 10, 11, 12, 13, 14, 15, 16⟩ ==
  ⟨1499642915, 2539650364, 1820938996, 3360072059, 3745081433, 68709067, 3070832761, 2113445077⟩

/-- Root of the perfect subtree at level `ℓ`, position `p`, over leaves `f`. -/
def rootAt (f : ℕ → State) : ℕ → ℕ → State
  | 0, p => f p
  | ℓ + 1, p => hnode (rootAt f ℓ (2 * p)) (rootAt f ℓ (2 * p + 1))

/-- A binary tree over leaves. -/
inductive HTree where
  | leaf (s : State)
  | node (l r : HTree)

def HTree.root : HTree → State
  | .leaf s => s
  | .node l r => hnode l.root r.root

def HTree.leaves : HTree → List State
  | .leaf s => [s]
  | .node l r => l.leaves ++ r.leaves

/-- The perfect tree at level `ℓ`, position `p`. -/
def perfect (f : ℕ → State) : ℕ → ℕ → HTree
  | 0, p => .leaf (f p)
  | ℓ + 1, p => .node (perfect f ℓ (2 * p)) (perfect f ℓ (2 * p + 1))

theorem perfect_root (f : ℕ → State) : ∀ ℓ p, (perfect f ℓ p).root = rootAt f ℓ p
  | 0, p => rfl
  | ℓ + 1, p => by simp [perfect, HTree.root, rootAt, perfect_root f ℓ]

/-- The leaves of the perfect tree at level `ℓ`, position `p` are `f` on `[2^ℓ p, 2^ℓ (p+1))`. -/
theorem perfect_leaves (f : ℕ → State) : ∀ ℓ p,
    (perfect f ℓ p).leaves = (List.range (2 ^ ℓ)).map fun i => f (2 ^ ℓ * p + i)
  | 0, p => by simp [perfect, HTree.leaves]
  | ℓ + 1, p => by
    simp only [perfect, HTree.leaves, perfect_leaves f ℓ]
    rw [pow_succ, show 2 ^ ℓ * 2 = 2 ^ ℓ + 2 ^ ℓ by ring, List.range_add, List.map_append, List.map_map]
    congr 1
    · apply List.map_congr_left; intro i _; congr 1; ring
    · apply List.map_congr_left; intro i _; simp only [Function.comp]; congr 1; ring

end StarkedAir.Spec.HeaderTree
