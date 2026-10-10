/-
**The Fiat–Shamir channel, Lean-first (VERIFIER-LEAN step 5).** stwo-zig's in-circuit channel
(`stark_verifier/channel.zig`, a port of StarkWare's `Blake2sM31Channel` with
`Blake2sM31MerkleChannel::mix_hash`). Its digest is two QM31 wires holding eight M31 limbs (the eight
digest words reduced mod P). Every operation absorbs `digest ‖ data` with Blake2s and reduces:

- `mix_u32s(v)`, `mix_commitment(root)`: Blake2s of the digest's eight words and the u32 words;
- `mix_qm31s(v)`: Blake2s of the digest's and the values' coordinates as words (16 bytes each);
- `draw_two_qm31s`: Blake2s of the digest's words and `n_draws, 0, 0, 0` over 37 bytes (the zero byte
  separates drawing from mixing one u32); `draw_qm31` keeps the first;
- `draw_point`: `((1 − t²)/(1 + t²), 2t/(1 + t²))` of a drawn `t`;
- after the proof of work, the digest absorbs the nonce (40 bytes).

`absorb` emits stwo-zig's builder calls for all of the hash-based operations (unpack the QM31 inputs
into words, Blake2s, `reduceHashValue`); `absorb_sound`: the new digest is `Spec.absorb` of the old one
and the data. `point_sound`: the drawn point's coordinates. The proof-of-work *check* (the hash's low
bits are zero) stays stwo-zig's: it only enforces the grinding bits, not what the transcript binds.
-/
import StarkedAir.Circuit.BlakeSound
import StarkedAir.Circuit.Composition

namespace StarkedAir.Circuit.Channel

open StarkedAir StarkedAir.Circuit Spec.Blake2s Q
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub)

/-! ### Spec -/

/-- A canonical M31 as a message word. -/
def fw (x : F) : Word := BitVec.ofNat 32 x.val

/-- A QM31 value's four coordinates as message words. -/
def qWords (x : Q) : List Word := [fw x.a, fw x.b, fw x.c, fw x.d]

/-- The QM31 of four limbs. -/
def qOf (l : ℕ → F) (o : ℕ) : Q := ⟨l o, l (o + 1), l (o + 2), l (o + 3)⟩

/-- `reduceHashValue`: each digest word mod P. -/
def reduce (h : ℕ → Word) (k : ℕ) : F := ((h k).toNat : F)

namespace Spec

/-- The digest after absorbing the QM31 values `xs` (unpacked to words), then the u32 words `vs`, over
`nBytes` bytes: limb `k` of the reduced Blake2s. -/
def absorb (xs : List Q) (vs : List Word) (nBytes : ℕ) : ℕ → F :=
  reduce (blake2sWords (xs.flatMap qWords ++ vs) nBytes)

/-- The channel state: the digest as its two QM31 halves, and the draws since the last mix. -/
structure St where
  lo : Q
  hi : Q
  nDraws : ℕ

def ofLimbs (l : ℕ → F) (nDraws : ℕ) : St := ⟨qOf l 0, qOf l 4, nDraws⟩

def mixU32s (s : St) (vs : List Word) : St := ofLimbs (absorb [s.lo, s.hi] vs (4 * (8 + vs.length))) 0
def mixCommitment (s : St) (root : List Word) : St := ofLimbs (absorb [s.lo, s.hi] root 64) 0
def mixQm31s (s : St) (xs : List Q) : St := ofLimbs (absorb ([s.lo, s.hi] ++ xs) [] (16 * (2 + xs.length))) 0
/-- `draw_two_qm31s` (both halves) and the state after it. -/
def drawTwo (s : St) : Q × Q × St :=
  let l := absorb [s.lo, s.hi, lit s.nDraws 0 0 0] [] 37
  (qOf l 0, qOf l 4, { s with nDraws := s.nDraws + 1 })
def powMix (s : St) (nonce : Q) : St := ofLimbs (absorb [s.lo, s.hi, nonce] [] 40) 0

end Spec

/-! ### Programs -/

/-- `unpack_idx` of each coordinate then `m31_to_u32` (`unpackQm31sToU32Words` of one wire). The unit
vectors' inverses: `i⁻¹ = −i`, `u⁻¹ = (2 − i)/5 · u`, `(iu)⁻¹ = −i · u⁻¹`. -/
def unpack1 (n x : ℕ) : Out (List ℕ) :=
  ⟨[.const n 1 0 0 0, .pmul (n + 1) x n, .m2u (n + 2) (n + 1),
    .const (n + 3) 0 1 0 0, .pmul (n + 4) x (n + 3), .const (n + 5) 0 2147483646 0 0, .mul (n + 6) (n + 4) (n + 5), .m2u (n + 7) (n + 6),
    .const (n + 8) 0 0 1 0, .pmul (n + 9) x (n + 8), .const (n + 10) 0 0 1717986918 1288490188, .mul (n + 11) (n + 9) (n + 10), .m2u (n + 12) (n + 11),
    .const (n + 13) 0 0 0 1, .pmul (n + 14) x (n + 13), .const (n + 15) 0 0 1288490188 429496729, .mul (n + 16) (n + 14) (n + 15), .m2u (n + 17) (n + 16)],
   [n + 2, n + 7, n + 12, n + 17], n + 18⟩

def unpack : ℕ → List ℕ → Out (List ℕ)
  | n, [] => ⟨[], [], n⟩
  | n, x :: xs => let a := unpack1 n x; let b := unpack a.next xs; ⟨a.ops ++ b.ops, a.res ++ b.res, b.next⟩

/-- One word's reduction from `m` (`two16` the constant `2^16`): low lane, high lane, `low + high·2^16`. -/
def redWord (m w two16 : ℕ) : List Op :=
  [.const m 1 0 0 0, .pmul (m + 1) w m, .const (m + 2) 0 1 0 0, .pmul (m + 3) w (m + 2),
   .const (m + 4) 0 2147483646 0 0, .mul (m + 5) (m + 3) (m + 4), .mul (m + 6) (m + 5) two16, .add (m + 7) (m + 1) (m + 6)]

/-- `from_partial_evals(v0, v1, v2, v3)` from `q`: `((v0 + v1·i) + v2·u) + v3·iu`. -/
def fpe (q v0 v1 v2 v3 : ℕ) : List Op :=
  [.const q 0 1 0 0, .const (q + 1) 0 0 1 0, .const (q + 2) 0 0 0 1,
   .mul (q + 3) v1 q, .add (q + 4) v0 (q + 3), .mul (q + 5) v2 (q + 1), .add (q + 6) (q + 4) (q + 5),
   .mul (q + 7) v3 (q + 2), .add (q + 8) (q + 6) (q + 7)]

/-- `reduceHashValue`: the result `(low, high)` registers. -/
def reduceOps (n : ℕ) (ws : List ℕ) : Out (ℕ × ℕ) :=
  let w := fun k => n + 8 + 8 * k
  ⟨.const n 65536 0 0 0 :: (List.range 8).flatMap (fun k => redWord (n + 1 + 8 * k) (ws.getD k 0) n) ++
    fpe (n + 65) (w 0) (w 1) (w 2) (w 3) ++ fpe (n + 74) (w 4) (w 5) (w 6) (w 7),
   (n + 73, n + 82), n + 83⟩

/-- Absorb: unpack the QM31 inputs `xs`, Blake2s of their words then the u32 words `vs`, reduce. -/
def absorb (n : ℕ) (xs vs : List ℕ) (nBytes : ℕ) : Out (ℕ × ℕ) :=
  let u := unpack n xs
  let h := blake2s u.next (u.res ++ vs) nBytes
  let r := reduceOps h.next h.res
  ⟨u.ops ++ h.ops ++ r.ops, r.res, r.next⟩

/-- `draw_point` from the drawn `t`. -/
def pointOps (n t : ℕ) : Out (ℕ × ℕ) :=
  ⟨[.mul n t t, .const (n + 1) 1 0 0 0, .add (n + 2) n (n + 1), .inv (n + 3) (n + 2), .const (n + 4) 1 0 0 0,
    .sub (n + 5) (n + 4) n, .mul (n + 6) (n + 5) (n + 3), .const (n + 7) 2 0 0 0, .mul (n + 8) (n + 7) t,
    .mul (n + 9) (n + 8) (n + 3)], (n + 6, n + 9), n + 10⟩

/-! ### Soundness -/

variable {ρ : ℕ → Q}

theorem F_m1 : ((2147483646 : ℕ) : F) = -1 := by decide
theorem F_u1 : 2 * ((1717986918 : ℕ) : F) - ((1288490188 : ℕ) : F) = 1 := by decide
theorem F_u2 : 2 * ((1288490188 : ℕ) : F) + ((1717986918 : ℕ) : F) = 0 := by decide
theorem F_iu1 : 2 * ((429496729 : ℕ) : F) + ((1288490188 : ℕ) : F) = -1 := by decide
theorem F_iu2 : 2 * ((1288490188 : ℕ) : F) - ((429496729 : ℕ) : F) = 0 := by decide

theorem mul_eq (x y : Q) : x * y =
    ⟨(cmul x.a x.b y.a y.b).1 + (cmul 2 1 (cmul x.c x.d y.c y.d).1 (cmul x.c x.d y.c y.d).2).1,
     (cmul x.a x.b y.a y.b).2 + (cmul 2 1 (cmul x.c x.d y.c y.d).1 (cmul x.c x.d y.c y.d).2).2,
     (cmul x.a x.b y.c y.d).1 + (cmul x.c x.d y.a y.b).1, (cmul x.a x.b y.c y.d).2 + (cmul x.c x.d y.a y.b).2⟩ := rfl

/-- Unpacking one wire: the four words are its coordinates. -/
theorem unpack1_sound {n x : ℕ} (h : Holds ρ (unpack1 n x).ops) :
    (unpack1 n x).res.map (word ∘ ρ) = qWords (ρ x) := by
  have g : ∀ op ∈ (unpack1 n x).ops, op.holds ρ := h
  simp only [unpack1, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨c0, p0, m0, c1, p1, i1, x1, m1, c2, p2, i2, x2, m2, c3, p3, i3, x3, m3⟩ := g
  simp only [Op.holds] at *
  simp only [unpack1, List.map_cons, List.map_nil, Function.comp, qWords]
  rw [m0.2, m1.2, m2.2, m3.2, word_m2u, word_m2u, word_m2u, word_m2u, x1, x2, x3, p0, p1, p2, p3, c0, c1, c2, c3, i1, i2, i3]
  simp only [mul_eq, lit, cmul, fw]
  simp only [Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, zero_mul, sub_zero, add_zero, zero_add, zero_sub]
  simp only [List.cons.injEq, and_true]
  refine ⟨trivial, ?_, ?_, ?_⟩
  · rw [F_m1]; ring_nf
  · congr 2
    linear_combination (ρ x).c * F_u1
  · congr 2
    linear_combination (-(ρ x).d) * F_iu1

theorem unpack_sound : ∀ {n : ℕ} {xs : List ℕ}, Holds ρ (unpack n xs).ops →
    (unpack n xs).res.map (word ∘ ρ) = xs.flatMap (qWords ∘ ρ)
  | _, [], _ => rfl
  | n, x :: xs, h => by
    simp only [unpack] at h ⊢
    rw [holds_append] at h
    rw [List.map_append, unpack1_sound h.1, unpack_sound h.2, List.flatMap_cons]
    rfl

theorem redWord_sound {m w two16 : ℕ} {W : Word} (h : Holds ρ (redWord m w two16)) (ht : ρ two16 = lit 65536 0 0 0)
    (hw : ρ w = pack W) : ρ (m + 7) = ⟨(W.toNat : F), 0, 0, 0⟩ := by
  have g : ∀ op ∈ redWord m w two16, op.holds ρ := h
  simp only [redWord, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨c0, p1, c2, p3, c4, m5, m6, a7⟩ := g
  simp only [Op.holds] at *
  rw [a7, m6, m5, p3, p1, c0, c2, c4, ht, hw]
  simp only [mul_eq, lit, cmul, pack]
  ext <;> simp only [Q.add_a, Q.add_b, Q.add_c, Q.add_d, Nat.cast_one, Nat.cast_zero, mul_one, mul_zero, zero_mul,
    sub_zero, add_zero, zero_sub, sub_self]
  · rw [F_m1]
    have := Nat.mod_add_div W.toNat 65536
    calc ((W.toNat % 65536 : ℕ) : F) + -(((W.toNat / 65536 : ℕ) : F) * -1) * ((65536 : ℕ) : F)
        = ((W.toNat % 65536 + 65536 * (W.toNat / 65536) : ℕ) : F) := by push_cast; ring
      _ = (W.toNat : F) := by rw [this]

theorem fpe_sound {q v0 v1 v2 v3 : ℕ} {f0 f1 f2 f3 : F} (h : Holds ρ (fpe q v0 v1 v2 v3))
    (h0 : ρ v0 = ⟨f0, 0, 0, 0⟩) (h1 : ρ v1 = ⟨f1, 0, 0, 0⟩) (h2 : ρ v2 = ⟨f2, 0, 0, 0⟩) (h3 : ρ v3 = ⟨f3, 0, 0, 0⟩) :
    ρ (q + 8) = ⟨f0, f1, f2, f3⟩ := by
  have g : ∀ op ∈ fpe q v0 v1 v2 v3, op.holds ρ := h
  simp only [fpe, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨ci, cu, ciu, m3, a4, m5, a6, m7, a8⟩ := g
  simp only [Op.holds] at *
  rw [a8, m7, a6, m5, a4, m3, ci, cu, ciu, h0, h1, h2, h3]
  simp only [mul_eq, lit, cmul]
  ext <;> simp

theorem reduce_sound {n : ℕ} {ws : List ℕ} {W : ℕ → Word} (h : Holds ρ (reduceOps n ws).ops)
    (hw : ∀ k < 8, ρ (ws.getD k 0) = pack (W k)) :
    ρ (reduceOps n ws).res.1 = qOf (reduce W) 0 ∧ ρ (reduceOps n ws).res.2 = qOf (reduce W) 4 := by
  simp only [reduceOps] at h ⊢
  rw [List.cons_append, List.cons_append] at h
  have ht : ρ n = lit 65536 0 0 0 := by have := h _ List.mem_cons_self; simpa [Op.holds] using this
  have hr : Holds ρ _ := fun op hop => h op (List.mem_cons_of_mem _ hop)
  rw [holds_append, holds_append] at hr
  obtain ⟨⟨hws, hf1⟩, hf2⟩ := hr
  have hk : ∀ k < 8, ρ (n + 8 + 8 * k) = ⟨reduce W k, 0, 0, 0⟩ := by
    intro k hk8
    have := redWord_sound (m := n + 1 + 8 * k) (fun op hop => hws op (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk8, hop⟩)) ht (hw k hk8)
    rw [show n + 1 + 8 * k + 7 = n + 8 + 8 * k by omega] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [show n + 73 = n + 65 + 8 by omega, fpe_sound hf1 (hk 0 (by omega)) (hk 1 (by omega)) (hk 2 (by omega)) (hk 3 (by omega))]
    rfl
  · rw [show n + 82 = n + 74 + 8 by omega, fpe_sound hf2 (hk 4 (by omega)) (hk 5 (by omega)) (hk 6 (by omega)) (hk 7 (by omega))]
    rfl

/-- **Absorbing is sound.** The new digest halves are `Spec.absorb` of the QM31 inputs (their
coordinates as words) and the u32 words. -/
theorem absorb_sound {n : ℕ} {xs vs : List ℕ} {nBytes : ℕ} (h : Holds ρ (absorb n xs vs nBytes).ops) (hB : nBytes < 2 ^ 32) :
    ρ (absorb n xs vs nBytes).res.1 = qOf (Spec.absorb (xs.map ρ) (vs.map (word ∘ ρ)) nBytes) 0 ∧
      ρ (absorb n xs vs nBytes).res.2 = qOf (Spec.absorb (xs.map ρ) (vs.map (word ∘ ρ)) nBytes) 4 := by
  simp only [absorb] at h ⊢
  rw [holds_append, holds_append] at h
  obtain ⟨⟨hu, hh⟩, hr⟩ := h
  have hw := blake2s_words hh hB
  have hp := blake2s_res_pack hh
  have hmsg : (List.map (word ∘ ρ) ((unpack n xs).res ++ vs)) = (xs.map ρ).flatMap qWords ++ vs.map (word ∘ ρ) := by
    rw [List.map_append, unpack_sound hu, List.flatMap_map]; rfl
  rw [hmsg] at hw
  have := reduce_sound (W := blake2sWords ((xs.map ρ).flatMap qWords ++ vs.map (word ∘ ρ)) nBytes) hr
    (fun k hk => by rw [hp k hk, hw k hk])
  exact this

/-! ### The channel operations -/

/-- `mix_u32s(vs)` (and `mix_commitment`, eight words). -/
def mixU32sP (n lo hi : ℕ) (vs : List ℕ) : Out (ℕ × ℕ) := absorb n [lo, hi] vs (4 * (8 + vs.length))
/-- `mix_qm31s(xs)`. -/
def mixQm31sP (n lo hi : ℕ) (xs : List ℕ) : Out (ℕ × ℕ) := absorb n ([lo, hi] ++ xs) [] (16 * (2 + xs.length))
/-- `draw_two_qm31s` right after a mix (`n_draws = 0`). -/
def drawP (n lo hi : ℕ) : Out (ℕ × ℕ) :=
  let a := absorb (n + 1) [lo, hi, n] [] 37
  ⟨.const n 0 0 0 0 :: a.ops, a.res, a.next⟩
/-- `draw_qm31`: the first half; the second is marked unused. -/
def drawQm31P (n lo hi : ℕ) : Out ℕ :=
  let d := drawP n lo hi
  ⟨d.ops ++ [.unused d.res.2], d.res.1, d.next⟩
/-- `draw_point`. -/
def drawPointP (n lo hi : ℕ) : Out (ℕ × ℕ) :=
  let d := drawQm31P n lo hi
  let p := pointOps d.next d.res
  ⟨d.ops ++ p.ops, p.res, p.next⟩
/-- The digest update after the proof of work: absorb the nonce. -/
def powMixP (n lo hi nonce : ℕ) : Out (ℕ × ℕ) := absorb n [lo, hi, nonce] [] 40

variable {s : Spec.St}

theorem mixU32s_sound {n lo hi : ℕ} {vs : List ℕ} (h : Holds ρ (mixU32sP n lo hi vs).ops) (hB : 4 * (8 + vs.length) < 2 ^ 32)
    (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) :
    ρ (mixU32sP n lo hi vs).res.1 = (Spec.mixU32s s (vs.map (word ∘ ρ))).lo ∧
      ρ (mixU32sP n lo hi vs).res.2 = (Spec.mixU32s s (vs.map (word ∘ ρ))).hi := by
  simp only [mixU32sP] at h ⊢
  have := absorb_sound h hB
  simp only [List.map_cons, List.map_nil, hl, hh] at this
  simpa [Spec.mixU32s, Spec.ofLimbs, List.length_map] using this

theorem mixQm31s_sound {n lo hi : ℕ} {xs : List ℕ} (h : Holds ρ (mixQm31sP n lo hi xs).ops) (hB : 16 * (2 + xs.length) < 2 ^ 32)
    (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) :
    ρ (mixQm31sP n lo hi xs).res.1 = (Spec.mixQm31s s (xs.map ρ)).lo ∧
      ρ (mixQm31sP n lo hi xs).res.2 = (Spec.mixQm31s s (xs.map ρ)).hi := by
  simp only [mixQm31sP] at h ⊢
  have := absorb_sound h hB
  simp only [List.map_append, List.map_cons, List.map_nil, hl, hh] at this
  simpa [Spec.mixQm31s, Spec.ofLimbs, List.length_map] using this

theorem draw_sound {n lo hi : ℕ} (h : Holds ρ (drawP n lo hi).ops) (h0 : s.nDraws = 0) (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) :
    ρ (drawP n lo hi).res.1 = (Spec.drawTwo s).1 ∧ ρ (drawP n lo hi).res.2 = (Spec.drawTwo s).2.1 := by
  simp only [drawP] at h ⊢
  have hc : ρ n = lit s.nDraws 0 0 0 := by
    have := h _ List.mem_cons_self; simp only [Op.holds] at this; rw [this, h0]
  have := absorb_sound (fun op hop => h op (List.mem_cons_of_mem _ hop)) (by norm_num)
  simp only [List.map_cons, List.map_nil, hl, hh, hc] at this
  simpa [Spec.drawTwo] using this

theorem drawQm31_sound {n lo hi : ℕ} (h : Holds ρ (drawQm31P n lo hi).ops) (h0 : s.nDraws = 0) (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) :
    ρ (drawQm31P n lo hi).res = (Spec.drawTwo s).1 := by
  simp only [drawQm31P] at h ⊢
  rw [holds_append] at h
  exact (draw_sound h.1 h0 hl hh).1

theorem point_sound {n t : ℕ} (h : Holds ρ (pointOps n t).ops) :
    1 + toQ (ρ t) ^ 2 ≠ 0 ∧
      toQ (ρ (pointOps n t).res.1) = (1 - toQ (ρ t) ^ 2) / (1 + toQ (ρ t) ^ 2) ∧
      toQ (ρ (pointOps n t).res.2) = 2 * toQ (ρ t) / (1 + toQ (ρ t) ^ 2) := by
  have g : ∀ op ∈ (pointOps n t).ops, op.holds ρ := h
  simp only [pointOps, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨m0, c1, a2, i3, c4, s5, m6, c7, m8, m9⟩ := g
  simp only [Op.holds] at *
  have e1 : toQ (ρ (n + 1)) = 1 := by rw [c1]; exact StarkedAir.Circuit.Composition.toQ_lit1
  have e4 : toQ (ρ (n + 4)) = 1 := by rw [c4]; exact StarkedAir.Circuit.Composition.toQ_lit1
  have e7 : toQ (ρ (n + 7)) = 2 := by
    rw [c7, StarkedAir.Circuit.Composition.toQ_lit]; simp [emb]; rfl
  have eden : toQ (ρ (n + 2)) = 1 + toQ (ρ t) ^ 2 := by rw [a2, toQ_add, m0, toQ_mul, e1]; ring
  have einv : toQ (ρ (n + 2)) * toQ (ρ (n + 3)) = 1 := by
    rw [← toQ_mul, i3, StarkedAir.Circuit.Composition.toQ_lit1]
  have hne : toQ (ρ (n + 2)) ≠ 0 := by intro z; rw [z, zero_mul] at einv; exact zero_ne_one einv
  have hinv : toQ (ρ (n + 3)) = (toQ (ρ (n + 2)))⁻¹ := eq_inv_of_mul_eq_one_right einv
  refine ⟨eden ▸ hne, ?_, ?_⟩
  · simp only [pointOps]
    rw [m6, toQ_mul, s5, toQ_sub, e4, m0, toQ_mul, hinv, eden, div_eq_mul_inv]; ring
  · simp only [pointOps]
    rw [m9, toQ_mul, m8, toQ_mul, e7, hinv, eden, div_eq_mul_inv]

theorem drawPoint_sound {n lo hi : ℕ} (h : Holds ρ (drawPointP n lo hi).ops) (h0 : s.nDraws = 0) (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) :
    let T := toQ (Spec.drawTwo s).1
    1 + T ^ 2 ≠ 0 ∧ toQ (ρ (drawPointP n lo hi).res.1) = (1 - T ^ 2) / (1 + T ^ 2) ∧
      toQ (ρ (drawPointP n lo hi).res.2) = 2 * T / (1 + T ^ 2) := by
  simp only [drawPointP] at h ⊢
  rw [holds_append] at h
  have ht := drawQm31_sound h.1 h0 hl hh
  have := point_sound h.2
  rw [ht] at this
  exact this

theorem powMix_sound {n lo hi nonce : ℕ} (h : Holds ρ (powMixP n lo hi nonce).ops) (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) :
    ρ (powMixP n lo hi nonce).res.1 = (Spec.powMix s (ρ nonce)).lo ∧
      ρ (powMixP n lo hi nonce).res.2 = (Spec.powMix s (ρ nonce)).hi := by
  simp only [powMixP] at h ⊢
  have := absorb_sound h (by norm_num)
  simp only [List.map_cons, List.map_nil, hl, hh] at this
  simpa [Spec.powMix, Spec.ofLimbs] using this

end StarkedAir.Circuit.Channel

namespace StarkedAir.Circuit.Channel

/-- An exported channel operation: hook 0 binds the digest halves then `nIn` inputs. -/
def opJson (nIn : ℕ) (body : ℕ → Out (List ℕ)) : String :=
  let o := body (2 + nIn)
  let ops := [Op.hook 0 [] (List.range (2 + nIn))] ++ o.ops
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[{",".intercalate (o.res.map toString)}]}"

def pair (o : Out (ℕ × ℕ)) : Out (List ℕ) := ⟨o.ops, [o.res.1, o.res.2], o.next⟩

def channelJson : List String → Option String
  | ["mix_u32s", k] => let k := k.toNat!; some (opJson k fun n => pair (mixU32sP n 0 1 ((List.range k).map (2 + ·))))
  | ["mix_qm31s", k] => let k := k.toNat!; some (opJson k fun n => pair (mixQm31sP n 0 1 ((List.range k).map (2 + ·))))
  | ["draw"] => some (opJson 0 fun n => pair (drawP n 0 1))
  | ["draw_qm31"] => some (opJson 0 fun n => let o := drawQm31P n 0 1; ⟨o.ops, [o.res], o.next⟩)
  | ["draw_point"] => some (opJson 0 fun n => pair (drawPointP n 0 1))
  | ["pow_mix"] => some (opJson 1 fun n => pair (powMixP n 0 1 2))
  | _ => none

end StarkedAir.Circuit.Channel
