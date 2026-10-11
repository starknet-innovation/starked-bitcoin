/-
**The proof-of-work check, Lean-first (VL-POW).** stwo-zig's in-circuit `Channel.pow`
(`stark_verifier/channel.zig`, a port of StarkWare's `Blake2sM31Channel::verify_pow_nonce` circuit):
- `prefixed = blake2s_m31(0x12345678 ‖ digest ‖ n_bits)` over 52 bytes;
- the nonce's high coordinates are zero (`nonce .* (0, 0, 1, 1) = 0`);
- `res = blake2s_m31(prefixed ‖ nonce)` over 40 bytes; its first limb's 31 bits are extracted
  (`extract_bits`: guess the low bit, check it is a bit, subtract, halve; the last value is the top
  bit; `validate_extract_bits` forbids `1…1` as the encoding of 0), and the low `n_bits` must be zero.

`powCheckP` emits those builder calls in order (the constants where the Zig creates them, since the
builder interns constants by first use). `powCheck_sound`: if its ops hold, `Spec.powOk`: the nonce's
high coordinates are zero and the reduced hash limb is divisible by `2^n_bits`.
-/
import StarkedAir.Circuit.Channel

namespace StarkedAir.Circuit.Pow

open StarkedAir StarkedAir.Circuit Q Channel

/-! ### Spec -/

/-- The proof of work holds for state `s` and `nonce` at `nBits`: the nonce's coordinates 2 and 3 are
zero, and limb 0 of `blake2s_m31(blake2s_m31(0x12345678 ‖ digest ‖ nBits) ‖ nonce)` has its low
`nBits` bits zero. -/
def Spec.powOk (s : Channel.Spec.St) (nonce : Q) (nBits : ℕ) : Prop :=
  let pre := Channel.Spec.absorb [lit 305419896 0 0 0, s.lo, s.hi, lit nBits 0 0 0] [] 52
  let h := Channel.Spec.absorb [qOf pre 0, qOf pre 4, nonce] [] 40
  nonce.c = 0 ∧ nonce.d = 0 ∧ (h 0).val % 2 ^ nBits = 0

/-! ### Program -/

/-- `assert_bits` on a one-lane value `x` (registers `m … m+3`): `x .* x`, `x − x²`, the lane mask,
the masked difference, `= 0` (`z` is the zero register). -/
def assertBit (m x z : ℕ) : List Op :=
  [.pmul m x x, .sub (m + 1) x m, .const (m + 2) 1 0 0 0, .pmul (m + 3) (m + 1) (m + 2), .eq (m + 3) z]

/-- `1/2` in M31. -/
def INV2 : ℕ := 1073741824

/-- `k` rounds of `extract_bits` from value register `v`, registers from `n`: guess the low bit,
`assert_bits`, subtract, halve. Returns the ops, the bit registers, the last value, the next register. -/
def rounds (z inv2 : ℕ) : ℕ → ℕ → ℕ → List Op × List ℕ × ℕ × ℕ
  | 0, n, v => ([], [], v, n)
  | k + 1, n, v =>
    let r := rounds z inv2 k (n + 7) (n + 6)
    ([.guess n (.lsb (.reg v))] ++ assertBit (n + 1) n z ++ [.sub (n + 5) v n, .mul (n + 6) (n + 5) inv2] ++ r.1,
     n :: r.2.1, r.2.2.1, r.2.2.2)

/-- The proof-of-work check from register `n`; `lo`, `hi` the digest, `nonce`. -/
def powCheckP (n lo hi nonce nBits : ℕ) : List Op :=
  let z := n
  let one := n + 1
  let a1 := absorb (n + 4) [n + 2, lo, hi, n + 3] [] 52
  let m1 := a1.next
  let a2 := absorb (m1 + 2) [a1.res.1, a1.res.2, nonce] [] 40
  let m2 := a2.next
  let fw := m2
  let r := rounds z (m2 + 1) 30 (m2 + 2) fw
  let bits := r.2.1 ++ [r.2.2.1]
  let m3 := r.2.2.2
  [.zero z, .one one, .const (n + 2) 305419896 0 0 0, .const (n + 3) nBits 0 0 0] ++ a1.ops ++
  [.const m1 0 0 1 1, .pmul (m1 + 1) nonce m1, .eq (m1 + 1) z] ++ a2.ops ++
  [.unused a2.res.2, .pmul fw a2.res.1 one, .const (m2 + 1) INV2 0 0 0] ++ r.1 ++
  assertBit m3 r.2.2.1 z ++
  [.const (m3 + 4) 0 0 0 0, .const (m3 + 5) 1 1 1 1, .guess (m3 + 6) (.invOrZero (.reg fw)),
   .pmul (m3 + 7) fw (m3 + 6), .sub (m3 + 8) (m3 + 7) (m3 + 5), .pmul (m3 + 9) (m3 + 8) (bits.getD 0 0),
   .sub (m3 + 10) (m3 + 9) (m3 + 4), .const (m3 + 11) 1 0 0 0, .pmul (m3 + 12) (m3 + 10) (m3 + 11), .eq (m3 + 12) z] ++
  (bits.take nBits).map fun b => .eq b z

/-! ### Soundness -/

variable {ρ : ℕ → Q}

theorem assertBit_sound {m x z : ℕ} (h : Holds ρ (assertBit m x z)) (hz : ρ z = lit 0 0 0 0) :
    (ρ x).a = 0 ∨ (ρ x).a = 1 := by
  have g : ∀ op ∈ assertBit m x z, op.holds ρ := h
  simp only [assertBit, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at g
  obtain ⟨p0, s1, c2, p3, e⟩ := g
  simp only [Op.holds] at p0 s1 c2 p3 e
  have := congrArg Q.a (e.trans hz)
  rw [p3, s1, p0, c2] at this
  simp only [Q.sub_a, lit, Nat.cast_one, mul_one, Nat.cast_zero] at this
  have hx : (ρ x).a * ((ρ x).a - 1) = 0 := by linear_combination -this
  rcases mul_eq_zero.mp hx with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- The bits' value: `b₀ + 2·(b₁ + 2·(… + 2·t))`. -/
def fold : List F → F → F
  | [], t => t
  | b :: bs, t => b + 2 * fold bs t

theorem inv2_mul (x : F) : (x * ((INV2 : ℕ) : F)) * 2 = x := by
  have : ((INV2 : ℕ) : F) * 2 = 1 := by decide
  rw [mul_assoc, this, mul_one]

theorem mul_base_a (x : Q) (c : F) : (x * ⟨c, 0, 0, 0⟩).a = x.a * c := by
  simp [mul_eq, cmul]

theorem rounds_sound {z inv2 : ℕ} (hz : ρ z = lit 0 0 0 0) (hi : ρ inv2 = lit INV2 0 0 0) :
    ∀ k n v, Holds ρ (rounds z inv2 k n v).1 →
      (∀ b ∈ (rounds z inv2 k n v).2.1, (ρ b).a = 0 ∨ (ρ b).a = 1) ∧
      (rounds z inv2 k n v).2.1.length = k ∧
      (ρ v).a = fold ((rounds z inv2 k n v).2.1.map fun b => (ρ b).a) (ρ (rounds z inv2 k n v).2.2.1).a
  | 0, n, v, _ => by simp [rounds, fold]
  | k + 1, n, v, h => by
    simp only [rounds] at h ⊢
    rw [holds_append, holds_append, holds_append] at h
    obtain ⟨⟨⟨_, ha⟩, hs⟩, hr⟩ := h
    obtain ⟨ib, il, iv⟩ := rounds_sound hz hi k (n + 7) (n + 6) hr
    refine ⟨?_, by simp [il], ?_⟩
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact assertBit_sound ha hz
      · exact ib b hb
    · have s5 := hs _ List.mem_cons_self
      have m6 := hs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [Op.holds] at s5 m6
      rw [List.map_cons, fold, ← iv, m6, hi]
      simp only [lit, Nat.cast_zero]
      rw [mul_base_a, s5, Q.sub_a]
      linear_combination (-1 : F) * inv2_mul ((ρ v).a - (ρ n).a)

/-- Bits as a natural number, low first. -/
def nv : List ℕ → ℕ
  | [] => 0
  | b :: bs => b + 2 * nv bs

theorem fold_nv : ∀ (bs : List F) (t : F), (∀ b ∈ bs, b = 0 ∨ b = 1) → (t = 0 ∨ t = 1) →
    fold bs t = ((nv (bs.map ZMod.val ++ [t.val]) : ℕ) : F)
  | [], t, _, ht => by rcases ht with rfl | rfl <;> simp [fold, nv]
  | b :: bs, t, hb, ht => by
    rw [fold, fold_nv bs t (fun x hx => hb x (List.mem_cons_of_mem _ hx)) ht, List.map_cons, List.cons_append, nv]
    push_cast
    congr 1
    rcases hb b List.mem_cons_self with rfl | rfl <;> simp

theorem nv_lt : ∀ bs : List ℕ, (∀ b ∈ bs, b ≤ 1) → nv bs < 2 ^ bs.length
  | [], _ => by simp [nv]
  | b :: bs, h => by
    have := nv_lt bs (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have := h b List.mem_cons_self
    simp only [nv, List.length_cons, pow_succ]; omega

theorem nv_dvd : ∀ (m : ℕ) (bs : List ℕ), (∀ i < m, bs.getD i 0 = 0) → 2 ^ m ∣ nv bs
  | 0, _, _ => by simp
  | m + 1, [], _ => by simp [nv]
  | m + 1, b :: bs, h => by
    have hb : b = 0 := h 0 (by omega)
    have := nv_dvd m bs (fun i hi => h (i + 1) (by omega))
    rw [nv, hb, zero_add, pow_succ, mul_comm]
    exact Nat.mul_dvd_mul_left 2 this

theorem nv_odd : ∀ (b : ℕ) (bs : List ℕ), b ≤ 1 → nv (b :: bs) % 2 = b := by
  intro b bs hb; simp only [nv]; omega

theorem val01 {x : F} (h : x = 0 ∨ x = 1) : x.val ≤ 1 := by
  rcases h with rfl | rfl <;> decide

theorem rounds_length (z inv2 : ℕ) : ∀ k n v, (rounds z inv2 k n v).2.1.length = k
  | 0, _, _ => rfl
  | k + 1, n, v => by simp [rounds, rounds_length z inv2 k]

theorem holds_one {o : Op} {l : List Op} (h : Holds ρ l) (ho : o ∈ l) : o.holds ρ := h o ho

/-- **The proof-of-work check is sound.** If `powCheckP`'s ops hold on the digest `s` and `nBits ≤ 30`,
the proof of work holds (`Spec.powOk`). -/
theorem powCheck_sound {n lo hi nonce nBits : ℕ} {s : Channel.Spec.St} (h : Holds ρ (powCheckP n lo hi nonce nBits))
    (hl : ρ lo = s.lo) (hh : ρ hi = s.hi) (hn : nBits ≤ 30) : Spec.powOk s (ρ nonce) nBits := by
  set a1 := absorb (n + 4) [n + 2, lo, hi, n + 3] [] 52 with ha1
  set a2 := absorb (a1.next + 2) [a1.res.1, a1.res.2, nonce] [] 40 with ha2
  set r := rounds n (a2.next + 1) 30 (a2.next + 2) a2.next with hr
  set m3 := r.2.2.2 with hm3
  set bits := r.2.1 ++ [r.2.2.1] with hbits
  simp only [powCheckP] at h
  rw [← ha1, ← ha2, ← hr, ← hm3, ← hbits] at h
  rw [holds_append, holds_append, holds_append, holds_append, holds_append, holds_append, holds_append,
    holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h9⟩ := h
  -- Constants.
  have hz : ρ n = lit 0 0 0 0 := holds_one h0 (o := .zero n) (by simp)
  have hone : ρ (n + 1) = lit 1 0 0 0 := holds_one h0 (o := .one (n + 1)) (by simp)
  have hpre : ρ (n + 2) = lit 305419896 0 0 0 := holds_one h0 (o := .const (n + 2) 305419896 0 0 0) (by simp)
  have hbw : ρ (n + 3) = lit nBits 0 0 0 := holds_one h0 (o := .const (n + 3) nBits 0 0 0) (by simp)
  -- The prefixed digest.
  have e1 := absorb_sound h1 (by norm_num)
  rw [← ha1] at e1
  simp only [List.map_cons, List.map_nil, hpre, hl, hh, hbw] at e1
  -- The nonce's high coordinates.
  have cm : ρ a1.next = lit 0 0 1 1 := holds_one h2 (o := .const a1.next 0 0 1 1) (by simp)
  have pm : (Op.pmul (a1.next + 1) nonce a1.next).holds ρ := holds_one h2 (by simp)
  have em : (Op.eq (a1.next + 1) n).holds ρ := holds_one h2 (by simp)
  simp only [Op.holds] at pm em
  have hcd := congrArg (fun q : Q => (q.c, q.d)) (pm.symm.trans (em.trans hz))
  simp only [cm, lit, Nat.cast_one, Nat.cast_zero, mul_one, Prod.mk.injEq] at hcd
  -- The hash.
  have e2 := absorb_sound h3 (by norm_num)
  rw [← ha2] at e2
  simp only [List.map_cons, List.map_nil, e1.1, e1.2] at e2
  have pf : (Op.pmul a2.next a2.res.1 (n + 1)).holds ρ := holds_one h4 (by simp)
  have ci : ρ (a2.next + 1) = lit INV2 0 0 0 := holds_one h4 (o := .const (a2.next + 1) INV2 0 0 0) (by simp)
  simp only [Op.holds] at pf
  have hfw : (ρ a2.next).a = Channel.Spec.absorb [qOf (Channel.Spec.absorb [lit 305419896 0 0 0, s.lo, s.hi,
      lit nBits 0 0 0] [] 52) 0, qOf (Channel.Spec.absorb [lit 305419896 0 0 0, s.lo, s.hi, lit nBits 0 0 0] [] 52) 4,
      ρ nonce] [] 40 0 := by
    rw [pf, e2.1, hone]; simp [qOf, lit]
  -- The bits.
  obtain ⟨rb, rl, rv⟩ := rounds_sound hz ci 30 (a2.next + 2) a2.next h5
  rw [← hr] at rb rl rv
  have hlast := assertBit_sound h6 hz
  have hb01 : ∀ b ∈ bits, (ρ b).a = 0 ∨ (ρ b).a = 1 := by
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact rb b hb
    · rw [List.mem_singleton.mp hb]; exact hlast
  set Bn := bits.map fun b => (ρ b).a.val with hBn
  have hval : (ρ a2.next).a = ((nv Bn : ℕ) : F) := by
    rw [rv, fold_nv _ _ (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx; exact rb b hb) hlast]
    congr 2
  have hlen : Bn.length = 31 := by simp [hBn, hbits, rl]
  have hlt : nv Bn < 2 ^ 31 := by
    have := nv_lt Bn (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx; exact val01 (hb01 b hb))
    rwa [hlen] at this
  -- `validate_extract_bits`: the value 0 has low bit 0.
  obtain ⟨b0, rest, hr0⟩ : ∃ b0 rest, r.2.1 = b0 :: rest := by
    rcases hrr : r.2.1 with _ | ⟨b0, rest⟩
    · rw [hrr] at rl; simp at rl
    · exact ⟨b0, rest, rfl⟩
  have hg0 : bits.getD 0 0 = b0 := by simp [hbits, hr0]
  rw [hg0] at h7
  have v1 : ρ (m3 + 5) = lit 1 1 1 1 := holds_one h7 (o := .const (m3 + 5) 1 1 1 1) (by simp)
  have v0 : ρ (m3 + 4) = lit 0 0 0 0 := holds_one h7 (o := .const (m3 + 4) 0 0 0 0) (by simp)
  have vk : ρ (m3 + 11) = lit 1 0 0 0 := holds_one h7 (o := .const (m3 + 11) 1 0 0 0) (by simp)
  have p7 : (Op.pmul (m3 + 7) a2.next (m3 + 6)).holds ρ := holds_one h7 (by simp)
  have s8 : (Op.sub (m3 + 8) (m3 + 7) (m3 + 5)).holds ρ := holds_one h7 (by simp)
  have p9 : (Op.pmul (m3 + 9) (m3 + 8) b0).holds ρ := holds_one h7 (by simp)
  have s10 : (Op.sub (m3 + 10) (m3 + 9) (m3 + 4)).holds ρ := holds_one h7 (by simp)
  have p12 : (Op.pmul (m3 + 12) (m3 + 10) (m3 + 11)).holds ρ := holds_one h7 (by simp)
  have e12 : (Op.eq (m3 + 12) n).holds ρ := holds_one h7 (by simp)
  simp only [Op.holds] at p7 s8 p9 s10 p12 e12
  have hv := congrArg Q.a (e12.trans hz)
  rw [p12, s10, p9, s8, p7, v1, v0, vk] at hv
  simp only [Q.sub_a, lit, Nat.cast_one, Nat.cast_zero, mul_one, sub_zero] at hv
  have hnP : nv Bn ≠ P := by
    intro hP
    have h0F : (ρ a2.next).a = 0 := by rw [hval, hP]; exact ZMod.natCast_self P
    rw [h0F, zero_mul, zero_sub, neg_one_mul, neg_eq_zero] at hv
    have hB0 : Bn = (ρ b0).a.val :: (rest ++ [r.2.2.1]).map (fun b => (ρ b).a.val) := by
      simp [hBn, hbits, hr0]
    have := nv_odd ((ρ b0).a.val) ((rest ++ [r.2.2.1]).map (fun b => (ρ b).a.val))
      (val01 (hb01 b0 (by simp [hbits, hr0])))
    rw [← hB0, hP, hv, ZMod.val_zero] at this
    exact absurd this (by unfold P; norm_num)
  have hlt' : nv Bn < P := by unfold P; unfold P at hnP; omega
  have hfv : (ρ a2.next).a.val = nv Bn := by rw [hval]; exact ZMod.val_natCast_of_lt hlt'
  -- The low bits are zero.
  have hzero : ∀ i < nBits, Bn.getD i 0 = 0 := by
    intro i hi
    have hib : i < bits.length := by simp [hbits, rl]; omega
    have he : (Op.eq (bits[i]) n).holds ρ := holds_one h9 (by
      simp only [List.mem_map]
      exact ⟨bits[i], List.mem_iff_getElem.mpr ⟨i, by simp; omega, by simp⟩, rfl⟩)
    simp only [Op.holds] at he
    rw [List.getD_eq_getElem _ _ (by simp [hBn]; omega), List.getElem_map, he, hz]
    rfl
  refine ⟨hcd.1, hcd.2, ?_⟩
  rw [← hfw, hfv]
  exact Nat.mod_eq_zero_of_dvd (nv_dvd nBits Bn hzero)

end StarkedAir.Circuit.Pow

namespace StarkedAir.Circuit.Pow

/-- The exported check at `nBits`: hook 0 binds the digest halves and the nonce. -/
def powJson (nBits : ℕ) : String :=
  let ops := [Op.hook 0 [] [0, 1, 2]] ++ powCheckP 3 0 1 2 nBits
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[]}"

end StarkedAir.Circuit.Pow
