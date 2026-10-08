/-
**The in-circuit Blake2s gadget computes Blake2s.** If the ops of `blake2s n msg nBytes` hold, its
result wires hold `hashW` (word-level Blake2s, below) of the message wires' words.
-/
import StarkedAir.Circuit.Gadgets

namespace StarkedAir.Circuit

open StarkedAir Spec.Blake2s

/-- **Word-level Blake2s**, as `blake2sU32s` computes it: message words `m` (little-endian
bytes), `nBytes` bytes, zero-padded to whole blocks; the chaining value after `b` blocks (a list,
so evaluation does not recompute earlier blocks). -/
def hashWL (m : ℕ → Word) (nBytes : ℕ) : ℕ → List Word
  | 0 => (List.range 8).map h0
  | b + 1 =>
    let h := hashWL m nBytes b
    (List.range 8).map (compress (fun i => h.getD i 0) (fun j => m (16 * b + j)) (min nBytes (64 * (b + 1)))
      (decide (b + 1 = nBlocks nBytes)))

def hashW (m : ℕ → Word) (nBytes b i : ℕ) : Word := (hashWL m nBytes b).getD i 0

theorem hashW_zero {m : ℕ → Word} {nBytes i : ℕ} (hi : i < 8) : hashW m nBytes 0 i = h0 i := by
  simp [hashW, hashWL, List.getElem?_range hi]

theorem hashW_succ {m : ℕ → Word} {nBytes b i : ℕ} (hi : i < 8) :
    hashW m nBytes (b + 1) i = compress (hashW m nBytes b) (fun j => m (16 * b + j)) (min nBytes (64 * (b + 1)))
      (decide (b + 1 = nBlocks nBytes)) i := by
  unfold hashW
  rw [hashWL, List.getD_eq_getElem _ _ (by simpa using hi)]
  simp

/-- The digest of word list `ws` over `nBytes` bytes. -/
def blake2sWords (ws : List Word) (nBytes : ℕ) : ℕ → Word := hashW (fun j => ws.getD j 0) nBytes (nBlocks nBytes)

/-- Little-endian bytes of words. -/
def wordBytes (ws : List Word) : List UInt8 :=
  ws.flatMap fun w => (List.range 4).map fun j => UInt8.ofNat (w.toNat / 2 ^ (8 * j))

-- The word-level hash agrees with the byte-level one (hashlib-tested) on the gadget's sizes.
private def testWords (n : ℕ) : List Word := (List.range n).map fun i => BitVec.ofNat 32 (0x9E3779B9 * (i + 1) + 12345)
#guard digest (blake2sWords (testWords 16) 64) == Spec.Blake2s.blake2s (wordBytes (testWords 16))
#guard digest (blake2sWords (testWords 32) 128) == Spec.Blake2s.blake2s (wordBytes (testWords 32))
#guard digest (blake2sWords (testWords 132) 528) == Spec.Blake2s.blake2s (wordBytes (testWords 132))

/-! ### Wires -/

namespace Q

theorem val_cast {a : ℕ} (h : a < P) : ((a : F)).val = a := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt h]

theorem word_lit {w : ℕ} (hw : w < 2 ^ 32) : word (lit (w % 65536) (w / 65536) 0 0) = BitVec.ofNat 32 w := by
  unfold word lit
  dsimp only
  rw [val_cast (by unfold P; omega), val_cast (by unfold P; omega), Nat.mod_add_div]

theorem word_pack (w : Word) : word (pack w) = w := by
  have := w.isLt
  unfold pack
  rw [show (⟨((w.toNat % 65536 : ℕ) : F), ((w.toNat / 65536 : ℕ) : F), 0, 0⟩ : Q) =
    lit (w.toNat % 65536) (w.toNat / 65536) 0 0 from rfl, word_lit this]
  exact BitVec.eq_of_toNat_eq (by simp)

end Q

open Q

/-! ### G steps -/

/-- The words of 16 state wires. -/
def vW (ρ : ℕ → Q) (st : ℕ → ℕ) : List Word := (List.range 16).map fun j => word (ρ (st j))

theorem vW_getD {ρ : ℕ → Q} {st : ℕ → ℕ} {j : ℕ} (hj : j < 16) : (vW ρ st).getD j 0 = word (ρ (st j)) := by
  unfold vW; rw [List.getD_eq_getElem _ _ (by simpa using hj)]; simp

theorem gIdx_spec {g : ℕ} (hg : g < 8) :
    (gIdx g).1 < 16 ∧ (gIdx g).2.1 < 16 ∧ (gIdx g).2.2.1 < 16 ∧ (gIdx g).2.2.2 < 16 ∧
    (gIdx g).1 ≠ (gIdx g).2.1 ∧ (gIdx g).1 ≠ (gIdx g).2.2.1 ∧ (gIdx g).1 ≠ (gIdx g).2.2.2 ∧
    (gIdx g).2.1 ≠ (gIdx g).2.2.1 ∧ (gIdx g).2.1 ≠ (gIdx g).2.2.2 ∧ (gIdx g).2.2.1 ≠ (gIdx g).2.2.2 := by
  interval_cases g <;> decide

theorem gStep_regs {ρ : ℕ → Q} {st0 : ℕ → ℕ} {g0 : ℕ} {msg : ℕ → ℕ} {k : ℕ}
    (hg : (gOp st0 g0 msg k).holds ρ) :
    vW ρ (gState st0 g0 (k + 1)) = gStep (fun j => word (ρ (msg j))) (vW ρ (gState st0 g0 k)) (k / 8) (k % 8) := by
  have hspec := gIdx_spec (g := k % 8) (Nat.mod_lt _ (by norm_num))
  unfold gOp at hg
  simp only [gState, gStep] at hg ⊢
  generalize gIdx (k % 8) = q at hg hspec ⊢
  obtain ⟨ia, ib, ic, id⟩ := q
  obtain ⟨la, lb, lc, ld, nab, nac, nad, nbc, nbd, ncd⟩ := hspec
  simp only [Op.holds] at hg
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4⟩ := hg
  simp only at la lb lc ld nab nac nad nbc nbd ncd h1 h2 h3 h4 ⊢
  rw [vW_getD la, vW_getD lb, vW_getD lc, vW_getD ld]
  apply List.ext_getElem (by simp [vW])
  intro j hj _
  simp only [vW, List.length_map, List.length_range] at hj
  simp only [vW, List.getElem_set, List.getElem_map, List.getElem_range]
  by_cases ja : j = ia
  · subst ja; simp [h1, word_pack, Ne.symm nab, Ne.symm nac, Ne.symm nad]
  by_cases jb : j = ib
  · subst jb; simp [h2, word_pack, ja, Ne.symm nbc, Ne.symm nbd]
  by_cases jc : j = ic
  · subst jc; simp [h3, word_pack, ja, jb, Ne.symm ncd]
  by_cases jd : j = id
  · subst jd; simp [h4, word_pack, ja, jb, jc]
  simp [ja, jb, jc, jd, Ne.symm ja, Ne.symm jb, Ne.symm jc, Ne.symm jd]

theorem steps_regs {ρ : ℕ → Q} {st0 : ℕ → ℕ} {g0 : ℕ} {msg : ℕ → ℕ} :
    ∀ k, (∀ q < k, (gOp st0 g0 msg q).holds ρ) →
      vW ρ (gState st0 g0 k) = steps (fun j => word (ρ (msg j))) (vW ρ st0) k
  | 0, _ => rfl
  | k + 1, h => by
    rw [gStep_regs (h k (by omega)), steps_regs k (fun q hq => h q (by omega))]
    rfl

/-! ### Blocks -/

theorem ivWord_lt (i t : ℕ) (last : Bool) (ht : t < 2 ^ 32) (hi : i < 8) : ivWord i t last < 2 ^ 32 := by
  unfold ivWord
  have : IVn.getD i 0 < 2 ^ 32 := by interval_cases i <;> decide
  split_ifs
  · exact Nat.xor_lt_two_pow this ht
  · exact Nat.xor_lt_two_pow this (by norm_num)
  · exact this

theorem const_word {ρ : ℕ → Q} {o w : ℕ} (h : (constU32 o w).holds ρ) (hw : w < 2 ^ 32) :
    word (ρ o) = BitVec.ofNat 32 w := by
  simp only [constU32, Op.holds] at h
  rw [h, word_lit hw]

/-- One block: from chaining words `H` and the block's message words to `compress`. -/
theorem block_sound {ρ : ℕ → Q} {n : ℕ} {msg : ℕ → ℕ} {nBytes nb b : ℕ} {H : ℕ → Word}
    (hops : Holds ρ (blockOps n msg nBytes nb b)) (hB : nBytes < 2 ^ 32)
    (hH : ∀ i < 8, word (ρ (chain n b i)) = H i) :
    ∀ i < 8, word (ρ (chain n (b + 1) i)) =
      compress H (fun j => word (ρ (msg (16 * b + j)))) (min nBytes (64 * (b + 1))) (decide (b + 1 = nb)) i := by
  intro i hi
  unfold blockOps at hops
  simp only [holds_append] at hops
  obtain ⟨⟨hc, hgs⟩, hx⟩ := hops
  set base := n + 9 + BLOCK * b
  set t := min nBytes (64 * (b + 1))
  have ht : t < 2 ^ 32 := lt_of_le_of_lt (min_le_left _ _) hB
  set st0 : ℕ → ℕ := fun j => if j < 8 then chain n b j else base + (j - 8)
  set m : ℕ → ℕ := fun j => msg (16 * b + j)
  -- The initial working vector.
  have hv0 : vW ρ st0 = initV H t (decide (b + 1 = nb)) := by
    apply List.ext_getElem (by simp [vW, initV])
    intro j hj _
    simp only [vW, List.length_map, List.length_range] at hj
    simp only [vW, initV, List.getElem_map, List.getElem_range]
    by_cases hj8 : j < 8
    · simp only [st0, if_pos hj8]; exact hH j hj8
    · have hc' := hc _ (List.mem_map.mpr ⟨j - 8, List.mem_range.mpr (by omega), rfl⟩)
      rw [show st0 j = base + (j - 8) by simp only [st0, if_neg hj8], const_word hc' (ivWord_lt _ _ _ ht (by omega))]
      simp only [if_neg hj8]
      unfold ivWord
      obtain ⟨q, hq, rfl⟩ : ∃ q, q < 8 ∧ j = q + 8 := ⟨j - 8, by omega, by omega⟩
      have t1 : t / 4294967296 = 0 := Nat.div_eq_of_lt ht
      interval_cases q <;> simp [IV, BitVec.ofNat_xor, t1] <;> (try split_ifs) <;> simp_all
  have hsteps := steps_regs (ρ := ρ) (st0 := st0) (g0 := base + 8) (msg := m) 80
    (fun q hq => hgs _ (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩))
  rw [hv0] at hsteps
  have hxi := hx _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  simp only [Op.holds] at hxi
  obtain ⟨-, -, -, hxo⟩ := hxi
  show word (ρ (n + 9 + BLOCK * b + 328 + i)) = _
  rw [hxo, word_pack, hH i hi, compress, ← hsteps, vW_getD (by omega), vW_getD (by omega)]

/-- **The gadget computes Blake2s.** -/
theorem blake2s_sound {ρ : ℕ → Q} {n : ℕ} {msg : List ℕ} {nBytes : ℕ}
    (hops : Holds ρ (blake2s n msg nBytes).ops) (hB : nBytes < 2 ^ 32) :
    ∀ i < 8, word (ρ ((blake2s n msg nBytes).res.getD i 0)) =
      hashW (fun j => word (ρ (msg.getD j n))) nBytes (nBlocks nBytes) i := by
  dsimp only [blake2s] at hops ⊢
  rw [List.cons_append] at hops
  have hrest : Holds ρ _ := fun op h => hops op (List.mem_cons_of_mem _ h)
  rw [holds_append] at hrest
  obtain ⟨hiv, hblocks⟩ := hrest
  have chain_ok : ∀ b ≤ nBlocks nBytes, ∀ i < 8,
      word (ρ (chain n b i)) = hashW (fun j => word (ρ (msg.getD j n))) nBytes b i := by
    intro b
    induction b with
    | zero =>
      intro _ i hi
      have h := hiv _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
      have hlt : (if i = 0 then Nat.xor (IVn.getD 0 0) 0x01010020 else IVn.getD i 0) < 2 ^ 32 := by
        interval_cases i <;> decide
      rw [show chain n 0 i = n + 1 + i from rfl, const_word h hlt, hashW_zero hi]
      interval_cases i <;> decide
    | succ b ih =>
      intro hb i hi
      have hblk : Holds ρ (blockOps n (fun j => msg.getD j n) nBytes (nBlocks nBytes) b) := fun op hop =>
        hblocks op (List.mem_flatMap.mpr ⟨b, List.mem_range.mpr (by omega), hop⟩)
      rw [block_sound hblk hB (ih (by omega)) i hi, hashW_succ hi]
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  exact chain_ok _ le_rfl i hi

/-- The result wires are the u32 wires of their words. -/
theorem blake2s_res_pack {ρ : ℕ → Q} {n : ℕ} {msg : List ℕ} {nBytes : ℕ}
    (hops : Holds ρ (blake2s n msg nBytes).ops) :
    ∀ i < 8, ρ ((blake2s n msg nBytes).res.getD i 0) = pack (word (ρ ((blake2s n msg nBytes).res.getD i 0))) := by
  dsimp only [blake2s] at hops ⊢
  intro i hi
  rw [List.getD_eq_getElem _ _ (by simpa using hi)]
  simp only [List.getElem_map, List.getElem_range]
  have hnb : 0 < nBlocks nBytes := lt_max_of_lt_left (by norm_num)
  obtain ⟨b, hb⟩ : ∃ b, nBlocks nBytes = b + 1 := ⟨nBlocks nBytes - 1, by omega⟩
  rw [hb]
  have hop := hops _ (List.mem_cons_of_mem _ (List.mem_append_right _ (List.mem_flatMap.mpr ⟨b,
    List.mem_range.mpr (by omega), List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)⟩)))
  simp only [Op.holds] at hop
  obtain ⟨-, -, -, h⟩ := hop
  show ρ (n + 9 + BLOCK * b + 328 + i) = pack (word (ρ (n + 9 + BLOCK * b + 328 + i)))
  have e := congrArg word h
  rw [word_pack] at e
  rw [e]; exact h

/-- The gadget's padding wire (its first op) holds the zero word. -/
theorem blake2s_zero {ρ : ℕ → Q} {n : ℕ} {msg : List ℕ} {nBytes : ℕ}
    (hops : Holds ρ (blake2s n msg nBytes).ops) : word (ρ n) = 0 := by
  dsimp only [blake2s] at hops
  have h := hops _ List.mem_cons_self
  rw [const_word h (by norm_num)]; rfl

/-- `blake2s_sound` with the message as a word list. -/
theorem blake2s_words {ρ : ℕ → Q} {n : ℕ} {msg : List ℕ} {nBytes : ℕ}
    (hops : Holds ρ (blake2s n msg nBytes).ops) (hB : nBytes < 2 ^ 32) :
    ∀ i < 8, word (ρ ((blake2s n msg nBytes).res.getD i 0)) = blake2sWords (msg.map (word ∘ ρ)) nBytes i := by
  intro i hi
  rw [blake2s_sound hops hB i hi, blake2sWords]
  congr 1
  funext j
  by_cases hj : j < msg.length
  · rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj)]; simp
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simpa using hj), blake2s_zero hops]

theorem word_m2u {x : Q} : word (Q.m2u x) = BitVec.ofNat 32 x.a.val := by
  unfold word Q.m2u
  dsimp only
  rw [val_cast (by have := ZMod.val_lt x.a; unfold P at *; omega),
    val_cast (by have := ZMod.val_lt x.a; unfold P at *; omega), Nat.mod_add_div]

/-- **The public-input digest**: Blake2s of the key words, then each input's base value as a word. -/
theorem pubsDigest_sound {ρ : ℕ → Q} {n : ℕ} {key pubs : List ℕ}
    (hops : Holds ρ (pubsDigest n key pubs).ops) (hB : 4 * (key.length + pubs.length) < 2 ^ 32) :
    ∀ i < 8, word (ρ ((pubsDigest n key pubs).res.getD i 0)) =
      blake2sWords (key.map (word ∘ ρ) ++ pubs.map (fun p => BitVec.ofNat 32 (ρ p).a.val))
        (4 * (key.length + pubs.length)) i := by
  dsimp only [pubsDigest] at hops ⊢
  rw [holds_append] at hops
  obtain ⟨hm, hb⟩ := hops
  intro i hi
  rw [blake2s_words hb (by simpa using hB) i hi, List.length_append, List.length_map, List.length_range,
    List.map_append, List.map_map]
  congr 2
  apply List.ext_getElem (by simp)
  intro j hj _
  simp only [List.length_map, List.length_range] at hj
  have := hm _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Op.holds] at this
  simp only [List.getElem_map, List.getElem_range, Function.comp, this.2, word_m2u]
  rw [List.getD_eq_getElem _ _ hj]

end StarkedAir.Circuit
