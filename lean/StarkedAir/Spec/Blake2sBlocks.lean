/-
**Blake2s block by block.** The compression depends only on the chaining words 0–7 and the message words
0–15; and hashing a message of `L` bytes is `max 1 ⌈L / 64⌉` compressions over its little-endian words
(zero past the end), with counters `64·(i + 1)` and the length, the last one final.
-/
import StarkedAir.Spec.Blake2s

namespace StarkedAir.Spec.Blake2s

theorem sigma_lt : ∀ r < 10, ∀ i < 16, sigma r i < 16 := by decide

theorem steps_congr {m m' : ℕ → Word} (hm : ∀ k < 16, m k = m' k) (v : List Word) :
    ∀ k ≤ 80, steps m v k = steps m' v k := by
  intro k hk
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [steps]
    rw [ih (by omega)]
    unfold gStep
    rw [hm _ (sigma_lt _ (by omega) _ (by omega)), hm _ (sigma_lt _ (by omega) _ (by omega))]

theorem initV_congr {h h' : ℕ → Word} (hh : ∀ i < 8, h i = h' i) (t : ℕ) (f : Bool) : initV h t f = initV h' t f := by
  unfold initV
  apply List.map_congr_left
  intro i hi
  by_cases h8 : i < 8
  · rw [if_pos h8, if_pos h8, hh i h8]
  · rw [if_neg h8, if_neg h8]

/-- **The compression reads chaining words 0–7 and message words 0–15 only.** -/
theorem compress_congr {h h' m m' : ℕ → Word} (hh : ∀ i < 8, h i = h' i) (hm : ∀ k < 16, m k = m' k) (t : ℕ) (f : Bool) :
    ∀ i < 8, compress h m t f i = compress h' m' t f i := by
  intro i hi
  unfold compress
  simp only
  rw [initV_congr hh, steps_congr hm _ 80 le_rfl, hh i hi]

/-- The message's little-endian word `k` of block `i` (zero past the end). -/
def wordAt (b : List UInt8) (i k : ℕ) : Word :=
  BitVec.ofNat 32 ((b.getD (64 * i + 4 * k) 0).toNat + 256 * (b.getD (64 * i + 4 * k + 1) 0).toNat +
    65536 * (b.getD (64 * i + 4 * k + 2) 0).toNat + 16777216 * (b.getD (64 * i + 4 * k + 3) 0).toNat)

/-- The chaining value after `i` full blocks, from `h` and counter `t`. -/
def chainS (h : ℕ → Word) (t : ℕ) (b : List UInt8) : ℕ → ℕ → Word
  | 0 => h
  | i + 1 => fun w => if w < 8 then compress (chainS h t b i) (wordAt b i) (t + 64 * (i + 1)) false w else 0

theorem leWord_pad (b : List UInt8) (n : ℕ) (k : ℕ) :
    leWord (b ++ List.replicate n 0) k = wordAt b 0 k := by
  have g : ∀ j, (b ++ List.replicate n 0).getD j 0 = b.getD j 0 := by
    intro j
    by_cases h : j < b.length
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (show b.length ≤ j by omega), List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega), List.getElem?_replicate]
      split_ifs <;> rfl
  unfold leWord wordAt
  rw [g, g, g, g]
  simp

theorem wordAt_drop (b : List UInt8) (i k : ℕ) : wordAt (b.drop 64) i k = wordAt b (i + 1) k := by
  have g : ∀ j, (b.drop 64).getD j 0 = b.getD (64 + j) 0 := by
    intro j; rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
  simp only [wordAt, g]
  congr 4 <;> ring_nf

theorem leWord_take (b : List UInt8) (k : ℕ) (hk : k < 16) : leWord (b.take 64) k = wordAt b 0 k := by
  have g : ∀ j < 64, (b.take 64).getD j 0 = b.getD j 0 := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hj]
  simp only [leWord, wordAt, Nat.mul_zero, Nat.zero_add]
  rw [g _ (by omega), g _ (by omega), g _ (by omega), g _ (by omega)]

theorem chainS_shift (h : ℕ → Word) (t : ℕ) (b : List UInt8) :
    ∀ i, ∀ w < 8, chainS (fun w => if w < 8 then compress h (wordAt b 0) (t + 64) false w else 0) (t + 64) (b.drop 64) i w =
      chainS h t b (i + 1) w := by
  intro i
  induction i with
  | zero => intro w hw; simp only [chainS, Nat.zero_add, Nat.mul_one]
  | succ i ih =>
    intro w hw
    simp only [chainS, if_pos hw]
    rw [show t + 64 + 64 * (i + 1) = t + 64 * (i + 1 + 1) by ring]
    exact compress_congr ih (fun k _ => wordAt_drop b i k) _ _ _ hw

/-- **Hashing block by block.** A message of `L` bytes, `max 1 ⌈L/64⌉ = m + 1` blocks: the last block is
compressed (final, counter `t + L`) from the chaining value after `m` full blocks. -/
theorem hashBlocks_eq : ∀ m (h : ℕ → Word) (t : ℕ) (b : List UInt8), b.length ≤ 64 * (m + 1) →
    (m = 0 ∨ 64 * m < b.length) →
    ∀ w < 8, hashBlocks h t b w = compress (chainS h t b m) (wordAt b m) (t + b.length) true w := by
  intro m
  induction m with
  | zero =>
    intro h t b hl _ w hw
    rcases b with _ | ⟨x, xs⟩
    · simp only [hashBlocks, chainS, List.length_nil, Nat.add_zero]
      apply compress_congr (fun _ _ => rfl) (fun k _ => by simp [wordAt]) _ _ _ hw
    · simp only [hashBlocks]
      rw [if_pos hl]
      simp only [chainS]
      apply compress_congr (fun _ _ => rfl) (fun k _ => by rw [leWord_pad]) _ _ _ hw
  | succ m ih =>
    intro h t b hl hm w hw
    have hlen : 64 < b.length := by omega
    rcases b with _ | ⟨x, xs⟩
    · simp at hlen
    simp only [hashBlocks]
    rw [if_neg (by simp only [List.length_cons] at hlen ⊢; omega)]
    set b := x :: xs
    have e := ih (fun i => ((List.range 8).map (compress h (leWord (b.take 64)) (t + 64) false)).getD i 0) (t + 64)
      (b.drop 64) (by simp; omega) (by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · exact Or.inl h0
        · right; simp; omega) w hw
    rw [e, List.length_drop, show t + 64 + (b.length - 64) = t + b.length by omega]
    apply compress_congr _ (fun k _ => wordAt_drop b m k) _ _ _ hw
    intro i hi
    have hh : (fun i => ((List.range 8).map (compress h (leWord (b.take 64)) (t + 64) false)).getD i 0) =
        (fun w => if w < 8 then compress h (wordAt b 0) (t + 64) false w else 0) := by
      funext i
      by_cases h8 : i < 8
      · rw [if_pos h8, List.getD_eq_getElem _ _ (by simpa using h8)]
        simp only [List.getElem_map, List.getElem_range]
        exact compress_congr (fun _ _ => rfl) (fun k hk => leWord_take b k hk) _ _ _ h8
      · rw [if_neg h8, List.getD_eq_default _ _ (by simpa using h8)]
    rw [hh]
    exact chainS_shift h t b m i hi

end StarkedAir.Spec.Blake2s

namespace StarkedAir.Spec.Blake2s

theorem digest_length (h : ℕ → Word) : (digest h).length = 32 := by simp [digest]

theorem digest_getD (h : ℕ → Word) {k j : ℕ} (hk : k < 8) (hj : j < 4) :
    (digest h).getD (4 * k + j) 0 = UInt8.ofNat ((h k).toNat / 2 ^ (8 * j)) := by
  interval_cases k <;> interval_cases j <;> simp [digest, List.range_succ]

theorem word_of_bytes (w : Word) :
    BitVec.ofNat 32 ((UInt8.ofNat (w.toNat / 2 ^ (8 * 0))).toNat + 256 * (UInt8.ofNat (w.toNat / 2 ^ (8 * 1))).toNat +
      65536 * (UInt8.ofNat (w.toNat / 2 ^ (8 * 2))).toNat + 16777216 * (UInt8.ofNat (w.toNat / 2 ^ (8 * 3))).toNat) = w := by
  have hw := w.isLt
  apply BitVec.eq_of_toNat_eq
  simp [UInt8.toNat_ofNat']
  omega

/-- **A digest pair read as 16 message words** is the two chaining values. -/
theorem leWord_digests (h h' : ℕ → Word) {k : ℕ} (hk : k < 16) :
    leWord (digest h ++ digest h') k = if k < 8 then h k else h' (k - 8) := by
  have g : ∀ j < 4, (digest h ++ digest h').getD (4 * k + j) 0 =
      if k < 8 then UInt8.ofNat ((h k).toNat / 2 ^ (8 * j)) else UInt8.ofNat ((h' (k - 8)).toNat / 2 ^ (8 * j)) := by
    intro j hj
    split_ifs with h8
    · rw [List.getD_append _ _ _ _ (by rw [digest_length]; omega), digest_getD h h8 hj]
    · rw [List.getD_append_right _ _ _ _ (by rw [digest_length]; omega), digest_length,
        show 4 * k + j - 32 = 4 * (k - 8) + j by omega, digest_getD h' (by omega) hj]
  unfold leWord
  rw [show 4 * k = 4 * k + 0 by ring, g 0 (by norm_num), g 1 (by norm_num), g 2 (by norm_num), g 3 (by norm_num)]
  split_ifs <;> exact word_of_bytes _

end StarkedAir.Spec.Blake2s
