/-
**The epoch root's soundness, gadget by gadget** (`Circuit/EpochRoot.lean`).

- `low31_sound`: a challenge word's value is its low 31 bits, and those are not `2^31 − 1` (the stream's
  rejection, `epoch.challenge`), so the value is canonical: the same M31 the native stream draws.
-/
import StarkedAir.Circuit.EpochRoot

namespace StarkedAir.Circuit.EpochRoot

open StarkedAir StarkedAir.Circuit Q
open StarkedAir.Circuit.BlockNodeK (kid kidsOps kidsNext keyMsg)

variable {ρ : ℕ → Q}

theorem holds_of_mem {ops : List Op} (h : Holds ρ ops) {o : Op} (ho : o ∈ ops) : o.holds ρ := h o ho

theorem isBase_lit (k : ℕ) : IsBase (lit k 0 0 0) := ⟨by simp [lit], by simp [lit], by simp [lit]⟩

theorem isBase_add {x y : Q} (hx : IsBase x) (hy : IsBase y) : IsBase (x + y) :=
  ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1], by simp [hx.2.2, hy.2.2]⟩

theorem isBase_sub {x y : Q} (hx : IsBase x) (hy : IsBase y) : IsBase (x - y) :=
  ⟨by simp [hx.1, hy.1], by simp [hx.2.1, hy.2.1], by simp [hx.2.2, hy.2.2]⟩

theorem isBase_mul {x y : Q} (hx : IsBase x) (hy : IsBase y) : IsBase (x * y) := by
  rw [BlockNode.mul_base _ _ hx hy]; exact ⟨rfl, rfl, rfl⟩

theorem mul_a {x y : Q} (hx : IsBase x) (hy : IsBase y) : (x * y).a = x.a * y.a := by
  rw [BlockNode.mul_base _ _ hx hy]

/-- **`low31` is sound.** For a u32 wire `w` and `ci = i`, the result is a base value whose canonical
form is the word's low 31 bits, and those bits are not `2^31 − 1`. -/
theorem low31_sound {w ci n : ℕ} (h : Holds ρ (low31 w ci n).ops) (hci : ρ ci = lit 0 1 0 0) (hw : IsU32 (ρ w)) :
    IsBase (ρ (low31 w ci n).res) ∧ (ρ (low31 w ci n).res).a.val = (word (ρ w)).toNat % 2 ^ 31 ∧
      (word (ρ w)).toNat % 2 ^ 31 ≠ 2 ^ 31 - 1 := by
  simp only [low31] at h ⊢
  have g := fun (o : Op) (ho : o ∈ _) => holds_of_mem h ho
  have lo := g (.guessU16 n (.coord 0 (.reg w))) (by simp)
  have tg := g (.guessM31 (n + 1) (.divC (.coord 1 (.reg w)) 32768)) (by simp)
  have o2 := g (ONE (n + 2)) (by simp)
  have s3 := g (.sub (n + 3) (n + 1) (n + 2)) (by simp)
  have m4 := g (.mul (n + 4) (n + 1) (n + 3)) (by simp)
  have c5 := g (.const (n + 5) 0 0 0 0) (by simp)
  have e45 := g (.eq (n + 4) (n + 5)) (by simp)
  have c6 := g (.const (n + 6) 32768 0 0 0) (by simp)
  have m7 := g (.mul (n + 7) (n + 1) (n + 6)) (by simp)
  have hg := g (.guessM31 (n + 8) (.divC (.coord 1 (.reg w)) 1)) (by simp)
  have s9 := g (.sub (n + 9) (n + 8) (n + 7)) (by simp)
  have c10 := g (.const (n + 10) 2 0 0 0) (by simp)
  have m11 := g (.mul (n + 11) (n + 9) (n + 10)) (by simp)
  have r12 := range16_sound (n := n + 12) (x := n + 11) (fun o ho => g o (by simp only [List.mem_append, List.mem_cons] at ho ⊢; simp [range16] at ho; rcases ho with rfl | rfl <;> simp [range16]))
  have m14 := g (.mul (n + 14) (n + 8) ci) (by simp)
  have a15 := g (.add (n + 15) n (n + 14)) (by simp)
  have ew := g (.eq w (n + 15)) (by simp)
  have c16 := g (.const (n + 16) 65536 0 0 0) (by simp)
  have m17 := g (.mul (n + 17) (n + 9) (n + 16)) (by simp)
  have a18 := g (.add (n + 18) n (n + 17)) (by simp)
  have c19 := g (.const (n + 19) 65535 0 0 0) (by simp)
  have s20 := g (.sub (n + 20) (n + 19) n) (by simp)
  have c21 := g (.const (n + 21) 32767 0 0 0) (by simp)
  have s22 := g (.sub (n + 22) (n + 21) (n + 9)) (by simp)
  have c23 := g (.const (n + 23) 131072 0 0 0) (by simp)
  have m24 := g (.mul (n + 24) (n + 22) (n + 23)) (by simp)
  have a25 := g (.add (n + 25) (n + 20) (n + 24)) (by simp)
  have i26 := g (.inv (n + 26) (n + 25)) (by simp)
  simp only [Op.holds, ONE] at lo tg o2 s3 m4 c5 e45 c6 m7 hg s9 c10 m11 m14 a15 ew c16 m17 a18 c19 s20 c21 s22 c23 m24 a25 i26
  clear g h
  -- Base-ness, register by register.
  have b0 := lo.1
  have b1 := tg
  have b2 : IsBase (ρ (n + 2)) := by rw [o2]; exact isBase_lit 1
  have b3 : IsBase (ρ (n + 3)) := by rw [s3]; exact isBase_sub b1 b2
  have b6 : IsBase (ρ (n + 6)) := by rw [c6]; exact isBase_lit _
  have b7 : IsBase (ρ (n + 7)) := by rw [m7]; exact isBase_mul b1 b6
  have b8 := hg
  have b9 : IsBase (ρ (n + 9)) := by rw [s9]; exact isBase_sub b8 b7
  have b10 : IsBase (ρ (n + 10)) := by rw [c10]; exact isBase_lit _
  have b16 : IsBase (ρ (n + 16)) := by rw [c16]; exact isBase_lit _
  have b17 : IsBase (ρ (n + 17)) := by rw [m17]; exact isBase_mul b9 b16
  have b18 : IsBase (ρ (n + 18)) := by rw [a18]; exact isBase_add b0 b17
  have b19 : IsBase (ρ (n + 19)) := by rw [c19]; exact isBase_lit _
  have b20 : IsBase (ρ (n + 20)) := by rw [s20]; exact isBase_sub b19 b0
  have b21 : IsBase (ρ (n + 21)) := by rw [c21]; exact isBase_lit _
  have b22 : IsBase (ρ (n + 22)) := by rw [s22]; exact isBase_sub b21 b9
  have b23 : IsBase (ρ (n + 23)) := by rw [c23]; exact isBase_lit _
  have b24 : IsBase (ρ (n + 24)) := by rw [m24]; exact isBase_mul b22 b23
  -- The base coordinates.
  set L := (ρ n).a with hL
  set T := (ρ (n + 1)).a with hT
  set H := (ρ (n + 8)).a with hH
  have eT : T * (T - 1) = 0 := by
    have := congrArg Q.a e45
    rw [m4, mul_a b1 b3, s3, c5, o2] at this
    simpa [lit] using this
  have e9 : (ρ (n + 9)).a = H - T * 32768 := by
    rw [s9]; simp only [sub_a]; rw [m7, mul_a b1 b6, c6]; simp [lit]; rfl
  have e11 : (ρ (n + 11)).a = (ρ (n + 9)).a * 2 := by rw [m11, mul_a b9 b10, c10]; simp [lit]
  have ew' : ρ w = ⟨L, H, 0, 0⟩ := by
    rw [ew, a15, m14, hci]; exact Q.lohi b0 b8
  have e18 : (ρ (n + 18)).a = L + (ρ (n + 9)).a * 65536 := by
    rw [a18]; simp only [add_a]; rw [m17, mul_a b9 b16, c16]; simp [lit]; rfl
  have e25 : (ρ (n + 25)).a = (65535 - L) + (32767 - (ρ (n + 9)).a) * 131072 := by
    rw [a25, add_a, s20, sub_a, m24, mul_a b22 b23, s22, sub_a, c19, c21, c23]; simp [lit]; rfl
  have b25 : IsBase (ρ (n + 25)) := by rw [a25]; exact isBase_add b20 b24
  have hd : (65535 - L) + (32767 - (ρ (n + 9)).a) * 131072 ≠ 0 := by
    intro h0
    have h25 : ρ (n + 25) = ⟨0, 0, 0, 0⟩ := by
      ext
      · rw [e25, h0]
      · exact b25.1
      · exact b25.2.1
      · exact b25.2.2
    have := congrArg Q.a i26
    rw [h25, Q.mul_def] at this
    simp [cmul, lit] at this
  -- Naturals.
  set X := (ρ (n + 9)).a with hX
  have hwa : (ρ w).b = H := by rw [ew']
  have hwa' : (ρ w).a = L := by rw [ew']
  have hl : L.val < 65536 := lo.2
  have hh : H.val < 65536 := by rw [← hwa]; exact hw.2.1
  have ht : T.val ≤ 1 := val_le_one_of_bool eT
  have r11 : ((ρ (n + 11)).a).val < 65536 := r12.2
  rw [e11] at r11
  clear_value L T H X
  have cL : L = ((L.val : ℕ) : F) := (ZMod.natCast_zmod_val L).symm
  have cT : T = ((T.val : ℕ) : F) := (ZMod.natCast_zmod_val T).symm
  have cH : H = ((H.val : ℕ) : F) := (ZMod.natCast_zmod_val H).symm
  have cX : X = ((X.val : ℕ) : F) := (ZMod.natCast_zmod_val X).symm
  set l := L.val with hl'
  set t := T.val with ht'
  set hv := H.val with hv'
  set x := X.val with hx'
  have hxP : x < P := val_lt_P X
  -- 2x mod P < 2^16.
  have h2x : (x * 2) % P < 65536 := by
    have : (X * 2).val = (x * 2) % P := by
      rw [cX, show ((x : ℕ) : F) * 2 = ((x * 2 : ℕ) : F) by push_cast; ring, ZMod.val_natCast]
    rw [← this]; exact r11
  -- H = X + 32768 T.
  have eH : H = ((x + t * 32768 : ℕ) : F) := by
    push_cast; rw [← cX, ← cT]; linear_combination (-1 : F) * e9
  have hvP : hv < P := by unfold P; omega
  -- h < 2^15 and hi = h + 2^15 t (the residue class near P/2 is too large for hi < 2^16).
  have hsplit : x < 32768 ∧ hv = x + t * 32768 := by
    by_cases hc : x * 2 < P
    · rw [Nat.mod_eq_of_lt hc] at h2x
      have hxs : x < 32768 := by omega
      refine ⟨hxs, natCast_inj_of_lt hvP (by unfold P; omega) ?_⟩
      rw [← cH]; exact eH
    · exfalso
      replace hc := Nat.le_of_not_lt hc
      have hlt : x * 2 - P < P := by unfold P at *; omega
      rw [Nat.mod_eq_sub_mod hc, Nat.mod_eq_of_lt hlt] at h2x
      have hsum : x + t * 32768 < P := by unfold P at *; omega
      have := natCast_inj_of_lt hvP hsum (by rw [← cH]; exact eH)
      unfold P at *; omega
  obtain ⟨hxs, hvx⟩ := hsplit
  have hnot : ¬ (l = 65535 ∧ x = 32767) := by
    rintro ⟨e1, e2⟩
    apply hd
    rw [cL, cX, e1, e2]; norm_num
  have h18 : (ρ (n + 18)).a.val = l + x * 65536 := by
    rw [e18, cL, cX, show ((l : ℕ) : F) + ((x : ℕ) : F) * 65536 = ((l + x * 65536 : ℕ) : F) by push_cast; ring,
      ZMod.val_natCast, Nat.mod_eq_of_lt (by unfold P; omega)]
  have hword : (word (ρ w)).toNat = l + 65536 * hv := by
    rw [ew', Q.word_mk, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨b18, ?_, ?_⟩
  · rw [h18, hword, hvx]; omega
  · rw [hword, hvx]; omega

/-! ### `logOf`: a count is `2^k` -/

theorem bs_getD {n j : ℕ} (hj : j < LOGS) : ((List.range LOGS).map fun i => n + i).getD j 0 = n + j := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]; rfl

theorem two_pow_lt_P {j : ℕ} (hj : j < LOGS) : 2 ^ j < P := by
  have : 2 ^ j ≤ 2 ^ 30 := Nat.pow_le_pow_right (by norm_num) (by unfold LOGS at hj; omega)
  unfold P; omega

/-- One bit at most: `Σ b = 1` over bits forces exactly one `1`. -/
theorem one_hot {m : ℕ} (b : ℕ → ℕ) (hb : ∀ i < m, b i ≤ 1) (hs : ∑ i ∈ Finset.range m, b i = 1) :
    ∃ k < m, ∀ i < m, b i = if i = k then 1 else 0 := by
  have : ∃ k ∈ Finset.range m, b k ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero (fun i hi => hc i hi)] at hs
    exact absurd hs (by norm_num)
  obtain ⟨k, hk, hk0⟩ := this
  have hk1 : b k = 1 := by have := hb k (Finset.mem_range.mp hk); omega
  refine ⟨k, Finset.mem_range.mp hk, fun i hi => ?_⟩
  split_ifs with hik
  · rw [hik]; exact hk1
  · have hsplit := Finset.add_sum_erase (Finset.range m) b hk
    rw [hs, hk1] at hsplit
    have hz : ∑ x ∈ (Finset.range m).erase k, b x = 0 := by omega
    exact (Finset.sum_eq_zero_iff.mp hz) i (Finset.mem_erase.mpr ⟨hik, Finset.mem_range.mpr hi⟩)

/-- **`logOf` is sound.** The count is `2^k` (`k < 31`) and the result register holds `k`. -/
theorem logOf_sound {cnt n : ℕ} (h : Holds ρ (logOf cnt n).ops) :
    ∃ k < LOGS, (ρ cnt).a = ((2 ^ k : ℕ) : F) ∧ (ρ (logOf cnt n).res).a = (k : F) := by
  -- The ops, by family.
  have hB : ∀ j < LOGS, ∀ o ∈ [Op.guessM31 (n + j) (.isEq (.reg cnt) (2 ^ j)), ONE (n + LOGS + 3 * j),
      .sub (n + LOGS + 3 * j + 1) (n + j) (n + LOGS + 3 * j), .mul (n + LOGS + 3 * j + 2) (n + j) (n + LOGS + 3 * j + 1)],
      o.holds ρ := fun j hj o ho => h o (by
    unfold logOf
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ho⟩)
  have hZ : (Op.const (n + 4 * LOGS) 0 0 0 0).holds ρ := h _ (by
    unfold logOf
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl))
  have hE : ∀ j < LOGS, (Op.eq (n + LOGS + 3 * j + 2) (n + 4 * LOGS)).holds ρ := fun j hj => h _ (by
    unfold logOf
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  have hT : ∀ j < LOGS, ∀ o ∈ [Op.const (n + 4 * LOGS + 1 + 6 * j) (2 ^ j % 2147483647) 0 0 0,
      .mul (n + 4 * LOGS + 1 + 6 * j + 1) (((List.range LOGS).map fun i => n + i).getD j 0) (n + 4 * LOGS + 1 + 6 * j),
      Op.const (n + 4 * LOGS + 1 + 6 * j + 2) j 0 0 0,
      .mul (n + 4 * LOGS + 1 + 6 * j + 3) (((List.range LOGS).map fun i => n + i).getD j 0) (n + 4 * LOGS + 1 + 6 * j + 2),
      .add (n + 4 * LOGS + 1 + 6 * j + 4)
        (if j = 0 then ((List.range LOGS).map fun i => n + i).getD 0 0 else n + 4 * LOGS + 1 + 6 * (j - 1) + 4)
        (if j = 0 then n + 4 * LOGS else ((List.range LOGS).map fun i => n + i).getD j 0),
      .add (n + 4 * LOGS + 1 + 6 * j + 5) (if j = 0 then n + 4 * LOGS + 1 + 6 * j + 1 else n + 4 * LOGS + 1 + 6 * (j - 1) + 5)
        (if j = 0 then n + 4 * LOGS else n + 4 * LOGS + 1 + 6 * j + 1)], o.holds ρ := fun j hj o ho => h o (by
    unfold logOf
    apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr hj, ho⟩))
  have hK : ∀ j < LOGS, (Op.add (n + 4 * LOGS + 1 + 6 * LOGS + j) (if j = 0 then n + 4 * LOGS else n + 4 * LOGS + 1 + 6 * LOGS + j - 1)
      (n + 4 * LOGS + 1 + 6 * j + 3)).holds ρ := fun j hj => h _ (by
    unfold logOf
    apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
  have hL : ∀ o ∈ [ONE (n + 4 * LOGS + 1 + 6 * LOGS + LOGS), Op.eq (n + 4 * LOGS + 1 + 6 * (LOGS - 1) + 4) (n + 4 * LOGS + 1 + 6 * LOGS + LOGS),
      Op.eq (n + 4 * LOGS + 1 + 6 * (LOGS - 1) + 5) cnt], o.holds ρ := fun o ho => h o (by
    unfold logOf
    exact List.mem_append_right _ ho)
  -- Per-position facts.
  set B : ℕ → F := fun j => (ρ (n + j)).a with hBdef
  have z0 : ρ (n + 4 * LOGS) = lit 0 0 0 0 := by simpa [Op.holds] using hZ
  have bit : ∀ j < LOGS, IsBase (ρ (n + j)) ∧ B j * (B j - 1) = 0 := by
    intro j hj
    have g := hB j hj
    have tg := g _ (List.mem_cons_self)
    have o1 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have s2 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have m3 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    have e := hE j hj
    simp only [Op.holds, ONE] at tg o1 s2 m3 e
    refine ⟨tg, ?_⟩
    have b1 : IsBase (ρ (n + LOGS + 3 * j)) := by rw [o1]; exact isBase_lit 1
    have b2 : IsBase (ρ (n + LOGS + 3 * j + 1)) := by rw [s2]; exact isBase_sub tg b1
    have := congrArg Q.a (m3.symm.trans (e.trans z0))
    rw [mul_a tg b2, s2, sub_a, o1] at this
    simpa [lit, B] using this
  have wt : ∀ j < LOGS, (ρ (n + 4 * LOGS + 1 + 6 * j + 1)).a = B j * ((2 ^ j : ℕ) : F) ∧
      (ρ (n + 4 * LOGS + 1 + 6 * j + 3)).a = B j * (j : F) := by
    intro j hj
    have g := hT j hj
    have c0 := g _ (List.mem_cons_self)
    have m1 := g _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have c2 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
    have m3 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    simp only [Op.holds, bs_getD hj] at c0 m1 c2 m3
    have bb := (bit j hj).1
    rw [Nat.mod_eq_of_lt (show 2 ^ j < 2147483647 from two_pow_lt_P hj)] at c0
    refine ⟨?_, ?_⟩
    · rw [m1, mul_a bb (by rw [c0]; exact isBase_lit _), c0]; rfl
    · rw [m3, mul_a bb (by rw [c2]; exact isBase_lit _), c2]; rfl
  -- The running sums.
  have acc : ∀ j < LOGS, (ρ (n + 4 * LOGS + 1 + 6 * j + 4)).a = ∑ i ∈ Finset.range (j + 1), B i ∧
      (ρ (n + 4 * LOGS + 1 + 6 * j + 5)).a = ∑ i ∈ Finset.range (j + 1), B i * ((2 ^ i : ℕ) : F) ∧
      (ρ (n + 4 * LOGS + 1 + 6 * LOGS + j)).a = ∑ i ∈ Finset.range (j + 1), B i * (i : F) := by
    intro j
    induction j with
    | zero =>
      intro hj
      have g := hT 0 hj
      have a4 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
      have a5 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
      have k0 := hK 0 hj
      simp only [Op.holds, if_true, bs_getD hj] at a4 a5 k0
      have w0 := wt 0 hj
      simp only [Nat.mul_zero, Nat.add_zero] at a4 a5 k0 w0 ⊢
      refine ⟨?_, ?_, ?_⟩
      · rw [a4, z0]; simp [lit, B]
      · rw [a5, add_a, w0.1, z0]; simp [lit]
      · rw [k0, add_a, w0.2, z0]; simp [lit]
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have g := hT (j + 1) hj
      have a4 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))))
      have a5 := g _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))
      have k1 := hK (j + 1) hj
      simp only [Op.holds, Nat.add_one_ne_zero, if_false, bs_getD hj, Nat.add_sub_cancel] at a4 a5 k1
      have w1 := wt (j + 1) hj
      rw [show n + 4 * LOGS + 1 + 6 * LOGS + (j + 1) - 1 = n + 4 * LOGS + 1 + 6 * LOGS + j by omega] at k1
      refine ⟨?_, ?_, ?_⟩
      · rw [a4, add_a, ih'.1, Finset.sum_range_succ _ (j + 1)]
      · rw [a5, add_a, ih'.2.1, w1.1, Finset.sum_range_succ _ (j + 1)]
      · rw [show n + 4 * LOGS + 1 + 6 * LOGS + (j + 1) = n + 4 * LOGS + 1 + 6 * LOGS + j + 1 by omega] at k1 ⊢
        rw [k1, add_a, ih'.2.2, w1.2, Finset.sum_range_succ _ (j + 1)]
  -- The end: Σ b = 1, Σ b 2^j = cnt.
  have hl := hL
  have o1 := hl _ (List.mem_cons_self)
  have eS := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have eC := hl _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  simp only [Op.holds, ONE] at o1 eS eC
  have hLs : LOGS - 1 < LOGS := by unfold LOGS; omega
  have fin := acc (LOGS - 1) hLs
  have hsucc : LOGS - 1 + 1 = LOGS := by unfold LOGS; rfl
  rw [hsucc] at fin
  have sumB : ∑ i ∈ Finset.range LOGS, B i = 1 := by
    rw [← fin.1, eS, o1]; simp [lit]
  have sumC : (ρ cnt).a = ∑ i ∈ Finset.range LOGS, B i * ((2 ^ i : ℕ) : F) := by
    rw [← fin.2.1, eC]
  -- Bits as naturals.
  have bv : ∀ i < LOGS, B i = (((B i).val : ℕ) : F) ∧ (B i).val ≤ 1 := fun i hi =>
    ⟨(ZMod.natCast_zmod_val _).symm, val_le_one_of_bool (bit i hi).2⟩
  have sumN : ∑ i ∈ Finset.range LOGS, (B i).val = 1 := by
    have hc : ((∑ i ∈ Finset.range LOGS, (B i).val : ℕ) : F) = 1 := by
      rw [Nat.cast_sum, ← sumB]
      exact Finset.sum_congr rfl (fun i hi => ((bv i (Finset.mem_range.mp hi)).1).symm)
    have hle : ∑ i ∈ Finset.range LOGS, (B i).val ≤ LOGS := by
      calc ∑ i ∈ Finset.range LOGS, (B i).val ≤ ∑ _i ∈ Finset.range LOGS, 1 :=
            Finset.sum_le_sum (fun i hi => (bv i (Finset.mem_range.mp hi)).2)
        _ = LOGS := by simp
    have hLP : LOGS < P := by unfold LOGS P; norm_num
    exact natCast_inj_of_lt (by omega) (by unfold P; norm_num) (by rw [hc]; simp)
  obtain ⟨k, hk, hone⟩ := one_hot (fun i => (B i).val) (fun i hi => (bv i hi).2) sumN
  have hBk : ∀ i < LOGS, B i = if i = k then 1 else 0 := fun i hi => by
    rw [(bv i hi).1, hone i hi]; split_ifs <;> simp
  refine ⟨k, hk, ?_, ?_⟩
  · rw [sumC, Finset.sum_congr rfl (fun i hi => by rw [hBk i (Finset.mem_range.mp hi)])]
    simp [Finset.sum_ite_eq', Finset.mem_range.mpr hk]
  · show (ρ (n + 4 * LOGS + 1 + 6 * LOGS + LOGS - 1)).a = (k : F)
    rw [show n + 4 * LOGS + 1 + 6 * LOGS + LOGS - 1 = n + 4 * LOGS + 1 + 6 * LOGS + (LOGS - 1) by unfold LOGS; omega, fin.2.2,
      Finset.sum_congr rfl (fun i hi => by rw [hBk i (Finset.mem_range.mp hi)])]
    simp [Finset.sum_ite_eq', Finset.mem_range.mpr hk]

/-! ### The links and the sums -/

theorem lt30_holds {m x : ℕ} {ops : List Op} (h : Holds ρ ops) (hs : BlockNode.lt30 m x ⊆ ops) :
    IsBase (ρ x) ∧ (ρ x).a.val < 2 ^ 30 := BlockNode.lt30_sound (fun o ho => h o (hs ho))

/-- **The links are sound.** Child 0 starts at `lo`, each child starts where the previous one ends, the
last ends at `hi + 1`; `lo` and `hi + 1` are below `2^30`. -/
theorem links_sound {M : ℕ} {p : ℕ → ℕ → ℕ} {lo hi n : ℕ} (hM : 0 < M) (h : Holds ρ (links M p lo hi n).ops) :
    ρ (p 0 BlockNode.LO) = ρ lo ∧
    (∀ i, i + 1 < M → ρ (p (i + 1) BlockNode.LO) = ρ (p i BlockNode.LO) + ρ (p i BlockNode.NN)) ∧
    ρ (p (M - 1) BlockNode.LO) + ρ (p (M - 1) BlockNode.NN) = ρ hi + lit 1 0 0 0 ∧
    (IsBase (ρ lo) ∧ (ρ lo).a.val < 2 ^ 30) ∧ (IsBase (ρ hi + lit 1 0 0 0) ∧ (ρ hi + lit 1 0 0 0).a.val < 2 ^ 30) := by
  unfold links at h
  have e0 := h _ (by
    apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
    apply List.mem_append_left; exact List.mem_singleton.mpr rfl)
  have ends : ∀ i < M, ρ (n + i) = ρ (p i BlockNode.LO) + ρ (p i BlockNode.NN) := fun i hi => by
    have := h _ (by
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))
    simpa [Op.holds] using this
  have chain : ∀ i, i + 1 < M → ρ (p (i + 1) BlockNode.LO) = ρ (n + i) := fun i hi => by
    have := h _ (by
      apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
      exact List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩))
    simpa [Op.holds] using this
  have o1 := h _ (by
    apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_cons_self))
  have a1 := h _ (by
    apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have e1 := h _ (by
    apply List.mem_append_left; apply List.mem_append_left
    exact List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
  simp only [Op.holds, ONE] at e0 o1 a1 e1
  have l1 := lt30_holds h (fun o ho => List.mem_append_left _ (List.mem_append_right _ ho))
  have l2 := lt30_holds h (fun o ho => List.mem_append_right _ ho)
  rw [a1, o1] at l2
  refine ⟨e0, fun i hi => (chain i hi).trans (ends i (by omega)), ?_, l1, l2⟩
  rw [← ends (M - 1) (by omega), show n + (M - 1) = n + M - 1 by omega, e1, a1, o1]

theorem val_add_lt30 {x y : F} (hx : x.val < 2 ^ 30) (hy : y.val < 2 ^ 30) : (x + y).val = x.val + y.val := by
  have hlt : x.val + y.val < 2 ^ 31 - 1 := by omega
  exact ZMod.val_add_of_lt hlt

/-- **The sums are sound.** With every child's limbs 2–6 base: the result limbs are base and their base
coordinates are the children's sums; the input count's is also the integer sum, below `2^30`. -/
theorem sums_sound {M : ℕ} {p : ℕ → ℕ → ℕ} {n : ℕ} (hM : 0 < M) (h : Holds ρ (sums M p n).ops)
    (hb : ∀ i < M, ∀ j < 5, IsBase (ρ (p i (BlockNode.SS + j)))) (hn : ∀ i < M, (ρ (p i BlockNode.NIN)).a.val < 2 ^ 30) :
    (∀ j < 5, IsBase (ρ (sumReg p n (M - 1) j)) ∧
      (ρ (sumReg p n (M - 1) j)).a = ∑ i ∈ Finset.range M, (ρ (p i (BlockNode.SS + j))).a) ∧
    (ρ (sumReg p n (M - 1) 4)).a.val = ∑ i ∈ Finset.range M, (ρ (p i BlockNode.NIN)).a.val ∧
    (ρ (sumReg p n (M - 1) 4)).a.val < 2 ^ 30 := by
  unfold sums at h
  have first := lt30_holds h (fun o ho => List.mem_append_left _ ho)
  have stepOp : ∀ i, i + 1 < M → ∀ o ∈ (List.range 5).map (fun j => Op.add (n + 14 * i + j) (sumReg p n i j) (p (i + 1) (BlockNode.SS + j))) ++
      BlockNode.lt30 (n + 14 * i + 5) (n + 14 * i + 4), o.holds ρ := fun i hi o ho =>
    h o (List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by omega), ho⟩))
  have claim : ∀ i < M, (∀ j < 5, IsBase (ρ (sumReg p n i j)) ∧
      (ρ (sumReg p n i j)).a = ∑ l ∈ Finset.range (i + 1), (ρ (p l (BlockNode.SS + j))).a) ∧
      (ρ (sumReg p n i 4)).a.val = ∑ l ∈ Finset.range (i + 1), (ρ (p l BlockNode.NIN)).a.val ∧
      (ρ (sumReg p n i 4)).a.val < 2 ^ 30 := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [sumReg, if_true, zero_add, Finset.sum_range_one]
      exact ⟨fun j hj => ⟨hb 0 hM j hj, trivial⟩, rfl, first.2⟩
    | succ i ih =>
      intro hi
      obtain ⟨ihv, ihn, ihl⟩ := ih (by omega)
      have g := stepOp i hi
      have reg : ∀ j, sumReg p n (i + 1) j = n + 14 * i + j := fun j => by simp [sumReg]
      have addj : ∀ j < 5, ρ (n + 14 * i + j) = ρ (sumReg p n i j) + ρ (p (i + 1) (BlockNode.SS + j)) := fun j hj => by
        have := g _ (List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩))
        simpa [Op.holds] using this
      have l30 := lt30_holds (ops := _) (fun o ho => g o ho) (fun o ho => List.mem_append_right _ ho)
      have vals : ∀ j < 5, IsBase (ρ (sumReg p n (i + 1) j)) ∧
          (ρ (sumReg p n (i + 1) j)).a = ∑ l ∈ Finset.range (i + 1 + 1), (ρ (p l (BlockNode.SS + j))).a := fun j hj => by
        rw [reg, addj j hj, Finset.sum_range_succ _ (i + 1), ← (ihv j hj).2]
        exact ⟨isBase_add (ihv j hj).1 (hb (i + 1) hi j hj), rfl⟩
      refine ⟨vals, ?_, ?_⟩
      · rw [reg, addj 4 (by norm_num), add_a, val_add_lt30 ihl ?_, ihn, Finset.sum_range_succ _ (i + 1)]
        · rfl
        · exact hn (i + 1) hi
      · rw [reg]; exact l30.2
  obtain ⟨v, nv, nl⟩ := claim (M - 1) (by omega)
  rw [show M - 1 + 1 = M by omega] at v nv
  exact ⟨v, nv, nl⟩

/-! ### The whole program -/

theorem chainOuts_length {α : Type} (f : ℕ → ℕ → Out α) (n : ℕ) : ∀ k, (chainOuts f n k).length = k
  | 0 => rfl
  | k + 1 => by simp [chainOuts, chainOuts_length f n k]

/-- The `i`-th gadget of a chain is `f i` at some register. -/
theorem chainOuts_get {α : Type} (f : ℕ → ℕ → Out α) (n : ℕ) :
    ∀ k i (hi : i < k), ∃ r, (chainOuts f n k)[i]'(by rw [chainOuts_length]; exact hi) = f i r
  | 0, _, hi => absurd hi (Nat.not_lt_zero _)
  | k + 1, i, hi => by
    by_cases hik : i < k
    · obtain ⟨r, hr⟩ := chainOuts_get f n k i hik
      refine ⟨r, ?_⟩
      simp only [chainOuts]
      rw [List.getElem_append_left (by rw [chainOuts_length]; exact hik)]
      exact hr
    · have hik' : i = k := by omega
      subst hik'
      refine ⟨match (chainOuts f n i).getLast? with | some o => o.next | none => n, ?_⟩
      simp only [chainOuts]
      rw [List.getElem_append_right (by rw [chainOuts_length])]
      simp only [chainOuts_length, Nat.sub_self, List.getElem_singleton]
      rfl

/-- The ops of the `i`-th gadget of a chain hold when the chain's ops hold. -/
theorem chainOuts_holds {α : Type} {f : ℕ → ℕ → Out α} {n k i : ℕ} (hi : i < k)
    (h : Holds ρ ((chainOuts f n k).flatMap (·.ops))) :
    ∃ r, (chainOuts f n k)[i]'(by rw [chainOuts_length]; exact hi) = f i r ∧ Holds ρ (f i r).ops := by
  obtain ⟨r, hr⟩ := chainOuts_get f n k i hi
  refine ⟨r, hr, fun o ho => h o (List.mem_flatMap.mpr ⟨_, List.getElem_mem _, by rw [hr]; exact ho⟩)⟩

/-- The program's parts hold separately. -/
theorem root_parts {M : ℕ} {prevV : Bool} (h : Holds ρ (epochRoot M prevV).ops) :
    let P := parts M prevV
    Holds ρ (kidsOps M) ∧ Holds ρ P.inp.ops ∧ Holds ρ P.lk.ops ∧
    Holds ρ (sameChallenge M fun i => (kid i).res.pubs) ∧ Holds ρ P.sm.ops ∧
    Holds ρ (P.logs.flatMap (·.ops)) ∧ Holds ρ (P.roots.flatMap (·.ops)) ∧ Holds ρ P.seed.ops ∧
    Holds ρ [constU32 P.ctrs 0, constU32 (P.ctrs + 1) 1] ∧ Holds ρ P.s0.ops ∧ Holds ρ P.s1.ops ∧
    Holds ρ [Op.const P.ci 0 1 0 0] ∧ Holds ρ (P.vals.flatMap (·.ops)) ∧
    Holds ρ ((List.range 12).map fun j => Op.eq ((P.vals.getD j ⟨[], 0, 0⟩).res) ((kid 0).res.pubs (BlockNode.CH + j))) ∧
    Holds ρ P.key.ops ∧ Holds ρ P.dg.ops := by
  simp only [epochRoot, holds_append] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩ := h
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩

/-! ### The seed and the challenge stream -/

/-- The register after the children's root packings (`parts`' `rn`). -/
def rootsNext (M : ℕ) (prevV : Bool) : ℕ :=
  let P := parts M prevV
  lastNext P.roots (lastNext P.logs P.sm.next)

/-- The seed message's registers (as `parts` builds them): the tag, `from`, `to`, the previous set's
digest (`prevV`), the final set's, then per child its start, `k` and seed-root words. -/
def seedMsg (M : ℕ) (prevV : Bool) : List ℕ :=
  let P := parts M prevV
  let rn := rootsNext M prevV
  let m2 := rn + 7
  (List.range 7).map (rn + ·) ++ [m2, m2 + 1] ++ (if prevV then P.inp.res.prev else []) ++ P.inp.res.fin ++
    (List.range M).flatMap fun i => [m2 + 2 + 2 * i, m2 + 3 + 2 * i] ++ (P.roots.getD i ⟨[], [], 0⟩).res

/-- The seed's words: Blake2s of the message words. -/
theorem root_seed {M : ℕ} {prevV : Bool} (h : Holds ρ (epochRoot M prevV).ops) (hB : 4 * (seedMsg M prevV).length < 2 ^ 32) :
    ∀ i < 8, word (ρ ((parts M prevV).seed.res.getD i 0)) =
      blake2sWords ((seedMsg M prevV).map (word ∘ ρ)) (4 * (seedMsg M prevV).length) i := by
  have hs := (root_parts h).2.2.2.2.2.2.2.1
  have hb : Holds ρ (blake2s (rootsNext M prevV + 7 + 2 + 2 * M) (seedMsg M prevV) (4 * (seedMsg M prevV).length)).ops :=
    fun o ho => hs o (List.mem_append_right _ ho)
  exact blake2s_words hb hB

/-- The seed's 8 words. -/
def seedWords (ρ : ℕ → Q) (M : ℕ) (prevV : Bool) : List Spec.Blake2s.Word :=
  (List.range 8).map (blake2sWords ((seedMsg M prevV).map (word ∘ ρ)) (4 * (seedMsg M prevV).length))

/-- The challenge stream's word `j`: word `j mod 8` of `Blake2s(seed ‖ j / 8)` (`epoch.challenge`'s
counter mode, 36 bytes). -/
def streamWord (ρ : ℕ → Q) (M : ℕ) (prevV : Bool) (j : ℕ) : Spec.Blake2s.Word :=
  blake2sWords (seedWords ρ M prevV ++ [BitVec.ofNat 32 (j / 8)]) 36 (j % 8)

theorem isU32_pack (w : Spec.Blake2s.Word) : IsU32 (pack w) := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · show ((w.toNat % 65536 : ℕ) : F).val < 65536
    rw [val_cast (by unfold P; omega)]; omega
  · show ((w.toNat / 65536 : ℕ) : F).val < 65536
    have := w.isLt
    rw [val_cast (by unfold P; omega)]; omega

theorem map_eq_range_getD {α β : Type} (f : α → β) (d : α) (l : List α) :
    l.map f = (List.range l.length).map fun i => f (l.getD i d) := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < l.length := by simpa using h1
  simp [List.getElem?_eq_getElem hi]

/-- **The challenge is the stream's.** Child 0's challenge limbs (7–18) are base, and their canonical
values are the low 31 bits of the stream's words 0–11, none of them the rejected `2^31 − 1`. -/
theorem root_challenge {M : ℕ} {prevV : Bool} (h : Holds ρ (epochRoot M prevV).ops)
    (hB : 4 * (seedMsg M prevV).length < 2 ^ 32) :
    ∀ j < 12, IsBase (ρ ((kid 0).res.pubs (BlockNode.CH + j))) ∧
      (ρ ((kid 0).res.pubs (BlockNode.CH + j))).a.val = (streamWord ρ M prevV j).toNat % 2 ^ 31 ∧
      (streamWord ρ M prevV j).toNat % 2 ^ 31 ≠ 2 ^ 31 - 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, hc, hs0, hs1, hci, hv, heq, -, -⟩ := root_parts h
  set P := parts M prevV with hP
  have c0 := const_word (hc _ List.mem_cons_self) (by norm_num)
  have c1 := const_word (hc _ (List.mem_cons_of_mem _ List.mem_cons_self)) (by norm_num)
  have ci : ρ P.ci = lit 0 1 0 0 := by simpa [Op.holds] using hci _ List.mem_cons_self
  have seedW := root_seed h hB
  -- The seed's result list mapped to words is `seedWords`.
  have hseedlen : P.seed.res.length = 8 := BlockRec.blake2s_length (rootsNext M prevV + 7 + 2 + 2 * M) (seedMsg M prevV) (4 * (seedMsg M prevV).length)
  have hsw : P.seed.res.map (word ∘ ρ) = seedWords ρ M prevV := by
    rw [map_eq_range_getD _ 0, hseedlen, seedWords]
    exact List.map_congr_left (fun i hi => seedW i (List.mem_range.mp hi))
  -- The two stream blocks.
  have w0 : ∀ i < 8, word (ρ (P.s0.res.getD i 0)) = streamWord ρ M prevV i := by
    intro i hi
    refine (blake2s_words hs0 (by norm_num) i hi).trans ?_
    rw [streamWord, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    show blake2sWords ((P.seed.res ++ [P.ctrs]).map (word ∘ ρ)) 36 i = _
    rw [List.map_append, hsw]; simp [c0]
  have w1 : ∀ i < 8, word (ρ (P.s1.res.getD i 0)) = streamWord ρ M prevV (8 + i) := by
    intro i hi
    refine (blake2s_words hs1 (by norm_num) i hi).trans ?_
    rw [streamWord, show (8 + i) / 8 = 1 by omega, show (8 + i) % 8 = i by omega]
    show blake2sWords ((P.seed.res ++ [P.ctrs + 1]).map (word ∘ ρ)) 36 i = _
    rw [List.map_append, hsw]; simp [c1]
  have l0 : P.s0.res.length = 8 := BlockRec.blake2s_length (P.ctrs + 2) (P.seed.res ++ [P.ctrs]) 36
  -- Each value: `low31` of the stream word, equal to child 0's limb.
  intro j hj
  obtain ⟨r, hr, hl⟩ := chainOuts_holds (f := fun j n => low31 ((P.s0.res ++ P.s1.res).getD j 0) P.ci n) (n := P.ci + 1) hj hv
  have hwj : IsU32 (ρ ((P.s0.res ++ P.s1.res).getD j 0)) ∧ word (ρ ((P.s0.res ++ P.s1.res).getD j 0)) = streamWord ρ M prevV j := by
    by_cases h8 : j < 8
    · rw [List.getD_append _ _ _ _ (by omega)]
      refine ⟨?_, w0 j h8⟩
      exact (congrArg IsU32 (blake2s_res_pack hs0 j h8)).mpr (isU32_pack _)
    · rw [List.getD_append_right _ _ _ _ (by omega), l0]
      obtain ⟨i, rfl⟩ : ∃ i, j = 8 + i := ⟨j - 8, by omega⟩
      rw [show 8 + i - 8 = i by omega]
      refine ⟨?_, w1 i (by omega)⟩
      exact (congrArg IsU32 (blake2s_res_pack hs1 i (by omega))).mpr (isU32_pack _)
  have ls := low31_sound hl ci hwj.1
  have e := heq _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only [Op.holds] at e
  have hget : (P.vals.getD j ⟨[], 0, 0⟩) = low31 ((P.s0.res ++ P.s1.res).getD j 0) P.ci r := by
    rw [List.getD_eq_getElem _ _ (by rw [show P.vals.length = 12 from chainOuts_length _ _ 12]; exact hj)]
    exact hr
  rw [hget] at e
  rw [← e, ← hwj.2]
  exact ls

/-! ### The epoch root, assembled -/

/-- A child section's summary limbs are guessed base values. -/
theorem bchild_base {n i : ℕ} (h : Holds ρ (BlockNode.bchild n i).ops) :
    ∀ k < BlockNode.NSUM, IsBase (ρ ((BlockNode.bchild n i).res.pubs k)) := by
  intro k hk
  dsimp only [BlockNode.bchild] at h ⊢
  have := h _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)))))
  simpa [Op.holds] using this

theorem kid_base {i : ℕ} (h : Holds ρ (kid i).ops) : ∀ k < BlockNode.NSUM, IsBase (ρ ((kid i).res.pubs k)) := by
  cases i with
  | zero => exact bchild_base h
  | succ i => exact bchild_base h

/-- **The epoch root is sound** (given each child's input count below `2^30`, which a proven child
summary has). With `p i` child `i`'s summary registers, `lo`/`hi` the epoch's range inputs:
1. the ranges: child 0 starts at `lo`, each child where the previous ends, the last ends at `hi + 1`;
   `lo`, `hi + 1` below `2^30`; each child's count is `2^k` with `k < 31`;
2. one challenge: every child's limbs 7–18 equal child 0's, which are the low 31 bits of the
   challenge stream over the seed (`streamWord`), never the rejected value;
3. the sums: limbs 2–5 and 6 of the result are the children's sums, the input count's integer sum
   below `2^30`. -/
theorem root_sound {M : ℕ} {prevV : Bool} (hM : 0 < M) (h : Holds ρ (epochRoot M prevV).ops)
    (hB : 4 * (seedMsg M prevV).length < 2 ^ 32)
    (hn : ∀ i < M, (ρ ((kid i).res.pubs BlockNode.NIN)).a.val < 2 ^ 30) :
    let P := parts M prevV
    let p : ℕ → ℕ → ℕ := fun i => (kid i).res.pubs
    -- 1. the ranges
    (ρ (p 0 BlockNode.LO) = ρ P.inp.res.lo ∧
      (∀ i, i + 1 < M → ρ (p (i + 1) BlockNode.LO) = ρ (p i BlockNode.LO) + ρ (p i BlockNode.NN)) ∧
      ρ (p (M - 1) BlockNode.LO) + ρ (p (M - 1) BlockNode.NN) = ρ P.inp.res.hi + lit 1 0 0 0 ∧
      (ρ P.inp.res.lo).a.val < 2 ^ 30 ∧ (ρ P.inp.res.hi + lit 1 0 0 0).a.val < 2 ^ 30 ∧
      ∀ i < M, ∃ k < LOGS, (ρ (p i BlockNode.NN)).a = ((2 ^ k : ℕ) : F) ∧
        (ρ (P.logs.getD i ⟨[], 0, 0⟩).res).a = (k : F)) ∧
    -- 2. one challenge, the stream's
    (∀ i < M, ∀ j < 12, ρ (p i (BlockNode.CH + j)) = ρ (p 0 (BlockNode.CH + j))) ∧
    (∀ j < 12, (ρ (p 0 (BlockNode.CH + j))).a.val = (streamWord ρ M prevV j).toNat % 2 ^ 31 ∧
      (streamWord ρ M prevV j).toNat % 2 ^ 31 ≠ 2 ^ 31 - 1) ∧
    -- 3. the sums
    ((∀ j < 5, (ρ (sumReg p P.lk.next (M - 1) j)).a = ∑ i ∈ Finset.range M, (ρ (p i (BlockNode.SS + j))).a) ∧
      (ρ (sumReg p P.lk.next (M - 1) 4)).a.val = ∑ i ∈ Finset.range M, (ρ (p i BlockNode.NIN)).a.val ∧
      (ρ (sumReg p P.lk.next (M - 1) 4)).a.val < 2 ^ 30) := by
  intro P p
  obtain ⟨hk, -, hlk, hsc, hsm, hlogs, -, -, -, -, -, -, -, -, -, -⟩ := root_parts h
  have lk := links_sound (M := M) (p := p) hM hlk
  have base : ∀ i < M, ∀ k < BlockNode.NSUM, IsBase (ρ (p i k)) := fun i hi => kid_base (BlockNodeK.kid_holds hi hk)
  have sm := sums_sound (M := M) (p := p) (n := P.lk.next) hM hsm
    (fun i hi j hj => base i hi _ (by unfold BlockNode.SS BlockNode.NSUM; omega)) hn
  have ch := root_challenge h hB
  refine ⟨⟨lk.1, lk.2.1, lk.2.2.1, lk.2.2.2.1.2, lk.2.2.2.2.2, fun i hi => ?_⟩, fun i hi j hj => ?_, fun j hj => (ch j hj).2,
    fun j hj => (sm.1 j hj).2, sm.2.1, sm.2.2⟩
  · obtain ⟨r, hr, hl⟩ := chainOuts_holds (f := fun i n => logOf (p i BlockNode.NN) n) (n := P.sm.next) hi hlogs
    obtain ⟨k, hk', e1, e2⟩ := logOf_sound hl
    refine ⟨k, hk', e1, ?_⟩
    have hget : P.logs.getD i ⟨[], 0, 0⟩ = logOf (p i BlockNode.NN) r := by
      rw [List.getD_eq_getElem _ _ (by rw [show P.logs.length = M from chainOuts_length _ _ M]; exact hi)]
      exact hr
    rw [hget]; exact e2
  · cases i with
    | zero => rfl
    | succ i =>
      have := hsc _ (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr (by omega),
        List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩⟩)
      simpa [Op.holds] using this

/-! ### The output digest -/

/-- **`digestOut` is sound**: its result words are Blake2s of the key, the set digests and each public
register's base value as a word. -/
theorem digestOut_sound {key fin prev : List ℕ} {prevV : Bool} {pubs : List ℕ} {dn : ℕ}
    (h : Holds ρ (digestOut key fin prev prevV pubs dn).ops)
    (hB : 4 * (key.length + fin.length + (if prevV then prev.length else 0) + pubs.length) < 2 ^ 32) :
    ∀ i < 8, word (ρ ((digestOut key fin prev prevV pubs dn).res.getD i 0)) =
      blake2sWords (key.map (word ∘ ρ) ++ fin.map (word ∘ ρ) ++ (if prevV then prev.map (word ∘ ρ) else []) ++
        pubs.map (fun r => BitVec.ofNat 32 (ρ r).a.val))
        (4 * (key.length + fin.length + (if prevV then prev.length else 0) + pubs.length)) i := by
  dsimp only [digestOut] at h ⊢
  rw [holds_append] at h
  obtain ⟨hm, hb⟩ := h
  have hlen : (key ++ fin ++ (if prevV then prev else []) ++ (List.range pubs.length).map (dn + ·)).length =
      key.length + fin.length + (if prevV then prev.length else 0) + pubs.length := by
    cases prevV <;> simp <;> omega
  intro i hi
  rw [blake2s_words hb (by rw [hlen]; exact hB) i hi, hlen]
  congr 1
  simp only [List.map_append]
  congr 1
  · cases prevV <;> simp
  · rw [map_eq_range_getD (fun r => BitVec.ofNat 32 (ρ r).a.val) 0 pubs, List.map_map]
    refine List.map_congr_left (fun j hj => ?_)
    have := hm _ (List.mem_map.mpr ⟨j, hj, rfl⟩)
    simp only [Op.holds] at this
    simp only [Function.comp, this.2, word_m2u]

/-- The digest's word message. -/
def digestWords (ρ : ℕ → Q) (M : ℕ) (prevV : Bool) : List Spec.Blake2s.Word :=
  let P := parts M prevV
  P.key.res.map (word ∘ ρ) ++ P.inp.res.fin.map (word ∘ ρ) ++ (if prevV then P.inp.res.prev.map (word ∘ ρ) else []) ++
    P.dpubs.map (fun r => BitVec.ofNat 32 (ρ r).a.val)

/-- **The output digest** is Blake2s of `digestWords` (the key, the set digests, then `from`, `to`, the
summed partial sum and input count, child 0's challenge limbs and each child's block-hash root limbs,
`parts`' `dpubs`); the key is Blake2s of the children's circuit hashes and keys. -/
theorem root_digest {M : ℕ} {prevV : Bool} (h : Holds ρ (epochRoot M prevV).ops)
    (hB : 4 * (8 + 8 + (if prevV then 8 else 0) + (parts M prevV).dpubs.length) < 2 ^ 32) (hK : 64 * M < 2 ^ 32) :
    (∀ i < 8, word (ρ ((epochRoot M prevV).results.getD i 0)) =
      blake2sWords (digestWords ρ M prevV) (4 * (8 + 8 + (if prevV then 8 else 0) + (parts M prevV).dpubs.length)) i) ∧
    (∀ i < 8, word (ρ ((parts M prevV).key.res.getD i 0)) = blake2sWords ((keyMsg M).map (word ∘ ρ)) (64 * M) i) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hkey, hdg⟩ := root_parts h
  refine ⟨fun i hi => ?_, fun i hi => blake2s_words hkey hK i hi⟩
  have hk8 : (parts M prevV).key.res.length = 8 := by
    show ((List.range 8).map _).length = 8; simp
  have hf8 : (parts M prevV).inp.res.fin.length = 8 := by
    show ((List.range 8).map _).length = 8; simp
  have hp8 : (parts M prevV).inp.res.prev.length = 8 := by
    show ((List.range 8).map _).length = 8; simp
  have hd : Holds ρ (digestOut (parts M prevV).key.res (parts M prevV).inp.res.fin (parts M prevV).inp.res.prev prevV
      (parts M prevV).dpubs (parts M prevV).key.next).ops := hdg
  have e := digestOut_sound hd (by rw [hk8, hf8, hp8]; exact hB) i hi
  rw [hk8, hf8, hp8] at e
  exact e

end StarkedAir.Circuit.EpochRoot
