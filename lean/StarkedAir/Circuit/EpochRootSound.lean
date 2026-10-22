/-
**The epoch root's soundness, gadget by gadget** (`Circuit/EpochRoot.lean`).

- `low31_sound`: a challenge word's value is its low 31 bits, and those are not `2^31 − 1` (the stream's
  rejection, `epoch.challenge`), so the value is canonical: the same M31 the native stream draws.
-/
import StarkedAir.Circuit.EpochRoot

namespace StarkedAir.Circuit.EpochRoot

open StarkedAir StarkedAir.Circuit Q

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

end StarkedAir.Circuit.EpochRoot
