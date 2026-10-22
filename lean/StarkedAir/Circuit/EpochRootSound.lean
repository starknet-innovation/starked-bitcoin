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

end StarkedAir.Circuit.EpochRoot
