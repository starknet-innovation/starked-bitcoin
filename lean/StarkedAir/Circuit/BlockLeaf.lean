/-
**The block leaf's own checks (BLOCK-REC), Lean-first.** A block leaf verifies a block proof with the
plain verifier, then checks what `rng_leaf` (Block/AggregateBlocks.lean) needs of the public inputs:
- the challenge's weights are powers of one `α`: `αₖ = α₁ᵏ` for `k < 26` (`α₀ = 1`);
- the BIP30 flag is the height's: `lost = 1` exactly when the height is 0, 91,722 or 91,812.

`checksP` is the program (hook 0 binds the height, the flag, then the 104 limbs of `α₀ … α₂₅`);
`checks_sound`: if its ops hold on base-field inputs and the height `H < P`, both facts hold.
-/
import StarkedAir.Circuit.CompositionLogUp
import StarkedAir.Spec.Coins
import StarkedAir.Block.AggregateBlocks

namespace StarkedAir.Circuit.BlockLeaf

open StarkedAir StarkedAir.Circuit StarkedAir.Circuit.Composition Q
open StarkedAir.Spec.QM31 (QM toQ emb toQ_mul toQ_add toQ_sub emb_inj)

/-- Registers: 0 the height, 1 the flag, `2 + j` limb `j` of the weights (`4k … 4k+3` for `αₖ`). -/
def N_IN : ℕ := 106
def NW : ℕ := 26

/-- `αₖ` as one QM31 register: `secure` of its four limbs, from register `N_IN + 9k` (result `+ 8`). -/
def wReg (k : ℕ) : ℕ := N_IN + 9 * k + 8
def M0 : ℕ := N_IN + 9 * NW
def M1 : ℕ := M0 + NW

def checksOps : List Op :=
  (List.range NW).flatMap (fun k => (secureOps (N_IN + 9 * k) (fun t => 2 + 4 * k + t)).ops) ++
  [.one M0, .eq (wReg 0) M0] ++
  (List.range (NW - 1)).flatMap (fun j => [.mul (M0 + j + 1) (wReg j) (wReg 1), .eq (wReg (j + 1)) (M0 + j + 1)]) ++
  [.const M1 91722 0 0 0, .const (M1 + 1) 91812 0 0 0, .sub (M1 + 2) 0 M1, .sub (M1 + 3) 0 (M1 + 1),
   .mul (M1 + 4) 0 (M1 + 2), .mul (M1 + 5) (M1 + 4) (M1 + 3),
   .mul (M1 + 6) 1 1, .eq (M1 + 6) 1,
   .mul (M1 + 7) 1 (M1 + 5), .zero (M1 + 8), .eq (M1 + 7) (M1 + 8),
   .guess (M1 + 9) (.invOrZero (.reg (M1 + 5))), .mul (M1 + 10) (M1 + 5) (M1 + 9),
   .sub (M1 + 11) M0 1, .sub (M1 + 12) (M1 + 10) M0, .mul (M1 + 13) (M1 + 11) (M1 + 12), .eq (M1 + 13) (M1 + 8)]

/-- The program with its input hook. -/
def checksP : List Op := .hook 0 [] (List.range N_IN) :: checksOps

/-! ### Soundness -/

variable {ρ : ℕ → Q}

theorem toQ_base {x : Q} (h : IsBase x) : toQ x = emb x.a := by
  obtain ⟨hb, hc, hd⟩ := h
  simp [Spec.QM31.toQ, hb, hc, hd, Spec.QM31.emb]

/-- `secure` of four base limbs is the QM31 value with those coordinates. -/
theorem secure_toQ (a b c d : F) :
    emb a + emb b * e1 + emb c * e2 + emb d * e3 = toQ ⟨a, b, c, d⟩ := by
  simp only [e1, e2, e3, Spec.QM31.toQ, lit, Nat.cast_zero, Nat.cast_one, map_zero, map_one, Spec.QM31.emb]
  ring

theorem holds_mem {o : Op} {l : List Op} (h : Holds ρ l) (ho : o ∈ l) : o.holds ρ := h o ho

/-- **The block leaf's checks are sound.** -/
theorem checks_sound (h : Holds ρ checksOps) (hb : ∀ j < N_IN, IsBase (ρ j)) {H : ℕ} (hH : H < P)
    (hh : (ρ 0).a = (H : F)) :
    (∀ k < NW, toQ ⟨(ρ (2 + 4 * k)).a, (ρ (3 + 4 * k)).a, (ρ (4 + 4 * k)).a, (ρ (5 + 4 * k)).a⟩ =
      toQ ⟨(ρ 6).a, (ρ 7).a, (ρ 8).a, (ρ 9).a⟩ ^ k) ∧
    (ρ 1).a = if Spec.Coins.bip30Lost H then 1 else 0 := by
  unfold checksOps at h
  rw [holds_append, holds_append, holds_append] at h
  obtain ⟨⟨⟨hsec, hone⟩, hpow⟩, hlost⟩ := h
  -- the weights as QM31 registers
  have hw : ∀ k < NW, val ρ (wReg k) =
      toQ ⟨(ρ (2 + 4 * k)).a, (ρ (3 + 4 * k)).a, (ρ (4 + 4 * k)).a, (ρ (5 + 4 * k)).a⟩ := by
    intro k hk
    have hs : Holds ρ (secureOps (N_IN + 9 * k) (fun t => 2 + 4 * k + t)).ops := fun o ho =>
      hsec o (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, ho⟩)
    have := secure_sound hs
    simp only [secureOps] at this
    unfold wReg
    rw [this]
    simp only [val]
    have b : ∀ t < 4, toQ (ρ (2 + 4 * k + t)) = emb (ρ (2 + 4 * k + t)).a := fun t ht =>
      toQ_base (hb _ (by unfold N_IN NW at *; omega))
    rw [b 0 (by norm_num), b 1 (by norm_num), b 2 (by norm_num), b 3 (by norm_num), secure_toQ]
    congr 2 <;> ring_nf
  have one_v : val ρ M0 = 1 := by
    have := holds_mem hone (o := .one M0) (by simp)
    simp only [Op.holds] at this
    rw [val, this, toQ_lit1]
  -- powers
  have hp : ∀ k < NW, val ρ (wReg k) = val ρ (wReg 1) ^ k := by
    intro k
    induction k with
    | zero =>
      intro _
      have := holds_mem hone (o := .eq (wReg 0) M0) (by simp)
      simp only [Op.holds] at this
      rw [pow_zero, ← one_v, val, val, this]
    | succ j ih =>
      intro hj
      have m := holds_mem hpow (o := .mul (M0 + j + 1) (wReg j) (wReg 1))
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by unfold NW at *; omega), by simp⟩)
      have e := holds_mem hpow (o := .eq (wReg (j + 1)) (M0 + j + 1))
        (List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by unfold NW at *; omega), by simp⟩)
      simp only [Op.holds] at m e
      rw [val, e, m, toQ_mul, ← val, ← val, ih (by omega), pow_succ]
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [← hw k hk, ← hw 1 (by unfold NW; norm_num), hp k hk]
  -- the flag
  have g := fun (o : Op) (ho : o ∈ _) => holds_mem hlost (o := o) ho
  have c1 := g (.const M1 91722 0 0 0) (by simp)
  have c2 := g (.const (M1 + 1) 91812 0 0 0) (by simp)
  have s2 := g (.sub (M1 + 2) 0 M1) (by simp)
  have s3 := g (.sub (M1 + 3) 0 (M1 + 1)) (by simp)
  have m4 := g (.mul (M1 + 4) 0 (M1 + 2)) (by simp)
  have m5 := g (.mul (M1 + 5) (M1 + 4) (M1 + 3)) (by simp)
  have m6 := g (.mul (M1 + 6) 1 1) (by simp)
  have e6 := g (.eq (M1 + 6) 1) (by simp)
  have m7 := g (.mul (M1 + 7) 1 (M1 + 5)) (by simp)
  have z8 := g (.zero (M1 + 8)) (by simp)
  have e7 := g (.eq (M1 + 7) (M1 + 8)) (by simp)
  have m10 := g (.mul (M1 + 10) (M1 + 5) (M1 + 9)) (by simp)
  have s11 := g (.sub (M1 + 11) M0 1) (by simp)
  have s12 := g (.sub (M1 + 12) (M1 + 10) M0) (by simp)
  have m13 := g (.mul (M1 + 13) (M1 + 11) (M1 + 12)) (by simp)
  have e13 := g (.eq (M1 + 13) (M1 + 8)) (by simp)
  simp only [Op.holds] at c1 c2 s2 s3 m4 m5 m6 e6 m7 z8 e7 m10 s11 s12 m13 e13
  set Lq := toQ (ρ 1) with hLq
  set Hq := toQ (ρ 0) with hHq
  have hL : Lq = emb (ρ 1).a := toQ_base (hb 1 (by unfold N_IN; norm_num))
  have hHe : Hq = emb (H : F) := by rw [hHq, toQ_base (hb 0 (by unfold N_IN; norm_num)), hh]
  have zero8 : toQ (ρ (M1 + 8)) = 0 := by rw [z8, toQ_lit0]
  have dval : toQ (ρ (M1 + 5)) = Hq * (Hq - emb (91722 : F)) * (Hq - emb (91812 : F)) := by
    rw [m5, toQ_mul, m4, toQ_mul, s2, toQ_sub, s3, toQ_sub, c1, c2, toQ_lit, toQ_lit]
    push_cast; ring
  have bool : Lq * Lq = Lq := by rw [hLq, ← toQ_mul, ← m6, e6]
  have prod0 : Lq * toQ (ρ (M1 + 5)) = 0 := by rw [hLq, ← toQ_mul, ← m7, e7, zero8]
  have inv1 : (1 - Lq) * (toQ (ρ (M1 + 5)) * toQ (ρ (M1 + 9)) - 1) = 0 := by
    have := congrArg toQ (m13.symm.trans e13)
    rw [toQ_mul, s11, s12, toQ_sub, toQ_sub, m10, toQ_mul, zero8] at this
    rw [← one_v, val] at *
    exact this
  have hl01 : (ρ 1).a = 0 ∨ (ρ 1).a = 1 := by
    have : Lq * (Lq - 1) = 0 := by rw [mul_sub, mul_one, bool, sub_self]
    rcases mul_eq_zero.mp this with h0 | h1
    · left; apply emb_inj; rw [← hL, h0]; simp [Spec.QM31.emb]
    · right; apply emb_inj; rw [← hL, sub_eq_zero.mp h1]; simp [Spec.QM31.emb]
  have hc1 : (91722 : ℕ) < P := by unfold P; norm_num
  have hc2 : (91812 : ℕ) < P := by unfold P; norm_num
  rcases hl01 with h0 | h1
  · -- not lost: the product is invertible, so the height is none of the three
    have hL0 : Lq = 0 := by rw [hL, h0]; simp [Spec.QM31.emb]
    rw [hL0, sub_zero, one_mul, sub_eq_zero] at inv1
    have hD : toQ (ρ (M1 + 5)) ≠ 0 := fun hz => by rw [hz, zero_mul] at inv1; exact zero_ne_one inv1
    rw [dval, hHe] at hD
    rw [h0]
    have : Spec.Coins.bip30Lost H = false := by
      unfold Spec.Coins.bip30Lost
      by_contra hc
      simp only [Bool.not_eq_false, Bool.or_eq_true, beq_iff_eq] at hc
      apply hD
      rcases hc with (rfl | rfl) | rfl <;> simp
    rw [this]; rfl
  · -- lost: the product is zero, so the height is one of the three
    have hL1 : Lq = 1 := by rw [hL, h1]; simp [Spec.QM31.emb]
    rw [hL1, one_mul, dval, hHe] at prod0
    rw [h1]
    have hF : (H : F) = 0 ∨ (H : F) = ((91722 : ℕ) : F) ∨ (H : F) = ((91812 : ℕ) : F) := by
      rcases mul_eq_zero.mp prod0 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · left; exact emb_inj (by rw [h]; simp [Spec.QM31.emb])
        · right; left; apply emb_inj; rw [sub_eq_zero.mp h]; push_cast; rfl
      · right; right; apply emb_inj; rw [sub_eq_zero.mp h]; push_cast; rfl
    have : Spec.Coins.bip30Lost H = true := by
      unfold Spec.Coins.bip30Lost
      simp only [Bool.or_eq_true, beq_iff_eq]
      rcases hF with h | h | h
      · left; left; exact natCast_inj_of_lt hH (by unfold P; norm_num) (by simpa using h)
      · left; right; exact natCast_inj_of_lt hH hc1 h
      · right; exact natCast_inj_of_lt hH hc2 h
    rw [this]; rfl

/-- **In terms of public inputs.** If the input registers hold the block's public inputs `p` (the
height at 2, the flag at `PUB_LOST`, the weights' limbs from `PUB_ALPHA 0`), the leaf's checks give
`rng_leaf`'s two hypotheses. -/
theorem checks_pub (h : Holds ρ checksOps) {p : ℕ → F} (hreg : ∀ j < N_IN, ρ j = ⟨if j = 0 then p 2 else if j = 1 then
      p Block.Coin.PUB_LOST else p (Block.Coin.PUB_ALPHA 0 + (j - 2)), 0, 0, 0⟩)
    {H : ℕ} (hH : H < P) (h2 : p 2 = (H : F)) :
    p Block.Coin.PUB_LOST = (if Spec.Coins.bip30Lost H then 1 else 0) ∧
      ∀ k < Block.Coin.W, Block.RunSum.pQ p (Block.Coin.PUB_ALPHA k) =
        Block.RunSum.pQ p (Block.Coin.PUB_ALPHA 1) ^ k := by
  have hb : ∀ j < N_IN, IsBase (ρ j) := fun j hj => by rw [hreg j hj]; exact ⟨rfl, rfl, rfl⟩
  have r0 : (ρ 0).a = p 2 := by rw [hreg 0 (by unfold N_IN; norm_num)]; simp
  obtain ⟨hpow, hl⟩ := checks_sound h hb hH (by rw [r0, h2])
  have r1 : (ρ 1).a = p Block.Coin.PUB_LOST := by rw [hreg 1 (by unfold N_IN; norm_num)]; simp
  have rw' : ∀ k < NW, ∀ t < 4, (ρ (2 + 4 * k + t)).a = p (Block.Coin.PUB_ALPHA k + t) := by
    intro k hk t ht
    rw [hreg _ (by unfold N_IN NW at *; omega)]
    simp only [show 2 + 4 * k + t ≠ 0 by omega, show 2 + 4 * k + t ≠ 1 by omega, if_false, Block.Coin.PUB_ALPHA]
    congr 1; omega
  refine ⟨r1 ▸ hl, fun k hk => ?_⟩
  have e := hpow k hk
  have q : ∀ j < NW, Block.RunSum.pQ p (Block.Coin.PUB_ALPHA j) =
      toQ ⟨(ρ (2 + 4 * j)).a, (ρ (3 + 4 * j)).a, (ρ (4 + 4 * j)).a, (ρ (5 + 4 * j)).a⟩ := by
    intro j hj
    have a0 := rw' j hj 0 (by norm_num)
    have a1 := rw' j hj 1 (by norm_num)
    have a2 := rw' j hj 2 (by norm_num)
    have a3 := rw' j hj 3 (by norm_num)
    simp only [Nat.add_zero] at a0
    rw [show 2 + 4 * j + 1 = 3 + 4 * j by omega] at a1
    rw [show 2 + 4 * j + 2 = 4 + 4 * j by omega] at a2
    rw [show 2 + 4 * j + 3 = 5 + 4 * j by omega] at a3
    rw [a0, a1, a2, a3]; rfl
  rw [q k (by unfold NW; exact hk), q 1 (by unfold NW; norm_num)]
  exact e

/-- The exported program. -/
def checksJson : String :=
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (checksP.map Op.toJson)}],\"results\":[]}"

end StarkedAir.Circuit.BlockLeaf
