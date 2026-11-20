/-
**The spent script's class (CONNECT-RULES step 3), soundness.** `block_urec` reads four bytes of each
record's `serTxOut` and sets `CP` (P2SH), `C20`, `C32` (version 0 witness program of 20 or 32 bytes).
`URec.class_spec` is the row: the flags are the byte patterns. `urec_class` reads the bytes from the
undo stream, and `claim_class` states the flags for a claim that is a real `serTxOut`, where they are
`isP2SH` and `isW` of the spent script (`Spec/SigClass.lean`).
-/
import StarkedAir.Block.CoinRecs
import StarkedAir.Spec.SigClass

namespace StarkedAir.Block.URec

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst)

section ClassRows

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem mem_class {c : Expr} (h : c ∈ classC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; exact Or.inr h

theorem czspec {z inv : ℕ} {e : Expr} (h : ∀ c ∈ isZero z inv e, c ∈ classC) {r : ℕ} (hr : r < n) :
    (M z r = 0 ∨ M z r = 1) ∧ (M z r = 1 ↔ e.eval n preCols pub M r = 0) := by
  have h1 := sat hsat (mem_class (h (boolC (k z)) (by simp [isZero]))) hr
  have h2 := sat hsat (mem_class (h (.mul (k z) e) (by simp [isZero]))) hr
  have h3 := sat hsat (mem_class (h (.mul (om (k z)) (.sub (.mul e (k inv)) one)) (by simp [isZero]))) hr
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, om, one, Nat.cast_one] at h1 h2 h3
  have hb : M z r = 0 ∨ M z r = 1 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  refine ⟨hb, ⟨fun h1' => by rw [h1', one_mul] at h2; exact h2, fun h0 => ?_⟩⟩
  rcases hb with hz | hz
  · rw [hz, h0] at h3; simp at h3
  · exact hz

/-- **A record row's class flags are the byte patterns.** With `b0` the script's length byte, `b1`, `b2`
its first two bytes (read when the length is one of the three) and `b3` its 23rd (read for P2SH). -/
theorem class_spec {r : ℕ} (hr : r < n) {b0 b1 b2 b3 : ℕ} (hb0 : b0 < 256) (hb1 : b1 < 256) (hb2 : b2 < 256)
    (hb3 : b3 < 256) (h0 : (M (U 0) r).val = b0)
    (h12 : M Z16 r + (M Z17 r + M Z22 r) = 1 → (M (U 1) r).val = b1 ∧ (M (U 2) r).val = b2)
    (h3 : M PC r = 1 → (M (U 3) r).val = b3) :
    ((M CP r = 1 ∧ (b0 = 0x17 ∧ b1 = 0xa9 ∧ b2 = 0x14 ∧ b3 = 0x87)) ∨
      (M CP r = 0 ∧ ¬ (b0 = 0x17 ∧ b1 = 0xa9 ∧ b2 = 0x14 ∧ b3 = 0x87))) ∧
    ((M C20 r = 1 ∧ (b0 = 0x16 ∧ b1 = 0 ∧ b2 = 0x14)) ∨ (M C20 r = 0 ∧ ¬ (b0 = 0x16 ∧ b1 = 0 ∧ b2 = 0x14))) ∧
    ((M C32 r = 1 ∧ (b0 = 0x22 ∧ b1 = 0 ∧ b2 = 0x20)) ∨ (M C32 r = 0 ∧ ¬ (b0 = 0x22 ∧ b1 = 0 ∧ b2 = 0x20))) := by
  have hP : P = 2147483647 := rfl
  have u0 : M (U 0) r = (b0 : F) := by rw [← h0, ZMod.natCast_zmod_val]
  have inj : ∀ {a b : ℕ}, a < 2 ^ 20 → b < 2 ^ 20 → ((a : ℕ) : F) = ((b : ℕ) : F) → a = b := fun ha hb h =>
    natCast_inj_of_lt (by omega) (by omega) h
  -- the three length flags
  have zf : ∀ (z inv v : ℕ), v < 256 → (∀ c ∈ isZero z inv (.sub (k (U 0)) (cst v)), c ∈ classC) →
      (M z r = 1 ∧ b0 = v) ∨ (M z r = 0 ∧ b0 ≠ v) := by
    intro z inv v hv hm
    have zs := czspec hsat hm hr
    simp only [Expr.eval, ev_k hr, eval_cst, u0, sub_eq_zero] at zs
    rcases zs.1 with h | h
    · exact Or.inr ⟨h, fun e => by rw [zs.2.2 (by rw [e])] at h; exact one_ne_zero h⟩
    · exact Or.inl ⟨h, inj (by omega) (by omega) (zs.2.1 h)⟩
  have f16 := zf Z16 I16 0x16 (by norm_num) (fun c hc => by simp only [classC, List.mem_append]; tauto)
  have f17 := zf Z17 I17 0x17 (by norm_num) (fun c hc => by simp only [classC, List.mem_append]; tauto)
  have f22 := zf Z22 I22 0x22 (by norm_num) (fun c hc => by simp only [classC, List.mem_append]; tauto)
  have zm := czspec hsat (z := ZM) (inv := IM) (e := patE) (fun c hc => by simp only [classC, List.mem_append]; tauto) hr
  simp only [patE, Expr.eval, ev_k hr, eval_cst, Nat.cast_ofNat] at zm
  have z87 := czspec hsat (z := Z87) (inv := I87) (e := .sub (k (U 3)) (cst 0x87))
    (fun c hc => by simp only [classC, List.mem_append]; exact Or.inl (Or.inr hc)) hr
  simp only [Expr.eval, ev_k hr, eval_cst, Nat.cast_ofNat] at z87
  have dpc := sat hsat (mem_class (c := .sub (k PC) (.mul (k Z17) (k ZM))) (by simp [classC])) hr
  have dcp := sat hsat (mem_class (c := .sub (k CP) (.mul (k PC) (k Z87))) (by simp [classC])) hr
  have d20 := sat hsat (mem_class (c := .sub (k C20) (.mul (k Z16) (k ZM))) (by simp [classC])) hr
  have d32 := sat hsat (mem_class (c := .sub (k C32) (.mul (k Z22) (k ZM))) (by simp [classC])) hr
  simp only [Expr.eval, ev_k hr, sub_eq_zero] at dpc dcp d20 d32
  -- the pattern test, once the two bytes are read
  have pat : M Z16 r + (M Z17 r + M Z22 r) = 1 → ∀ (z16 z17 z22 : ℕ), M Z16 r = (z16 : F) → M Z17 r = (z17 : F) →
      M Z22 r = (z22 : F) → z16 ≤ 1 → z17 ≤ 1 → z22 ≤ 1 →
      (M ZM r = 1 ∧ b1 + 256 * b2 = 0xa9 * z17 + 256 * (0x14 * (z16 + z17) + 0x20 * z22)) ∨
      (M ZM r = 0 ∧ b1 + 256 * b2 ≠ 0xa9 * z17 + 256 * (0x14 * (z16 + z17) + 0x20 * z22)) := by
    intro hs z16 z17 z22 e16 e17 e22 l16 l17 l22
    obtain ⟨v1, v2⟩ := h12 hs
    have u1 : M (U 1) r = (b1 : F) := by rw [← v1, ZMod.natCast_zmod_val]
    have u2 : M (U 2) r = (b2 : F) := by rw [← v2, ZMod.natCast_zmod_val]
    rw [u1, u2, e16, e17, e22] at zm
    have key : ((b1 : F) - 0xa9 * (z17 : F) + 256 * ((b2 : F) - 0x14 * ((z16 : F) + (z17 : F)) - 0x20 * (z22 : F)) = 0) ↔
        b1 + 256 * b2 = 0xa9 * z17 + 256 * (0x14 * (z16 + z17) + 0x20 * z22) := by
      constructor
      · intro h
        apply inj (by omega) (by omega)
        push_cast; linear_combination h
      · intro h
        have := congrArg (fun x : ℕ => (x : F)) h
        push_cast at this; linear_combination this
    rcases zm.1 with h | h
    · exact Or.inr ⟨h, fun e => by rw [zm.2.2 (key.mpr e)] at h; exact one_ne_zero h⟩
    · exact Or.inl ⟨h, key.mp (zm.2.1 h)⟩
  rcases f16 with ⟨a16, e16⟩ | ⟨a16, n16⟩
  · -- length 0x16
    have a17 : M Z17 r = 0 := by rcases f17 with ⟨-, e⟩ | ⟨a, -⟩ <;> [omega; exact a]
    have a22 : M Z22 r = 0 := by rcases f22 with ⟨-, e⟩ | ⟨a, -⟩ <;> [omega; exact a]
    have cp0 : M CP r = 0 := by rw [dcp, dpc, a17]; ring
    have c32 : M C32 r = 0 := by rw [d32, a22]; ring
    refine ⟨Or.inr ⟨cp0, by omega⟩, ?_, Or.inr ⟨c32, by omega⟩⟩
    rcases pat (by rw [a16, a17, a22]; ring) 1 0 0 (by simp [a16]) (by simp [a17]) (by simp [a22]) le_rfl
      (by norm_num) (by norm_num) with ⟨m, e⟩ | ⟨m, e⟩
    · exact Or.inl ⟨by rw [d20, a16, m]; ring, e16, by omega, by omega⟩
    · exact Or.inr ⟨by rw [d20, m]; ring, by omega⟩
  rcases f17 with ⟨a17, e17⟩ | ⟨a17, n17⟩
  · -- length 0x17
    have a22 : M Z22 r = 0 := by rcases f22 with ⟨-, e⟩ | ⟨a, -⟩ <;> [omega; exact a]
    have c20 : M C20 r = 0 := by rw [d20, a16]; ring
    have c32 : M C32 r = 0 := by rw [d32, a22]; ring
    refine ⟨?_, Or.inr ⟨c20, by omega⟩, Or.inr ⟨c32, by omega⟩⟩
    rcases pat (by rw [a16, a17, a22]; ring) 0 1 0 (by simp [a16]) (by simp [a17]) (by simp [a22]) (by norm_num)
      le_rfl (by norm_num) with ⟨m, e⟩ | ⟨m, e⟩
    · have pc1 : M PC r = 1 := by rw [dpc, a17, m]; ring
      have v3 := h3 pc1
      have u3 : M (U 3) r = (b3 : F) := by rw [← v3, ZMod.natCast_zmod_val]
      rw [u3, sub_eq_zero] at z87
      rcases z87.1 with h | h
      · refine Or.inr ⟨by rw [dcp, h]; ring, fun e' => ?_⟩
        rw [z87.2.2 (by rw [e'.2.2.2]; norm_num)] at h; exact one_ne_zero h
      · refine Or.inl ⟨by rw [dcp, pc1, h]; ring, e17, by omega, by omega, ?_⟩
        exact inj (by omega) (by norm_num) (by have := z87.2.1 h; push_cast; exact this)
    · exact Or.inr ⟨by rw [dcp, dpc, m]; ring, by omega⟩
  have cp0 : M CP r = 0 := by rw [dcp, dpc, a17]; ring
  have c20 : M C20 r = 0 := by rw [d20, a16]; ring
  rcases f22 with ⟨a22, e22⟩ | ⟨a22, n22⟩
  · -- length 0x22
    refine ⟨Or.inr ⟨cp0, by omega⟩, Or.inr ⟨c20, by omega⟩, ?_⟩
    rcases pat (by rw [a16, a17, a22]; ring) 0 0 1 (by simp [a16]) (by simp [a17]) (by simp [a22]) (by norm_num)
      (by norm_num) le_rfl with ⟨m, e⟩ | ⟨m, e⟩
    · exact Or.inl ⟨by rw [d32, a22, m]; ring, e22, by omega, by omega⟩
    · exact Or.inr ⟨by rw [d32, m]; ring, by omega⟩
  · exact ⟨Or.inr ⟨cp0, by omega⟩, Or.inr ⟨c20, by omega⟩, Or.inr ⟨by rw [d32, a22]; ring, by omega⟩⟩

end ClassRows

end StarkedAir.Block.URec

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch
open StarkedAir.Sha256 (cst)
open StarkedAir.Spec.ConnectRules (isP2SH isW)

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : SizeOk Ls)
include hL hsat hL24

/-- A URec read of the undo stream with multiplicity expression `me` equal to 1: the byte at the position. -/
theorem urec_read {r : ℕ} (hr : r < 2 ^ Ls 13) {kk : ℕ} (hk : kk < URec.lookups.length) (huse : isUse 13 kk = true)
    {me pe be : Expr} (hsl : URec.lookups.getD kk ⟨0, .const 0, []⟩ = ⟨Undo.REL_UBYTE, .neg me, [pe, be]⟩)
    (hm : me.eval (2 ^ Ls 13) URec.preCols pub (inst 13).main r = 1) :
    ∃ q, q < (pub 8).val ∧ pe.eval (2 ^ Ls 13) URec.preCols pub (inst 13).main r = (q : F) ∧
      (be.eval (2 ^ Ls 13) URec.preCols pub (inst 13).main r).val = ((Ub inst pub).getD q 0).toNat := by
  have hpre : (hashSys.comp 13).air.pre = URec.preCols := rfl
  have hsite := site_mem hL (i := 13) (by decide) hr (k := kk) hk
  have hsl' : siteLookup hashSys ((13, r, kk) : Site) = ⟨Undo.REL_UBYTE, .neg me, [pe, be]⟩ := hsl
  exact undo_read hL hsat hL24 hsite huse (by simp [siteRel, hsl'])
    (by
      show siteEval hashSys inst pub (13, r, kk) (siteLookup hashSys (13, r, kk)).mult = -1
      rw [hsl']
      simp [siteEval, hpre, hL 13 (by decide), Expr.eval, hm])
    (by
      show (siteLookup hashSys (13, r, kk)).vals.map (siteEval hashSys inst pub (13, r, kk)) = _
      rw [hsl']
      simp [siteEval, hpre, hL 13 (by decide)])

/-- **The class bytes of a record**: the script's length byte, its first two bytes and its 23rd, where
`block_urec` reads them. -/
theorem urec_class_bytes {r : ℕ} (hr : r < 2 ^ Ls 13) (hon : (inst 13).main URec.ON r = 1) :
    ((inst 13).main (URec.U 0) r).val = ((Ub inst pub).getD (((inst 13).main URec.S r).val + 17) 0).toNat ∧
    ((inst 13).main URec.Z16 r + ((inst 13).main URec.Z17 r + (inst 13).main URec.Z22 r) = 1 →
      ((inst 13).main (URec.U 1) r).val = ((Ub inst pub).getD (((inst 13).main URec.S r).val + 18) 0).toNat ∧
      ((inst 13).main (URec.U 2) r).val = ((Ub inst pub).getD (((inst 13).main URec.S r).val + 19) 0).toNat) ∧
    ((inst 13).main URec.PC r = 1 →
      ((inst 13).main (URec.U 3) r).val = ((Ub inst pub).getD (((inst 13).main URec.S r).val + 40) 0).toNat) := by
  have hU := undo_len hL hsat hL24
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hP : P = 2147483647 := rfl
  obtain ⟨hS, -⟩ := urec_byte_at hL hsat hL24 hr hon (c := 0) (by norm_num)
  have ek : ∀ c, (URec.k c).eval (2 ^ Ls 13) URec.preCols pub (inst 13).main r = (inst 13).main c r :=
    fun c => URec.ev_k hr
  have pos : ∀ {q c : ℕ}, c ≤ 40 → q < (pub 8).val → (inst 13).main URec.S r + (c : F) = (q : F) →
      ((inst 13).main URec.S r).val + c = q := fun hc hq h => by
    apply Coin.lift _ (by omega) (by omega)
    push_cast; rw [ZMod.natCast_zmod_val, h]
  refine ⟨?_, fun hz => ⟨?_, ?_⟩, fun hpc => ?_⟩
  · obtain ⟨q, hq, hp, hb⟩ := urec_read hL hsat hL24 hr (kk := 20) (by simp [URec.lookups]) (by decide)
      (me := URec.k URec.ON) (pe := .add (URec.k URec.S) (cst 17)) (be := URec.k (URec.U 0)) rfl (by rw [ek, hon])
    simp only [Expr.eval, ek, StarkedAir.Sha256.eval_cst] at hp hb
    rw [pos (by norm_num) hq (by simpa using hp)]; exact hb
  · obtain ⟨q, hq, hp, hb⟩ := urec_read hL hsat hL24 hr (kk := 21) (by simp [URec.lookups]) (by decide)
      (me := .mul (URec.k URec.ON) (.add (URec.k URec.Z16) (.add (URec.k URec.Z17) (URec.k URec.Z22))))
      (pe := .add (URec.k URec.S) (cst 18)) (be := URec.k (URec.U 1)) rfl
      (by simp only [Expr.eval, ek, hon, one_mul]; exact hz)
    simp only [Expr.eval, ek, StarkedAir.Sha256.eval_cst] at hp hb
    rw [pos (by norm_num) hq (by simpa using hp)]; exact hb
  · obtain ⟨q, hq, hp, hb⟩ := urec_read hL hsat hL24 hr (kk := 22) (by simp [URec.lookups]) (by decide)
      (me := .mul (URec.k URec.ON) (.add (URec.k URec.Z16) (.add (URec.k URec.Z17) (URec.k URec.Z22))))
      (pe := .add (URec.k URec.S) (cst 19)) (be := URec.k (URec.U 2)) rfl
      (by simp only [Expr.eval, ek, hon, one_mul]; exact hz)
    simp only [Expr.eval, ek, StarkedAir.Sha256.eval_cst] at hp hb
    rw [pos (by norm_num) hq (by simpa using hp)]; exact hb
  · obtain ⟨q, hq, hp, hb⟩ := urec_read hL hsat hL24 hr (kk := 23) (by simp [URec.lookups]) (by decide)
      (me := .mul (URec.k URec.ON) (URec.k URec.PC)) (pe := .add (URec.k URec.S) (cst 40))
      (be := URec.k (URec.U 3)) rfl (by simp only [Expr.eval, ek, hon, one_mul]; exact hpc)
    simp only [Expr.eval, ek, StarkedAir.Sha256.eval_cst] at hp hb
    rw [pos (by norm_num) hq (by simpa using hp)]; exact hb

/-- **An input's class is its record's**: the coin row's `UP`, `U20`, `U32` are URec row `J`'s flags. -/
theorem coin_urec_class {j : ℕ} (hj : j < 2 ^ Ls 14) (hki : (inst 14).main Coin.KI j = 1) :
    ∃ rj < 2 ^ Ls 13, (inst 13).main URec.ON rj = 1 ∧ (inst 14).main Coin.J j = (inst 13).main URec.J rj ∧
      (inst 14).main Coin.UP j = (inst 13).main URec.CP rj ∧ (inst 14).main Coin.U20 j = (inst 13).main URec.C20 rj ∧
      (inst 14).main Coin.U32 j = (inst 13).main URec.C32 rj := by
  have hsite := site_mem hL (i := 14) (by decide) hj (k := 3) (by simp [hashSys, Coin.coin, Coin.lookups])
  have hm : siteMult hashSys inst pub (14, j, 3) = -1 := by
    simp [siteMult, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Expr.eval, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj, hki]
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hsite rfl hm
  rw [show siteRel hashSys (14, j, 3) = 23 from rfl, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 13 ∧ k' = 19 := by omega
  have us := urec_sat' hL hsat hL24
  refine ⟨r', hr', ?_, ?_⟩
  · have hm' : (inst 13).main URec.ON r' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, Expr.eval, URec.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
    rcases URec.on_bool us hr' with h | h
    · exact absurd h hm'
    · exact h
  have e1 : siteVals hashSys inst pub (13, r', 19) = [(inst 13).main URec.J r',
      (inst 13).main (URec.C 0) r' + 256 * (inst 13).main (URec.C 1) r',
      (inst 13).main (URec.C 2) r' + 256 * (inst 13).main (URec.C 3) r',
      (inst 13).main (URec.V 0) r' + 256 * (inst 13).main (URec.V 1) r' + 65536 * (inst 13).main (URec.V 2) r',
      (inst 13).main (URec.V 3) r' + 256 * (inst 13).main (URec.V 4) r' + 65536 * (inst 13).main (URec.V 5) r' +
        16777216 * (inst 13).main (URec.V 6) r',
      (inst 13).main (URec.X 0) r' + 256 * (inst 13).main (URec.X 1) r' + 65536 * (inst 13).main (URec.X 2) r',
      (inst 13).main URec.CP r', (inst 13).main URec.C20 r', (inst 13).main URec.C32 r'] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 13 (by decide), URec.urec, URec.lookups, URec.k, URec.limb,
      Expr.eval, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hr']
  have e2 : siteVals hashSys inst pub (14, j, 3) = [(inst 14).main Coin.J j, (inst 14).main Coin.CLO j,
      (inst 14).main Coin.CHI j, (inst 14).main Coin.VL j, (inst 14).main Coin.VH j, (inst 14).main Coin.CTX j,
      (inst 14).main Coin.UP j, (inst 14).main Coin.U20 j, (inst 14).main Coin.U32 j] := by
    simp [siteVals, siteEval, siteLookup, hashSys, hL 14 (by decide), Coin.coin, Coin.lookups, Coin.k,
      StarkedAir.Sha256.eval_col, wrap_zero hj]
  rw [e1, e2] at hsv
  simp only [List.cons.injEq, and_true] at hsv
  obtain ⟨a, -, -, -, -, -, g1, g2, g3⟩ := hsv
  exact ⟨a.symm, g1.symm, g2.symm, g3.symm⟩

/-- **A claim's class.** For an input whose claim is a real output's serialization, the coin row's flags
are the spent script's classes: P2SH, and a version 0 witness program of 20 or of 32 bytes. -/
theorem claim_class {j : ℕ} (hj : j < 2 ^ Ls 14) {c : Claim} (hc : ClaimAt inst pub (Ls 13) j c)
    {o : Spec.Block.TxOut} (ho : c.ser = Spec.Block.serTxOut o) :
    (((inst 14).main Coin.UP j = 1 ∧ isP2SH o.scriptPubKey = true) ∨
      ((inst 14).main Coin.UP j = 0 ∧ isP2SH o.scriptPubKey = false)) ∧
    (((inst 14).main Coin.U20 j = 1 ∧ isW 20 o.scriptPubKey = true) ∨
      ((inst 14).main Coin.U20 j = 0 ∧ isW 20 o.scriptPubKey = false)) ∧
    (((inst 14).main Coin.U32 j = 1 ∧ isW 32 o.scriptPubKey = true) ∨
      ((inst 14).main Coin.U32 j = 0 ∧ isW 32 o.scriptPubKey = false)) := by
  obtain ⟨hki, -, rj, hrj, honj, hJ, htl, u0, hu0, h9, hlen, hser, -, -⟩ := hc
  obtain ⟨rj', hrj', hon', hJ', e1, e2, e3⟩ := coin_urec_class hL hsat hL24 hj hki
  obtain rfl : rj' = rj := urec_j_inj hL hsat hL24 hrj' hrj hon' honj (hJ'.symm.trans hJ)
  have hU := undo_len hL hsat hL24
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have hP : P = 2147483647 := rfl
  obtain ⟨hS, -⟩ := urec_byte_at hL hsat hL24 hrj' honj (c := 0) (by norm_num)
  set s := ((inst 13).main URec.S rj').val with hs
  have hu : u0 = s + 9 := by
    apply Coin.lift _ (by omega) (by omega)
    rw [← hu0]; push_cast; rw [hs, ZMod.natCast_zmod_val]
  -- the claim's bytes are the stream's
  have hget : ∀ i < c.ser.length, (Spec.Block.serTxOut o).getD i 0 = (Ub inst pub).getD (s + 9 + i) 0 := by
    intro i hi
    have := congrArg (fun l : Spec.Block.Bytes => l.getD i 0) hser
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi, Option.map_some,
      Option.getD_some] at this
    rw [← ho, List.getD_eq_getElem?_getD, this, hu, List.getD_eq_getElem?_getD]
  have len9 : 9 ≤ c.ser.length := by rw [ho]; exact Spec.ConnectRules.serTxOut_len_ge o
  -- with a one-byte length `Lb`, every byte up to the script's end
  have hall : ∀ Lb : ℕ, Lb < 253 → (Spec.Block.serTxOut o).getD 8 0 = UInt8.ofNat Lb → ∀ i < 9 + Lb,
      (Spec.Block.serTxOut o).getD i 0 = (Ub inst pub).getD (s + 9 + i) 0 := by
    intro Lb hLb h8 i hi
    have hn := (Spec.ConnectRules.ser_len_byte o hLb).mp h8
    exact hget i (by rw [ho, Spec.ConnectRules.serTxOut_len_small o (by omega)]; omega)
  have g8 := hget 8 (by omega)
  obtain ⟨hb0, hb12, hb3⟩ := urec_class_bytes hL hsat hL24 hrj' honj
  rw [← hs] at hb0 hb12 hb3
  obtain ⟨s1, s2, s3⟩ := URec.class_spec (urec_sat' hL hsat hL24) hrj'
    (b0 := ((Ub inst pub).getD (s + 17) 0).toNat) (b1 := ((Ub inst pub).getD (s + 18) 0).toNat)
    (b2 := ((Ub inst pub).getD (s + 19) 0).toNat) (b3 := ((Ub inst pub).getD (s + 40) 0).toNat)
    (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) hb0 hb12 hb3
  have tn := fun (x : UInt8) (v : ℕ) (hv : v < 256) => Spec.ConnectRules.u8_toNat_iff x hv
  rw [e1, e2, e3]
  refine ⟨?_, ?_, ?_⟩
  · -- P2SH
    have fwd : (((Ub inst pub).getD (s + 17) 0).toNat = 0x17 ∧ ((Ub inst pub).getD (s + 18) 0).toNat = 0xa9 ∧
        ((Ub inst pub).getD (s + 19) 0).toNat = 0x14 ∧ ((Ub inst pub).getD (s + 40) 0).toNat = 0x87) ↔
        isP2SH o.scriptPubKey = true := by
      rw [Spec.ConnectRules.ser_p2sh, tn _ 0x17 (by norm_num), tn _ 0xa9 (by norm_num), tn _ 0x14 (by norm_num),
        tn _ 0x87 (by norm_num)]
      constructor
      · rintro ⟨a, b, c', d⟩
        have h8 : (Spec.Block.serTxOut o).getD 8 0 = UInt8.ofNat 23 := by rw [g8]; exact a
        have ha := hall 23 (by norm_num) h8
        exact ⟨h8, by rw [ha 9 (by norm_num)]; exact b, by rw [ha 10 (by norm_num)]; exact c',
          by rw [ha 31 (by norm_num)]; exact d⟩
      · rintro ⟨a, b, c', d⟩
        have ha := hall 23 (by norm_num) a
        exact ⟨by rw [← g8]; exact a, by rw [← ha 9 (by norm_num)]; exact b, by rw [← ha 10 (by norm_num)]; exact c',
          by rw [← ha 31 (by norm_num)]; exact d⟩
    rcases s1 with ⟨h1, hp⟩ | ⟨h0, hnp⟩
    · exact Or.inl ⟨h1, fwd.mp hp⟩
    · exact Or.inr ⟨h0, by rw [Bool.eq_false_iff]; exact fun q => hnp (fwd.mpr q)⟩
  · -- a 20-byte program
    have fwd : (((Ub inst pub).getD (s + 17) 0).toNat = 0x16 ∧ ((Ub inst pub).getD (s + 18) 0).toNat = 0 ∧
        ((Ub inst pub).getD (s + 19) 0).toNat = 0x14) ↔ isW 20 o.scriptPubKey = true := by
      rw [Spec.ConnectRules.ser_w o (k := 20) (by norm_num), tn _ 0x16 (by norm_num), tn _ 0 (by norm_num),
        tn _ 0x14 (by norm_num)]
      constructor
      · rintro ⟨a, b, c'⟩
        have h8 : (Spec.Block.serTxOut o).getD 8 0 = UInt8.ofNat 22 := by rw [g8]; exact a
        have ha := hall 22 (by norm_num) h8
        exact ⟨h8, by rw [ha 9 (by norm_num)]; exact b, by rw [ha 10 (by norm_num)]; exact c'⟩
      · rintro ⟨a, b, c'⟩
        have ha := hall 22 (by norm_num) a
        exact ⟨by rw [← g8]; exact a, by rw [← ha 9 (by norm_num)]; exact b, by rw [← ha 10 (by norm_num)]; exact c'⟩
    rcases s2 with ⟨h1, hp⟩ | ⟨h0, hnp⟩
    · exact Or.inl ⟨h1, fwd.mp hp⟩
    · exact Or.inr ⟨h0, by rw [Bool.eq_false_iff]; exact fun q => hnp (fwd.mpr q)⟩
  · -- a 32-byte program
    have fwd : (((Ub inst pub).getD (s + 17) 0).toNat = 0x22 ∧ ((Ub inst pub).getD (s + 18) 0).toNat = 0 ∧
        ((Ub inst pub).getD (s + 19) 0).toNat = 0x20) ↔ isW 32 o.scriptPubKey = true := by
      rw [Spec.ConnectRules.ser_w o (k := 32) (by norm_num), tn _ 0x22 (by norm_num), tn _ 0 (by norm_num),
        tn _ 0x20 (by norm_num)]
      constructor
      · rintro ⟨a, b, c'⟩
        have h8 : (Spec.Block.serTxOut o).getD 8 0 = UInt8.ofNat 34 := by rw [g8]; exact a
        have ha := hall 34 (by norm_num) h8
        exact ⟨h8, by rw [ha 9 (by norm_num)]; exact b, by rw [ha 10 (by norm_num)]; exact c'⟩
      · rintro ⟨a, b, c'⟩
        have ha := hall 34 (by norm_num) a
        exact ⟨by rw [← g8]; exact a, by rw [← ha 9 (by norm_num)]; exact b, by rw [← ha 10 (by norm_num)]; exact c'⟩
    rcases s3 with ⟨h1, hp⟩ | ⟨h0, hnp⟩
    · exact Or.inl ⟨h1, fwd.mp hp⟩
    · exact Or.inr ⟨h0, by rw [Bool.eq_false_iff]; exact fun q => hnp (fwd.mpr q)⟩

end System

end StarkedAir.Block
