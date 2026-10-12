/-
**Witness tree soundness, system level (M3a.5e).** In a satisfied block system with the commitment
checked, the commitment node's second hash (the digest the context component compares with the
commitment output) is `SHA256d(witnessRoot ++ nonce)`, where `witnessRoot` is the Merkle root of
`[0^32, wtxid(tx 1), …]` and `nonce` is the state whose limbs the context yields at row 79.
-/
import StarkedAir.Block.MerkleLink
import StarkedAir.Block.WMerkleSound
import StarkedAir.Block.CtxSound

namespace StarkedAir.Block

open StarkedAir
open StarkedAir.Sha256 (pre cst limb word messageAt outputAt)

/-- The nonce limb `j` of the context's digest tuples (register `LG (j xor 1)`). -/
def ctxLimb (M : ℕ → ℕ → F) (r j : ℕ) : F := M (Ctx.LG (if j % 2 = 0 then j + 1 else j - 1)) r

/-- The leaves of the witness tree. -/
def wleaves (b : Spec.Block.Blk) : List Spec.Block.Bytes :=
  List.replicate 32 0 :: (b.txs.drop 1).map Spec.Block.wtxid

theorem wleaves_length (b : Spec.Block.Blk) (h : 1 ≤ b.txs.length) : (wleaves b).length = b.txs.length := by
  simp [wleaves]; omega


theorem half16_zero : ∀ h, Sha256.half16 0#32 h = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- Words from their 16-bit limbs. -/
theorem words_of_limbs {f g : ℕ → Spec.Sha256.Word}
    (h : (List.range 16).map (fun j => ((Sha256.half16 (f (j / 2)) (j % 2) : ℕ) : F)) =
      (List.range 16).map (fun j => ((Sha256.half16 (g (j / 2)) (j % 2) : ℕ) : F))) :
    ∀ t < 8, f t = g t := by
  intro t ht
  have lj : ∀ j < 16, Sha256.half16 (f (j / 2)) (j % 2) = Sha256.half16 (g (j / 2)) (j % 2) := by
    intro j hj
    have e := congrArg (fun l => l[j]?) h
    simp only [List.getElem?_map, List.getElem?_range hj, Option.map_some, Option.some.injEq] at e
    have hb : ∀ (y : Spec.Sha256.Word) (h : ℕ), Sha256.half16 y h < P := fun y h =>
      Fields.lt_P (by have := half16_lt y h; omega)
    exact natCast_inj_of_lt (hb _ _) (hb _ _) e
  have h0 := lj (2 * t) (by omega)
  have h1 := lj (2 * t + 1) (by omega)
  rw [show 2 * t / 2 = t by omega, show 2 * t % 2 = 0 by omega] at h0
  rw [show (2 * t + 1) / 2 = t by omega, show (2 * t + 1) % 2 = 1 by omega] at h1
  exact word_of_halves h0 h1

/-- The zero state. -/
def zeroState : Spec.Sha256.State := ⟨0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32, 0#32⟩

theorem zeroState_bytes : Spec.Block.stateBytes zeroState = List.replicate 32 0 := by decide

theorem zeroState_word (t : ℕ) : Spec.Bitcoin.stateWord zeroState t = 0#32 := by
  unfold Spec.Bitcoin.stateWord zeroState; split <;> rfl

theorem baseL_pos {N l : ℕ} (hN1 : 1 ≤ N) (hl : 2 ≤ l) : 1 ≤ Merkle.baseL N l := by
  obtain ⟨m, rfl⟩ : ∃ m, l = m + 2 := ⟨l - 2, by omega⟩
  show 1 ≤ Merkle.baseL N (m + 1) + Merkle.cntL N (m + 1)
  have := Merkle.cntL_pos hN1 (m + 1); omega

theorem wleaves_get {b : Spec.Block.Blk} {i : ℕ} (hi : 1 ≤ i) {tx : Spec.Block.Tx} (h : b.txs[i]? = some tx) :
    (wleaves b).getD i [] = Spec.Block.wtxid tx := by
  obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
  simp [wleaves, List.getD_eq_getElem?_getD, List.getElem?_drop, h]

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {Ls : ℕ → ℕ}
  (hL : ∀ i < 15, (inst i).logSize = Ls i) (hsat : hashSys.SatisfiedExt inst pub [])
include hL hsat

theorem hash_ctx_sat' : ∀ r < 2 ^ Ls 7, ∀ c ∈ Ctx.constraints,
    c.eval (2 ^ Ls 7) Ctx.preCols pub (inst 7).main r = 0 := by
  have := hsat.1 7 (by decide); rw [hL 7 (by decide)] at this; exact this

theorem hash_wmerkle_sat' : ∀ r < 2 ^ Ls 8, ∀ c ∈ WMerkle.constraints,
    c.eval (2 ^ Ls 8) WMerkle.preCols pub (inst 8).main r = 0 := by
  have := hsat.1 8 (by decide); rw [hL 8 (by decide)] at this; exact this

/-- **Any digest use** (a node block's child read, the txid tree's root read, or the context's commitment
read) with multiplicity `−1` reads a second hash's output, the zero digest, or the coinbase nonce yielded
at context row 79. -/
theorem digest_any (hL24 : ∀ i < 15, Ls i ≤ 23) {i r k : ℕ}
    (hu : (i = 3 ∧ (k = 4 ∨ k = 5)) ∨ (i = 4 ∧ k = 2) ∨ (i = 7 ∧ (k = 10 ∨ k = 11)))
    (hr : r < 2 ^ Ls i) (hm : siteMult hashSys inst pub (i, r, k) = -1) :
    (∃ q', 72 * q' + 72 ≤ 2 ^ Ls 3 ∧ (inst 3).main Sha.DBL (72 * q') = 1 ∧
      siteVals hashSys inst pub (3, 72 * q' + 71, 2) = siteVals hashSys inst pub (i, r, k)) ∨
    siteVals hashSys inst pub (i, r, k) = (Ctx.ZERO_ID : F) :: (List.range 16).map (fun _ => (0 : F)) ∨
    (79 < 2 ^ Ls 7 ∧ (inst 7).main Ctx.HC 79 ≠ 0 ∧
      siteVals hashSys inst pub (i, r, k) = (Ctx.NONCE_ID : F) :: (List.range 16).map (ctxLimb (inst 7).main 79)) := by
  have ss := hash_sha_sat hL hsat
  have hs1 : ((i, r, k) : Site) ∈ sites hashSys inst := by
    rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h | h⟩ <;> (try subst h) <;>
      exact site_mem hL (by decide) hr (by simp [hashSys, Sha.sha, Sha.lookups, Merkle.merkle, Merkle.lookups,
        Ctx.ctx, Ctx.lookups])
  have huse : isUse i k = true := by rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h | h⟩ <;> (try subst h) <;> rfl
  obtain ⟨i', r', k', hr', hy, hsm, hsv⟩ := link hL hsat hL24 hs1 huse hm
  have e : siteRel hashSys (i, r, k) = 7 := by
    rcases hu with ⟨rfl, h | h⟩ | ⟨rfl, rfl⟩ | ⟨rfl, h | h⟩ <;> (try subst h) <;> rfl
  rw [e, yt] at hy
  rcases (by omega : (i' = 3 ∧ k' = 2) ∨ (i' = 7 ∧ k' = 7) ∨ (i' = 7 ∧ k' = 8)) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · left
    have hdy : (inst 3).main Sha.DBL r' * (inst 3).main Sha.YM r' ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups, Expr.eval, Sha.k,
        StarkedAir.Sha256.eval_col, wrap_zero hr'] using hsm
    have h71 : r' % 72 = 71 := by
      have := Sha.order_sat ss (c := .mul (Sha.k Sha.YM) (Sha.om (pre Sha.FIN3))) (by simp [Sha.orderC]) hr'
      simp only [Expr.eval, Sha.k, Sha.om, Sha.one, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst,
        wrap_zero hr', Nat.cast_one] at this
      rw [Sha.eval_per72 ss (i := Sha.FIN3) (f := fun q => if q = 71 then 1 else 0) rfl hr'] at this
      by_contra h
      simp only [h, if_false, Nat.cast_zero, sub_zero, mul_one] at this
      exact hdy (by rw [this, mul_zero])
    have hd1 : (inst 3).main Sha.DBL r' = 1 := by
      rcases Sha.kbool ss (c := Sha.DBL) (by simp) hr' with h | h
      · rw [h, zero_mul] at hdy; exact absurd rfl hdy
      · exact h
    refine ⟨r' / 72, by omega, ?_, ?_⟩
    · have := Sha.per_const ss (X := Sha.DBL) (by simp) (s := 72 * (r' / 72)) (by omega) 71 (by norm_num) (by omega)
      rw [show 72 * (r' / 72) + 71 = r' by omega, hd1] at this; exact this.symm
    · rw [show 72 * (r' / 72) + 71 = r' by omega]; exact hsv
  · right; left
    rw [← hsv]
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups,
      StarkedAir.Sha256.eval_cst]
  · right; right
    have cs := hash_ctx_sat' hL hsat
    have hm8 : siteMult hashSys inst pub (7, r', 8) =
        ((Ctx.preCols.getD Ctx.P_LT80 (.periodic [0])).eval (2 ^ Ls 7) r' -
          (Ctx.preCols.getD Ctx.P_LT79 (.periodic [0])).eval (2 ^ Ls 7) r') * (inst 7).main Ctx.HC r' := by
      simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
      simp [Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.ev_p (M := (inst 7).main) (pub := pub) hr',
        Ctx.ev_k (M := (inst 7).main) (pub := pub) hr']
    have h79 : r' = 79 := by
      by_contra h
      apply hsm
      rw [hm8]
      simp only [Ctx.preCols, Ctx.P_LT80, Ctx.P_LT79, List.getD_cons_succ, List.getD_cons_zero, PreCol.eval]
      rcases (by omega : r' < 79 ∨ 80 ≤ r') with h' | h'
      · rw [if_pos (by omega), if_pos h']; ring
      · rw [if_neg (by omega), if_neg (by omega)]; ring
    subst h79
    refine ⟨hr', fun h0 => hsm (by rw [hm8, h0, mul_zero]), ?_⟩
    rw [← hsv]
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.limbs, ctxLimb,
      StarkedAir.Sha256.eval_cst, Ctx.ev_k (M := (inst 7).main) (pub := pub) hr']

/-- **A second hash's id is below `2^28`**: a message id, or a tree node's. -/
theorem dbl_mid_lt (hL24 : ∀ i < 15, Ls i ≤ 23) {q : ℕ} (hn : 72 * q + 72 ≤ 2 ^ Ls 3) (hd : (inst 3).main Sha.DBL (72 * q) = 1) :
    ((inst 3).main Sha.MID (72 * q)).val < 2 ^ 28 := by
  have ss := hash_sha_sat hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  by_cases h : ((inst 3).main Sha.MID (72 * q)).val < Merkle.NB
  · unfold Merkle.NB at h; omega
  · obtain ⟨hq2, -, hno, hme⟩ := node_period hL hsat hL24 hn hd (by omega)
    have hsr : 72 * (q - 2) < 2 ^ Ls 3 := by omega
    obtain ⟨r', h' | h'⟩ := node_link hL hsat hL24 hsr (by
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hsr, hno, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hsr,
        show (72 * (q - 2)) % 72 = 0 by omega]; simp)
    · have hr' := h'.1; rw [← hme, h'.2.2.1, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold Merkle.NB; omega))]; unfold Merkle.NB; omega
    · have hr' := h'.1; rw [← hme, h'.2.1, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega))]
      unfold WMerkle.NBW; omega

/-- **A node block's child read**: its multiplicity and its tuple (the child id, then the half's words as
16-bit limbs). -/
theorem child_site {p : ℕ} (hp : 72 * p + 72 ≤ 2 ^ Ls 3) (ho : (inst 3).main Sha.NODE (72 * p) = 1) (half : ℕ)
    (hh : half ≤ 1) :
    siteMult hashSys inst pub (3, 72 * p + 11 + 8 * half, 4 + half) = -1 ∧
    siteVals hashSys inst pub (3, 72 * p + 11 + 8 * half, 4 + half) =
      (if half = 0 then (inst 3).main Sha.LID (72 * p) else (inst 3).main Sha.RID (72 * p)) ::
        (List.range 16).map (fun j => ((Sha256.half16 (messageAt (inst 3).main (72 * p) (8 * half + j / 2)) (j % 2) : ℕ) : F)) := by
  have ss := hash_sha_sat hL hsat
  have hs : (72 * p) % 72 = 0 := by omega
  set x := 72 * p + 11 + 8 * half with hx
  have hxr : x < 2 ^ Ls 3 := by omega
  have hxs : x = 72 * p + (11 + 8 * half) := by omega
  have hnode : (inst 3).main Sha.NODE x = 1 := by
    rw [hxs, Sha.per_const ss (X := Sha.NODE) (by simp) hs _ (by omega) (by omega), ho]
  constructor
  · simp only [siteMult, siteEval, siteLookup, hashSys, hL 3 (by decide)]
    simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide, show (3 : ℕ) ≠ 2 by decide, ↓reduceIte]
    interval_cases half
    · simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, Sha.k,
        StarkedAir.Sha256.eval_col, wrap_zero hxr, hnode, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.DLR) (f := fun q => if q = 11 then 1 else 0) rfl hxr,
        show x % 72 = 11 by omega]; simp
    · simp only [Sha.sha, Sha.lookups, List.getD_cons_succ, List.getD_cons_zero, Expr.eval, Sha.k,
        StarkedAir.Sha256.eval_col, wrap_zero hxr, hnode, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.DRR) (f := fun q => if q = 19 then 1 else 0) rfl hxr,
        show x % 72 = 19 by omega]; simp
  · have hu : siteVals hashSys inst pub (3, x, 4 + half) =
        ((if half = 0 then Sha.k Sha.LID else Sha.k Sha.RID) :: Sha.nodeWordLimbs).map
          (Expr.eval (2 ^ Ls 3) Sha.preCols pub (inst 3).main x) := by
      interval_cases half <;> simp [siteVals, siteEval, siteLookup, hashSys, hL 3 (by decide), Sha.sha, Sha.lookups]
    rw [hu, List.map_cons]
    congr 1
    · interval_cases half
      · simp only [if_true, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hxr]
        rw [hxs, Sha.per_const ss (X := Sha.LID) (by simp) hs (11 + 8 * 0) (by omega) (by omega)]
      · simp only [show (1 : ℕ) ≠ 0 by decide, if_false, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hxr]
        rw [hxs, Sha.per_const ss (X := Sha.RID) (by simp) hs (11 + 8 * 1) (by omega) (by omega)]
    · apply List.ext_getElem
      · simp [Sha.nodeWordLimbs]
      · intro j h1 h2
        have hj : j < 16 := by simpa [Sha.nodeWordLimbs] using h1
        simp only [List.getElem_map, List.getElem_range]
        rw [← List.getD_eq_getElem _ (cst 0) h1, show x = 72 * p + 11 + 8 * half by rfl,
          Sha.node_tuple ss (s := 72 * p) (by omega) hj half hh]

/-- Witness-tree ids are at most `ZERO_ID`, which only leaf 0 has. -/
theorem wid_small (hL24 : ∀ i < 15, Ls i ≤ 23) {N : ℕ} (hN : pub 1 = (N : F)) (hN1 : 1 ≤ N) (hN25 : N < 2 ^ Ls 1)
    (hW : (inst 8).main WMerkle.WON 0 = 1)
    {l j : ℕ} (hj : j < Merkle.cntL N l) (hl : l = 0 ∨ (1 ≤ l ∧ 2 ≤ Merkle.cntL N (l - 1))) :
    WMerkle.idOf N l j < P ∧ WMerkle.idOf N l j ≤ Ctx.ZERO_ID ∧
      (WMerkle.idOf N l j = Ctx.ZERO_ID → l = 0 ∧ j = 0) := by
  have ks := hash_wmerkle_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  have tr := WMerkle.tree_rows ks (show 0 < 2 ^ Ls 8 by positivity) (by omega) hW hN hN1 (by omega)
  have hP : Ctx.ZERO_ID < P := by unfold Ctx.ZERO_ID P; norm_num
  rcases hl with rfl | ⟨h1, h2⟩
  · simp only [Merkle.cntL] at hj
    by_cases h0 : j = 0
    · subst h0; simp only [WMerkle.idOf, if_true]; exact ⟨hP, le_refl _, fun _ => by simp⟩
    · simp only [WMerkle.idOf, if_true, if_neg h0]; unfold Ctx.ZERO_ID at *; refine ⟨by omega, by omega, by omega⟩
  · obtain ⟨hlt, -⟩ := tr.1 l h1 h2
    simp only [WMerkle.idOf, if_neg (show l ≠ 0 by omega)]
    unfold WMerkle.NBW Ctx.ZERO_ID at *; refine ⟨by omega, by omega, by omega⟩

/-- A node block with a witness-tree id is a witness-tree row's. -/
theorem wnode_row (hL24 : ∀ i < 15, Ls i ≤ 23) {x : ℕ} (hx : x < 2 ^ Ls 3)
    (hm : (Expr.mul (pre Sha.ROW0) (Sha.k Sha.NODE)).eval (2 ^ Ls 3) Sha.preCols pub (inst 3).main x = 1)
    (hge : WMerkle.NBW ≤ ((inst 3).main Sha.MID x).val) :
    ∃ r' < 2 ^ Ls 8, (inst 3).main Sha.MID x = ((WMerkle.NBW + r' : ℕ) : F) ∧
      (inst 3).main Sha.LID x = (inst 8).main WMerkle.LEFT r' ∧ (inst 3).main Sha.RID x = (inst 8).main WMerkle.RIGHT r' := by
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  obtain ⟨r', h | h⟩ := node_link hL hsat hL24 hx hm
  · rw [h.2.2.1, ZMod.val_natCast_of_lt (Fields.lt_P (by unfold Merkle.NB; omega))] at hge
    unfold WMerkle.NBW Merkle.NB at hge; omega
  · exact ⟨r', h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **A witness-tree node's child**: the node block's half holds the state of the child's entry, given the
child's level (an id below `ZERO_ID` is a second hash; `ZERO_ID` is the zero leaf). -/
theorem wchild (hL24 : ∀ i < 15, Ls i ≤ 23) {lw : List Spec.Block.Bytes} {N l j p half : ℕ}
    (hp : 72 * p + 72 ≤ 2 ^ Ls 3) (ho : (inst 3).main Sha.NODE (72 * p) = 1) (hh : half ≤ 1)
    (hcid : (if half = 0 then (inst 3).main Sha.LID (72 * p) else (inst 3).main Sha.RID (72 * p)) =
      (WMerkle.idOf N l j : F))
    (hsm : WMerkle.idOf N l j < P) (hle : WMerkle.idOf N l j ≤ Ctx.ZERO_ID)
    (hz : WMerkle.idOf N l j = Ctx.ZERO_ID → (Spec.Block.lvs lw l).getD j [] = List.replicate 32 0)
    (ih : ∀ q, 72 * q + 72 ≤ 2 ^ Ls 3 → (inst 3).main Sha.DBL (72 * q) = 1 →
      (inst 3).main Sha.MID (72 * q) = (WMerkle.idOf N l j : F) →
      Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) = (Spec.Block.lvs lw l).getD j []) :
    ∃ o : Spec.Sha256.State, (∀ t < 8, messageAt (inst 3).main (72 * p) (8 * half + t) = Spec.Bitcoin.stateWord o t) ∧
      Spec.Block.stateBytes o = (Spec.Block.lvs lw l).getD j [] := by
  obtain ⟨hm, hv⟩ := child_site hL hsat hp ho half hh
  rcases digest_any hL hsat hL24 (i := 3) (k := 4 + half) (Or.inl ⟨rfl, by interval_cases half <;> simp⟩)
    (by omega) hm with ⟨q', hq', hd', hy⟩ | hz0 | ⟨-, -, hn⟩
  · rw [digest_vals hL hsat hq', hv, hcid] at hy
    simp only [List.cons.injEq] at hy
    obtain ⟨hmid, hlimbs⟩ := hy
    refine ⟨outputAt (inst 3).main (72 * q'), fun t ht => ?_, ih q' hq' hd' hmid⟩
    exact (words_of_limbs (f := fun t => messageAt (inst 3).main (72 * p) (8 * half + t))
      (g := Spec.Bitcoin.stateWord (outputAt (inst 3).main (72 * q'))) hlimbs.symm t ht)
  · rw [hv, hcid] at hz0
    simp only [List.cons.injEq] at hz0
    obtain ⟨hid, hlimbs⟩ := hz0
    have e := natCast_inj_of_lt hsm (by unfold Ctx.ZERO_ID P; norm_num) hid
    refine ⟨zeroState, fun t ht => ?_, by rw [zeroState_bytes, hz e]⟩
    rw [zeroState_word]
    refine words_of_limbs (f := fun t => messageAt (inst 3).main (72 * p) (8 * half + t)) (g := fun _ => 0#32)
      ?_ t ht
    rw [hlimbs]; simp [half16_zero]
  · rw [hv, hcid] at hn
    simp only [List.cons.injEq] at hn
    have e := natCast_inj_of_lt hsm (by unfold Ctx.NONCE_ID P; norm_num) hn.1
    unfold Ctx.NONCE_ID Ctx.ZERO_ID at *; omega

/-- **Every witness-tree entry's second hash** outputs that entry of the tree over `wleaves b`. -/
theorem wid_digest (hL24 : ∀ i < 15, Ls i ≤ 23) {b : Spec.Block.Blk}
    (hb : Spec.Block.parseBlock (Fields.blockBytes (inst 0).main (pub 0).val) = some b)
    (hN : pub 1 = (b.txs.length : F)) (hN1 : 1 ≤ b.txs.length) (hN25 : b.txs.length < 2 ^ Ls 1)
    (hW : (inst 8).main WMerkle.WON 0 = 1) :
    ∀ l, (l = 0 ∨ (1 ≤ l ∧ 2 ≤ Merkle.cntL b.txs.length (l - 1))) → ∀ i < Merkle.cntL b.txs.length l,
      ∀ q, 72 * q + 72 ≤ 2 ^ Ls 3 → (inst 3).main Sha.DBL (72 * q) = 1 →
        (inst 3).main Sha.MID (72 * q) = (WMerkle.idOf b.txs.length l i : F) →
        Spec.Block.stateBytes (outputAt (inst 3).main (72 * q)) = (Spec.Block.lvs (wleaves b) l).getD i [] := by
  have ms := hash_msg_sat hL hsat
  have ss := hash_sha_sat hL hsat
  have ks := hash_wmerkle_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  set N := b.txs.length with hNdef
  have tr := WMerkle.tree_rows ks (show 0 < 2 ^ Ls 8 by positivity) (by omega) hW hN hN1 (by omega)
  have hlw : (wleaves b).length = N := wleaves_length b hN1
  intro l
  induction l with
  | zero =>
    intro _ i hi q hq hd hm
    simp only [Merkle.cntL] at hi
    have hlt := dbl_mid_lt hL hsat hL24 hq hd
    by_cases hi0 : i = 0
    · exfalso
      subst hi0
      simp only [WMerkle.idOf, if_true] at hm
      rw [hm, ZMod.val_natCast_of_lt (by unfold Ctx.ZERO_ID P; norm_num)] at hlt
      unfold Ctx.ZERO_ID at hlt; omega
    simp only [WMerkle.idOf, if_true, if_neg hi0] at hm
    have hmid : ((inst 3).main Sha.MID (72 * q)).val < Merkle.NB := by
      rw [hm, ZMod.val_natCast_of_lt (Fields.lt_P (m := 2 + 2 * i) (by omega))]; unfold Merkle.NB; omega
    obtain ⟨b', hp', r0, h0, f0, hm0, -, hnh⟩ := digest_tx hL hsat hL24 (Sha.dbl_pos ss hq hd) hq hd hmid
    rw [hb] at hp'; cases hp'
    have hh : (inst 2).main Msg.HDR r0 = 0 := by
      rcases Msg.bool_col ms (e := Msg.HDR) (by simp) h0 with h | h
      · exact h
      · exfalso
        rw [Msg.mid_eq ms h0, h, sub_self, zero_mul, hm] at hm0
        have := natCast_inj_of_lt (a := 0) (b := 2 + 2 * i) (Fields.lt_P (by norm_num)) (Fields.lt_P (by omega))
          (by simpa using hm0)
        omega
    obtain ⟨i', tx, hti, hget, hout⟩ := hnh hh
    have hi' : i' < N := by
      have := List.getElem?_eq_some_iff.mp hget; exact this.1
    have hw := Fields.bool_val (Msg.bool_col ms (e := Msg.WTX) (by simp) h0)
    rw [Msg.mid_eq ms h0, hh, sub_zero, one_mul, hti, hw.1, hm] at hm0
    have e : ((1 + 2 * i' + ((inst 2).main Msg.WTX r0).val : ℕ) : F) = ((2 + 2 * i : ℕ) : F) := by
      push_cast at hm0 ⊢; linear_combination hm0
    have en := natCast_inj_of_lt (Fields.lt_P (by omega)) (Fields.lt_P (by omega)) e
    have hw1 : (inst 2).main Msg.WTX r0 = 1 := by
      rw [hw.1, show ((inst 2).main Msg.WTX r0).val = 1 by omega]; simp
    have hii : i' = i := by omega
    subst hii
    rw [hout, if_pos hw1]
    simp only [Spec.Block.lvs]
    exact (wleaves_get (by omega) hget).symm
  | succ l ih =>
    intro hl i hi q hq hd hm
    have hc2 : 2 ≤ Merkle.cntL N l := by rcases hl with h | ⟨-, h⟩ <;> simp_all
    have hil : i < (Merkle.cntL N l + 1) / 2 := hi
    obtain ⟨hlt, rows⟩ := tr.1 (l + 1) (by omega) (by simpa using hc2)
    have hmv : ((inst 3).main Sha.MID (72 * q)).val = WMerkle.NBW + Merkle.baseL N (l + 1) + i := by
      rw [hm, WMerkle.idOf, if_neg (by omega), ZMod.val_natCast_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega))]
    obtain ⟨hq2, hnp, hno, hme⟩ := node_period hL hsat hL24 hq hd (by rw [hmv]; unfold WMerkle.NBW Merkle.NB; omega)
    set s := 72 * (q - 2) with hs
    have hsr : s < 2 ^ Ls 3 := by omega
    obtain ⟨r', hr', hmr, hlr, hrr⟩ := wnode_row hL hsat hL24 hsr (by
      simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hsr, hno, mul_one]
      rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hsr,
        show s % 72 = 0 by omega]; simp) (by rw [hs, hme, hmv]; omega)
    have hrow : r' = Merkle.baseL N (l + 1) + i := by
      have e : ((WMerkle.NBW + r' : ℕ) : F) = ((WMerkle.NBW + Merkle.baseL N (l + 1) + i : ℕ) : F) := by
        rw [← hmr, hs, hme, hm, WMerkle.idOf, if_neg (by omega)]
      have := natCast_inj_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega))
        (Fields.lt_P (by unfold WMerkle.NBW; omega)) e
      omega
    subst hrow
    obtain ⟨ra, rI, -, rL1, rPB, rOdd, rLast, -⟩ := rows i hi
    have hr0 : Merkle.baseL N (l + 1) + i = 0 ↔ (l + 1 = 1 ∧ i = 0) := by
      rcases Nat.eq_zero_or_pos l with h | h
      · subst h; simp [Merkle.baseL]
      · have := baseL_pos (N := N) hN1 (show 2 ≤ l + 1 by omega); omega
    obtain ⟨-, kl, kr⟩ := WMerkle.kids ks hr' ra hr0 (show 1 ≤ l + 1 by omega)
      (rfl : Merkle.cntL N l = Merkle.cntL N (l + 1 - 1)) hc2 hil (by simpa using rL1)
      (fun h => by simpa using rPB h) rI (by simpa using rOdd) (by rw [rLast]; rfl)
    simp only [Nat.add_sub_cancel] at kl kr
    have ihl : l = 0 ∨ (1 ≤ l ∧ 2 ≤ Merkle.cntL N (l - 1)) := by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact Or.inl h
      · right; refine ⟨h, ?_⟩
        have := Merkle.cntL_le (N := N) (l - 1); rw [show l - 1 + 1 = l by omega] at this; omega
    have child : ∀ half ≤ 1, ∃ o : Spec.Sha256.State,
        (∀ t < 8, messageAt (inst 3).main s (8 * half + t) = Spec.Bitcoin.stateWord o t) ∧
        Spec.Block.stateBytes o = (Spec.Block.lvs (wleaves b) l).getD
          (if half = 0 then 2 * i else min (2 * i + 1) (Merkle.cntL N l - 1)) [] := by
      intro half hh
      have hj : (if half = 0 then 2 * i else min (2 * i + 1) (Merkle.cntL N l - 1)) < Merkle.cntL N l := by
        split_ifs <;> omega
      obtain ⟨w1, w2, w3⟩ := wid_small hL hsat hL24 hN hN1 hN25 hW hj ihl
      refine wchild hL hsat hL24 (p := q - 2) (by omega) hno hh ?_ w1 w2 (fun e => ?_) (ih ihl _ hj)
      · interval_cases half
        · simp only [if_true]; rw [hlr, kl]
        · simp only [show (1 : ℕ) ≠ 0 by decide, if_false]; rw [hrr, kr]
      · obtain ⟨rfl, h0⟩ := w3 e
        rw [h0]; simp [Spec.Block.lvs, wleaves]
    obtain ⟨oL, wL, bL⟩ := child 0 (by norm_num)
    obtain ⟨oR, wR, bR⟩ := child 1 (by norm_num)
    simp only [if_true, show (1 : ℕ) ≠ 0 by decide, if_false] at bL bR
    have hout := Sha.node_out ss hq2 hq hd (by rw [show q - 1 = q - 1 by rfl]; exact hnp) hno
    have hmsg : Spec.Sha256.compress Spec.Sha256.IV (messageAt (inst 3).main s) =
        Spec.Sha256.compress Spec.Sha256.IV (HashSpec.pairWords oL oR) := by
      apply StarkedAir.HeaderChain.compress_congr
      intro t ht
      unfold HashSpec.pairWords
      split_ifs with h8
      · have := wL t h8; simpa using this
      · have := wR (t - 8) (by omega); rw [show 8 * 1 + (t - 8) = t by omega] at this; exact this
    rw [hout, hmsg, npad_eq, dbl_digest, ← HashSpec.sha256d_pair, bL, bR]
    have hlen := lvs_len (wleaves b) l
    rw [hlw] at hlen
    have hg := Spec.Block.level_get (Spec.Block.lvs (wleaves b) l) i (by rw [hlen]; exact hil)
    simp only [Spec.Block.lvs, List.getD_eq_getElem?_getD, hg, Option.getD_some]
    rw [hlen]

/-- The 16 limbs of a state, as digest tuples carry them. -/
def stLimbs (o : Spec.Sha256.State) : List F :=
  (List.range 16).map fun j => ((Sha256.half16 (Spec.Bitcoin.stateWord o (j / 2)) (j % 2) : ℕ) : F)

/-- **Witness tree soundness (M3a.5e).** When the commitment is checked (`HC`), the digest the context reads
at row 117 is `SHA256d(root ++ nonce)`: `root` is the Merkle root of `wleaves b` and `nonce` the state whose
limbs the context yields at row 79. -/
theorem wmerkle_sound (hL24 : ∀ i < 15, Ls i ≤ 23) (h256 : 256 ≤ 2 ^ Ls 7) {b : Spec.Block.Blk}
    (hb : Spec.Block.parseBlock (Fields.blockBytes (inst 0).main (pub 0).val) = some b)
    (hN : pub 1 = (b.txs.length : F)) (hN1 : 1 ≤ b.txs.length) (hN25 : b.txs.length < 2 ^ Ls 1)
    (hc : (inst 7).main Ctx.HC 0 = 1) :
    ∃ oN oC : Spec.Sha256.State, stLimbs oN = (List.range 16).map (ctxLimb (inst 7).main 79) ∧
      stLimbs oC = (List.range 16).map (ctxLimb (inst 7).main 117) ∧
      Spec.Block.stateBytes oC = Spec.Block.sha256d ((Spec.Block.merkleRoot (wleaves b)).1 ++ Spec.Block.stateBytes oN) := by
  have ss := hash_sha_sat hL hsat
  have cs := hash_ctx_sat' hL hsat
  have ks := hash_wmerkle_sat' hL hsat
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, rb8, rb9, rb10, rb11, rb12, rb13, rb14⟩ := rows_le_all hL24
  set N := b.txs.length with hNdef
  have hlw : (wleaves b).length = N := wleaves_length b hN1
  have hn0 : 0 < 2 ^ Ls 7 := by positivity
  have hn8 : 0 < 2 ^ Ls 8 := by positivity
  have hcst := fun X (hX : X ∈ Ctx.consts) r (hr : r < 2 ^ Ls 7) =>
    Ctx.const_eq (n := 2 ^ Ls 7) (pub := pub) (M := (inst 7).main) cs hX r hr
  -- the commitment row: the context's `wcid` use
  have hs9 := site_mem hL (i := 7) (by decide) hn0 (k := 9) (by simp [hashSys, Ctx.ctx, Ctx.lookups])
  have hm9 : siteMult hashSys inst pub (7, 0, 9) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
    simp [Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.ev_first (M := (inst 7).main) (pub := pub) hn0,
      Ctx.ev_k (M := (inst 7).main) (pub := pub) hn0, hc]
  obtain ⟨i', rc, k', hrc, hy, hsm, hsv⟩ := link hL hsat hL24 hs9 rfl hm9
  have e16 : siteRel hashSys (7, 0, 9) = 16 := rfl
  rw [e16, yt] at hy
  obtain ⟨rfl, rfl⟩ : i' = 8 ∧ k' = 2 := by omega
  have hrt : (inst 8).main WMerkle.RT rc = 1 := by
    have : (inst 8).main WMerkle.RT rc ≠ 0 := by
      simpa [siteMult, siteEval, siteLookup, hashSys, hL 8 (by decide), WMerkle.wmerkle, WMerkle.lookups, Expr.eval,
        WMerkle.k, StarkedAir.Sha256.eval_col, wrap_zero hrc] using hsm
    exact (WMerkle.kbool ks (c := WMerkle.RT) (by simp) hrc).resolve_left this
  have hcid : (inst 7).main Ctx.CID 0 = ((WMerkle.NBW + rc : ℕ) : F) := by
    have h1 : siteVals hashSys inst pub (8, rc, 2) = [(WMerkle.NBW : F) + (inst 8).main WMerkle.RIX rc] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 8 (by decide), WMerkle.wmerkle, WMerkle.lookups,
        WMerkle.nodeId, WMerkle.k, StarkedAir.Sha256.eval_col, StarkedAir.Sha256.eval_cst, wrap_zero hrc, Expr.eval]
    have h2 : siteVals hashSys inst pub (7, 0, 9) = [(inst 7).main Ctx.CID 0] := by
      simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups,
        Ctx.ev_k (M := (inst 7).main) (pub := pub) hn0]
    rw [h1, h2, WMerkle.rix_eq ks rc hrc] at hsv
    simp only [List.cons.injEq, and_true] at hsv
    rw [← hsv]; push_cast; ring
  have hW := WMerkle.won_of_rt ks hrc hrt
  -- the tree's height and root
  have hex : ∃ H, Merkle.cntL N H = 1 := ⟨N, by
    have := Merkle.cntL_bound hN1 N; have := Merkle.cntL_pos hN1 N; omega⟩
  obtain ⟨H, hH, hHl⟩ : ∃ H, Merkle.cntL N H = 1 ∧ ∀ l < H, 2 ≤ Merkle.cntL N l := by
    refine ⟨Nat.find hex, Nat.find_spec hex, fun l hl => ?_⟩
    have := Nat.find_min hex hl; have := Merkle.cntL_pos hN1 l; omega
  obtain ⟨rr, hrr, hrt', hrid⟩ := WMerkle.root_row ks hn8 (by omega) hW hN hN1 (by omega) hH hHl
  obtain rfl : rr = rc := WMerkle.rt_unique ks hrr hrc hrt' hrt
  obtain ⟨hleft, hright⟩ := WMerkle.commit_row ks hrr hrt
  -- the context's digest read at row 117
  have h117 : 117 < 2 ^ Ls 7 := by omega
  have hs10 := site_mem hL (i := 7) (by decide) h117 (k := 10) (by simp [hashSys, Ctx.ctx, Ctx.lookups])
  have hm10 : siteMult hashSys inst pub (7, 117, 10) = -1 := by
    simp only [siteMult, siteEval, siteLookup, hashSys, hL 7 (by decide)]
    simp [Ctx.ctx, Ctx.lookups, Expr.eval, Ctx.ev_p (M := (inst 7).main) (pub := pub) h117,
      Ctx.ev_k (M := (inst 7).main) (pub := pub) h117]
    simp only [Ctx.preCols, Ctx.P_LT118, Ctx.P_LT117, List.getD_cons_succ, List.getD_cons_zero, PreCol.eval,
      hcst Ctx.HC (by simp [Ctx.consts]) 117 h117, hc]
    norm_num
  have hv10 : siteVals hashSys inst pub (7, 117, 10) =
      ((WMerkle.NBW + rr : ℕ) : F) :: (List.range 16).map (ctxLimb (inst 7).main 117) := by
    rw [← hcid, ← hcst Ctx.CID (by simp [Ctx.consts]) 117 h117]
    simp [siteVals, siteEval, siteLookup, hashSys, hL 7 (by decide), Ctx.ctx, Ctx.lookups, Ctx.limbs, ctxLimb,
      Ctx.ev_k (M := (inst 7).main) (pub := pub) h117]
  have hsmall : WMerkle.NBW + rr < P := Fields.lt_P (by unfold WMerkle.NBW; omega)
  rcases digest_any hL hsat hL24 (i := 7) (k := 10) (Or.inr (Or.inr ⟨rfl, Or.inl rfl⟩)) h117 hm10 with
    ⟨q, hq, hd, hyq⟩ | hz | ⟨-, -, hn⟩
  rotate_left
  · rw [hv10] at hz; simp only [List.cons.injEq] at hz
    have := natCast_inj_of_lt hsmall (by unfold Ctx.ZERO_ID P; norm_num) hz.1
    unfold WMerkle.NBW Ctx.ZERO_ID at this; omega
  · rw [hv10] at hn; simp only [List.cons.injEq] at hn
    have := natCast_inj_of_lt hsmall (by unfold Ctx.NONCE_ID P; norm_num) hn.1
    unfold WMerkle.NBW Ctx.NONCE_ID at this; omega
  rw [digest_vals hL hsat hq, hv10] at hyq
  simp only [List.cons.injEq] at hyq
  obtain ⟨hmq, hlimbs⟩ := hyq
  -- the commitment node's block
  have hmv : ((inst 3).main Sha.MID (72 * q)).val = WMerkle.NBW + rr := by
    rw [hmq, ZMod.val_natCast_of_lt hsmall]
  obtain ⟨hq2, hnp, hno, hme⟩ := node_period hL hsat hL24 hq hd (by rw [hmv]; unfold WMerkle.NBW Merkle.NB; omega)
  set s := 72 * (q - 2) with hs
  have hsr : s < 2 ^ Ls 3 := by omega
  obtain ⟨r', hr', hmr, hlr, hrr'⟩ := wnode_row hL hsat hL24 hsr (by
    simp only [Expr.eval, Sha.k, StarkedAir.Sha256.eval_col, wrap_zero hsr, hno, mul_one]
    rw [Sha.eval_per72 ss (i := Sha.ROW0) (f := fun q => if q = 0 then 1 else 0) rfl hsr,
      show s % 72 = 0 by omega]; simp) (by rw [hs, hme, hmv]; omega)
  obtain rfl : r' = rr := by
    have e : ((WMerkle.NBW + r' : ℕ) : F) = ((WMerkle.NBW + rr : ℕ) : F) := by rw [← hmr, hs, hme, hmq]
    have := natCast_inj_of_lt (Fields.lt_P (by unfold WMerkle.NBW; omega)) hsmall e
    omega
  -- the left half: the root's state
  have hl0 : H = 0 ∨ (1 ≤ H ∧ 2 ≤ Merkle.cntL N (H - 1)) := by
    rcases Nat.eq_zero_or_pos H with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hHl (H - 1) (by omega)⟩
  obtain ⟨w1, w2, w3⟩ := wid_small hL hsat hL24 hN hN1 hN25 hW (l := H) (j := 0) (by rw [hH]; norm_num) hl0
  obtain ⟨oL, wL, bL⟩ := wchild hL hsat hL24 (lw := wleaves b) (l := H) (j := 0) (p := q - 2) (half := 0) (by omega) hno
    (by norm_num) (by simp only [if_true]; rw [hlr, hleft, hrid]) w1 w2
    (fun e => by obtain ⟨rfl, -⟩ := w3 e; simp [Spec.Block.lvs, wleaves])
    (wid_digest hL hsat hL24 hb hN hN1 hN25 hW H hl0 0 (by rw [hH]; norm_num))
  -- the right half: the nonce
  obtain ⟨hmR, hvR⟩ := child_site hL hsat (p := q - 2) (by omega) hno 1 (by norm_num)
  rw [← hs] at hmR hvR
  simp only [show (1 : ℕ) ≠ 0 by decide, if_false, hrr', hright] at hvR
  have hNP : Ctx.NONCE_ID < P := by unfold Ctx.NONCE_ID P; norm_num
  have hnl : (List.range 16).map (fun j => ((Sha256.half16 (messageAt (inst 3).main s (8 * 1 + j / 2)) (j % 2) : ℕ) : F)) =
      (List.range 16).map (ctxLimb (inst 7).main 79) := by
    rcases digest_any hL hsat hL24 (i := 3) (k := 4 + 1) (Or.inl ⟨rfl, by simp⟩) (by omega) hmR with
      ⟨q', hq', hd', hy⟩ | hz | ⟨-, -, hn⟩
    · exfalso
      rw [digest_vals hL hsat hq', hvR] at hy
      simp only [List.cons.injEq] at hy
      have := dbl_mid_lt hL hsat hL24 hq' hd'
      rw [hy.1, ZMod.val_natCast_of_lt hNP] at this
      unfold Ctx.NONCE_ID at this; omega
    · exfalso
      rw [hvR] at hz; simp only [List.cons.injEq] at hz
      have := natCast_inj_of_lt hNP (by unfold Ctx.ZERO_ID P; norm_num) hz.1
      unfold Ctx.NONCE_ID Ctx.ZERO_ID at this; omega
    · rw [hvR] at hn; simp only [List.cons.injEq] at hn; exact hn.2
  let oN : Spec.Sha256.State := ⟨messageAt (inst 3).main s 8, messageAt (inst 3).main s 9,
    messageAt (inst 3).main s 10, messageAt (inst 3).main s 11, messageAt (inst 3).main s 12,
    messageAt (inst 3).main s 13, messageAt (inst 3).main s 14, messageAt (inst 3).main s 15⟩
  have wN : ∀ t < 8, messageAt (inst 3).main s (8 * 1 + t) = Spec.Bitcoin.stateWord oN t := by
    intro t ht; interval_cases t <;> rfl
  refine ⟨oN, outputAt (inst 3).main (72 * q), ?_, ?_, ?_⟩
  · rw [← hnl, stLimbs]
    apply List.map_congr_left
    intro j hj
    rw [List.mem_range] at hj
    rw [wN (j / 2) (by omega)]
  · rw [stLimbs]; exact hlimbs
  · have hout := Sha.node_out ss hq2 hq hd hnp hno
    have hmsg : Spec.Sha256.compress Spec.Sha256.IV (messageAt (inst 3).main s) =
        Spec.Sha256.compress Spec.Sha256.IV (HashSpec.pairWords oL oN) := by
      apply StarkedAir.HeaderChain.compress_congr
      intro t ht
      unfold HashSpec.pairWords
      split_ifs with h8
      · have := wL t h8; simpa using this
      · have := wN (t - 8) (by omega); rw [show 8 * 1 + (t - 8) = t by omega] at this; exact this
    rw [hout, hmsg, npad_eq, dbl_digest, ← HashSpec.sha256d_pair, bL]
    have hlen := lvs_len (wleaves b) H
    rw [hlw, hH] at hlen
    have hroot := Spec.Block.merkleRoot_lvs (wleaves b) H (fun k hk => by
      rw [lvs_len, hlw]; exact hHl k hk) hlen
    rw [hroot]
    match h : Spec.Block.lvs (wleaves b) H, hlen with
    | [a], _ => simp

end System

end StarkedAir.Block
