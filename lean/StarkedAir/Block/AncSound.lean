/-
**Soundness of the ancestry component** (`Anc.lean`, D-043 part 3, option A).

`anc_sound`: in a trace satisfying the ancestry AIR, either the CSV bit (public input 5) is 0 and the MTP
limbs (public inputs 3, 7) are 0, or the CSV bit is 1, the trace has at least 4096 rows, and
* the 12 headers of periods 0–11 hash to the hashes read from their rows (`sha256d`), each committing to
  the previous one's hash (`prevHash`);
* period 11's hash is the block hash (public inputs 25–40, in `HashPub.hash_pub`'s limb form);
* the MTP is the median of periods 0–10's times (`Spec.Bitcoin.medianTimePast`, newest first).

The hashing and linkage come from the header chain's proofs: the ancestry trace satisfies the header
chain's base constraints (`HeaderChain.ChainSat`) for public inputs read from the trace itself
(`pubOf`), since the ancestry AIR keeps those constraints except the two that pin the first prev-hash and
the last hash to public inputs.
-/
import StarkedAir.Block.Anc
import StarkedAir.Gadgets.MtpSound

namespace StarkedAir

/-- An expression without public inputs. -/
def Expr.pubFree : Expr → Bool
  | .col _ _ _ => true
  | .const _ => true
  | .add a b => a.pubFree && b.pubFree
  | .sub a b => a.pubFree && b.pubFree
  | .mul a b => a.pubFree && b.pubFree
  | .neg a => a.pubFree
  | .pub _ => false

theorem Expr.eval_pubFree (n : ℕ) (pc : List PreCol) (pub pub' : ℕ → F) (main : ℕ → ℕ → F) (r : ℕ) :
    ∀ e : Expr, e.pubFree = true → e.eval n pc pub main r = e.eval n pc pub' main r
  | .col t i off, _ => by cases t <;> rfl
  | .const _, _ => rfl
  | .add a b, h => by
    simp only [Expr.pubFree, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_pubFree n pc pub pub' main r a h.1, Expr.eval_pubFree n pc pub pub' main r b h.2]
  | .sub a b, h => by
    simp only [Expr.pubFree, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_pubFree n pc pub pub' main r a h.1, Expr.eval_pubFree n pc pub pub' main r b h.2]
  | .mul a b, h => by
    simp only [Expr.pubFree, Bool.and_eq_true] at h
    simp only [Expr.eval, Expr.eval_pubFree n pc pub pub' main r a h.1, Expr.eval_pubFree n pc pub pub' main r b h.2]
  | .neg a, h => by
    simp only [Expr.pubFree] at h
    simp only [Expr.eval, Expr.eval_pubFree n pc pub pub' main r a h]
  | .pub _, h => by simp [Expr.pubFree] at h

end StarkedAir

namespace StarkedAir.Block.Anc

open StarkedAir StarkedAir.Sha256 StarkedAir.HeaderChain StarkedAir.Spec.Sha256 StarkedAir.Spec.Bitcoin

set_option maxRecDepth 100000 in
theorem base_pubFree : ∀ c ∈ Sha256.constraints ++ plumbing ++ linkNF, c.pubFree = true := by decide

theorem sumPow_pubFree (f : ℕ → Expr) (hf : ∀ i, (f i).pubFree = true) : ∀ k, (sumPow f k).pubFree = true
  | 0 => rfl
  | k + 1 => by simp [sumPow, Expr.pubFree, sumPow_pubFree f hf k, hf k, cst]

theorem limb_pubFree (X h : ℕ) (off : ℤ) : (limb X h off).pubFree = true :=
  sumPow_pubFree _ (fun _ => rfl) 16

/-! ## The header chain's base constraints -/

/-- Public inputs read from the trace: 0..15 the first header's prev-hash (rows 5..12, `w`), 16..31 the
last header's hash (its rows 212..215, `a` and `e`). -/
def pubOf (n : ℕ) (main : ℕ → ℕ → F) (i : ℕ) : F :=
  if i < 16 then (limb W (i % 2)).eval n HeaderChain.preCols (fun _ => 0) main (5 + i / 2)
  else if i < 32 then
    (if (i - 16) / 2 < 4 then (limb A (i % 2)).eval n HeaderChain.preCols (fun _ => 0) main (n - 256 + 215 - (i - 16) / 2)
     else (limb E (i % 2)).eval n HeaderChain.preCols (fun _ => 0) main (n - 256 + 215 - ((i - 16) / 2 - 4)))
  else 0

/-- **The median from counts.** Of 11 values, if at most 5 are above `M` and at most 5 below, `M` is
their median (`Spec.Bitcoin.medianTimePast`). -/
theorem median_of_counts {M : ℕ} {l : List ℕ} (hl : l.length = 11)
    (ha : l.countP (fun t => M < t) ≤ 5) (hb : l.countP (fun t => t < M) ≤ 5) :
    medianTimePast l = M := by
  unfold medianTimePast
  dsimp only
  rw [List.take_of_length_le (by omega), hl]
  set s := l.mergeSort (fun a b => decide (a ≤ b))
  have hperm : s.Perm l := List.mergeSort_perm l _
  have hsort : s.Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : ℕ => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega) (fun a b => by simp; omega) l
    simpa using this
  have hlen : s.length = 11 := by rw [hperm.length_eq, hl]
  have k1 := sorted_lt_iff (t := M) hsort 5 (by omega)
  have k2 := sorted_lt_iff (t := M + 1) hsort 5 (by omega)
  have f1 : (s.filter (· < M)).length = l.countP (fun t => t < M) := by
    rw [(hperm.filter _).length_eq, List.countP_eq_length_filter]
  have f2 : (s.filter (· < M + 1)).length + l.countP (fun t => M < t) = 11 := by
    rw [(hperm.filter _).length_eq, ← List.countP_eq_length_filter, ← hl]
    have := List.length_eq_countP_add_countP (fun t => decide (t < M + 1)) (l := l)
    rw [this]; congr 1
    first | done | (apply List.countP_congr; intro x _; simp) | (apply List.countP_congr; intro x _; simp; omega)
  rw [f1] at k1
  have : ¬ s.getD 5 0 < M := fun h => by have := k1.mp h; omega
  have : s.getD 5 0 < M + 1 := k2.mpr (by omega)
  show s.getD 5 0 = M
  omega

theorem countP_range_map (f : ℕ → ℕ) (p : ℕ → Bool) : ∀ n,
    ((List.range n).map f).countP p = ∑ k ∈ Finset.range n, (p (f k)).toNat
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.countP_append, countP_range_map f p n, Finset.sum_range_succ]
    cases h : p (f n) <;> simp [h]

theorem pubOf_link {n k h : ℕ} (hk : k < 8) (hh : h ≤ 1) (main : ℕ → ℕ → F) :
    pubOf n main (2 * k + h) = (limb W h).eval n HeaderChain.preCols (fun _ => 0) main (5 + k) := by
  unfold pubOf
  rw [if_pos (by omega), show (2 * k + h) % 2 = h by omega, show (2 * k + h) / 2 = k by omega]

theorem pubOf_out {n jj h : ℕ} (hjj : jj < 4) (hh : h ≤ 1) (hn : 256 ≤ n) (main : ℕ → ℕ → F) :
    pubOf n main (16 + 2 * (3 - jj) + h) = (limb A h).eval n HeaderChain.preCols (fun _ => 0) main (n - 256 + 212 + jj) ∧
    pubOf n main (16 + 2 * (7 - jj) + h) = (limb E h).eval n HeaderChain.preCols (fun _ => 0) main (n - 256 + 212 + jj) := by
  constructor <;> unfold pubOf
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), show (16 + 2 * (3 - jj) + h) % 2 = h by omega,
      show 16 + 2 * (3 - jj) + h - 16 = 2 * (3 - jj) + h by omega, show (2 * (3 - jj) + h) / 2 = 3 - jj by omega,
      show n - 256 + 215 - (3 - jj) = n - 256 + 212 + jj by omega]
  · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), show (16 + 2 * (7 - jj) + h) % 2 = h by omega,
      show 16 + 2 * (7 - jj) + h - 16 = 2 * (7 - jj) + h by omega, show (2 * (7 - jj) + h) / 2 - 4 = 3 - jj by omega,
      show n - 256 + 215 - (3 - jj) = n - 256 + 212 + jj by omega]

section Sat

variable {L : ℕ} {pub : ℕ → F} {main : ℕ → ℕ → F} (hsat : anc.air.Satisfied L pub main)
include hsat

theorem asat {c : Expr} (hc : c ∈ Anc.constraints) {r : ℕ} (hr : r < 2 ^ L) :
    c.eval (2 ^ L) HeaderChain.preCols pub main r = 0 := hsat r hr c hc

theorem anc_sat {c : Expr} (hc : c ∈ ancCs) {r : ℕ} (hr : r < 2 ^ L) :
    c.eval (2 ^ L) HeaderChain.preCols pub main r = 0 :=
  asat hsat (by simp only [Anc.constraints, List.mem_append]; right; exact hc) hr

/-- **The ancestry trace is a header chain** (base constraints, public inputs `pubOf`). -/
theorem chainSat (hL : 8 ≤ L) : ChainSat (2 ^ L) (pubOf (2 ^ L) main) main := by
  have h256 : 256 ∣ 2 ^ L := by
    rw [show 2 ^ L = 2 ^ 8 * 2 ^ (L - 8) by rw [← pow_add]; congr 1; omega]; exact Dvd.intro _ rfl
  have hn : 256 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL)
  intro r hr c hc
  simp only [baseConstraints, List.mem_append] at hc
  rcases hc with ((hc | hc) | hc) | hc
  · rw [← Expr.eval_pubFree _ _ pub _ _ _ c (base_pubFree c (by simp [hc]))]
    exact asat hsat (by simp only [Anc.constraints, List.mem_append]; left; left; left; exact hc) hr
  · rw [← Expr.eval_pubFree _ _ pub _ _ _ c (base_pubFree c (by simp [hc]))]
    exact asat hsat (by simp only [Anc.constraints, List.mem_append]; left; left; right; exact hc) hr
  · simp only [linkage, List.mem_flatMap, List.mem_range, List.mem_append] at hc
    obtain ⟨k, hk, hc | hc⟩ := hc
    · have hm : c ∈ linkNF := List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, hc⟩
      rw [← Expr.eval_pubFree _ _ pub _ _ _ c (base_pubFree c (by simp [hm]))]
      exact asat hsat (by simp only [Anc.constraints, List.mem_append]; left; right; exact hm) hr
    · simp only [eqLimbs, List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      obtain ⟨h, hh, rfl⟩ := hc
      have hh1 : h ≤ 1 := by rcases hh with rfl | rfl <;> omega
      have hcol : HeaderChain.preCols.getD (LINK0 + k) (.periodic [0]) = oneRow (5 + k) := by interval_cases k <;> rfl
      rw [eval_mul', eval_mul', eval_oneRow hcol hr, eval_first hr]
      by_cases hrow : r = 5 + k
      · subst hrow
        rw [if_pos (by omega), if_pos (by omega), one_mul, one_mul, eval_sub', sub_eq_zero]
        show _ = pubOf (2 ^ L) main (2 * k + h)
        rw [pubOf_link hk hh1, Expr.eval_pubFree _ _ (pubOf (2 ^ L) main) (fun _ => 0) _ _ _ (limb_pubFree _ _ _)]
      · by_cases h1 : r % 256 = 5 + k
        · rw [if_neg (show ¬ r < 256 by omega)]; simp
        · rw [if_neg h1]; simp
  · simp only [outputs, List.mem_flatMap, List.mem_range, List.mem_append] at hc
    obtain ⟨jj, hjj, hc⟩ := hc
    have hcol : HeaderChain.preCols.getD (OUT0 + jj) (.periodic [0]) = oneRow (212 + jj) := by interval_cases jj <;> rfl
    have po := fun h (hh : h ≤ 1) => pubOf_out (main := main) hjj hh hn
    rcases hc with hc | hc <;>
    · simp only [eqLimbs, List.mem_map, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hc
      obtain ⟨h, hh, rfl⟩ := hc
      have hh1 : h ≤ 1 := by rcases hh with rfl | rfl <;> omega
      rw [eval_mul', eval_mul', eval_oneRow hcol hr, eval_last hr]
      by_cases hrow : r = 2 ^ L - 256 + 212 + jj
      · subst hrow
        rw [if_pos (by omega), if_pos (by omega), one_mul, one_mul, eval_sub', sub_eq_zero]
        first
        | (show _ = pubOf (2 ^ L) main (16 + 2 * (3 - jj) + h)
           rw [(po h hh1).1, Expr.eval_pubFree _ _ (pubOf (2 ^ L) main) (fun _ => 0) _ _ _ (limb_pubFree _ _ _)])
        | (show _ = pubOf (2 ^ L) main (16 + 2 * (7 - jj) + h)
           rw [(po h hh1).2, Expr.eval_pubFree _ _ (pubOf (2 ^ L) main) (fun _ => 0) _ _ _ (limb_pubFree _ _ _)])
      · obtain ⟨q, hq⟩ := h256
        by_cases h1 : r % 256 = 212 + jj
        · rw [if_neg (show ¬ 2 ^ L ≤ r + 256 by omega)]; simp
        · rw [if_neg h1]; simp

/-! ## The CSV bit, the trace size, the block hash -/

theorem gate_sat {c : Expr} (hc : c ∈ gates) {r : ℕ} (hr : r < 2 ^ L) :
    c.eval (2 ^ L) HeaderChain.preCols pub main r = 0 :=
  anc_sat hsat (by simp only [ancCs, List.mem_append]; right; exact hc) hr

theorem act_bool : pub PUB_CSV = 0 ∨ pub PUB_CSV = 1 := by
  have := gate_sat hsat (c := .mul act (.sub act (cst 1))) (by simp [gates]) (r := 0) (by positivity)
  simp only [Expr.eval, act, eval_cst, Nat.cast_one, mul_eq_zero, sub_eq_zero] at this
  exact this

theorem off_zero (h0 : pub PUB_CSV = 0) : pub PUB_MLO = 0 ∧ pub PUB_MHI = 0 := by
  have a := gate_sat hsat (c := .mul (.sub (cst 1) act) (.pub PUB_MLO)) (by simp [gates]) (r := 0) (by positivity)
  have b := gate_sat hsat (c := .mul (.sub (cst 1) act) (.pub PUB_MHI)) (by simp [gates]) (r := 0) (by positivity)
  simp only [Expr.eval, act, eval_cst, h0, Nat.cast_one, sub_zero, one_mul] at a b
  exact ⟨a, b⟩

/-- With the CSV bit the trace has at least `2^12` rows. -/
theorem rows_ge (h1 : pub PUB_CSV = 1) : 12 ≤ L := by
  by_contra hlt
  push_neg at hlt
  have hn0 : 0 < 2 ^ L := by positivity
  have hw : wrap (2 ^ L) 0 2048 = 0 := by
    unfold wrap
    have : ((0 : ℕ) : ℤ) + 2048 = ((2 ^ L : ℕ) : ℤ) * 2 ^ (11 - L) := by
      push_cast; rw [← pow_add, show L + (11 - L) = 11 by omega]; norm_num
    rw [this, Int.mul_emod_right]; rfl
  have cp := gate_sat hsat (c := .sub (col FCOPY) (pre FIRST)) (by simp [gates]) hn0
  have g := gate_sat hsat (c := .mul (.mul act (pre FIRST)) (col FCOPY 2048)) (by simp [gates]) hn0
  simp only [Expr.eval, eval_col, wrap_zero hn0, eval_first hn0, act, sub_eq_zero] at cp
  simp only [Expr.eval, eval_col, hw, eval_first hn0, act, h1, cp] at g
  simp at g

/-- **The block hash.** Period 11's hash is public inputs 25–40 (limb `2w + h` is half `h` of word `w`). -/
theorem hash_out (hL : 8 ≤ L) (h1 : pub PUB_CSV = 1) :
    ∀ w < 8, ∀ h ≤ 1, pub (PUB_HASH + 2 * w + h) = ((half16 (stateWord (hashAt main NANC) w) h : ℕ) : F) := by
  have hL12 := rows_ge hsat h1
  have hn : 4096 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL12)
  have hcs := chainSat hsat hL
  have key : ∀ jj < 4, ∀ h ≤ 1,
      pub (PUB_HASH + 2 * (3 - jj) + h) = ((half16 (word main A (2816 + 212 + jj)) h : ℕ) : F) ∧
      pub (PUB_HASH + 2 * (7 - jj) + h) = ((half16 (word main E (2816 + 212 + jj)) h : ℕ) : F) := by
    intro jj hjj h hh
    have hr : 212 + jj < 2 ^ L := by omega
    have hcol : HeaderChain.preCols.getD (OUT0 + jj) (.periodic [0]) = oneRow (212 + jj) := by interval_cases jj <;> rfl
    have hsel : (Expr.mul (.mul (pre (OUT0 + jj)) (pre FIRST)) act).eval (2 ^ L) HeaderChain.preCols pub main (212 + jj) = 1 := by
      simp only [Expr.eval, eval_oneRow hcol hr, eval_first hr, act, h1,
        show (212 + jj) % 256 = 212 + jj by omega, show 212 + jj < 256 by omega, if_true]; simp
    have h2816 : ((256 * NANC : ℕ) : ℤ) = 2816 := by norm_num [NANC]
    have hw : wrap (2 ^ L) (212 + jj) ((256 * NANC : ℕ) : ℤ) = 2816 + 212 + jj := by
      have h' : (4096 : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast hn
      rw [h2816, wrap_eq (by omega) (by omega)]; omega
    have mem : ∀ X b, (X = A ∧ b = PUB_HASH + 2 * (3 - jj) ∨ X = E ∧ b = PUB_HASH + 2 * (7 - jj)) →
        Expr.mul (.mul (.mul (pre (OUT0 + jj)) (pre FIRST)) act) (.sub (limb X h ((256 * NANC : ℕ) : ℤ)) (.pub (b + h)))
          ∈ ancCs := by
      intro X b hXb
      simp only [ancCs, hashOut, List.mem_append, List.mem_flatMap, List.mem_range]
      left; left; left; left
      refine ⟨jj, hjj, ?_⟩
      rcases hXb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left; simp only [eqLimbs, List.mem_map, List.mem_cons, List.mem_singleton]
        exact ⟨h, by omega, by push_cast; rfl⟩
      · right; simp only [eqLimbs, List.mem_map, List.mem_cons, List.mem_singleton]
        exact ⟨h, by omega, by push_cast; rfl⟩
    have ev : ∀ X b, (X = A ∧ b = PUB_HASH + 2 * (3 - jj) ∨ X = E ∧ b = PUB_HASH + 2 * (7 - jj)) →
        pub (b + h) = ((half16 (word main X (2816 + 212 + jj)) h : ℕ) : F) := by
      intro X b hXb
      have c := anc_sat hsat (mem X b hXb) hr
      have hb : ∀ i < 32, (main (X + i) (2816 + 212 + jj)).val ≤ 1 :=
        bits hcs (by omega) (by rcases hXb with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
      rw [eval_mul', hsel, one_mul, eval_sub', eval_limb hw hb hh, sub_eq_zero] at c
      exact c.symm
    exact ⟨ev A _ (Or.inl ⟨rfl, rfl⟩), ev E _ (Or.inr ⟨rfl, rfl⟩)⟩
  intro w hw h hh
  rw [hashAt, outputAt, stAt_word main _ hw]
  by_cases h4 : w < 4
  · simp only [h4, if_true]
    have := (key (3 - w) (by omega) h hh).1
    rw [show 3 - (3 - w) = w by omega, show 2816 + 212 + (3 - w) = 256 * NANC + 144 + 71 - w by unfold NANC; omega] at this
    exact this
  · simp only [h4, if_false]
    have := (key (7 - w) (by omega) h hh).2
    rw [show 7 - (7 - w) = w by omega,
      show 2816 + 212 + (7 - w) = 256 * NANC + 144 + 71 - (w - 4) by unfold NANC; omega] at this
    exact this

/-! ## The comparisons -/

/-- The MTP as a number. -/
def mtpOf (pub : ℕ → F) : ℕ := (pub PUB_MLO).val + 65536 * (pub PUB_MHI).val

theorem ev_tl {X rr : ℕ} (hL : 8 ≤ L) (hrr : rr < 2 ^ L) (hX : X + 32 ≤ 96) {h : ℕ} (hh : h ≤ 1) :
    (timeLimb X h 0).eval (2 ^ L) HeaderChain.preCols pub main rr = ((tl (word main X rr) h : ℕ) : F) := by
  unfold timeLimb
  rw [eval_add', eval_mul', eval_cst, ev_beByte (by omega) (wrap_zero hrr) (bits (chainSat hsat hL) hrr hX),
    ev_beByte (by omega) (wrap_zero hrr) (bits (chainSat hsat hL) hrr hX)]
  unfold tl; push_cast; ring

/-- Where `cmpSel` is on, the flag is `[a < w]` on the times' numeric values. -/
theorem cmp_bit (hL : 8 ≤ L) {rr : ℕ} (hr : rr < 2 ^ L) (hsel : cmpSel.eval (2 ^ L) HeaderChain.preCols pub main rr = 1) :
    bit main 108 rr = decide (leN (word main A rr) < leN (word main W rr)) := by
  have hcs := chainSat hsat hL
  have cLo := anc_sat hsat (c := ancLo) (by simp [ancCs]) hr
  have cHi := anc_sat hsat (c := ancHi) (by simp [ancCs]) hr
  have hbool : ∀ c, 108 ≤ c → c < 124 → (main c rr).val ≤ 1 :=
    fun c h1 h2 => bool_val (sha_sat hcs) hr (Or.inr ⟨h1, h2⟩)
  have eb : bE.eval (2 ^ L) HeaderChain.preCols pub main rr = ((bit main 108 rr).toNat : F) :=
    ev_bit (wrap_zero hr) (hbool 108 (by norm_num) (by norm_num))
  have ec : cE.eval (2 ^ L) HeaderChain.preCols pub main rr = ((bit main 109 rr).toNat : F) :=
    ev_bit (wrap_zero hr) (hbool 109 (by norm_num) (by norm_num))
  have ed : ∀ h ≤ 1, (dLimb h).eval (2 ^ L) HeaderChain.preCols pub main rr =
      (((word main E rr).toNat / 2 ^ (16 * h) % 2 ^ 16 : ℕ) : F) :=
    fun h hh => ev_window (by omega) (wrap_zero hr) (bits hcs hr (by decide))
  set T := word main A rr
  set t := word main W rr
  have eT0 := ev_tl hsat hL hr (X := A) (by decide) (h := 0) (by norm_num)
  have eT1 := ev_tl hsat hL hr (X := A) (by decide) (h := 1) (by norm_num)
  have et0 := ev_tl hsat hL hr (X := W) (by decide) (h := 0) (by norm_num)
  have et1 := ev_tl hsat hL hr (X := W) (by decide) (h := 1) (by norm_num)
  have ed0 := ed 0 (by norm_num); have ed1 := ed 1 (by norm_num)
  unfold ancLo at cLo; unfold ancHi at cHi
  simp only [eval_mul', eval_sub', eval_add', eval_cst, hsel, eb, ec, eT0, eT1, et0, et1, ed0, ed1, one_mul]
    at cLo cHi
  have hT := leN_tl T; have ht := leN_tl t
  have lT0 := tl_lt T 0; have lT1 := tl_lt T 1; have lt0 := tl_lt t 0; have lt1 := tl_lt t 1
  have ld0 := Nat.mod_lt ((word main E rr).toNat / 2 ^ (16 * 0)) (show 0 < 2 ^ 16 by norm_num)
  have ld1 := Nat.mod_lt ((word main E rr).toNat / 2 ^ (16 * 1)) (show 0 < 2 ^ 16 by norm_num)
  have lc := Bool.toNat_le (bit main 109 rr)
  set d0 := (word main E rr).toNat / 2 ^ (16 * 0) % 2 ^ 16
  set d1 := (word main E rr).toNat / 2 ^ (16 * 1) % 2 ^ 16
  set c := (bit main 109 rr).toNat
  cases hb : bit main 108 rr
  · simp only [hb, Bool.toNat_false, Nat.cast_zero, zero_mul, zero_add, sub_zero, one_mul] at cLo cHi
    have n0 : tl t 0 + d0 = tl T 0 + 65536 * c :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cLo)
    have n1 : tl t 1 + d1 + c = tl T 1 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cHi)
    symm; simp only [decide_eq_false_iff_not, not_lt]; omega
  · simp only [hb, Bool.toNat_true, Nat.cast_one, one_mul, sub_self, zero_mul, add_zero] at cLo cHi
    have n0 : tl T 0 + 1 + d0 = tl t 0 + 65536 * c :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cLo)
    have n1 : tl T 1 + d1 + c = tl t 1 :=
      natCast_inj_of_lt (lt_P_of (by omega)) (lt_P_of (by omega)) (by push_cast; linear_combination cHi)
    symm; simp only [decide_eq_true_eq]; omega

section Period

variable {k : ℕ} (hk : 256 * (k + 1) ≤ 2 ^ L)
include hk

theorem ev_cmpSel {i : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 2) :
    cmpSel.eval (2 ^ L) HeaderChain.preCols pub main (256 * k + 228 + i) = 1 := by
  unfold cmpSel slotSel
  simp only [Expr.eval]
  rw [show 256 * k + 228 + i = 256 * k + (228 + i) by omega,
    ev_sel (j := k) hk (k := 0) (by norm_num) (by omega), ev_sel (j := k) hk (k := 1) (by norm_num) (by omega)]
  rcases (by omega : i = 1 ∨ i = 2) with rfl | rfl <;> simp

theorem op_sat {c : Expr} {h : ℕ} (hh : h ≤ 1) (hc : c ∈ operands h) {rr : ℕ} (hr : rr < 2 ^ L) :
    c.eval (2 ^ L) HeaderChain.preCols pub main rr = 0 :=
  anc_sat hsat (by
    simp only [ancCs, List.mem_append, List.mem_flatMap]
    left; left; left; right
    exact ⟨h, by rcases (by omega : h = 0 ∨ h = 1) with rfl | rfl <;> simp, hc⟩) hr

/-- An operand row pins a word to another one, `off` rows up. -/
theorem op_word {i X off : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 2) (hX : X + 32 ≤ 96) (hoff : off ≤ 228)
    (hmem : ∀ h ≤ 1, Expr.mul (slotSel i) (.sub (limb X h) (limb W h (-(off : ℤ)))) ∈ operands h) (hL : 8 ≤ L) :
    word main X (256 * k + 228 + i) = word main W (256 * k + 228 + i - off) := by
  have hr : 256 * k + 228 + i < 2 ^ L := by omega
  have hcs := chainSat hsat hL
  have hs : (slotSel i).eval (2 ^ L) HeaderChain.preCols pub main (256 * k + 228 + i) = 1 := ev_slotSel hk (by omega) (by omega)
  have e : ∀ h ≤ 1, ((half16 (word main X (256 * k + 228 + i)) h : ℕ) : F) =
      ((half16 (word main W (256 * k + 228 + i - off)) h : ℕ) : F) := fun h hh => by
    have := op_sat hsat hk hh (hmem h hh) hr
    rw [eval_mul', hs, one_mul, eval_sub', eval_limb (wrap_zero hr) (bits hcs hr hX) hh,
      eval_limb (wrap_back (by omega) hr) (bits hcs (by omega) (by decide)) hh] at this
    exact sub_eq_zero.mp this
  exact word_of_halves (e 0 (by norm_num)) (e 1 (by norm_num))

/-- An operand row's time limbs are the MTP's. -/
theorem op_mtp {i X : ℕ} (hi1 : 1 ≤ i) (hi : i ≤ 2) (hX : X + 32 ≤ 96)
    (hmem : ∀ h ≤ 1, Expr.mul (slotSel i) (.sub (timeLimb X h 0) (mpub h)) ∈ operands h) (hL : 8 ≤ L) :
    leN (word main X (256 * k + 228 + i)) = mtpOf pub := by
  have hr : 256 * k + 228 + i < 2 ^ L := by omega
  have hs : (slotSel i).eval (2 ^ L) HeaderChain.preCols pub main (256 * k + 228 + i) = 1 := ev_slotSel hk (by omega) (by omega)
  have e : ∀ h ≤ 1, (mpub h).eval (2 ^ L) HeaderChain.preCols pub main (256 * k + 228 + i) =
      ((tl (word main X (256 * k + 228 + i)) h : ℕ) : F) := fun h hh => by
    have := op_sat hsat hk hh (hmem h hh) hr
    rw [eval_mul', hs, one_mul, eval_sub', ev_tl hsat hL hr hX hh] at this
    exact (sub_eq_zero.mp this).symm
  have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num)
  simp only [mpub, Expr.eval, if_true, show (1 : ℕ) ≠ 0 by norm_num, if_false] at e0 e1
  rw [mtpOf, e0, e1, ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (lt_P_of (by have := tl_lt (word main X (256 * k + 228 + i)) 0; omega)),
    Nat.mod_eq_of_lt (lt_P_of (by have := tl_lt (word main X (256 * k + 228 + i)) 1; omega)), leN_tl]

/-- The MTP's public limbs are 16-bit. -/
theorem mtp_limbs (hL : 8 ≤ L) : (pub PUB_MLO).val < 65536 ∧ (pub PUB_MHI).val < 65536 := by
  have hr : 256 * k + 228 + 1 < 2 ^ L := by omega
  have hs : (slotSel 1).eval (2 ^ L) HeaderChain.preCols pub main (256 * k + 228 + 1) = 1 := ev_slotSel hk (by omega) (by omega)
  have e : ∀ h ≤ 1, (mpub h).eval (2 ^ L) HeaderChain.preCols pub main (256 * k + 228 + 1) =
      ((tl (word main A (256 * k + 228 + 1)) h : ℕ) : F) := fun h hh => by
    have := op_sat hsat hk hh (c := Expr.mul (slotSel 1) (.sub (timeLimb A h 0) (mpub h))) (by simp [operands]) hr
    rw [eval_mul', hs, one_mul, eval_sub', ev_tl hsat hL hr (by decide) hh] at this
    exact (sub_eq_zero.mp this).symm
  have e0 := e 0 (by norm_num); have e1 := e 1 (by norm_num)
  simp only [mpub, Expr.eval, if_true, show (1 : ℕ) ≠ 0 by norm_num, if_false] at e0 e1
  rw [e0, e1, ZMod.val_natCast, ZMod.val_natCast]
  exact ⟨lt_of_le_of_lt (Nat.mod_le _ _) (tl_lt _ 0), lt_of_le_of_lt (Nat.mod_le _ _) (tl_lt _ 1)⟩

/-- Slot 1's flag: the MTP is below the header's time. -/
theorem flag_above (hL : 8 ≤ L) :
    bit main 108 (256 * k + 229) = decide (mtpOf pub < leN (headerWord main k 17)) := by
  have hr : 256 * k + 229 < 2 ^ L := by omega
  rw [cmp_bit hsat hL hr (by simpa using ev_cmpSel hsat hk (i := 1) (by norm_num) (by norm_num)),
    show 256 * k + 229 = 256 * k + 228 + 1 by omega,
    op_mtp hsat hk (i := 1) (X := A) (by norm_num) (by norm_num) (by decide) (fun h _ => by simp [operands]) hL,
    op_word hsat hk (i := 1) (X := W) (off := 152) (by norm_num) (by norm_num) (by decide) (by norm_num)
      (fun h _ => by simp [operands]) hL]
  simp [headerWord, show 256 * k + 228 + 1 - 152 = 256 * k + 76 + (17 - 16) by omega]

/-- Slot 2's flag: the header's time is below the MTP. -/
theorem flag_below (hL : 8 ≤ L) :
    bit main 108 (256 * k + 230) = decide (leN (headerWord main k 17) < mtpOf pub) := by
  have hr : 256 * k + 230 < 2 ^ L := by omega
  rw [cmp_bit hsat hL hr (by simpa using ev_cmpSel hsat hk (i := 2) (by norm_num) (by norm_num)),
    show 256 * k + 230 = 256 * k + 228 + 2 by omega,
    op_mtp hsat hk (i := 2) (X := W) (by norm_num) (by norm_num) (by decide) (fun h _ => by simp [operands]) hL,
    op_word hsat hk (i := 2) (X := A) (off := 153) (by norm_num) (by norm_num) (by decide) (by norm_num)
      (fun h _ => by simp [operands]) hL]
  simp [headerWord, show 256 * k + 228 + 2 - 153 = 256 * k + 76 + (17 - 16) by omega]

end Period

/-! ## The counts -/

/-- At most 5 of the 11 predecessors' times are above the MTP, and at most 5 below. -/
theorem counts_le (hL : 8 ≤ L) (h1 : pub PUB_CSV = 1) :
    ∑ k ∈ Finset.range NANC, (decide (mtpOf pub < leN (headerWord main k 17))).toNat ≤ 5 ∧
    ∑ k ∈ Finset.range NANC, (decide (leN (headerWord main k 17) < mtpOf pub)).toNat ≤ 5 := by
  have hL12 := rows_ge hsat h1
  have hn : 4096 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL12)
  have hcs := chainSat hsat hL
  have hr : 240 < 2 ^ L := by omega
  have hsel : (Expr.mul (.mul (pre MTPC) (pre FIRST)) act).eval (2 ^ L) HeaderChain.preCols pub main 240 = 1 := by
    have := ev_sel (logSize := L) (pub := pub) (main := main) (j := 0) (by omega) (k := 11) (by norm_num) (q := 240) (by norm_num)
    simp only [Nat.mul_zero, Nat.zero_add] at this
    simp only [Expr.eval, show MTPC = MTP0 + 11 from rfl, this, eval_first hr, act, h1]; simp
  have hb : ∀ rr, rr < 2 ^ L → (main 108 rr).val ≤ 1 :=
    fun rr h => bool_val (sha_sat hcs) h (Or.inr ⟨by norm_num, by norm_num⟩)
  have esum : ∀ (s : ℕ) (fl : ℕ → Bool), 229 ≤ s → s ≤ 230 →
      (∀ k < NANC, bit main 108 (256 * k + s) = fl k) →
      (countSum s).eval (2 ^ L) HeaderChain.preCols pub main 240 = ((∑ k ∈ Finset.range NANC, (fl k).toNat : ℕ) : F) := by
    intro s fl hs1 hs2 hfl
    unfold countSum
    rw [eval_foldl_list _ (fun k => flagAt s k), eval_cst, Nat.cast_zero, zero_add, list_range_sum, Nat.cast_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [Finset.mem_range, NANC] at hk
    have hw : wrap (2 ^ L) 240 ((256 * k : ℕ) + (s : ℤ) - 240) = 256 * k + s := by
      have h' : (4096 : ℤ) ≤ ((2 ^ L : ℕ) : ℤ) := by exact_mod_cast hn
      rw [wrap_eq (by omega) (by omega)]; omega
    unfold flagAt
    rw [ev_bit hw (hb _ (by omega)), hfl k (by unfold NANC; omega)]
  have hAbits := bits hcs hr (base := A) (by decide)
  have hEbits := bits hcs hr (base := E) (by decide)
  constructor
  · have c := anc_sat hsat (c := (counts.getD 0 (cst 0))) (by simp [ancCs, counts]) hr
    simp only [counts, List.getD_cons_zero] at c
    rw [eval_mul', hsel, one_mul, eval_sub', eval_add',
      esum 229 (fun k => decide (mtpOf pub < leN (headerWord main k 17))) (by norm_num) (by norm_num)
        (fun k hk => flag_above hsat (k := k) (by unfold NANC at hk; omega) hL),
      ev_window (by norm_num) (wrap_zero hr) hAbits, eval_cst, sub_eq_zero] at c
    have hr8 := Nat.mod_lt ((word main A 240).toNat / 2 ^ 0) (show 0 < 2 ^ 3 by norm_num)
    set R := (word main A 240).toNat / 2 ^ 0 % 2 ^ 3
    have hS : ∑ k ∈ Finset.range NANC, (decide (mtpOf pub < leN (headerWord main k 17))).toNat ≤ NANC :=
      le_trans (Finset.sum_le_sum (fun k _ => Bool.toNat_le _)) (by simp)
    set S : ℕ := ∑ k ∈ Finset.range NANC, (decide (mtpOf pub < leN (headerWord main k 17))).toNat with hSdef
    have c' : ((S + R : ℕ) : F) = ((5 : ℕ) : F) := by push_cast; push_cast at c; exact c
    have := natCast_inj_of_lt (lt_P_of (by unfold NANC at hS; omega)) (lt_P_of (by norm_num)) c'
    omega
  · have c := anc_sat hsat (c := (counts.getD 1 (cst 0))) (by simp [ancCs, counts]) hr
    simp only [counts, List.getD_cons_succ, List.getD_cons_zero] at c
    rw [eval_mul', hsel, one_mul, eval_sub', eval_add',
      esum 230 (fun k => decide (leN (headerWord main k 17) < mtpOf pub)) (by norm_num) (by norm_num)
        (fun k hk => flag_below hsat (k := k) (by unfold NANC at hk; omega) hL),
      ev_window (by norm_num) (wrap_zero hr) hEbits, eval_cst, sub_eq_zero] at c
    have hr8 := Nat.mod_lt ((word main E 240).toNat / 2 ^ 0) (show 0 < 2 ^ 3 by norm_num)
    set R := (word main E 240).toNat / 2 ^ 0 % 2 ^ 3
    have hS : ∑ k ∈ Finset.range NANC, (decide (leN (headerWord main k 17) < mtpOf pub)).toNat ≤ NANC :=
      le_trans (Finset.sum_le_sum (fun k _ => Bool.toNat_le _)) (by simp)
    set S : ℕ := ∑ k ∈ Finset.range NANC, (decide (leN (headerWord main k 17) < mtpOf pub)).toNat with hSdef
    have c' : ((S + R : ℕ) : F) = ((5 : ℕ) : F) := by push_cast; push_cast at c; exact c
    have := natCast_inj_of_lt (lt_P_of (by unfold NANC at hS; omega)) (lt_P_of (by norm_num)) c'
    omega

/-! ## Soundness -/

/-- **Ancestry soundness.** -/
theorem anc_sound (hL : 8 ≤ L) :
    (pub PUB_CSV = 0 ∧ pub PUB_MLO = 0 ∧ pub PUB_MHI = 0) ∨
    (pub PUB_CSV = 1 ∧ 12 ≤ L ∧
      (∀ j ≤ NANC, sha256d (headerWord main j) = hashAt main j) ∧
      (∀ j, 1 ≤ j → j ≤ NANC → prevHash (headerWord main j) = hashAt main (j - 1)) ∧
      (∀ w < 8, ∀ h ≤ 1, pub (PUB_HASH + 2 * w + h) = ((half16 (stateWord (hashAt main NANC) w) h : ℕ) : F)) ∧
      ((pub PUB_MLO).val < 65536 ∧ (pub PUB_MHI).val < 65536) ∧
      mtpOf pub = medianTimePast ((List.range NANC).map (fun k => timeOf (headerWord main k))).reverse) := by
  rcases act_bool hsat with h0 | h1
  · exact Or.inl ⟨h0, off_zero hsat h0⟩
  right
  have hL12 := rows_ge hsat h1
  have hn : 4096 ≤ 2 ^ L := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hL12)
  have hcs := chainSat hsat hL
  refine ⟨h1, hL12, fun j hj => header_hash hcs (by unfold NANC at hj; omega),
    fun j hj1 hj => header_link hcs (by unfold NANC at hj; omega) hj1, hash_out hsat hL h1,
    mtp_limbs hsat (k := 0) (by omega) hL, ?_⟩
  obtain ⟨ca, cb⟩ := counts_le hsat hL h1
  symm
  apply median_of_counts
  · simp [NANC]
  · rw [List.countP_reverse, countP_range_map]; exact ca
  · rw [List.countP_reverse, countP_range_map]; exact cb

end Sat

end StarkedAir.Block.Anc
