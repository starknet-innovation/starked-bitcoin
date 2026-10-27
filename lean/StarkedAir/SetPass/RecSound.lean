/-
**Records (`set_rec`), soundness at the component level.** In a satisfied `set_rec` trace whose
lookups are answered (the byte reads by a byte function `S`, the range checks, the fingerprints), the
on rows are a prefix `[0, e)`, row `r` is record `r` of the segment, and:

- `rows_sound`: `IDX r = r`, and `i_out − i_in = e`;
- `parse_sound`: the records start at 0, each after the previous one's `49 + len` bytes, the last one
  ends at the segment length; the records read from the bytes (`recAt`) encode exactly the segment's
  bytes (`SetFile.encRec`), each is `RecOk` with height below `2^24`; the code bytes are the code's
  little-endian bytes;
- `order_sound`: the records are strictly sorted (`SetFile.Sorted`), the first above the incoming key
  when there is one, the last's key is the outgoing key (`keyB`: txid bytes, then `vout` big-endian;
  `keyLt_of_lex`);
- `amount_sound`, `height_sound`: the outgoing amount and highest height from the incoming ones;
- `sum_sound`: the outgoing sum is the incoming one plus `1/(z − φ)` per record, `φ` the coin tuple's
  fingerprint (`tupleOf`, with the record's `txi` as its last term).

The lookup results are hypotheses here (`Hyp`); the segment system's link supplies them.
-/
import StarkedAir.SetPass.Rec
import StarkedAir.Block.CoinEvents
import StarkedAir.Spec.SetFile

namespace StarkedAir.SetPass.Rec

open StarkedAir
open StarkedAir.Sha256 (col pre cst boolC eval_col eval_cst wrap_back)
open StarkedAir.Spec.QM31 (QM toQ emb coordsOf toQ_coordsOf coordsOf_toQ toQ_mul toQ_add toQ_sub)
open StarkedAir.Spec.SetFile (encRec RecOk keyLt lexLt Sorted amountOf sortedAfter)

/-! ### Bytes and records -/

/-- `k` bytes of `S` from `a`. -/
def bytesAt (S : ℕ → ℕ) (a k : ℕ) : Spec.Block.Bytes := (List.range k).map fun i => UInt8.ofNat (S (a + i))

/-- The record at `st` with `ser` length `ln`, read from the bytes: `txid(32) ‖ vout(4) ‖ height(4) ‖
cb(1) ‖ txi(4) ‖ len(4) ‖ ser(len)`. -/
def recAt (S : ℕ → ℕ) (st ln : ℕ) : Spec.CoinEpoch.CEv :=
  (⟨bytesAt S st 32, Spec.Block.le (bytesAt S (st + 32) 4)⟩,
    (2 * Spec.Block.le (bytesAt S (st + 36) 4) + S (st + 40), bytesAt S (st + 49) ln),
    Spec.Block.le (bytesAt S (st + 41) 4))

theorem bytesAt_length (S : ℕ → ℕ) (a k : ℕ) : (bytesAt S a k).length = k := by simp [bytesAt]

theorem bytesAt_add (S : ℕ → ℕ) (a k l : ℕ) : bytesAt S a (k + l) = bytesAt S a k ++ bytesAt S (a + k) l := by
  simp only [bytesAt, List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Function.comp, Nat.add_assoc]

theorem bytesAt_succ (S : ℕ → ℕ) (a k : ℕ) : bytesAt S a (k + 1) = UInt8.ofNat (S a) :: bytesAt S (a + 1) k := by
  rw [Nat.add_comm k 1, bytesAt_add]
  simp [bytesAt]

theorem toNat_ofNat_lt {x : ℕ} (h : x < 256) : (UInt8.ofNat x).toNat = x := by
  rw [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt h

theorem getD_bytesAt {S : ℕ → ℕ} (hS : ∀ q, S q < 256) {a k i : ℕ} (hi : i < k) :
    ((bytesAt S a k).getD i 0).toNat = S (a + i) := by
  simp [bytesAt, List.getD_eq_getElem?_getD, hi, toNat_ofNat_lt (hS _)]

/-- **Little-endian bytes.** -/
theorem le_bytesAt {S : ℕ → ℕ} (hS : ∀ q, S q < 256) : ∀ (k a : ℕ),
    Spec.Block.le (bytesAt S a k) = ∑ i ∈ Finset.range k, S (a + i) * 256 ^ i
  | 0, a => by simp [bytesAt, Spec.Block.le]
  | k + 1, a => by
    rw [bytesAt_succ, Finset.sum_range_succ']
    show (UInt8.ofNat (S a)).toNat + 256 * Spec.Block.le (bytesAt S (a + 1) k) = _
    rw [le_bytesAt hS k (a + 1), toNat_ofNat_lt (hS _), Finset.mul_sum]
    simp only [add_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show a + (i + 1) = a + 1 + i by omega, pow_succ]; ring

theorem le_bytesAt4 {S : ℕ → ℕ} (hS : ∀ q, S q < 256) (a : ℕ) :
    Spec.Block.le (bytesAt S a 4) = S a + 256 * S (a + 1) + 65536 * S (a + 2) + 16777216 * S (a + 3) := by
  rw [le_bytesAt hS]; simp [Finset.sum_range_succ]; ring

theorem leBytes_bytesAt {S : ℕ → ℕ} {a : ℕ} : Spec.Block.leBytes 4 (Spec.Block.le (bytesAt S a 4)) = bytesAt S a 4 :=
  Spec.Block.leBytes_le' (bytesAt_length _ _ _)

/-- **A record read from the bytes encodes them**, given the head's checks: `cb ≤ 1` and the length
field `ln`. -/
theorem encRec_recAt {S : ℕ → ℕ} {st ln : ℕ} (hcb : S (st + 40) ≤ 1)
    (hln : Spec.Block.le (bytesAt S (st + 45) 4) = ln) :
    encRec (recAt S st ln) = bytesAt S st (49 + ln) := by
  have h2 : (2 * Spec.Block.le (bytesAt S (st + 36) 4) + S (st + 40)) / 2 = Spec.Block.le (bytesAt S (st + 36) 4) := by
    omega
  have h1 : (2 * Spec.Block.le (bytesAt S (st + 36) 4) + S (st + 40)) % 2 = S (st + 40) := by omega
  have hcbB : [UInt8.ofNat (S (st + 40))] = bytesAt S (st + 40) 1 := by simp [bytesAt]
  simp only [encRec, recAt, Spec.SetFile.txid, Spec.SetFile.vout, Spec.SetFile.code, Spec.SetFile.ser, Spec.SetFile.txi, h2, h1, bytesAt_length,
    leBytes_bytesAt, hcbB, ← hln]
  generalize Spec.Block.le (bytesAt S (st + 45) 4) = ln
  rw [show 49 + ln = 32 + 4 + 4 + 1 + 4 + 4 + ln by omega, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add, bytesAt_add,
    bytesAt_add]

/-! ### Keys -/

/-- Key byte `i` of a record: its txid's bytes, then `vout` big-endian. -/
def keyB (x : Spec.CoinEpoch.CEv) (i : ℕ) : ℕ :=
  if i < 32 then ((Spec.SetFile.txid x).getD i 0).toNat else Spec.SetFile.vout x / 256 ^ (35 - i) % 256

/-- Lexicographic order on key bytes. -/
def KeyLex (a b : ℕ → ℕ) : Prop := ∃ d < 36, (∀ i < d, a i = b i) ∧ a d < b d

theorem lexLt_of_getD : ∀ (x y : Spec.Block.Bytes), x.length = y.length → ∀ d < x.length,
    (∀ i < d, x.getD i 0 = y.getD i 0) → (x.getD d 0).toNat < (y.getD d 0).toNat → lexLt x y = true
  | [], _, _, d, hd, _, _ => by simp at hd
  | a :: as, [], h, _, _, _, _ => by simp at h
  | a :: as, b :: bs, h, d, hd, he, hlt => by
    cases d with
    | zero =>
      simp only [List.getD_cons_zero] at hlt
      simp [lexLt, UInt8.lt_iff_toNat_lt, hlt]
    | succ d =>
      have hab : a = b := by simpa using he 0 (by omega)
      have ih := lexLt_of_getD as bs (by simpa using h) d (by simp at hd; omega)
        (fun i hi => by simpa using he (i + 1) (by omega)) (by simpa using hlt)
      simp [lexLt, hab, ih]

/-- **The key order is lexicographic on key bytes** (for 32-byte txids and 32-bit `vout`s). -/
theorem keyLt_of_lex {x y : Spec.CoinEpoch.CEv} (hx : (Spec.SetFile.txid x).length = 32) (hy : (Spec.SetFile.txid y).length = 32)
    (hvx : Spec.SetFile.vout x < 2 ^ 32) (hvy : Spec.SetFile.vout y < 2 ^ 32) (h : KeyLex (keyB x) (keyB y)) : keyLt x y = true := by
  obtain ⟨d, hd, heq, hlt⟩ := h
  unfold keyLt
  by_cases hd32 : d < 32
  · have : lexLt (Spec.SetFile.txid x) (Spec.SetFile.txid y) = true := by
      apply lexLt_of_getD _ _ (by rw [hx, hy]) d (by omega)
      · intro i hi
        have := heq i hi
        simp only [keyB, show i < 32 by omega, if_true] at this
        exact UInt8.toNat_inj.mp this
      · simpa [keyB, hd32] using hlt
    simp [this]
  · have htx : Spec.SetFile.txid x = Spec.SetFile.txid y := by
      apply List.ext_getElem (by rw [hx, hy])
      intro i h1 h2
      have := heq i (by omega)
      simp only [keyB, show i < 32 by omega, if_true] at this
      have e := UInt8.toNat_inj.mp this
      simpa [List.getD_eq_getElem?_getD, h1, h2] using e
    have hv : Spec.SetFile.vout x < Spec.SetFile.vout y := by
      have k := fun i (hi : i < d) => heq i hi
      simp only [keyB] at k hlt
      rw [if_neg hd32] at hlt
      have k32 := k 32; have k33 := k 33; have k34 := k 34
      simp only [show ¬ (32 < 32) by omega, show ¬ (33 < 32) by omega, show ¬ (34 < 32) by omega, if_false] at k32 k33 k34
      norm_num at k32 k33 k34 hlt
      interval_cases d <;> norm_num at hlt <;> omega
    simp [htx, hv]

/-! ### The trace -/

/-- **The lookups' answers** (the system link supplies them): the head and amount bytes are the byte
function `S` at the record's positions (below the segment length), the range-checked columns are
bytes, the fingerprint is the Horner value of the `ser` bytes; and the incoming public values are in
range. -/
structure Hyp (n : ℕ) (pub : ℕ → F) (M : ℕ → ℕ → F) (S : ℕ → ℕ) : Prop where
  byte : ∀ q, S q < 256
  hb : ∀ r < n, M ON r = 1 → ∀ j : ℕ, j < 49 → ∃ q < (pub PUB_LEN).val, M START r + (j : F) = (q : F) ∧ (M (HB j) r).val = S q
  ab : ∀ r < n, M ON r = 1 → ∀ j : ℕ, j < 8 → ∃ q < (pub PUB_LEN).val,
    M START r + ((49 + j : ℕ) : F) = (q : F) ∧ (M (AB j) r).val = S q
  r8 : ∀ r < n, M ON r = 1 → ∀ i < 3,
    (M (C i) r).val < 256 ∧ (M (D i) r).val < 256 ∧ (M (SB i) r).val < 256 ∧ (M (MD i) r).val < 256
  am : ∀ r < n, ∀ j < 12, (M (AM j) r).val < 256
  delta : ∀ r < n, M ON r = 1 → (r ≠ 0 ∨ pub PUB_HASLAST = 1) → (M DELTA r).val < 256
  fp : ∀ r < n, M ON r = 1 → ∃ u0 : ℕ, u0 < P ∧ M START r + 49 = (u0 : F) ∧
    toQ ⟨M FH r, M (FH + 1) r, M (FH + 2) r, M (FH + 3) r⟩ =
      Block.FpWalk.horner (Block.FpWalk.gQ pub) ((List.range (M LENC r).val).map fun i => emb ((S (u0 + i) : ℕ) : F))
  hasLast : pub PUB_HASLAST = 0 ∨ pub PUB_HASLAST = 1
  lastIn : ∀ j < 36, (pub (PUB_LAST_IN j)).val < 256
  amtIn : ∀ j < 12, (pub (PUB_AMT_IN j)).val < 256
  maxIn : (pub PUB_MAXH_IN).val < 2 ^ 24

theorem cast_val (x : F) : ((x.val : ℕ) : F) = x := ZMod.natCast_zmod_val x

theorem val_of_eq {x : F} {a : ℕ} (h : x = (a : F)) (ha : a < P) : x.val = a := by
  rw [h]; exact ZMod.val_natCast_of_lt ha

theorem lift {a b : ℕ} (h : (a : F) = (b : F)) (ha : a < P) (hb : b < P) : a = b := natCast_inj_of_lt ha hb h

theorem P_big : 2 ^ 30 < P := by unfold P; norm_num

/-- The on rows are `[0, e)`, `0 < e < n`. -/
structure OnPre (n : ℕ) (M : ℕ → ℕ → F) (e : ℕ) : Prop where
  pos : 0 < e
  lt : e < n
  on : ∀ r < n, M ON r = if r < e then 1 else 0

section Rows

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

omit hsat in
theorem ev_k {c r : ℕ} (hr : r < n) : (k c).eval n preCols pub M r = M c r := by simp [k, eval_col, wrap_zero hr]
omit hsat in
theorem ev_kp {c r : ℕ} (hr : r + 1 < n) : (kp c).eval n preCols pub M (r + 1) = M c r := by
  simp only [kp, eval_col]
  rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) hr]; rfl
omit hsat in
theorem ev_kn {c r : ℕ} (hr : r + 1 < n) : (kn c).eval n preCols pub M r = M c (r + 1) := by
  simp [kn, eval_col, wrap_one hr]
omit hsat in
theorem ev_first {r : ℕ} (hr : r < n) : first.eval n preCols pub M r = if r = 0 then 1 else 0 := by
  simp [first, pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval]
omit hsat in
theorem ev_notFirst {r : ℕ} (hr : r < n) : notFirst.eval n preCols pub M r = if r = 0 then 0 else 1 := by
  simp only [notFirst, om, one, Expr.eval, eval_cst, ev_first hr]; split_ifs <;> simp
omit hsat in
theorem ev_isLast {r : ℕ} (hr : r < n) : isLast.eval n preCols pub M r = if r + 1 < n then 0 else 1 := by
  simp only [isLast, om, one, Expr.eval, eval_cst]
  simp only [pre, Expr.eval, wrap_zero hr, preCols, PreCol.eval, List.getD_cons_succ, List.getD_cons_zero]
  split_ifs <;> simp
omit hsat in
theorem ev_one {r : ℕ} : one.eval n preCols pub M r = 1 := by simp [one, eval_cst]
omit hsat in
theorem ev_hb {j r : ℕ} (hr : r < n) : (hb j).eval n preCols pub M r = M (HB j) r := ev_k hr
omit hsat in
theorem ev_pair {a b : Expr} {r : ℕ} : (pair a b).eval n preCols pub M r =
    a.eval n preCols pub M r + 256 * b.eval n preCols pub M r := by simp [pair, Expr.eval, eval_cst]

omit hsat in
theorem mem_lc {c : Expr} (h : c ∈ localC) : c ∈ constraints := by
  simp only [constraints, List.mem_append]; left; left; left; left; exact h

/-- A constraint of `localC`'s explicit middle part. -/
theorem lc {c : Expr} {r : ℕ} (hr : r < n) (h : c ∈ localC) : c.eval n preCols pub M r = 0 := hsat r hr c (mem_lc h)

theorem bool_of {c : ℕ} {r : ℕ} (hr : r < n) (h : boolC (k c) ∈ localC) : M c r = 0 ∨ M c r = 1 := by
  have := lc hsat hr h
  simp only [boolC, Expr.eval, ev_k hr, eval_cst, Nat.cast_one] at this
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

/-! ### Membership in `localC` (ten pieces) -/

omit hsat in
theorem memA {c : ℕ} (h : c ∈ [ON, LST, GT]) : boolC (k c) ∈ localC := by
  unfold localC
  iterate 9 apply List.mem_append_left
  exact List.mem_map.2 ⟨c, h, rfl⟩
omit hsat in
theorem memB {c : ℕ} (h : c ∈ [K 1, K 2, K 3]) : boolC (k c) ∈ localC := by
  unfold localC
  iterate 8 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨c, h, rfl⟩)
omit hsat in
theorem memC {j : ℕ} (h : j < 11) : boolC (k (AC (j + 1))) ∈ localC := by
  unfold localC
  iterate 7 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)
omit hsat in
theorem memD {j : ℕ} (h : j < 36) : boolC (k (DIFF j)) ∈ localC := by
  unfold localC
  iterate 6 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)
omit hsat in
theorem memPrev {j : ℕ} (h : j < 36) :
    Expr.sub (k (PREV j)) (.add (.mul notFirst (kp (keyCol j))) (.mul first (.pub (PUB_LAST_IN j)))) ∈ localC := by
  unfold localC
  iterate 4 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)

/-- The comparison's prefix: `cmp − Σ_{i<j} DIFF i`. -/
def beforeE (j : ℕ) : Expr := (List.range j).foldl (fun acc i => .sub acc (k (DIFF i))) cmp

omit hsat in
theorem memBefore {j : ℕ} (h : j < 36) :
    Expr.mul (.sub (beforeE j) (k (DIFF j))) (.sub (k (keyCol j)) (k (PREV j))) ∈ localC := by
  unfold localC
  iterate 3 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)
omit hsat in
theorem memLastOut {j : ℕ} (h : j < 36) : Expr.mul (k LST) (.sub (k (keyCol j)) (.pub (PUB_LAST_OUT j))) ∈ localC := by
  unfold localC
  iterate 2 apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)

/-- Amount byte `j`'s constraint. -/
def amtC (j : ℕ) : Expr :=
  let prev := Expr.add (.mul notFirst (kp (AM j))) (.mul first (.pub (PUB_AMT_IN j)))
  let add := if j < 8 then Expr.mul (k ON) (k (AB j)) else cst 0
  let cin := if j = 0 then cst 0 else k (AC j)
  let cout := if j = 11 then cst 0 else Expr.mul (cst 256) (k (AC (j + 1)))
  .sub (k (AM j)) (.sub (.add (.add prev add) cin) cout)

omit hsat in
theorem memAmt {j : ℕ} (h : j < 12) : amtC j ∈ localC := by
  unfold localC
  apply List.mem_append_left
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)
omit hsat in
theorem memAmtOut {j : ℕ} (h : j < 12) : Expr.mul isLast (.sub (k (AM j)) (.pub (PUB_AMT_OUT j))) ∈ localC := by
  unfold localC
  exact List.mem_append_right _ (List.mem_map.2 ⟨j, List.mem_range.2 h, rfl⟩)

end Rows

/-- Membership in `localC`'s explicit middle part (piece 5). -/
theorem memE {c : Expr} (h : c ∈ ([ -- rows: a nonempty prefix; the last record
        .mul first (om (k ON)), .mul notFirst (.mul (k ON) (om (kp ON))), .mul isLast (k ON),
        .sub (k LST) (.mul (k ON) (om (kn ON))),
        -- the index and the count
        .mul first (k IDX), .mul notFirst (.mul (k ON) (.sub (.sub (k IDX) (kp IDX)) one)),
        .mul (k LST) (.sub (.add (k IDX) one) (.sub (.pub PUB_I_OUT) (.pub PUB_I_IN))),
        -- positions
        .mul first (k START),
        .mul notFirst (.mul (k ON) (.sub (k START) (.add (.add (kp START) (cst 49)) (kp LENC)))),
        .mul (k LST) (.sub (.add (.add (k START) (cst 49)) (k LENC)) (.pub PUB_LEN)),
        .mul (k ON) (.sub (k START) (b3 SB)),
        -- the fields
        .sub (k LENC) lenOf, .mul (k ON) (hb 48), .mul (k ON) (.sub (.sub (k LENC) (cst 8)) (b3 D)),
        .mul (k ON) (boolC (hb 40)), .mul (k ON) (hb 39),
        .sub (k (C 0)) (.sub (.add (.mul (cst 2) (hb 36)) (hb 40)) (.mul (cst 256) (k (K 1)))),
        .sub (k (C 1)) (.sub (.add (.mul (cst 2) (hb 37)) (k (K 1))) (.mul (cst 256) (k (K 2)))),
        .sub (k (C 2)) (.sub (.add (.mul (cst 2) (hb 38)) (k (K 2))) (.mul (cst 256) (k (K 3)))),
        .sub (k (C 3)) (.add (.mul (cst 2) (hb 39)) (k (K 3))),
        -- the highest height
        .sub (k PMX) (.add (.mul notFirst (kp MX)) (.mul first (.pub PUB_MAXH_IN))),
        .sub (k MX) (.add (k PMX) (.mul (k GT) (.sub height (k PMX)))),
        .mul (k GT) (om (k ON)),
        .mul (k ON) (.sub (b3 MD) (.add (.mul (k GT) (.sub (.sub height (k PMX)) one))
          (.mul (om (k GT)) (.sub (k PMX) height)))),
        .mul isLast (.sub (k MX) (.pub PUB_MAXH_OUT)),
        -- the key: one differing byte when comparing, equal before it, greater there
        .sub ((List.range 36).foldl (fun acc j => .add acc (k (DIFF j))) (cst 0)) cmp,
        .sub (k DELTA) (.sub ((List.range 36).foldl (fun acc j =>
          .add acc (.mul (k (DIFF j)) (.sub (k (keyCol j)) (k (PREV j))))) (cst 0)) cmp) ] : List Expr)) : c ∈ localC := by
  unfold localC
  iterate 5 apply List.mem_append_left
  exact List.mem_append_right _ h

section Rows2

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0)
include hsat

theorem on_bool {r : ℕ} (hr : r < n) : M ON r = 0 ∨ M ON r = 1 := bool_of hsat hr (memA (by simp))

/-- **On rows are a prefix** `[0, e)`, `0 < e < n`. -/
theorem on_prefix (hn : 0 < n) : ∃ e, OnPre n M e := by
  have h0 : M ON 0 = 1 := by
    have := lc hsat hn (c := .mul first (om (k ON))) (memE (by simp))
    simp only [Expr.eval, ev_first hn, if_true, om, one, eval_cst, ev_k hn, Nat.cast_one, one_mul] at this
    exact (sub_eq_zero.mp this).symm
  have hl : M ON (n - 1) = 0 := by
    have := lc hsat (show n - 1 < n by omega) (c := .mul isLast (k ON)) (memE (by simp))
    simp only [Expr.eval, ev_isLast (show n - 1 < n by omega), show ¬ (n - 1 + 1 < n) by omega, if_false, one_mul,
      ev_k (show n - 1 < n by omega)] at this
    exact this
  have hstep : ∀ r, r + 1 < n → M ON (r + 1) = 1 → M ON r = 1 := by
    intro r hr h1
    have := lc hsat hr (c := .mul notFirst (.mul (k ON) (om (kp ON)))) (memE (by simp))
    simp only [Expr.eval, ev_notFirst hr, show r + 1 ≠ 0 by omega, if_false, om, one, eval_cst, Nat.cast_one, one_mul,
      ev_k hr, ev_kp hr, h1] at this
    exact (sub_eq_zero.mp this).symm
  have ex : ∃ r, r < n ∧ M ON r = 0 := ⟨n - 1, by omega, hl⟩
  obtain ⟨heN, he0⟩ := Nat.find_spec ex
  have hmin : ∀ r < Nat.find ex, ¬ (r < n ∧ M ON r = 0) := fun r h => Nat.find_min ex h
  generalize Nat.find ex = e at heN he0 hmin
  have hepos : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; rw [h0] at he0; exact absurd he0 one_ne_zero
    · exact h
  refine ⟨e, ⟨hepos, heN, fun r hr => ?_⟩⟩
  split_ifs with hlt
  · rcases on_bool hsat hr with h | h
    · exact absurd ⟨hr, h⟩ (hmin r hlt)
    · exact h
  · rcases on_bool hsat hr with h | h
    · exact h
    · exfalso
      have : ∀ d, r - d < n → M ON (r - d) = 1 := by
        intro d
        induction d with
        | zero => intro _; simpa using h
        | succ d ih =>
          intro hd
          by_cases hdr : d < r
          · exact hstep (r - (d + 1)) (by omega) (by rw [show r - (d + 1) + 1 = r - d by omega]; exact ih (by omega))
          · rw [show r - (d + 1) = r - d by omega]; exact ih (by omega)
      have := this (r - e) (by omega)
      rw [show r - (r - e) = e by omega, he0] at this; exact zero_ne_one this

variable {e : ℕ} (E : OnPre n M e)
include E

omit hsat in
theorem on_of {r : ℕ} (hr : r < e) : M ON r = 1 := by rw [E.on r (by have := E.lt; omega), if_pos hr]
omit hsat in
theorem off_of {r : ℕ} (hr : r < n) (he : e ≤ r) : M ON r = 0 := by rw [E.on r hr, if_neg (by omega)]

theorem lst_val {r : ℕ} (hr : r < n) : M LST r = if r + 1 = e then 1 else 0 := by
  have := lc hsat hr (c := .sub (k LST) (.mul (k ON) (om (kn ON)))) (memE (by simp))
  simp only [Expr.eval, ev_k hr, om, one, eval_cst, Nat.cast_one, sub_eq_zero] at this
  rw [this]
  have := E.lt
  by_cases h1 : r + 1 < n
  · rw [ev_kn h1, E.on r hr, E.on (r + 1) h1]
    split_ifs <;> first | (exfalso; omega) | simp
  · rw [E.on r hr, if_neg (by omega), if_neg (by omega), zero_mul]

/-- **Rows**: row `r < e` has index `r`, and the record count is `i_out − i_in`. -/
theorem rows_sound : (∀ r < e, M IDX r = (r : F)) ∧ pub PUB_I_OUT - pub PUB_I_IN = (e : F) := by
  have hen := E.lt
  have hp := E.pos
  have hidx : ∀ r < e, M IDX r = (r : F) := by
    intro r
    induction r with
    | zero =>
      intro _
      have := lc hsat (show 0 < n by omega) (c := .mul first (k IDX)) (memE (by simp))
      simpa [Expr.eval, ev_first (show 0 < n by omega), ev_k (show 0 < n by omega)] using this
    | succ r ih =>
      intro hr
      have h1 : r + 1 < n := by omega
      have := lc hsat h1 (c := .mul notFirst (.mul (k ON) (.sub (.sub (k IDX) (kp IDX)) one))) (memE (by simp))
      simp only [Expr.eval, ev_notFirst h1, show r + 1 ≠ 0 by omega, if_false, one_mul, ev_k h1, ev_kp h1,
        on_of E hr, ev_one] at this
      rw [ih (by omega)] at this
      push_cast; linear_combination this
  refine ⟨hidx, ?_⟩
  have hl : e - 1 < n := by omega
  have := lc hsat hl (c := .mul (k LST) (.sub (.add (k IDX) one) (.sub (.pub PUB_I_OUT) (.pub PUB_I_IN)))) (memE (by simp))
  simp only [Expr.eval, ev_k hl, ev_one] at this
  rw [lst_val hsat E hl, if_pos (by omega), one_mul, hidx (e - 1) (by have := E.pos; omega)] at this
  rw [show ((e - 1 : ℕ) : F) = (e : F) - 1 by rw [Nat.cast_sub (by omega)]; simp] at this
  linear_combination -this

end Rows2

/-! ### Positions and fields -/

section Fields

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {S : ℕ → ℕ}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) {e : ℕ} (E : OnPre n M e) (H : Hyp n pub M S)
include hsat E H

omit hsat E H in
theorem ev_b3 {f : ℕ → ℕ} {r : ℕ} (hr : r < n) :
    (b3 f).eval n preCols pub M r = M (f 0) r + 256 * M (f 1) r + 65536 * M (f 2) r := by
  simp [b3, pair, Expr.eval, eval_cst, ev_k hr]

/-- A record's start, below `2^24`. -/
theorem start_lt {r : ℕ} (hr : r < e) : (M START r).val < 2 ^ 24 := by
  have hrn : r < n := by have := E.lt; omega
  have := lc hsat hrn (c := .mul (k ON) (.sub (k START) (b3 SB))) (memE (by simp))
  simp only [Expr.eval, ev_k hrn, ev_b3 hrn, on_of E hr, one_mul, sub_eq_zero] at this
  obtain ⟨a0, -, b0, -⟩ := H.r8 r hrn (on_of E hr) 0 (by norm_num)
  obtain ⟨a1, -, b1, -⟩ := H.r8 r hrn (on_of E hr) 1 (by norm_num)
  obtain ⟨a2, -, b2, -⟩ := H.r8 r hrn (on_of E hr) 2 (by norm_num)
  have e1 : M START r = (((M (SB 0) r).val + 256 * (M (SB 1) r).val + 65536 * (M (SB 2) r).val : ℕ) : F) := by
    rw [this]; push_cast; simp only [cast_val]
  rw [val_of_eq e1 (by have := P_big; omega)]; omega

/-- Head byte `j` of record `r` is `S (start + j)`, a position below the segment length. -/
theorem hb_val {r j : ℕ} (hr : r < e) (hj : j < 49) :
    (M (HB j) r).val = S ((M START r).val + j) ∧ (M START r).val + j < (pub PUB_LEN).val := by
  have hrn : r < n := by have := E.lt; omega
  obtain ⟨q, hq, hpos, hv⟩ := H.hb r hrn (on_of E hr) j hj
  have hs := start_lt hsat E H hr
  have : (M START r).val + j = q := by
    apply lift _ (by have := P_big; omega) (by have := ZMod.val_lt (pub PUB_LEN); unfold P at *; omega)
    push_cast; rw [cast_val]; exact hpos
  rw [hv, this]; exact ⟨rfl, hq⟩

/-- Amount byte `j` of record `r` is `S (start + 49 + j)`. -/
theorem ab_val {r j : ℕ} (hr : r < e) (hj : j < 8) :
    (M (AB j) r).val = S ((M START r).val + 49 + j) ∧ (M START r).val + 49 + j < (pub PUB_LEN).val := by
  have hrn : r < n := by have := E.lt; omega
  obtain ⟨q, hq, hpos, hv⟩ := H.ab r hrn (on_of E hr) j hj
  have hs := start_lt hsat E H hr
  have : (M START r).val + 49 + j = q := by
    apply lift _ (by have := P_big; omega) (by have := ZMod.val_lt (pub PUB_LEN); unfold P at *; omega)
    push_cast; rw [cast_val]; rw [← hpos]; push_cast; ring
  rw [hv, this]; exact ⟨rfl, hq⟩

/-- The record's fields: the length (three bytes, the fourth zero, at least 8), the coinbase flag,
height's top byte zero. -/
theorem fields {r : ℕ} (hr : r < e) :
    (M LENC r).val = S ((M START r).val + 45) + 256 * S ((M START r).val + 46) + 65536 * S ((M START r).val + 47) ∧
    S ((M START r).val + 48) = 0 ∧ 8 ≤ (M LENC r).val ∧ (M LENC r).val < 2 ^ 24 ∧
    S ((M START r).val + 40) ≤ 1 ∧ S ((M START r).val + 39) = 0 := by
  have hrn : r < n := by have := E.lt; omega
  have hon := on_of E hr
  have hS := H.byte
  have hbv := fun j (hj : j < 49) => (hb_val hsat E H hr hj).1
  have c1 := lc hsat hrn (c := .sub (k LENC) lenOf) (memE (by simp))
  have c2 := lc hsat hrn (c := .mul (k ON) (hb 48)) (memE (by simp))
  have c3 := lc hsat hrn (c := .mul (k ON) (.sub (.sub (k LENC) (cst 8)) (b3 D))) (memE (by simp))
  have c4 := lc hsat hrn (c := .mul (k ON) (boolC (hb 40))) (memE (by simp))
  have c5 := lc hsat hrn (c := .mul (k ON) (hb 39)) (memE (by simp))
  simp only [lenOf, Expr.eval, ev_k hrn, ev_hb hrn, ev_pair, ev_b3 hrn, eval_cst, hon, one_mul, sub_eq_zero, boolC,
    Nat.cast_ofNat, Nat.cast_one] at c1 c2 c3 c4 c5
  have v45 := hbv 45 (by norm_num); have v46 := hbv 46 (by norm_num); have v47 := hbv 47 (by norm_num)
  have v48 := hbv 48 (by norm_num); have v40 := hbv 40 (by norm_num); have v39 := hbv 39 (by norm_num)
  have b45 := hS ((M START r).val + 45); have b46 := hS ((M START r).val + 46); have b47 := hS ((M START r).val + 47)
  obtain ⟨L, hLd⟩ : ∃ L, L = S ((M START r).val + 45) + 256 * S ((M START r).val + 46) + 65536 * S ((M START r).val + 47) :=
    ⟨_, rfl⟩
  have hL : M LENC r = (L : F) := by
    rw [c1, ← cast_val (M (HB 45) r), ← cast_val (M (HB 46) r), ← cast_val (M (HB 47) r), v45, v46, v47, hLd]; push_cast; ring
  have hLv : (M LENC r).val = L := val_of_eq hL (by have := P_big; omega)
  obtain ⟨-, d0, -, -⟩ := H.r8 r hrn hon 0 (by norm_num)
  obtain ⟨-, d1, -, -⟩ := H.r8 r hrn hon 1 (by norm_num)
  obtain ⟨-, d2, -, -⟩ := H.r8 r hrn hon 2 (by norm_num)
  have h8 : L = (M (D 0) r).val + 256 * (M (D 1) r).val + 65536 * (M (D 2) r).val + 8 := by
    apply lift _ (by have := P_big; omega) (by have := P_big; omega)
    rw [← hL]; push_cast; simp only [cast_val]; linear_combination c3
  refine ⟨hLv.trans hLd, ?_, by omega, by omega, ?_, ?_⟩
  · rw [← v48, c2]; rfl
  · rw [← v40]
    rcases mul_eq_zero.mp c4 with h | h
    · rw [h]; simp
    · rw [sub_eq_zero.mp h, ZMod.val_one]
  · rw [← v39, c5]; rfl

/-- **The records are consecutive**: from 0, each after the previous one's `49 + len` bytes, the
last one ending at the segment length. -/
theorem chain :
    (M START 0).val = 0 ∧ (∀ r, r + 1 < e → (M START (r + 1)).val = (M START r).val + 49 + (M LENC r).val) ∧
    (M START (e - 1)).val + 49 + (M LENC (e - 1)).val = (pub PUB_LEN).val := by
  have hen := E.lt
  have hp := E.pos
  refine ⟨?_, fun r hr => ?_, ?_⟩
  · have := lc hsat (show 0 < n by omega) (c := .mul first (k START)) (memE (by simp))
    simp only [Expr.eval, ev_first (show 0 < n by omega), if_true, one_mul, ev_k (show 0 < n by omega)] at this
    rw [this]; rfl
  · have h1 : r + 1 < n := by omega
    have := lc hsat h1 (c := .mul notFirst (.mul (k ON) (.sub (k START) (.add (.add (kp START) (cst 49)) (kp LENC)))))
      (memE (by simp))
    simp only [Expr.eval, ev_notFirst h1, show r + 1 ≠ 0 by omega, if_false, one_mul, ev_k h1, ev_kp h1,
      on_of E hr, eval_cst, sub_eq_zero, Nat.cast_ofNat] at this
    have s0 := start_lt hsat E H (show r < e by omega)
    have l0 := (fields hsat E H (show r < e by omega)).2.2.2.1
    apply val_of_eq _ (by have := P_big; omega)
    rw [this]; push_cast; simp only [cast_val]
  · have hl : e - 1 < n := by omega
    have := lc hsat hl (c := .mul (k LST) (.sub (.add (.add (k START) (cst 49)) (k LENC)) (.pub PUB_LEN))) (memE (by simp))
    simp only [Expr.eval, ev_k hl, eval_cst, Nat.cast_ofNat] at this
    rw [lst_val hsat E hl, if_pos (by omega), one_mul, sub_eq_zero] at this
    have s0 := start_lt hsat E H (show e - 1 < e by omega)
    have l0 := (fields hsat E H (show e - 1 < e by omega)).2.2.2.1
    symm; apply val_of_eq _ (by have := P_big; omega)
    rw [← this]; push_cast; simp only [cast_val]

/-- Record `r` as read from the bytes. -/
def recR (M : ℕ → ℕ → F) (S : ℕ → ℕ) (r : ℕ) : Spec.CoinEpoch.CEv := recAt S (M START r).val (M LENC r).val

/-- The segment's records. -/
def recs (M : ℕ → ℕ → F) (S : ℕ → ℕ) (e : ℕ) : List Spec.CoinEpoch.CEv := (List.range e).map (recR M S)

theorem recR_enc {r : ℕ} (hr : r < e) : encRec (recR M S r) = bytesAt S (M START r).val (49 + (M LENC r).val) := by
  obtain ⟨hl, h48, -, -, hcb, -⟩ := fields hsat E H hr
  apply encRec_recAt hcb
  rw [le_bytesAt4 H.byte, hl, h48]; ring_nf

/-- **The records encode the segment's bytes.** -/
theorem parse_bytes : (recs M S e).flatMap encRec = (List.range (pub PUB_LEN).val).map fun q => UInt8.ofNat (S q) := by
  obtain ⟨c0, cs, cl⟩ := chain hsat E H
  have hp := E.pos
  have key : ∀ r < e, ((List.range (r + 1)).map (recR M S)).flatMap encRec =
      bytesAt S 0 ((M START r).val + 49 + (M LENC r).val) := by
    intro r
    induction r with
    | zero => intro hr; simp [recR_enc hsat E H hr, c0]
    | succ r ih =>
      intro hr
      rw [List.range_succ, List.map_append, List.flatMap_append, ih (by omega), List.map_singleton, List.flatMap_singleton,
        recR_enc hsat E H hr, cs r hr]
      generalize (M START r).val + 49 + (M LENC r).val = A
      generalize (M LENC (r + 1)).val = B
      rw [show A + 49 + B = A + (49 + B) by ring, bytesAt_add S 0 A (49 + B), zero_add]
  have := key (e - 1) (by omega)
  rw [show e - 1 + 1 = e by omega, cl] at this
  unfold recs; rw [this]; simp [bytesAt]

/-- **Every record is well formed**, with height below `2^24`. -/
theorem recR_ok {r : ℕ} (hr : r < e) : RecOk (recR M S r) ∧ Spec.SetFile.code (recR M S r) / 2 < 2 ^ 24 := by
  obtain ⟨-, -, h8, hlt, hcb, h39⟩ := fields hsat E H hr
  have hS := H.byte
  have hh : Spec.Block.le (bytesAt S ((M START r).val + 36) 4) < 2 ^ 24 := by
    rw [le_bytesAt4 hS]
    have := hS ((M START r).val + 36); have := hS ((M START r).val + 36 + 1); have := hS ((M START r).val + 36 + 2)
    rw [show (M START r).val + 36 + 3 = (M START r).val + 39 by ring, h39]; omega
  have l4 := fun a => Spec.Block.le_lt (bytesAt S a 4)
  simp only [bytesAt_length] at l4
  refine ⟨⟨by simp [recR, recAt, Spec.SetFile.txid, bytesAt_length], ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have := l4 ((M START r).val + 32); simp only [recR, recAt, Spec.SetFile.vout]; norm_num at this ⊢; omega
  · simp only [recR, recAt, Spec.SetFile.code]; omega
  · have := l4 ((M START r).val + 41); simp only [recR, recAt, Spec.SetFile.txi]; norm_num at this ⊢; omega
  · simp [recR, recAt, Spec.SetFile.ser, bytesAt_length, h8]
  · simp only [recR, recAt, Spec.SetFile.ser, bytesAt_length]; omega
  · simp only [recR, recAt, Spec.SetFile.code]; omega

/-- The record's code. -/
theorem code_eq {r : ℕ} (hr : r < e) : Spec.SetFile.code (recR M S r) =
    2 * (S ((M START r).val + 36) + 256 * S ((M START r).val + 37) + 65536 * S ((M START r).val + 38)) +
      S ((M START r).val + 40) := by
  obtain ⟨-, -, -, -, -, h39⟩ := fields hsat E H hr
  simp only [recR, recAt, Spec.SetFile.code, le_bytesAt4 H.byte]
  rw [show (M START r).val + 36 + 3 = (M START r).val + 39 by ring, h39,
    show (M START r).val + 36 + 1 = (M START r).val + 37 by ring, show (M START r).val + 36 + 2 = (M START r).val + 38 by ring]
  ring

/-- **The code bytes** are the code's little-endian bytes. -/
theorem code_bytes {r i : ℕ} (hr : r < e) (hi : i < 4) :
    (M (C i) r).val = Spec.SetFile.code (recR M S r) / 256 ^ i % 256 := by
  have hrn : r < n := by have := E.lt; omega
  have hon := on_of E hr
  have hbv := fun j (hj : j < 49) => (hb_val hsat E H hr hj).1
  obtain ⟨-, -, -, -, hcb, h39⟩ := fields hsat E H hr
  have bK := fun c (hc : c ∈ [K 1, K 2, K 3]) => bool_of hsat hrn (memB hc)
  have k1 := bK (K 1) (by simp); have k2 := bK (K 2) (by simp); have k3 := bK (K 3) (by simp)
  have c0 := lc hsat hrn (c := .sub (k (C 0)) (.sub (.add (.mul (cst 2) (hb 36)) (hb 40)) (.mul (cst 256) (k (K 1)))))
    (memE (by simp))
  have c1 := lc hsat hrn (c := .sub (k (C 1)) (.sub (.add (.mul (cst 2) (hb 37)) (k (K 1))) (.mul (cst 256) (k (K 2)))))
    (memE (by simp))
  have c2 := lc hsat hrn (c := .sub (k (C 2)) (.sub (.add (.mul (cst 2) (hb 38)) (k (K 2))) (.mul (cst 256) (k (K 3)))))
    (memE (by simp))
  have c3 := lc hsat hrn (c := .sub (k (C 3)) (.add (.mul (cst 2) (hb 39)) (k (K 3)))) (memE (by simp))
  simp only [Expr.eval, ev_k hrn, ev_hb hrn, eval_cst, sub_eq_zero, Nat.cast_ofNat] at c0 c1 c2 c3
  obtain ⟨a0, -, -, -⟩ := H.r8 r hrn hon 0 (by norm_num)
  obtain ⟨a1, -, -, -⟩ := H.r8 r hrn hon 1 (by norm_num)
  obtain ⟨a2, -, -, -⟩ := H.r8 r hrn hon 2 (by norm_num)
  have hS := H.byte
  set st := (M START r).val with hst
  have s36 := hS (st + 36); have s37 := hS (st + 37); have s38 := hS (st + 38)
  -- the carries as naturals
  have kv : ∀ x : F, x = 0 ∨ x = 1 → x = ((x.val : ℕ) : F) ∧ x.val ≤ 1 := by
    intro x hx; rcases hx with h | h <;> simp [h, ZMod.val_one]
  obtain ⟨ek1, lk1⟩ := kv _ k1; obtain ⟨ek2, lk2⟩ := kv _ k2; obtain ⟨ek3, lk3⟩ := kv _ k3
  have n0 : (M (C 0) r).val + 256 * (M (K 1) r).val = 2 * S (st + 36) + S (st + 40) := by
    apply lift _ (by have := P_big; omega) (by have := P_big; omega)
    push_cast; simp only [cast_val]; rw [← hbv 36 (by norm_num), ← hbv 40 (by norm_num)]; simp only [cast_val]
    linear_combination c0
  have n1 : (M (C 1) r).val + 256 * (M (K 2) r).val = 2 * S (st + 37) + (M (K 1) r).val := by
    apply lift _ (by have := P_big; omega) (by have := P_big; omega)
    push_cast; simp only [cast_val]; rw [← hbv 37 (by norm_num)]; simp only [cast_val]
    linear_combination c1
  have n2 : (M (C 2) r).val + 256 * (M (K 3) r).val = 2 * S (st + 38) + (M (K 2) r).val := by
    apply lift _ (by have := P_big; omega) (by have := P_big; omega)
    push_cast; simp only [cast_val]; rw [← hbv 38 (by norm_num)]; simp only [cast_val]
    linear_combination c2
  have n3 : (M (C 3) r).val = (M (K 3) r).val := by
    have : M (C 3) r = M (K 3) r := by rw [c3, ← cast_val (M (HB 39) r), hbv 39 (by norm_num), h39]; simp
    rw [this]
  rw [code_eq hsat E H hr, ← hst]
  have := H.byte (st + 40)
  interval_cases i <;> (try norm_num) <;> omega

end Fields

/-! ### Sums of expressions -/

theorem list_sum_range {β : Type} [AddCommMonoid β] (f : ℕ → β) : ∀ m, ((List.range m).map f).sum = ∑ i ∈ Finset.range m, f i
  | 0 => by simp
  | m + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range f m, Finset.sum_range_succ]; simp

theorem ev_foldl_add {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r : ℕ} (g : ℕ → Expr) :
    ∀ (l : List ℕ) (a : Expr), (l.foldl (fun acc j => Expr.add acc (g j)) a).eval n preCols pub M r =
      a.eval n preCols pub M r + (l.map fun j => (g j).eval n preCols pub M r).sum
  | [], a => by simp
  | j :: l, a => by rw [List.foldl_cons, ev_foldl_add g l, List.map_cons, List.sum_cons]; simp [Expr.eval, add_assoc]

theorem ev_foldl_sub {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {r : ℕ} (g : ℕ → Expr) :
    ∀ (l : List ℕ) (a : Expr), (l.foldl (fun acc j => Expr.sub acc (g j)) a).eval n preCols pub M r =
      a.eval n preCols pub M r - (l.map fun j => (g j).eval n preCols pub M r).sum
  | [], a => by simp
  | j :: l, a => by rw [List.foldl_cons, ev_foldl_sub g l, List.map_cons, List.sum_cons]; simp [Expr.eval]; ring

/-- One-hot from a sum of booleans. -/
theorem one_hot {v : ℕ → F} {m : ℕ} (hm : m < P) (hb : ∀ j < m, v j = 0 ∨ v j = 1) (hs : ∑ j ∈ Finset.range m, v j = 1) :
    ∃ d < m, v d = 1 ∧ ∀ j < m, j ≠ d → v j = 0 := by
  have hv : ∀ j < m, v j = (((v j).val : ℕ) : F) ∧ (v j).val ≤ 1 := by
    intro j hj; rcases hb j hj with h | h <;> simp [h, ZMod.val_one]
  have hsn : ∑ j ∈ Finset.range m, (v j).val = 1 := by
    have hle : ∑ j ∈ Finset.range m, (v j).val ≤ m := by
      calc ∑ j ∈ Finset.range m, (v j).val ≤ ∑ j ∈ Finset.range m, 1 :=
            Finset.sum_le_sum fun j hj => (hv j (Finset.mem_range.mp hj)).2
        _ = m := by simp
    apply lift _ (by omega) (by unfold P; norm_num)
    push_cast
    rw [← hs]; apply Finset.sum_congr rfl; intro j hj; exact (hv j (Finset.mem_range.mp hj)).1.symm
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ Finset.range m, (v d).val ≠ 0 := by
    by_contra hc; push Not at hc; rw [Finset.sum_eq_zero hc] at hsn; exact zero_ne_one hsn
  have hdm := Finset.mem_range.mp hd
  have hd1 : (v d).val = 1 := by have := (hv d hdm).2; omega
  refine ⟨d, hdm, by rw [(hv d hdm).1, hd1]; simp, fun j hj hne => ?_⟩
  have : (v j).val + (v d).val ≤ 1 := by
    have hpair : (v j).val + (v d).val = ∑ x ∈ {j, d}, (v x).val := (Finset.sum_pair (f := fun x => (v x).val) hne).symm
    rw [hpair, ← hsn]
    apply Finset.sum_le_sum_of_subset
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp <;> omega
  rw [(hv j hj).1, show (v j).val = 0 by omega]; simp

theorem isChain_range {α : Type} {R : α → α → Prop} (f : ℕ → α) :
    ∀ m, (∀ r, r + 1 < m → R (f r) (f (r + 1))) → ((List.range m).map f).IsChain R
  | 0, _ => by simp
  | m + 1, h => by
    rw [List.range_succ, List.map_append, List.isChain_append]
    refine ⟨isChain_range f m (fun r hr => h r (by omega)), List.isChain_singleton _, ?_⟩
    intro x hx y hy
    rw [List.getLast?_map, List.getLast?_range] at hx
    simp only [List.map_cons, List.map_nil, List.head?_cons, Option.mem_def, Option.some.injEq] at hy
    split_ifs at hx with h0
    · simp at hx
    · simp only [Option.map_some, Option.mem_def, Option.some.injEq] at hx
      subst hx hy
      have := h (m - 1) (by omega)
      rwa [show m - 1 + 1 = m by omega] at this

/-! ### The key order -/

section Order

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {S : ℕ → ℕ}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) {e : ℕ} (E : OnPre n M e) (H : Hyp n pub M S)
include hsat E H

/-- Key byte `j` of row `r` is the record's. -/
theorem key_val {r j : ℕ} (hr : r < e) (hj : j < 36) :
    (M (keyCol j) r).val = keyB (recR M S r) j ∧ (M (keyCol j) r).val < 256 := by
  have hS := H.byte
  have hbv := fun i (hi : i < 49) => (hb_val hsat E H hr hi).1
  set st := (M START r).val with hst
  by_cases h32 : j < 32
  · have e1 : (M (keyCol j) r).val = S (st + j) := by simp only [keyCol, if_pos h32]; exact hbv j (by omega)
    rw [e1]
    refine ⟨?_, hS _⟩
    simp only [keyB, if_pos h32, recR, recAt, Spec.SetFile.txid, ← hst]
    rw [getD_bytesAt hS h32]
  · have hv : Spec.SetFile.vout (recR M S r) = S (st + 32) + 256 * S (st + 33) + 65536 * S (st + 34) + 16777216 * S (st + 35) := by
      simp only [recR, recAt, Spec.SetFile.vout, le_bytesAt4 hS, ← hst]
    have v32 := hbv 32 (by norm_num); have v33 := hbv 33 (by norm_num); have v34 := hbv 34 (by norm_num)
    have v35 := hbv 35 (by norm_num)
    have b32 := hS (st + 32); have b33 := hS (st + 33); have b34 := hS (st + 34); have b35 := hS (st + 35)
    simp only [keyB, if_neg h32, hv]
    interval_cases j <;> simp only [keyCol] <;> norm_num [v32, v33, v34, v35] <;> omega

/-- The previous key at a comparing row: the previous record's, or the incoming one at row 0. -/
def prevKey (pub : ℕ → F) (M : ℕ → ℕ → F) (S : ℕ → ℕ) (r j : ℕ) : ℕ :=
  if r = 0 then (pub (PUB_LAST_IN j)).val else keyB (recR M S (r - 1)) j

/-- **A comparing row's key is above the previous key.** -/
theorem row_above {r : ℕ} (hr : r < e) (hc : r ≠ 0 ∨ pub PUB_HASLAST = 1) :
    KeyLex (prevKey pub M S r) (keyB (recR M S r)) := by
  have hrn : r < n := by have := E.lt; omega
  have hon := on_of E hr
  -- the comparison flag is 1
  have hcmp : cmp.eval n preCols pub M r = 1 := by
    simp only [cmp, Expr.eval, ev_k hrn, ev_first hrn, hon]
    rcases hc with h | h
    · simp [h]
    · by_cases h0 : r = 0 <;> simp [h0, h]
  -- the previous key
  have hprev : ∀ j < 36, (M (PREV j) r).val = prevKey pub M S r j ∧ (M (PREV j) r).val < 256 := by
    intro j hj
    have := lc hsat hrn (memPrev hj)
    simp only [Expr.eval, ev_k hrn, ev_notFirst hrn, ev_first hrn, sub_eq_zero] at this
    by_cases h0 : r = 0
    · subst h0; simp only [if_true, zero_mul, one_mul, zero_add] at this
      rw [this]; exact ⟨by simp [prevKey], H.lastIn j hj⟩
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp only [if_neg h0, one_mul, zero_mul, add_zero, ev_kp hrn] at this
      rw [this]; simp only [prevKey, if_neg h0, show r' + 1 - 1 = r' by omega]
      exact key_val hsat E H (by omega) hj
  -- one differing byte
  have hdb : ∀ j < 36, M (DIFF j) r = 0 ∨ M (DIFF j) r = 1 := fun j hj => bool_of hsat hrn (memD hj)
  have hsum := lc hsat hrn (c := .sub ((List.range 36).foldl (fun acc j => .add acc (k (DIFF j))) (cst 0)) cmp)
    (memE (by simp))
  simp only [Expr.eval, ev_foldl_add, eval_cst, Nat.cast_zero, zero_add, hcmp, sub_eq_zero, ev_k hrn,
    list_sum_range (fun j => M (DIFF j) r)] at hsum
  obtain ⟨d, hd, hd1, hd0⟩ := one_hot (by unfold P; norm_num) hdb hsum
  refine ⟨d, hd, fun i hi => ?_, ?_⟩
  · -- equal before `d`
    have := lc hsat hrn (memBefore (show i < 36 by omega))
    simp only [Expr.eval, beforeE, ev_foldl_sub, ev_k hrn, hcmp, list_sum_range (fun j => M (DIFF j) r)] at this
    rw [Finset.sum_eq_zero (fun x hx => hd0 x (by simp at hx; omega) (by simp at hx; omega)),
      hd0 i (by omega) (by omega)] at this
    simp only [sub_zero, one_mul, sub_eq_zero] at this
    rw [← (hprev i (by omega)).1, ← (key_val hsat E H hr (show i < 36 by omega)).1, this]
  · -- greater at `d`
    have := lc hsat hrn (c := .sub (k DELTA) (.sub ((List.range 36).foldl (fun acc j =>
      .add acc (.mul (k (DIFF j)) (.sub (k (keyCol j)) (k (PREV j))))) (cst 0)) cmp)) (memE (by simp))
    simp only [Expr.eval, ev_foldl_add, eval_cst, Nat.cast_zero, zero_add, hcmp, sub_eq_zero, ev_k hrn,
      list_sum_range (fun j => M (DIFF j) r * (M (keyCol j) r - M (PREV j) r))] at this
    rw [Finset.sum_eq_single d (fun x hx hne => by rw [hd0 x (by simpa using hx) hne, zero_mul])
      (fun h => absurd (Finset.mem_range.mpr hd) h), hd1, one_mul] at this
    have hdl := H.delta r hrn hon hc
    obtain ⟨kv, kl⟩ := key_val hsat E H hr hd
    obtain ⟨pv, pl⟩ := hprev d hd
    have : (M (keyCol d) r).val = (M (PREV d) r).val + 1 + (M DELTA r).val := by
      apply lift _ (by have := P_big; omega) (by have := P_big; omega)
      push_cast; simp only [cast_val]; rw [this]; ring
    rw [← kv, ← pv]; omega

/-- **Order**: the records are strictly sorted, the first is above the incoming key when there is
one, and the last's key is the outgoing key. -/
theorem order_sound :
    Sorted (recs M S e) ∧
    (pub PUB_HASLAST = 1 → KeyLex (fun j => (pub (PUB_LAST_IN j)).val) (keyB (recR M S 0))) ∧
    (∀ j < 36, (pub (PUB_LAST_OUT j)).val = keyB (recR M S (e - 1)) j) := by
  have hp := E.pos
  have hen := E.lt
  refine ⟨?_, fun h1 => ?_, fun j hj => ?_⟩
  · apply isChain_range
    intro r hr
    have ok := fun q (hq : q < e) => (recR_ok hsat E H hq).1
    obtain ⟨t1, v1, -⟩ := ok r (by omega)
    obtain ⟨t2, v2, -⟩ := ok (r + 1) hr
    apply keyLt_of_lex t1 t2 v1 v2
    have := row_above hsat E H hr (Or.inl (by omega))
    unfold KeyLex at this ⊢
    simpa [prevKey] using this
  · have := row_above hsat E H hp (Or.inr h1)
    unfold KeyLex at this ⊢
    simpa [prevKey] using this
  · have hl : e - 1 < n := by omega
    have := lc hsat hl (memLastOut hj)
    simp only [Expr.eval, ev_k hl] at this
    rw [lst_val hsat E hl, if_pos (by omega), one_mul, sub_eq_zero] at this
    rw [← this]; exact (key_val hsat E H (by omega) hj).1

end Order

/-! ### The amount -/

/-- The amount bytes of row `r`, as a number. -/
def amtV (M : ℕ → ℕ → F) (r : ℕ) : ℕ := ∑ j ∈ Finset.range 12, (M (AM j) r).val * 256 ^ j
/-- A 12-byte public amount. -/
def pubAmt (pub : ℕ → F) (base : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range 12, (pub (base j)).val * 256 ^ j
/-- The amount bytes read on row `r`. -/
def abV (M : ℕ → ℕ → F) (r : ℕ) : ℕ := ∑ j ∈ Finset.range 8, (M (AB j) r).val * 256 ^ j

section Totals

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {S : ℕ → ℕ}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) {e : ℕ} (E : OnPre n M e) (H : Hyp n pub M S)
include hsat E H

theorem amt_byte {r j : ℕ} (hr : r < n) (hj : j < 12) :
    (M (AM j) r).val + 256 * (if j = 11 then 0 else (M (AC (j + 1)) r).val) =
      (if r = 0 then (pub (PUB_AMT_IN j)).val else (M (AM j) (r - 1)).val) +
      (if j < 8 ∧ r < e then (M (AB j) r).val else 0) + (if j = 0 then 0 else (M (AC j) r).val) := by
  have c := lc hsat hr (memAmt hj)
  have c' : (k (AM j)).eval n preCols pub M r -
      (((Expr.add (.mul notFirst (kp (AM j))) (.mul first (.pub (PUB_AMT_IN j)))).eval n preCols pub M r +
        (if j < 8 then Expr.mul (k ON) (k (AB j)) else cst 0).eval n preCols pub M r +
        (if j = 0 then cst 0 else k (AC j)).eval n preCols pub M r) -
        (if j = 11 then cst 0 else Expr.mul (cst 256) (k (AC (j + 1)))).eval n preCols pub M r) = 0 := c
  have hprev : (Expr.add (.mul notFirst (kp (AM j))) (.mul first (.pub (PUB_AMT_IN j)))).eval n preCols pub M r =
      (((if r = 0 then (pub (PUB_AMT_IN j)).val else (M (AM j) (r - 1)).val) : ℕ) : F) := by
    by_cases h0 : r = 0
    · subst h0; simp [Expr.eval, ev_notFirst hr, ev_first hr, cast_val]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp [Expr.eval, ev_notFirst hr, ev_first hr, ev_kp hr, cast_val]
  have hpl : (if r = 0 then (pub (PUB_AMT_IN j)).val else (M (AM j) (r - 1)).val) < 256 := by
    split_ifs with h0
    · exact H.amtIn j hj
    · exact H.am (r - 1) (by omega) j hj
  have hadd : (if j < 8 then Expr.mul (k ON) (k (AB j)) else cst 0).eval n preCols pub M r =
      (((if j < 8 ∧ r < e then (M (AB j) r).val else 0) : ℕ) : F) := by
    by_cases h8 : j < 8
    · rw [if_pos h8]; simp only [Expr.eval, ev_k hr, E.on r hr]
      by_cases he : r < e
      · simp [he, h8, cast_val]
      · simp [he]
    · simp [h8, eval_cst]
  have hal : (if j < 8 ∧ r < e then (M (AB j) r).val else 0) < 256 := by
    split_ifs with h
    · rw [(ab_val hsat E H h.2 h.1).1]; exact H.byte _
    · norm_num
  have bAC : ∀ i, 1 ≤ i → i < 12 → M (AC i) r = 0 ∨ M (AC i) r = 1 := fun i h1 h2 => by
    have := bool_of hsat hr (memC (j := i - 1) (by omega)); rwa [show i - 1 + 1 = i by omega] at this
  have hcin : (if j = 0 then cst 0 else k (AC j)).eval n preCols pub M r =
      (((if j = 0 then 0 else (M (AC j) r).val) : ℕ) : F) := by
    split_ifs <;> simp [eval_cst, ev_k hr, cast_val]
  have hcl : (if j = 0 then 0 else (M (AC j) r).val) ≤ 1 := by
    split_ifs with h
    · norm_num
    · rcases bAC j (by omega) hj with g | g <;> simp [g, ZMod.val_one]
  have hcout : (if j = 11 then cst 0 else Expr.mul (cst 256) (k (AC (j + 1)))).eval n preCols pub M r =
      ((256 * (if j = 11 then 0 else (M (AC (j + 1)) r).val) : ℕ) : F) := by
    split_ifs <;> simp [eval_cst, Expr.eval, ev_k hr, cast_val]
  have hol : (if j = 11 then 0 else (M (AC (j + 1)) r).val) ≤ 1 := by
    split_ifs with h
    · norm_num
    · rcases bAC (j + 1) (by omega) (by omega) with g | g <;> simp [g, ZMod.val_one]
  rw [ev_k hr, hprev, hadd, hcin, hcout] at c'
  have hA := H.am r hr j hj
  apply lift _ (by have := P_big; omega) (by have := P_big; omega)
  push_cast; rw [cast_val]; push_cast at c'; linear_combination c'

/-- **A row's amount** is the previous one's plus the record's amount bytes. -/
theorem amt_row {r : ℕ} (hr : r < n) :
    amtV M r = (if r = 0 then pubAmt pub PUB_AMT_IN else amtV M (r - 1)) + (if r < e then abV M r else 0) := by
  have q := fun j (hj : j < 12) => amt_byte hsat E H hr (j := j) hj
  have q0 := q 0 (by norm_num); have q1 := q 1 (by norm_num); have q2 := q 2 (by norm_num)
  have q3 := q 3 (by norm_num); have q4 := q 4 (by norm_num); have q5 := q 5 (by norm_num)
  have q6 := q 6 (by norm_num); have q7 := q 7 (by norm_num); have q8 := q 8 (by norm_num)
  have q9 := q 9 (by norm_num); have q10 := q 10 (by norm_num); have q11 := q 11 (by norm_num)
  norm_num at q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11
  simp only [amtV, pubAmt, abV, Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  by_cases h0 : r = 0
  · subst h0
    by_cases he : 0 < e <;> simp only [he, ↓reduceIte] at q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 ⊢ <;> omega
  · by_cases he : r < e <;> simp only [h0, he, ↓reduceIte] at q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 ⊢ <;> omega

theorem amt_acc : ∀ r < n, amtV M r = pubAmt pub PUB_AMT_IN + ∑ q ∈ Finset.range (r + 1), (if q < e then abV M q else 0) := by
  intro r
  induction r with
  | zero => intro hr; rw [amt_row hsat E H hr]; simp
  | succ r ih =>
    intro hr
    rw [amt_row hsat E H hr, if_neg (by omega), show r + 1 - 1 = r by omega, ih (by omega), Finset.sum_range_succ _ (r + 1)]
    ring

theorem take8_ser {r : ℕ} (hr : r < e) :
    Spec.SetFile.amountOf (recR M S r) = abV M r := by
  obtain ⟨-, -, h8, -, -, -⟩ := fields hsat E H hr
  have hs : (Spec.SetFile.ser (recR M S r)).take 8 = bytesAt S ((M START r).val + 49) 8 := by
    simp only [recR, recAt, Spec.SetFile.ser]
    rw [show (M LENC r).val = 8 + ((M LENC r).val - 8) by omega, bytesAt_add]
    exact List.take_left' (bytesAt_length _ _ _)
  rw [Spec.SetFile.amountOf, hs, le_bytesAt H.byte, abV]
  apply Finset.sum_congr rfl
  intro j hj
  rw [(ab_val hsat E H hr (Finset.mem_range.mp hj)).1]

/-- **The amount**: the outgoing amount is the incoming one plus the records' amounts. -/
theorem amount_sound :
    pubAmt pub PUB_AMT_OUT = pubAmt pub PUB_AMT_IN + ((recs M S e).map Spec.SetFile.amountOf).sum ∧
    ∀ j < 12, (pub (PUB_AMT_OUT j)).val < 256 := by
  have hen := E.lt
  have hl : n - 1 < n := by omega
  have hout : ∀ j < 12, pub (PUB_AMT_OUT j) = M (AM j) (n - 1) := by
    intro j hj
    have := lc hsat hl (memAmtOut hj)
    simp only [Expr.eval, ev_isLast hl, show ¬ (n - 1 + 1 < n) by omega, if_false, one_mul, ev_k hl, sub_eq_zero] at this
    exact this.symm
  refine ⟨?_, fun j hj => by rw [hout j hj]; exact H.am _ hl j hj⟩
  have e1 : pubAmt pub PUB_AMT_OUT = amtV M (n - 1) := by
    unfold pubAmt amtV; apply Finset.sum_congr rfl; intro j hj; rw [hout j (Finset.mem_range.mp hj)]
  rw [e1, amt_acc hsat E H (n - 1) hl, show n - 1 + 1 = n by omega, ← Finset.sum_range_add_sum_Ico _ (le_of_lt hen)]
  rw [Finset.sum_eq_zero (s := Finset.Ico e n) (fun q hq => by rw [if_neg (by simp at hq; omega)]), add_zero]
  unfold recs
  rw [List.map_map, list_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  rw [if_pos (Finset.mem_range.mp hq), Function.comp_apply, take8_ser hsat E H (Finset.mem_range.mp hq)]

/-! ### The highest height -/

/-- Row `r`'s height. -/
def htV (M : ℕ → ℕ → F) (r : ℕ) : ℕ := (M (HB 36) r).val + 256 * (M (HB 37) r).val + 65536 * (M (HB 38) r).val

theorem ht_code {r : ℕ} (hr : r < e) : Spec.SetFile.code (recR M S r) / 2 = htV M r ∧ htV M r < 2 ^ 24 := by
  obtain ⟨-, -, -, -, hcb, -⟩ := fields hsat E H hr
  have hbv := fun j (hj : j < 49) => (hb_val hsat E H hr hj).1
  rw [code_eq hsat E H hr, htV, hbv 36 (by norm_num), hbv 37 (by norm_num), hbv 38 (by norm_num)]
  have := H.byte ((M START r).val + 36); have := H.byte ((M START r).val + 37); have := H.byte ((M START r).val + 38)
  constructor <;> omega

theorem max_row {r : ℕ} (hr : r < n) (hp : (if r = 0 then (pub PUB_MAXH_IN).val else (M MX (r - 1)).val) < 2 ^ 24) :
    (M MX r).val = max (if r = 0 then (pub PUB_MAXH_IN).val else (M MX (r - 1)).val) (if r < e then htV M r else 0) := by
  set pv := (if r = 0 then (pub PUB_MAXH_IN).val else (M MX (r - 1)).val) with hpv
  have c1 := lc hsat hr (c := .sub (k PMX) (.add (.mul notFirst (kp MX)) (.mul first (.pub PUB_MAXH_IN)))) (memE (by simp))
  have hP : M PMX r = (pv : F) := by
    simp only [Expr.eval, ev_k hr, ev_notFirst hr, ev_first hr, sub_eq_zero] at c1
    rw [c1, hpv]
    by_cases h0 : r = 0
    · subst h0; simp [cast_val]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      simp [ev_kp hr, cast_val]
  have c2 := lc hsat hr (c := .sub (k MX) (.add (k PMX) (.mul (k GT) (.sub height (k PMX))))) (memE (by simp))
  have c3 := lc hsat hr (c := .mul (k GT) (om (k ON))) (memE (by simp))
  have c4 := lc hsat hr (c := .mul (k ON) (.sub (b3 MD) (.add (.mul (k GT) (.sub (.sub height (k PMX)) one))
      (.mul (om (k GT)) (.sub (k PMX) height))))) (memE (by simp))
  have hg := bool_of hsat hr (memA (c := GT) (by simp))
  simp only [height, Expr.eval, ev_k hr, ev_hb hr, ev_pair, ev_b3 hr, eval_cst, om, one, Nat.cast_ofNat, Nat.cast_one,
    sub_eq_zero, hP] at c2 c3 c4
  have hg01 : M GT r = 0 ∨ M GT r = 1 := hg
  by_cases he : r < e
  · have hon := on_of E he
    have hbv := fun j (hj : j < 49) => (hb_val hsat E H he hj).1
    have hht : M (HB 36) r + 256 * M (HB 37) r + 65536 * M (HB 38) r = ((htV M r : ℕ) : F) := by
      simp only [htV]; push_cast; simp only [cast_val]
    obtain ⟨-, hlt⟩ := ht_code hsat E H he
    rw [hht] at c2 c4
    rw [hon, one_mul] at c4
    obtain ⟨-, -, -, m0⟩ := H.r8 r hr hon 0 (by norm_num)
    obtain ⟨-, -, -, m1⟩ := H.r8 r hr hon 1 (by norm_num)
    obtain ⟨-, -, -, m2⟩ := H.r8 r hr hon 2 (by norm_num)
    have hmd : M (MD 0) r + 256 * M (MD 1) r + 65536 * M (MD 2) r =
        (((M (MD 0) r).val + 256 * (M (MD 1) r).val + 65536 * (M (MD 2) r).val : ℕ) : F) := by
      push_cast; simp only [cast_val]
    rw [hmd] at c4
    rw [if_pos he]
    rcases hg01 with g | g
    · rw [g] at c2 c4
      simp only [zero_mul, add_zero, sub_zero, one_mul, zero_add] at c2 c4
      have : pv = htV M r + ((M (MD 0) r).val + 256 * (M (MD 1) r).val + 65536 * (M (MD 2) r).val) := by
        apply lift _ (by have := P_big; omega) (by have := P_big; omega)
        push_cast at c4 ⊢; linear_combination -c4
      rw [c2, ZMod.val_natCast_of_lt (by have := P_big; omega)]; omega
    · rw [g] at c2 c4
      simp only [one_mul, sub_self, zero_mul, add_zero] at c2 c4
      have : htV M r = pv + 1 + ((M (MD 0) r).val + 256 * (M (MD 1) r).val + 65536 * (M (MD 2) r).val) := by
        apply lift _ (by have := P_big; omega) (by have := P_big; omega)
        push_cast at c4 ⊢; linear_combination -c4
      rw [c2, show (pv : F) + (((htV M r : ℕ) : F) - pv) = ((htV M r : ℕ) : F) by ring,
        ZMod.val_natCast_of_lt (by have := P_big; omega)]; omega
  · have hoff := off_of E hr (by omega)
    rw [hoff, sub_zero, mul_one] at c3
    rw [c3] at c2
    simp only [zero_mul, add_zero] at c2
    rw [if_neg he, c2, ZMod.val_natCast_of_lt (by have := P_big; omega)]; simp

theorem max_acc : ∀ r < n, (M MX r).val =
    ((List.range (min (r + 1) e)).map (htV M)).foldl max (pub PUB_MAXH_IN).val ∧ (M MX r).val < 2 ^ 24 := by
  have hlt : ∀ m, m ≤ e → ((List.range m).map (htV M)).foldl max (pub PUB_MAXH_IN).val < 2 ^ 24 := by
    intro m
    induction m with
    | zero => intro _; simpa using H.maxIn
    | succ m ih =>
      intro hm
      rw [List.range_succ, List.map_append, List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
      have := (ht_code hsat E H (show m < e by omega)).2
      have := ih (by omega); omega
  intro r
  induction r with
  | zero =>
    intro hr
    have := max_row hsat E H hr (by simpa using H.maxIn)
    simp only [if_true] at this
    have hp := E.pos
    rw [show min (0 + 1) e = 1 by omega]
    have h0 := (ht_code hsat E H hp).2
    simp only [List.range_one, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
    rw [this, if_pos hp]
    exact ⟨rfl, by have := H.maxIn; omega⟩
  | succ r ih =>
    intro hr
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have := max_row hsat E H hr (by simpa using ih2)
    simp only [show r + 1 ≠ 0 by omega, if_false, show r + 1 - 1 = r by omega] at this
    rw [this, ih1]
    by_cases he : r + 1 < e
    · rw [if_pos he, show min (r + 1 + 1) e = min (r + 1) e + 1 by omega, List.range_succ, List.map_append,
        List.foldl_append]
      simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil, show min (r + 1) e = r + 1 by omega]
      refine ⟨by simp, ?_⟩
      have := (ht_code hsat E H he).2
      have := hlt (r + 1) (by omega); omega
    · rw [if_neg he, show min (r + 1 + 1) e = min (r + 1) e by omega, Nat.max_zero]
      exact ⟨rfl, hlt _ (by omega)⟩

/-- **The highest height**: the outgoing one is the maximum of the incoming one and the records'
heights (`code / 2`), below `2^24`. -/
theorem height_sound :
    (pub PUB_MAXH_OUT).val = ((recs M S e).map fun x => Spec.SetFile.code x / 2).foldl max (pub PUB_MAXH_IN).val ∧
    (pub PUB_MAXH_OUT).val < 2 ^ 24 := by
  have hen := E.lt
  have hl : n - 1 < n := by omega
  have := lc hsat hl (c := .mul isLast (.sub (k MX) (.pub PUB_MAXH_OUT))) (memE (by simp))
  simp only [Expr.eval, ev_isLast hl, show ¬ (n - 1 + 1 < n) by omega, if_false, one_mul, ev_k hl, sub_eq_zero] at this
  obtain ⟨h1, h2⟩ := max_acc hsat E H (n - 1) hl
  rw [← this, h1, show min (n - 1 + 1) e = e by omega]
  refine ⟨?_, by rw [h1, show min (n - 1 + 1) e = e by omega] at h2; exact h2⟩
  unfold recs
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro q hq
  exact ((ht_code hsat E H (List.mem_range.mp hq)).1).symm

end Totals

/-! ### The running sum -/

open StarkedAir.Block.ExtSum (QE)
open StarkedAir.Block.ExtSum.QE

/-- A record's fraction: `1/(z − φ)` of its coin tuple (`tupleOf`, with `txi` as the last term), with
the public `z`, weights and `γ`. -/
noncomputable def frac (pub : ℕ → F) (x : Spec.CoinEpoch.CEv) : QM :=
  (Block.RunSum.pQ pub PUB_Z - Block.phiOf pub (Block.tupleOf (Block.FpWalk.gQ pub) (Spec.SetFile.txid x)
    (Spec.SetFile.vout x) (Spec.SetFile.code x) (Spec.SetFile.ser x) (Spec.SetFile.txi x)))⁻¹

section Sum

variable {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {S : ℕ → ℕ}
  (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) {e : ℕ} (E : OnPre n M e) (H : Hyp n pub M S)
include hsat E H

omit hsat E H in
theorem ev_colQ' {c r : ℕ} (hr : r < n) : toQ ((colQ c).ev n preCols pub M r) = Block.RunSum.cQ M c r := by
  simp [Block.RunSum.cQ, ev, colQ, eval_col, wrap_zero hr]

omit hsat E H in
theorem ev_pubQ' {i r : ℕ} : toQ ((pubQ i).ev n preCols pub M r) = Block.RunSum.pQ pub i := by
  simp [Block.RunSum.pQ, ev, pubQ, Expr.eval]

omit E H in
theorem frac_row {r : ℕ} (hr : r < n) :
    (Block.RunSum.pQ pub PUB_Z - toQ (phi.ev n preCols pub M r)) * Block.RunSum.cQ M FC r = emb (M ON r) := by
  have h := toQ_zero_of (n := n) (pre := preCols) (pub := pub) (M := M) (r := r)
    (x := (((pubQ PUB_Z).sub phi).mul (colQ FC)).sub (base (k ON)))
    (fun c hc => hsat r hr c (by simp [constraints, fracC, hc]))
  rw [ev_sub, toQ_sub, ev_mul, toQ_mul, ev_sub, toQ_sub, ev_colQ' hr, toQ_ev_base, ev_pubQ', ev_k hr] at h
  exact sub_eq_zero.mp h

omit E H in
theorem zero_row {r : ℕ} (hr : r < n) (hm : M ON r = 0) : Block.RunSum.cQ M FC r = 0 := by
  have h : ∀ j < 4, M (FC + j) r = 0 := by
    intro j hj
    have hz : Expr.mul (om (k ON)) (col (FC + j)) ∈ zeroC := by
      simp only [zeroC, colQ, coords, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
      interval_cases j <;> simp
    have := hsat r hr (.mul (om (k ON)) (col (FC + j)))
      (by simp only [constraints, List.mem_append]; left; left; right; exact hz)
    simpa [Expr.eval, eval_col, eval_cst, wrap_zero hr, om, one, k, hm] using this
  have h0 := h 0 (by norm_num); have h1 := h 1 (by norm_num); have h2 := h 2 (by norm_num); have h3 := h 3 (by norm_num)
  simp only [Nat.add_zero] at h0
  simp [Block.RunSum.cQ, toQ, h0, h1, h2, h3]

omit E H in
theorem acc_row {r : ℕ} (hr : r < n) : Block.RunSum.cQ M ACC r =
    (if r = 0 then Block.RunSum.pQ pub PUB_SUM_IN else Block.RunSum.cQ M ACC (r - 1)) + Block.RunSum.cQ M FC r := by
  have h := toQ_zero_of (n := n) (pre := preCols) (pub := pub) (M := M) (r := r)
    (x := (colQ ACC).sub ((((base notFirst).mul (colQ ACC (-1))).add ((base first).mul (pubQ PUB_SUM_IN))).add (colQ FC)))
    (fun c hc => hsat r hr c (by simp [constraints, accC, hc]))
  rw [ev_sub, toQ_sub, ev_add, toQ_add, ev_add, toQ_add, ev_mul, toQ_mul, ev_mul, toQ_mul, toQ_ev_base, toQ_ev_base,
    ev_colQ' hr, ev_colQ' hr, ev_pubQ', ev_notFirst hr, ev_first hr] at h
  by_cases h0 : r = 0
  · simp only [h0, if_true] at h ⊢
    simp only [StarkedAir.Spec.QM31.emb_zero, StarkedAir.Spec.QM31.emb_one, zero_mul, one_mul, zero_add] at h
    linear_combination h
  · simp only [h0, if_false] at h ⊢
    have hp : toQ ((colQ ACC (-1)).ev n preCols pub M r) = Block.RunSum.cQ M ACC (r - 1) := by
      have hw : wrap n r (-1) = r - 1 := by
        rw [show (-1 : ℤ) = -((1 : ℕ) : ℤ) by simp, wrap_back (by omega) (by omega)]
      simp [Block.RunSum.cQ, ev, colQ, eval_col, hw]
    rw [hp] at h
    simp only [StarkedAir.Spec.QM31.emb_zero, StarkedAir.Spec.QM31.emb_one, zero_mul, one_mul, add_zero] at h
    linear_combination h

omit E H in
theorem acc_sum : ∀ r < n, Block.RunSum.cQ M ACC r =
    Block.RunSum.pQ pub PUB_SUM_IN + ∑ q ∈ Finset.range (r + 1), Block.RunSum.cQ M FC q := by
  intro r
  induction r with
  | zero => intro hr; rw [acc_row hsat hr, if_pos rfl]; simp
  | succ r ih =>
    intro hr
    rw [acc_row hsat hr, if_neg (by omega), show r + 1 - 1 = r by omega, ih (by omega), Finset.sum_range_succ _ (r + 1)]
    ring

omit hsat E H in
/-- The fingerprint `φ = Σⱼ αⱼ tⱼ` of a row, as `phiOf` of the row's tuple values. -/
theorem ev_phi (r : ℕ) : toQ (phi.ev n preCols pub M r) = Block.phiOf pub (tuple.map (Expr.eval n preCols pub M r)) := by
  have gen : ∀ (l : List ℕ) (a : QE), toQ ((l.foldl (fun acc j => acc.add ((pubQ (PUB_ALPHA j)).mul
      (base (tuple.getD j (cst 0))))) a).ev n preCols pub M r) = toQ (a.ev n preCols pub M r) +
        (l.map fun j => Block.RunSum.pQ pub (PUB_ALPHA j) * emb ((tuple.getD j (cst 0)).eval n preCols pub M r)).sum := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons j l ih =>
      intro a
      rw [List.foldl_cons, ih, ev_add, toQ_add, ev_mul, toQ_mul, toQ_ev_base, ev_pubQ', List.map_cons, List.sum_cons,
        add_assoc]
  show toQ (((List.range Block.Coin.W).foldl _ (base (cst 0))).ev n preCols pub M r) = _
  rw [gen, toQ_ev_base]
  simp only [eval_cst, Nat.cast_zero, StarkedAir.Spec.QM31.emb_zero, zero_add, Block.phiOf]
  congr 1

/-- **The row's tuple is the record's coin tuple.** -/
theorem tuple_eq {r : ℕ} (hr : r < e) :
    tuple.map (Expr.eval n preCols pub M r) = Block.tupleOf (Block.FpWalk.gQ pub) (Spec.SetFile.txid (recR M S r))
      (Spec.SetFile.vout (recR M S r)) (Spec.SetFile.code (recR M S r)) (Spec.SetFile.ser (recR M S r))
      (Spec.SetFile.txi (recR M S r)) := by
  have hrn : r < n := by have := E.lt; omega
  have hS := H.byte
  set st := (M START r).val with hst
  have hbF : ∀ j < 49, M (HB j) r = ((S (st + j) : ℕ) : F) := fun j hj => by
    rw [← cast_val (M (HB j) r), (hb_val hsat E H hr hj).1]
  -- the fingerprint
  obtain ⟨u0, hu0P, hu0, hfp⟩ := H.fp r hrn (on_of E hr)
  have hs0 := start_lt hsat E H hr
  have hu : u0 = st + 49 := by
    apply lift _ hu0P (by have := P_big; omega)
    rw [← hu0]; push_cast; rw [cast_val]
  have hser : (Spec.SetFile.ser (recR M S r)).map (fun b => emb ((b.toNat : ℕ) : F)) =
      (List.range (M LENC r).val).map fun i => emb ((S (u0 + i) : ℕ) : F) := by
    simp only [recR, recAt, Spec.SetFile.ser, bytesAt, List.map_map, hu, ← hst]
    apply List.map_congr_left; intro i _
    simp [toNat_ofNat_lt (hS _)]
  have hh : coordsOf (Block.FpWalk.horner (Block.FpWalk.gQ pub)
      ((Spec.SetFile.ser (recR M S r)).map fun b => emb ((b.toNat : ℕ) : F))) =
      ⟨M FH r, M (FH + 1) r, M (FH + 2) r, M (FH + 3) r⟩ := by
    rw [hser, ← hfp, coordsOf_toQ]
  -- the code
  have cb := fun i (hi : i < 4) => code_bytes hsat E H hr hi
  have hcode := (recR_ok hsat E H hr).1.2.2.1
  have hv : Spec.SetFile.vout (recR M S r) = S (st + 32) + 256 * S (st + 33) + 65536 * S (st + 34) + 16777216 * S (st + 35) := by
    simp only [recR, recAt, Spec.SetFile.vout, le_bytesAt4 hS, ← hst]
  have hti : Spec.SetFile.txi (recR M S r) = S (st + 41) + 256 * S (st + 42) + 65536 * S (st + 43) + 16777216 * S (st + 44) := by
    simp only [recR, recAt, Spec.SetFile.txi, le_bytesAt4 hS, ← hst]
  have b32 := hS (st + 32); have b33 := hS (st + 33); have b34 := hS (st + 34); have b35 := hS (st + 35)
  have c0 := cb 0 (by norm_num); have c1 := cb 1 (by norm_num); have c2 := cb 2 (by norm_num); have c3 := cb 3 (by norm_num)
  have hC : ∀ i < 4, M (C i) r = (((M (C i) r).val : ℕ) : F) := fun i _ => (cast_val _).symm
  simp only [Block.tupleOf, hh, tuple, List.map_append, List.map_cons, List.map_nil]
  congr 1
  · -- txid limbs
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi16 := List.mem_range.mp hi
    simp only [Function.comp, txidLimb, Block.txidLimb, recR, recAt, Spec.SetFile.txid]
    split_ifs
    · rw [ev_pair, ev_hb hrn, ev_hb hrn, hbF _ (by omega), hbF _ (by omega), getD_bytesAt hS (by omega),
        getD_bytesAt hS (by omega)]; push_cast; ring
    · rw [ev_pair, ev_hb hrn, ev_hb hrn, hbF _ (by omega), hbF _ (by omega), getD_bytesAt hS (by omega),
        getD_bytesAt hS (by omega)]; push_cast; ring
  · simp only [List.cons.injEq, ev_pair, ev_hb hrn, ev_k hrn, and_true, true_and]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hbF 32 (by norm_num), hbF 33 (by norm_num), hv, show (S (st + 32) + 256 * S (st + 33) + 65536 * S (st + 34) +
        16777216 * S (st + 35)) % 65536 = S (st + 32) + 256 * S (st + 33) by omega]; push_cast; ring
    · rw [hbF 34 (by norm_num), hbF 35 (by norm_num), hv, show (S (st + 32) + 256 * S (st + 33) + 65536 * S (st + 34) +
        16777216 * S (st + 35)) / 65536 = S (st + 34) + 256 * S (st + 35) by omega]; push_cast; ring
    · rw [hC 0 (by norm_num), hC 1 (by norm_num), c0, c1,
        show Spec.SetFile.code (recR M S r) % 65536 = Spec.SetFile.code (recR M S r) / 256 ^ 0 % 256 +
          256 * (Spec.SetFile.code (recR M S r) / 256 ^ 1 % 256) by norm_num; omega]
      push_cast; ring
    · rw [hC 2 (by norm_num), hC 3 (by norm_num), c2, c3,
        show Spec.SetFile.code (recR M S r) / 65536 = Spec.SetFile.code (recR M S r) / 256 ^ 2 % 256 +
          256 * (Spec.SetFile.code (recR M S r) / 256 ^ 3 % 256) by norm_num; omega]
      push_cast; ring
    · simp only [recR, recAt, Spec.SetFile.ser, bytesAt_length, cast_val]
    · simp only [txi, Expr.eval, ev_pair, ev_hb hrn, eval_cst, hti, hbF 41 (by norm_num), hbF 42 (by norm_num),
        hbF 43 (by norm_num), hbF 44 (by norm_num)]
      push_cast; ring

/-- **The sum**: the outgoing sum is the incoming one plus each record's `1/(z − φ)`. -/
theorem sum_sound :
    Block.RunSum.pQ pub PUB_SUM_OUT = Block.RunSum.pQ pub PUB_SUM_IN + ((recs M S e).map (frac pub)).sum := by
  have hen := E.lt
  have hl : n - 1 < n := by omega
  have h := toQ_zero_of (n := n) (pre := preCols) (pub := pub) (M := M) (r := n - 1)
    (x := (base isLast).mul ((colQ ACC).sub (pubQ PUB_SUM_OUT))) (fun c hc => hsat _ hl c (by simp [constraints, lastC, hc]))
  rw [ev_mul, toQ_mul, toQ_ev_base, ev_sub, toQ_sub, ev_colQ' hl, ev_isLast hl, if_neg (by omega),
    StarkedAir.Spec.QM31.emb_one, one_mul, ev_pubQ'] at h
  rw [← sub_eq_zero.mp h, acc_sum hsat (n - 1) hl, show n - 1 + 1 = n by omega,
    ← Finset.sum_range_add_sum_Ico _ (le_of_lt hen)]
  rw [Finset.sum_eq_zero (s := Finset.Ico e n) (fun q hq => zero_row hsat (by simp at hq; omega)
    (off_of E (by simp at hq; omega) (by simp at hq; omega))), add_zero]
  unfold recs
  rw [List.map_map, list_sum_range]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq' := Finset.mem_range.mp hq
  have hfr := frac_row hsat (show q < n by omega)
  rw [on_of E hq', StarkedAir.Spec.QM31.emb_one, ev_phi, tuple_eq hsat E H hq'] at hfr
  simp only [Function.comp, frac]
  exact eq_inv_of_mul_eq_one_right hfr

end Sum

/-! ### Together -/

/-- **`set_rec` is sound.** A satisfied trace with its lookups answered (`Hyp`) has on rows `[0, e)`;
their records (`recs`, read from the bytes `S`) encode the segment's bytes, are well formed (heights
below `2^24`) and strictly sorted (above the incoming key when there is one); and the public outgoing
count, last key, amount, highest height and sum are the incoming ones advanced over the records. The
rows' positions, lengths and code bytes are `chain`, `fields` and `code_bytes`. -/
theorem rec_sound {n : ℕ} {pub : ℕ → F} {M : ℕ → ℕ → F} {S : ℕ → ℕ}
    (hsat : ∀ r < n, ∀ c ∈ constraints, c.eval n preCols pub M r = 0) (hn : 0 < n) (H : Hyp n pub M S) :
    ∃ e, OnPre n M e ∧
      (∀ r < e, M IDX r = (r : F)) ∧ pub PUB_I_OUT - pub PUB_I_IN = (e : F) ∧
      (recs M S e).flatMap encRec = (List.range (pub PUB_LEN).val).map (fun q => UInt8.ofNat (S q)) ∧
      (∀ x ∈ recs M S e, RecOk x ∧ Spec.SetFile.code x / 2 < 2 ^ 24) ∧
      Sorted (recs M S e) ∧
      (pub PUB_HASLAST = 1 → KeyLex (fun j => (pub (PUB_LAST_IN j)).val) (keyB (recR M S 0))) ∧
      (∀ j < 36, (pub (PUB_LAST_OUT j)).val = keyB (recR M S (e - 1)) j) ∧
      pubAmt pub PUB_AMT_OUT = pubAmt pub PUB_AMT_IN + ((recs M S e).map Spec.SetFile.amountOf).sum ∧
      (∀ j < 12, (pub (PUB_AMT_OUT j)).val < 256) ∧
      (pub PUB_MAXH_OUT).val = ((recs M S e).map fun x => Spec.SetFile.code x / 2).foldl max (pub PUB_MAXH_IN).val ∧
      (pub PUB_MAXH_OUT).val < 2 ^ 24 ∧
      Block.RunSum.pQ pub PUB_SUM_OUT = Block.RunSum.pQ pub PUB_SUM_IN + ((recs M S e).map (frac pub)).sum := by
  obtain ⟨e, E⟩ := on_prefix hsat hn
  obtain ⟨h1, h2⟩ := rows_sound hsat E
  obtain ⟨o1, o2, o3⟩ := order_sound hsat E H
  obtain ⟨a1, a2⟩ := amount_sound hsat E H
  obtain ⟨m1, m2⟩ := height_sound hsat E H
  refine ⟨e, E, h1, h2, parse_bytes hsat E H, ?_, o1, o2, o3, a1, a2, m1, m2, sum_sound hsat E H⟩
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  exact recR_ok hsat E H (List.mem_range.mp hr)

end StarkedAir.SetPass.Rec
