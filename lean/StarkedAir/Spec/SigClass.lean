/-
**Script classes for the sigop cost (CONNECT-RULES step 3).** `CountWitnessSigOps` only looks at whether
a script is a version 0 witness program of 20 or 32 bytes (`isW`), and `GetP2SHSigOpCount` at whether
it is P2SH. `countWitness_eq` restates the count with these classes; `ser_p2sh`, `ser_w` read the
classes from fixed bytes of a `serTxOut`, which is what `block_urec` does.
-/
import StarkedAir.Spec.ConnectRules
import StarkedAir.Spec.BlockSer

namespace StarkedAir.Spec.ConnectRules

open StarkedAir.Spec StarkedAir.Spec.Block

/-- A version 0 witness program of `k` bytes: `OP_0`, a push of `k` bytes, nothing else. -/
def isW (k : ℕ) (s : Bytes) : Bool := s.length == k + 2 && s[0]? == some 0 && s[1]? == some (UInt8.ofNat k)

/-- The accurate count of a witness stack's last item (0 for an empty stack). -/
def lastAcc (w : List Bytes) : ℕ := (w.getLast?.map sigOpsAccurate).getD 0

theorem isW_iff (k : ℕ) (s : Bytes) :
    isW k s = true ↔ s.length = k + 2 ∧ s[0]? = some 0 ∧ s[1]? = some (UInt8.ofNat k) := by
  simp [isW, and_assoc]

/-- **`WitnessSigOps` of a script's program** by class: 1 for 20 bytes, the witness script's count for 32. -/
theorem wsig_class (s : Bytes) (wit : List Bytes) :
    (match witnessProgram s with
      | some (v, prog) => witnessSigOps v prog wit
      | none => 0) = if isW 20 s then 1 else if isW 32 s then lastAcc wit else 0 := by
  match s with
  | [] => simp [witnessProgram, isW]
  | [v] => simp [witnessProgram, isW]
  | v :: l :: prog =>
    have h20 : isW 20 (v :: l :: prog) = true ↔ prog.length = 20 ∧ v = 0 ∧ l = 20 := by
      rw [isW_iff]; simp
    have h32 : isW 32 (v :: l :: prog) = true ↔ prog.length = 32 ∧ v = 0 ∧ l = 32 := by
      rw [isW_iff]; simp
    have hl : ∀ k : ℕ, k < 256 → (l = UInt8.ofNat k ↔ l.toNat = k) := fun k hk => by
      constructor
      · rintro rfl; simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hk]
      · intro e; apply UInt8.toNat_inj.mp; simp [e, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hk]
    simp only [witnessProgram, List.length_cons]
    by_cases hc : 4 ≤ prog.length + 1 + 1 ∧ prog.length + 1 + 1 ≤ 42 ∧ (v = 0 ∨ (0x51 ≤ v ∧ v ≤ 0x60)) ∧
        l.toNat + 2 = prog.length + 1 + 1
    · rw [if_pos hc]
      obtain ⟨c1, c2, c3, c4⟩ := hc
      by_cases hv : v = 0
      · subst hv
        simp only [if_true, witnessSigOps]
        by_cases p20 : prog.length = 20
        · rw [if_pos p20, if_pos (h20.mpr ⟨p20, rfl, (hl 20 (by norm_num)).mpr (by omega)⟩)]
        · rw [if_neg p20, if_neg (show ¬ isW 20 (0 :: l :: prog) = true by rw [h20]; tauto)]
          by_cases p32 : prog.length = 32
          · rw [if_pos p32, if_pos (h32.mpr ⟨p32, rfl, (hl 32 (by norm_num)).mpr (by omega)⟩)]; rfl
          · rw [if_neg p32, if_neg (show ¬ isW 32 (0 :: l :: prog) = true by rw [h32]; tauto)]
      · have hv51 : 0x51 ≤ v.toNat := by
          rcases c3 with h | h
          · exact absurd h hv
          · have := UInt8.le_iff_toNat_le.mp h.1; simpa using this
        simp only [hv, if_false, witnessSigOps]
        rw [if_neg (by omega), if_neg (show ¬ isW 20 (v :: l :: prog) = true by rw [h20]; tauto),
          if_neg (show ¬ isW 32 (v :: l :: prog) = true by rw [h32]; tauto)]
    · rw [if_neg hc]
      rw [if_neg (show ¬ isW 20 (v :: l :: prog) = true by
          rw [h20]; rintro ⟨p, hv, hl20⟩
          exact hc ⟨by omega, by omega, Or.inl hv, by rw [(hl 20 (by norm_num)).mp hl20]; omega⟩),
        if_neg (show ¬ isW 32 (v :: l :: prog) = true by
          rw [h32]; rintro ⟨p, hv, hl32⟩
          exact hc ⟨by omega, by omega, Or.inl hv, by rw [(hl 32 (by norm_num)).mp hl32]; omega⟩)]

/-- A P2SH script is no witness program. -/
theorem p2sh_not_wp {s : Bytes} (h : isP2SH s = true) : witnessProgram s = none := by
  match s with
  | [] => rfl
  | [v] => rfl
  | v :: l :: prog =>
    simp only [isP2SH, Bool.and_eq_true, beq_iff_eq, List.length_cons, List.getElem?_cons_zero,
      Option.some.injEq] at h
    obtain ⟨⟨⟨-, hv⟩, -⟩, -⟩ := h
    simp only [witnessProgram]
    rw [if_neg]
    rintro ⟨-, -, h3, -⟩
    subst hv
    rcases h3 with h3 | h3
    · exact absurd h3 (by decide)
    · exact absurd h3.2 (by decide)

/-- **`CountWitnessSigOps` by classes.** -/
theorem countWitness_eq (sig spent : Bytes) (wit : List Bytes) :
    countWitnessSigOps sig spent wit =
      if isW 20 spent then 1 else if isW 32 spent then lastAcc wit
      else if isP2SH spent && pushOnly sig then
        (if isW 20 (lastPush sig) then 1 else if isW 32 (lastPush sig) then lastAcc wit else 0)
      else 0 := by
  have h1 := wsig_class spent wit
  have h2 := wsig_class (lastPush sig) wit
  unfold countWitnessSigOps
  cases hw : witnessProgram spent with
  | some p =>
    obtain ⟨v, prog⟩ := p
    rw [hw] at h1
    simp only at h1 ⊢
    rw [h1]
    have hp : isP2SH spent = false := by
      by_contra hc
      rw [Bool.not_eq_false] at hc
      rw [p2sh_not_wp hc] at hw; cases hw
    simp [hp]
  | none =>
    rw [hw] at h1
    simp only at h1 ⊢
    have a20 : isW 20 spent = false := by
      by_contra hc; rw [Bool.not_eq_false] at hc; rw [if_pos hc] at h1; exact absurd h1 (by norm_num)
    rw [a20] at h1 ⊢
    simp only [Bool.false_eq_true, if_false] at h1 ⊢
    by_cases c32 : isW 32 spent = true
    · -- impossible: a 32-byte program is a witness program
      exfalso
      have := (isW_iff 32 spent).mp c32
      match spent, this with
      | v :: l :: prog, ⟨hlen, hv, hl⟩ =>
        simp only [List.getElem?_cons_zero, Option.some.injEq, List.getElem?_cons_succ] at hv hl
        simp only [witnessProgram, List.length_cons] at hw
        rw [if_pos ⟨by simp at hlen; omega, by simp at hlen; omega, Or.inl hv, by
          subst hl; simp at hlen ⊢; omega⟩] at hw
        cases hw
    · rw [if_neg c32]
      by_cases hp : (isP2SH spent && pushOnly sig) = true
      · rw [if_pos hp, if_pos hp]; exact h2
      · rw [if_neg hp, if_neg hp]

/-! ### The classes in a `serTxOut` -/

/-- The script length's first CompactSize byte is `c < 253` exactly when the length is `c`. -/
theorem ser_len_byte (o : TxOut) {c : ℕ} (hc : c < 253) :
    (serTxOut o).getD 8 0 = UInt8.ofNat c ↔ o.scriptPubKey.length = c := by
  have hl := leBytes_length 8 (o.value % 2 ^ 64).toNat
  unfold serTxOut serVarBytes
  rw [List.getD_append_right _ _ _ _ (by omega), hl, Nat.sub_self]
  have hof : ∀ a b : ℕ, a < 256 → b < 256 → (UInt8.ofNat a = UInt8.ofNat b ↔ a = b) := fun a b ha hb => by
    constructor
    · intro h
      have := congrArg UInt8.toNat h
      simpa [UInt8.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using this
    · rintro rfl; rfl
  unfold serCompact
  by_cases h1 : o.scriptPubKey.length < 253
  · rw [if_pos h1]; simp only [List.cons_append, List.nil_append, List.getD_cons_zero]
    exact hof _ _ (by omega) (by omega)
  · rw [if_neg h1]
    constructor
    · intro h
      exfalso
      split_ifs at h <;> simp only [List.cons_append, List.getD_cons_zero] at h <;>
        · have := congrArg UInt8.toNat h
          simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt (show c < 256 by omega)] at this
          omega
    · intro h; omega

/-- With a one-byte length, the script starts at byte 9. -/
theorem ser_script_byte (o : TxOut) (h : o.scriptPubKey.length < 253) (i : ℕ) :
    (serTxOut o).getD (9 + i) 0 = o.scriptPubKey.getD i 0 := by
  have hl := leBytes_length 8 (o.value % 2 ^ 64).toNat
  unfold serTxOut serVarBytes serCompact
  rw [if_pos h, List.getD_append_right _ _ _ _ (by omega), hl, show 9 + i - 8 = i + 1 by omega]
  simp

/-- **P2SH, read from the serialization**: bytes 8, 9, 10 and 31 are `17 a9 14 … 87`. -/
theorem ser_p2sh (o : TxOut) : isP2SH o.scriptPubKey = true ↔
    (serTxOut o).getD 8 0 = 0x17 ∧ (serTxOut o).getD 9 0 = 0xa9 ∧ (serTxOut o).getD 10 0 = 0x14 ∧
      (serTxOut o).getD 31 0 = 0x87 := by
  have hb := ser_len_byte o (c := 23) (by norm_num)
  have e8 : (UInt8.ofNat 23) = (0x17 : UInt8) := rfl
  rw [e8] at hb
  simp only [isP2SH, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    have hs := fun i => ser_script_byte o (by omega) i
    refine ⟨hb.mpr h1, ?_, ?_, ?_⟩
    · rw [show (9 : ℕ) = 9 + 0 from rfl, hs, List.getD_eq_getElem?_getD, h2]; rfl
    · rw [show (10 : ℕ) = 9 + 1 from rfl, hs, List.getD_eq_getElem?_getD, h3]; rfl
    · rw [show (31 : ℕ) = 9 + 22 from rfl, hs, List.getD_eq_getElem?_getD, h4]; rfl
  · rintro ⟨h1, h2, h3, h4⟩
    have hlen := hb.mp h1
    have hs := fun i => ser_script_byte o (by omega) i
    rw [show (9 : ℕ) = 9 + 0 from rfl, hs] at h2
    rw [show (10 : ℕ) = 9 + 1 from rfl, hs] at h3
    rw [show (31 : ℕ) = 9 + 22 from rfl, hs] at h4
    refine ⟨⟨⟨hlen, ?_⟩, ?_⟩, ?_⟩
    · rw [List.getElem?_eq_getElem (by omega), ← h2, List.getD_eq_getElem _ _ (by omega)]
    · rw [List.getElem?_eq_getElem (by omega), ← h3, List.getD_eq_getElem _ _ (by omega)]
    · rw [List.getElem?_eq_getElem (by omega), ← h4, List.getD_eq_getElem _ _ (by omega)]

/-- **A version 0 program of `k` bytes, read from the serialization**: bytes 8, 9, 10 are `k + 2`, `0`, `k`. -/
theorem ser_w (o : TxOut) {k : ℕ} (hk : k + 2 < 253) : isW k o.scriptPubKey = true ↔
    (serTxOut o).getD 8 0 = UInt8.ofNat (k + 2) ∧ (serTxOut o).getD 9 0 = 0 ∧
      (serTxOut o).getD 10 0 = UInt8.ofNat k := by
  have hb := ser_len_byte o (c := k + 2) hk
  rw [isW_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hs := fun i => ser_script_byte o (by omega) i
    refine ⟨hb.mpr h1, ?_, ?_⟩
    · rw [show (9 : ℕ) = 9 + 0 from rfl, hs, List.getD_eq_getElem?_getD, h2]; rfl
    · rw [show (10 : ℕ) = 9 + 1 from rfl, hs, List.getD_eq_getElem?_getD, h3]; rfl
  · rintro ⟨h1, h2, h3⟩
    have hlen := hb.mp h1
    have hs := fun i => ser_script_byte o (by omega) i
    rw [show (9 : ℕ) = 9 + 0 from rfl, hs] at h2
    rw [show (10 : ℕ) = 9 + 1 from rfl, hs] at h3
    refine ⟨hlen, ?_, ?_⟩
    · rw [List.getElem?_eq_getElem (by omega), ← h2, List.getD_eq_getElem _ _ (by omega)]
    · rw [List.getElem?_eq_getElem (by omega), ← h3, List.getD_eq_getElem _ _ (by omega)]

theorem serTxOut_len_ge (o : TxOut) : 9 ≤ (serTxOut o).length := by
  unfold serTxOut serVarBytes serCompact
  simp only [List.length_append, leBytes_length]
  split_ifs <;> simp <;> omega

theorem serTxOut_len_small (o : TxOut) (h : o.scriptPubKey.length < 253) :
    (serTxOut o).length = 9 + o.scriptPubKey.length := by
  unfold serTxOut serVarBytes serCompact
  rw [if_pos h]; simp [leBytes_length]; omega

theorem u8_toNat_iff (x : UInt8) {v : ℕ} (hv : v < 256) : x.toNat = v ↔ x = UInt8.ofNat v :=
  ⟨fun e => UInt8.toNat_inj.mp (by simp [e, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hv]),
    by rintro rfl; simp [UInt8.toNat_ofNat', Nat.mod_eq_of_lt hv]⟩

/-! ### The count as two flags -/

theorem isW_excl {s : Bytes} (h : isW 20 s = true) : isW 32 s = false := by
  rw [Bool.eq_false_iff]; intro h'
  have a := ((isW_iff 20 s).mp h).1
  have b := ((isW_iff 32 s).mp h').1
  omega

theorem p2sh_not_w {s : Bytes} (h : isP2SH s = true) (k : ℕ) (hk : k ≠ 21) : isW k s = false := by
  rw [Bool.eq_false_iff]; intro h'
  have a := ((isW_iff k s).mp h').1
  simp only [isP2SH, Bool.and_eq_true, beq_iff_eq] at h
  omega

/-- The 20-byte program flags of an input: the spent script's, and the redeem script's under P2SH. -/
def w20Of (sig spent : Bytes) : ℕ :=
  (if isW 20 spent then 1 else 0) + (if isP2SH spent && pushOnly sig && isW 20 (lastPush sig) then 1 else 0)

/-- The 32-byte program flags of an input. -/
def n32Of (sig spent : Bytes) : ℕ :=
  (if isW 32 spent then 1 else 0) + (if isP2SH spent && pushOnly sig && isW 32 (lastPush sig) then 1 else 0)

theorem w20Of_le (sig spent : Bytes) : w20Of sig spent ≤ 1 := by
  unfold w20Of
  by_cases a : isW 20 spent = true
  · have hp : isP2SH spent = false := by
      by_contra hc; rw [Bool.not_eq_false] at hc
      rw [p2sh_not_w hc 20 (by norm_num)] at a; exact absurd a (by simp)
    simp [a, hp]
  · simp only [a, Bool.false_eq_true, if_false, zero_add]; split_ifs <;> omega

theorem n32Of_le (sig spent : Bytes) : n32Of sig spent ≤ 1 := by
  unfold n32Of
  by_cases a : isW 32 spent = true
  · have hp : isP2SH spent = false := by
      by_contra hc; rw [Bool.not_eq_false] at hc
      rw [p2sh_not_w hc 32 (by norm_num)] at a; exact absurd a (by simp)
    simp [a, hp]
  · simp only [a, Bool.false_eq_true, if_false, zero_add]; split_ifs <;> omega

/-- **`CountWitnessSigOps` as two flags**: one for a 20-byte program, and the witness script's count
for a 32-byte program. -/
theorem count_split (sig spent : Bytes) (wit : List Bytes) :
    countWitnessSigOps sig spent wit = w20Of sig spent + n32Of sig spent * lastAcc wit := by
  rw [countWitness_eq]
  unfold w20Of n32Of
  by_cases a : isW 20 spent = true
  · have hp : isP2SH spent = false := by
      by_contra hc; rw [Bool.not_eq_false] at hc
      rw [p2sh_not_w hc 20 (by norm_num)] at a; exact absurd a (by simp)
    simp [a, hp, isW_excl a]
  by_cases b : isW 32 spent = true
  · have hp : isP2SH spent = false := by
      by_contra hc; rw [Bool.not_eq_false] at hc
      rw [p2sh_not_w hc 32 (by norm_num)] at b; exact absurd b (by simp)
    simp [a, b, hp]
  by_cases c : (isP2SH spent && pushOnly sig) = true
  · by_cases d : isW 20 (lastPush sig) = true
    · simp [a, b, c, d, isW_excl d]
    · by_cases e : isW 32 (lastPush sig) = true
      · simp [a, b, c, d, e]
      · simp [a, b, c, d, e]
  · simp [a, b, c]

theorem lastPush_nil : lastPush [] = [] := by simp [lastPush, opsD]

theorem acc_nil : sigOpsAccurate [] = 0 := by simp [sigOpsAccurate, ops, accGo]

end StarkedAir.Spec.ConnectRules
