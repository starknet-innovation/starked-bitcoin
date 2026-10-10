/-
**The statement mixing, Lean-first (VERIFIER-LEAN step 3b).** Before the main commitment, `verifyPlain`
(`src/recursion/plain_verifier.zig`) feeds the transcript, with stwo-zig's channel `mixU32s` (hook 3 here):
- for a system proof, the component count;
- per component: the trace log size (hook 4: the host's constant, so one program serves every size), the
  AIR digest's 8 words and the public-input count;
- each public input, as a u32 (`m31_to_u32`).

`statement_sound`: if the ops hold and hook 4 returns the log size, the words each mix call receives are,
in order, exactly `stmtWords` (the native `prove.mixStatement` encoding). This is what binds the public
inputs and the AIRs to the proof's transcript.
-/
import StarkedAir.Circuit.Gadgets
import StarkedAir.Circuit.BlakeSound

namespace StarkedAir.Circuit.Statement

open StarkedAir StarkedAir.Circuit

/-- A component's statement: its AIR digest (8 words) and its public-input registers. -/
structure PartSt where
  digest : List ℕ
  pubs : List ℕ

/-- The program, from register `n`: component count, then per component the header words and each
public input. Registers: `n` the count; per component `10` header registers, then `1` per public input. -/
def headerOps (o : ℕ) (d : List ℕ) (nPub : ℕ) : List Op :=
  [.hook 4 [] [o]] ++ (List.range 8).map (fun i => constU32 (o + 1 + i) (d.getD i 0)) ++ [constU32 (o + 9) nPub,
    .hook 3 ((List.range 10).map (o + ·)) []]

def pubOps (o : ℕ) (pubs : List ℕ) : List Op :=
  (List.range pubs.length).flatMap fun k => [.m2u (o + k) (pubs.getD k 0), .hook 3 [o + k] []]

def partOps (o : ℕ) (p : PartSt) : List Op := headerOps o p.digest p.pubs.length ++ pubOps (o + 10) p.pubs
def partSize (p : PartSt) : ℕ := 10 + p.pubs.length

def stmtOps (n : ℕ) (system : Bool) (parts : List PartSt) : List Op :=
  (if system then [constU32 n parts.length, .hook 3 [n] []] else []) ++
  (parts.foldl (fun (acc : List Op × ℕ) p => (acc.1 ++ partOps acc.2 p, acc.2 + partSize p)) ([], n + 1)).1

/-- The mix calls: each hook 3's arguments, in order. -/
def mixArgs : List Op → List (List ℕ)
  | [] => []
  | .hook 3 args _ :: rest => args :: mixArgs rest
  | _ :: rest => mixArgs rest

theorem mixArgs_append (a b : List Op) : mixArgs (a ++ b) = mixArgs a ++ mixArgs b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | hook id args outs =>
      by_cases h : id = 3
      · subst h; simp [mixArgs, ih]
      · rw [List.cons_append]
        rw [mixArgs.eq_def, mixArgs.eq_def (Op.hook id args outs :: xs)]
        rcases id with _ | _ | _ | _ | id <;> simp_all
    | _ => simp [mixArgs, ih]

/-- **The native statement words**: the count (systems), per component `[L, digest, n_pubs]`, then each
public input's value. -/
def stmtWords (system : Bool) (L : ℕ) (parts : List (List ℕ × List ℕ)) : List (List ℕ) :=
  (if system then [[parts.length]] else []) ++
  parts.flatMap fun p => (L :: p.1 ++ [p.2.length]) :: p.2.map fun v => [v]

variable {ρ : ℕ → Q}

/-- A register's value as a u32. -/
def wv (ρ : ℕ → Q) (r : ℕ) : ℕ := (Q.word (ρ r)).toNat

theorem wv_const {o w : ℕ} (hw : w < 2 ^ 32) (h : (constU32 o w).holds ρ) : wv ρ o = w := by
  simp only [constU32, Op.holds] at h
  rw [wv, h, Q.word_lit hw, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hw]

theorem wv_m2u {o x : ℕ} (h : (Op.m2u o x).holds ρ) : wv ρ o = (ρ x).a.val := by
  simp only [Op.holds] at h
  rw [wv, h.2, word_m2u, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (lt_trans (ZMod.val_lt _) (by unfold P; norm_num))]

theorem mixArgs_headerOps (o : ℕ) (d : List ℕ) (nPub : ℕ) : mixArgs (headerOps o d nPub) = [(List.range 10).map (o + ·)] := by
  simp [headerOps, mixArgs, mixArgs_append, constU32, List.range_succ]

theorem mixArgs_pubOps (o : ℕ) (pubs : List ℕ) : mixArgs (pubOps o pubs) = (List.range pubs.length).map fun k => [o + k] := by
  unfold pubOps
  induction pubs.length with
  | zero => rfl
  | succ m ih => rw [List.range_succ, List.flatMap_append, mixArgs_append, ih]; simp [mixArgs]

/-- One component's mixed words. -/
theorem part_words {o : ℕ} {p : PartSt} {L : ℕ} (hL : L < 2 ^ 32) (hd : ∀ w ∈ p.digest, w < 2 ^ 32) (hdl : p.digest.length = 8)
    (hn : p.pubs.length < 2 ^ 32) (h4 : ∀ r, Op.hook 4 [] [r] ∈ partOps o p → wv ρ r = L)
    (h : Holds ρ (partOps o p)) :
    (mixArgs (partOps o p)).map (List.map (wv ρ)) = (L :: p.digest ++ [p.pubs.length]) :: p.pubs.map fun r => [(ρ r).a.val] := by
  have inH : ∀ x ∈ headerOps o p.digest p.pubs.length, x ∈ partOps o p := fun x hx => List.mem_append_left _ hx
  have inP : ∀ x ∈ pubOps (o + 10) p.pubs, x ∈ partOps o p := fun x hx => List.mem_append_right _ hx
  have hc : ∀ i < 8, wv ρ (o + 1 + i) = p.digest.getD i 0 := fun i hi =>
    wv_const (by rw [List.getD_eq_getElem _ _ (by omega)]; exact hd _ (List.getElem_mem _))
      (h _ (inH _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))))
  have hc9 : wv ρ (o + 9) = p.pubs.length := wv_const hn (h _ (inH _ (List.mem_append_right _ (List.Mem.head _))))
  have h0 : wv ρ o = L := h4 o (inH _ (List.mem_append_left _ (List.mem_append_left _ (List.Mem.head _))))
  have hval : ∀ i < 10, wv ρ (o + i) = (L :: p.digest ++ [p.pubs.length]).getD i 0 := by
    intro i hi
    rcases Nat.lt_or_ge i 9 with h9 | h9
    · rcases i with _ | i
      · simpa using h0
      · rw [show o + (i + 1) = o + 1 + i by omega, hc i (by omega), List.cons_append, List.getD_cons_succ,
          List.getD_append _ _ _ _ (by omega)]
    · obtain rfl : i = 9 := by omega
      rw [hc9, List.cons_append, List.getD_cons_succ, List.getD_append_right _ _ _ _ (by omega), hdl]; rfl
  unfold partOps
  rw [mixArgs_append, mixArgs_headerOps, mixArgs_pubOps, List.map_append]
  simp only [List.map_cons, List.map_nil, List.singleton_append, List.cons.injEq]
  constructor
  · apply List.ext_getElem (by simp [hdl])
    intro i h1 h2
    have hi : i < 10 := by simpa using h1
    simp only [List.getElem_map, List.getElem_range]
    rw [hval i hi, List.getD_eq_getElem _ _ h2]
  · apply List.ext_getElem (by simp)
    intro k h1 h2
    have hk : k < p.pubs.length := by simpa using h1
    simp only [List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
    have hm := h _ (inP _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.Mem.head _⟩))
    rw [wv_m2u hm, List.getD_eq_getElem _ _ hk]

def partsFold (parts : List PartSt) (s : List Op × ℕ) : List Op × ℕ :=
  parts.foldl (fun (acc : List Op × ℕ) p => (acc.1 ++ partOps acc.2 p, acc.2 + partSize p)) s

theorem partsFold_ops : ∀ (parts : List PartSt) (s : List Op × ℕ), ∃ rest, (partsFold parts s).1 = s.1 ++ rest
  | [], s => ⟨[], by simp [partsFold]⟩
  | p :: ps, s => by
    obtain ⟨r, hr⟩ := partsFold_ops ps (s.1 ++ partOps s.2 p, s.2 + partSize p)
    exact ⟨partOps s.2 p ++ r, by simp only [partsFold, List.foldl_cons] at hr ⊢; rw [hr, List.append_assoc]⟩

/-- The statement's public-input values and digests (what the words encode). -/
def stmtSpec (ρ : ℕ → Q) (parts : List PartSt) : List (List ℕ × List ℕ) :=
  parts.map fun p => (p.digest, p.pubs.map fun r => (ρ r).a.val)

theorem partsFold_words {L : ℕ} (hL : L < 2 ^ 32) : ∀ (parts : List PartSt) (s : List Op × ℕ),
    (∀ p ∈ parts, (∀ w ∈ p.digest, w < 2 ^ 32) ∧ p.digest.length = 8 ∧ p.pubs.length < 2 ^ 32) →
    (∀ r, Op.hook 4 [] [r] ∈ (partsFold parts s).1 → wv ρ r = L) →
    Holds ρ (partsFold parts s).1 →
    (mixArgs (partsFold parts s).1).map (List.map (wv ρ)) =
      (mixArgs s.1).map (List.map (wv ρ)) ++ (stmtSpec ρ parts).flatMap fun p => (L :: p.1 ++ [p.2.length]) :: p.2.map fun v => [v]
  | [], s, _, _, _ => by simp [partsFold, stmtSpec]
  | p :: ps, s, hp, h4, h => by
    have e : partsFold (p :: ps) s = partsFold ps (s.1 ++ partOps s.2 p, s.2 + partSize p) := by simp [partsFold]
    rw [e] at h4 h ⊢
    obtain ⟨r, hr⟩ := partsFold_ops ps (s.1 ++ partOps s.2 p, s.2 + partSize p)
    have hin : ∀ x ∈ partOps s.2 p, x ∈ (partsFold ps (s.1 ++ partOps s.2 p, s.2 + partSize p)).1 := by
      intro x hx; rw [hr]; exact List.mem_append_left _ (List.mem_append_right _ hx)
    obtain ⟨hd, hdl, hn⟩ := hp p (by simp)
    have hw := part_words hL hd hdl hn (fun q hq => h4 q (hin _ hq)) (fun x hx => h x (hin x hx))
    rw [partsFold_words hL ps _ (fun q hq => hp q (by simp [hq])) h4 h]
    simp only
    rw [mixArgs_append, List.map_append, hw]
    simp [stmtSpec, List.append_assoc]

/-- **The statement mixing is sound.** If the ops hold, hook 4 returns `L`, and the constants fit in
32 bits, the words the transcript absorbs (hook 3's arguments, in order) are exactly the native
statement encoding: the component count (systems), then per component `[L, digest, n_pubs]` and each
public input's M31 value. -/
theorem statement_sound {n : ℕ} {system : Bool} {parts : List PartSt} {L : ℕ} (hL : L < 2 ^ 32)
    (hp : ∀ p ∈ parts, (∀ w ∈ p.digest, w < 2 ^ 32) ∧ p.digest.length = 8 ∧ p.pubs.length < 2 ^ 32)
    (hcount : parts.length < 2 ^ 32)
    (h4 : ∀ r, Op.hook 4 [] [r] ∈ stmtOps n system parts → wv ρ r = L) (h : Holds ρ (stmtOps n system parts)) :
    (mixArgs (stmtOps n system parts)).map (List.map (wv ρ)) = stmtWords system L (stmtSpec ρ parts) := by
  have e : stmtOps n system parts = (if system then [constU32 n parts.length, .hook 3 [n] []] else []) ++
      (partsFold parts ([], n + 1)).1 := rfl
  rw [e] at h h4 ⊢
  rw [holds_append] at h
  rw [mixArgs_append, List.map_append, partsFold_words hL parts ([], n + 1) hp
    (fun r hr => h4 r (List.mem_append_right _ hr)) h.2]
  unfold stmtWords
  simp only [mixArgs, List.map_nil, List.nil_append, stmtSpec, List.length_map]
  congr 1
  cases system
  · simp; rfl
  · have hc := wv_const hcount (h.1 _ (List.Mem.head _))
    simp [mixArgs, constU32, hc]

/-! ### The production form: the header words from the host -/

/-- Per component: hook 4 creates the 10 header constants (log size, AIR digest, public-input count), as
the hand-written code does; then the mix, then each public input. -/
def partOpsH (o : ℕ) (nPub : ℕ) (pubs : List ℕ) : List Op :=
  [.hook 4 [] ((List.range 10).map (o + ·)), .hook 3 ((List.range 10).map (o + ·)) []] ++ pubOps (o + 10) pubs

def stmtOpsH (n : ℕ) (system : Bool) (parts : List (List ℕ)) : List Op :=
  (if system then [constU32 n parts.length, .hook 3 [n] []] else []) ++
  (parts.foldl (fun (acc : List Op × ℕ) p => (acc.1 ++ partOpsH acc.2 p.length p, acc.2 + 10 + p.length)) ([], n + 1)).1

/-- **The public inputs are mixed exactly.** Each public input register's mix call absorbs that input's M31
value as a u32. -/
theorem pub_mixed {o : ℕ} {pubs : List ℕ} (h : Holds ρ (pubOps o pubs)) :
    (mixArgs (pubOps o pubs)).map (List.map (wv ρ)) = pubs.map fun r => [(ρ r).a.val] := by
  rw [mixArgs_pubOps]
  apply List.ext_getElem (by simp)
  intro k h1 h2
  have hk : k < pubs.length := by simpa using h1
  simp only [List.getElem_map, List.getElem_range, List.map_cons, List.map_nil]
  have hm := h _ (List.mem_flatMap.mpr ⟨k, List.mem_range.mpr hk, List.Mem.head _⟩)
  rw [wv_m2u hm, List.getD_eq_getElem _ _ hk]

theorem partH_mixed {o nPub : ℕ} {pubs : List ℕ} (h : Holds ρ (partOpsH o nPub pubs)) :
    mixArgs (partOpsH o nPub pubs) = ((List.range 10).map (o + ·)) :: mixArgs (pubOps (o + 10) pubs) ∧
    (mixArgs (pubOps (o + 10) pubs)).map (List.map (wv ρ)) = pubs.map fun r => [(ρ r).a.val] := by
  refine ⟨?_, pub_mixed fun x hx => h x (List.mem_append_right _ hx)⟩
  simp [partOpsH, mixArgs, mixArgs_append]

def stmtJson (system : Bool) (nPubs : List ℕ) : String :=
  let nIn := nPubs.sum
  let regs := (nPubs.foldl (fun (acc : List (List ℕ) × ℕ) k => (acc.1 ++ [(List.range k).map (acc.2 + ·)], acc.2 + k)) ([], 0)).1
  let ops := [Op.hook 0 [] (List.range nIn)] ++ stmtOpsH nIn system regs
  s!"\{\"schema\":\"starked-glue-v1\",\"ops\":[{",".intercalate (ops.map Op.toJson)}],\"results\":[]}"

end StarkedAir.Circuit.Statement
