/-
**Toy lookup system (IR-LOGUP test): a byte range check.** `table` has the bytes `0 … 255` as a
preprocessed column and a main multiplicity column; `user` looks up its main column with
multiplicity `−1`. `user_bytes`: in any satisfying instance, every user value is a byte.
Exported as `byte_table` / `byte_user`; the Zig test `air.system` proves and verifies it.
-/
import StarkedAir.Lookup

namespace StarkedAir.ByteLookup

def table : Comp where
  air := { name := "byte_table", nMain := 1, pre := [.periodic (List.range 256)], constraints := [] }
  lookups := [⟨1, .col .main 0 0, [.col .pre 0 0]⟩]

def user : Comp where
  air := { name := "byte_user", nMain := 1, pre := [], constraints := [] }
  lookups := [⟨1, .const (P - 1), [.col .main 0 0]⟩]

def sys : System := ⟨2, fun i => if i = 0 then table else user⟩

theorem natCast_P_sub_one : ((P - 1 : ℕ) : F) = -1 := by
  rw [eq_neg_iff_add_eq_zero]
  have h : (P - 1 : ℕ) + 1 = P := by unfold P; norm_num
  have e : (((P - 1 + 1 : ℕ)) : F) = 0 := by rw [h]; exact ZMod.natCast_self _
  rwa [Nat.cast_add, Nat.cast_one] at e

theorem mem_sites {sys : System} {inst : ℕ → Inst} {s : Site} :
    s ∈ sites sys inst ↔ s.1 < sys.m ∧ s.2.1 < 2 ^ (inst s.1).logSize ∧ s.2.2 < (sys.comp s.1).lookups.length := by
  obtain ⟨i, r, k⟩ := s
  simp [sites]

/-- **Every user value is a byte**, in any satisfying instance whose user trace has fewer than
`P` rows and whose table covers `0 … 255` (at least 256 rows). -/
theorem user_bytes {inst : ℕ → Inst} {pub : ℕ → F} (hsat : sys.Satisfied inst pub)
    (hcount : 2 ^ (inst 1).logSize < P) {r : ℕ} (hr : r < 2 ^ (inst 1).logSize) :
    ((inst 1).main 0 (wrap (2 ^ (inst 1).logSize) r 0)).val < 256 := by
  have hs0 : ((1, r, 0) : Site) ∈ sites sys inst := mem_sites.mpr ⟨by simp [sys], hr, by simp [sys, user]⟩
  -- Use sites are the user's: multiplicity −1.
  have huse : ∀ s ∈ sites sys inst, s.1 = 1 → siteMult sys inst pub s = -1 := by
    intro s hs h1
    obtain ⟨i, r', k⟩ := s
    simp only at h1; subst h1
    have hk : k = 0 := by have := (mem_sites.mp hs).2.2; simp [sys, user] at this; omega
    subst hk
    exact natCast_P_sub_one
  have hsites : sites sys inst = (List.range (2 ^ (inst 0).logSize)).map (fun r => ((0, r, 0) : Site)) ++
      (List.range (2 ^ (inst 1).logSize)).map (fun r => ((1, r, 0) : Site)) := by
    simp only [sites, show sys.m = 2 from rfl, show List.range 2 = [0, 1] from rfl, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, show (sys.comp 0).lookups.length = 1 from rfl,
      show (sys.comp 1).lookups.length = 1 from rfl, show List.range 1 = [0] from rfl, List.map_cons,
      List.map_nil, ← List.map_eq_flatMap]
  have hcnt : ((sites sys inst).filter fun s => s.1 = 1).length < P := by
    rw [hsites, List.filter_append, List.filter_eq_nil_iff.mpr (by simp), List.filter_eq_self.mpr (by simp),
      List.nil_append, List.length_map, List.length_range]
    exact hcount
  obtain ⟨s, hs, hnu, -, hv⟩ := used_in_table hsat.2 (fun i _ => i = 1) huse hcnt hs0
  obtain ⟨i, r', k⟩ := s
  have hm := mem_sites.mp hs
  simp only at hnu hm
  have hi : i = 0 := by simp [sys] at hm; omega
  subst hi
  have hk : k = 0 := by simp [sys, table] at hm; omega
  subst hk
  simp [siteVals, siteEval, siteLookup, sys, table, user, Expr.eval, PreCol.eval] at hv
  rw [← hv, ZMod.val_natCast]
  calc _ ≤ _ := Nat.mod_le _ _
    _ < 256 := by
      rw [List.getElem?_range (Nat.mod_lt _ (by norm_num))]
      simp only [Option.getD_some]
      exact Nat.mod_lt _ (by norm_num)

end StarkedAir.ByteLookup
