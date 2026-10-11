/-
**The coin proof's epoch layer (M3b, layer 5), circuit side.** The spec encoding of an epoch coin event is
the coin component's tuple (`encE`: `tupleOf` with `ctx = index − N(code / 2)`), and with the public
weights `αₖ = αᵏ` a tuple's fingerprint `φ` is its `tuplePoly` at `α` (`phiOf_poly`), the polynomial the
epoch theorems use.
-/
import StarkedAir.Block.CoinEvents
import StarkedAir.Spec.CoinEpoch

namespace StarkedAir.Block

open StarkedAir StarkedAir.Spec.CoinEpoch StarkedAir.Spec.Utxo Polynomial StarkedAir.LogUpSZ
open StarkedAir.Spec.QM31 (QM toQ emb coordsOf toQ_coordsOf coordsOf_toQ)

/-- The spec encoding of an epoch coin event. -/
noncomputable def encE (N : ℕ → ℕ) (γ : QM) (e : CEv) : List F :=
  tupleOf γ e.1.hash e.1.n e.2.1.1 e.2.1.2 (e.2.2 - N (e.2.1.1 / 2))

theorem encE_length (N : ℕ → ℕ) (γ : QM) (e : CEv) : (encE N γ e).length = 26 := tupleOf_length _ _ _ _ _ _

theorem list_sum_range_qm (f : ℕ → QM) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n + 1 => by rw [List.range_succ, List.map_append, List.sum_append, list_sum_range_qm f n, Finset.sum_range_succ]; simp

/-- **The fingerprint is the tuple polynomial at `α`** when the public weights are `αᵏ`. -/
theorem phiOf_poly (pub : ℕ → F) (α : QM) (hα : ∀ k < Coin.W, RunSum.pQ pub (Coin.PUB_ALPHA k) = α ^ k)
    (tu : List F) (htu : tu.length = Coin.W) : phiOf pub tu = (tuplePoly (K := QM) tu).eval α := by
  unfold phiOf tuplePoly
  rw [list_sum_range_qm, eval_finset_sum, htu]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hα k (Finset.mem_range.mp hk), eval_mul, eval_C, eval_pow, eval_X]
  show α ^ k * emb (tu.getD k 0) = (algebraMap F QM (tu.getD k 0)) * α ^ k
  rw [mul_comm]; rfl

/-- **Txid limbs determine a 32-byte txid.** -/
theorem txidLimb_inj {h h' : Spec.Block.Bytes} (hl : h.length = 32) (hl' : h'.length = 32)
    (he : ∀ i < 16, txidLimb h i = txidLimb h' i) : h = h' := by
  apply List.ext_getElem (by rw [hl, hl'])
  intro p hp hp'
  have hp32 : p < 32 := by omega
  have b1 := UInt8.toNat_lt (h.getD (4 * (p / 4) + 3) 0)
  have b2 := UInt8.toNat_lt (h.getD (4 * (p / 4) + 2) 0)
  have b3 := UInt8.toNat_lt (h.getD (4 * (p / 4) + 1) 0)
  have b4 := UInt8.toNat_lt (h.getD (4 * (p / 4)) 0)
  have c1 := UInt8.toNat_lt (h'.getD (4 * (p / 4) + 3) 0)
  have c2 := UInt8.toNat_lt (h'.getD (4 * (p / 4) + 2) 0)
  have c3 := UInt8.toNat_lt (h'.getD (4 * (p / 4) + 1) 0)
  have c4 := UInt8.toNat_lt (h'.getD (4 * (p / 4)) 0)
  have e0 := he (2 * (p / 4)) (by omega)
  have e1 := he (2 * (p / 4) + 1) (by omega)
  simp only [txidLimb, show (2 * (p / 4)) % 2 = 0 by omega, show (2 * (p / 4) + 1) % 2 = 1 by omega,
    show 2 * (p / 4) / 2 = p / 4 by omega, show (2 * (p / 4) + 1) / 2 = p / 4 by omega, if_true,
    one_ne_zero, if_false] at e0 e1
  have q : p = 4 * (p / 4) ∨ p = 4 * (p / 4) + 1 ∨ p = 4 * (p / 4) + 2 ∨ p = 4 * (p / 4) + 3 := by omega
  have key : (h.getD p 0).toNat = (h'.getD p 0).toNat := by
    rcases q with q | q | q | q <;> rw [q] <;> omega
  rw [← List.getD_eq_getElem _ 0 hp, ← List.getD_eq_getElem _ 0 hp']
  exact UInt8.toNat_inj.mp key

theorem limbs_inj {n m : ℕ} (hn : n < 2 ^ 32) (hm : m < 2 ^ 32)
    (h1 : ((n % 65536 : ℕ) : F) = ((m % 65536 : ℕ) : F)) (h2 : ((n / 65536 : ℕ) : F) = ((m / 65536 : ℕ) : F)) : n = m := by
  have a := natCast_inj_of_lt (by unfold P; omega) (by unfold P; omega) h1
  have b := natCast_inj_of_lt (lt_of_lt_of_le (show n / 65536 < 2 ^ 16 by omega) (by unfold P; norm_num))
    (lt_of_lt_of_le (show m / 65536 < 2 ^ 16 by omega) (by unfold P; norm_num)) h2
  omega

theorem txidLimb_lt (b : Spec.Block.Bytes) (i : ℕ) : txidLimb b i < 2 ^ 17 := by
  unfold txidLimb
  dsimp only
  split_ifs
  · have := UInt8.toNat_lt (b.getD (4 * (i / 2) + 3) 0); have := UInt8.toNat_lt (b.getD (4 * (i / 2) + 2) 0); omega
  · have := UInt8.toNat_lt (b.getD (4 * (i / 2) + 1) 0); have := UInt8.toNat_lt (b.getD (4 * (i / 2)) 0); omega

/-- An event's `serTxOut` as field values. -/
def bytesF (e : CEv) : List F := e.2.1.2.map fun b => ((b.toNat : ℕ) : F)

/-- A well-formed event: its fields fit the tuple's limbs. -/
def WFE (N : ℕ → ℕ) (e : CEv) : Prop :=
  e.1.hash.length = 32 ∧ e.1.n < 2 ^ 32 ∧ e.2.1.1 < 2 ^ 32 ∧ N (e.2.1.1 / 2) ≤ e.2.2 ∧
    e.2.2 - N (e.2.1.1 / 2) < P ∧ e.2.1.2.length < P

theorem horner_bytesF (γ : QM) (e : CEv) :
    FpWalk.horner γ (e.2.1.2.map fun b => emb ((b.toNat : ℕ) : F)) = hornerF γ (bytesF e) := by
  unfold FpWalk.horner hornerF bytesF
  rw [List.foldl_map, List.foldl_map]; rfl

/-- **The encoding is injective** on well-formed events whose bytes `γ` separates. -/
theorem encE_inj (N : ℕ → ℕ) {S : Finset (List F)} {γ : QM} (hγ : γ ∉ fpBad (𝕂 := QM) S) {e e' : CEv}
    (hw : WFE N e) (hw' : WFE N e') (hs : bytesF e ∈ S) (hs' : bytesF e' ∈ S) (he : encE N γ e = encE N γ e') : e = e' := by
  obtain ⟨h32, hn, hc, hix, hct, hsl⟩ := hw
  obtain ⟨h32', hn', hc', hix', hct', hsl'⟩ := hw'
  unfold encE tupleOf at he
  simp only [List.append_assoc, List.cons_append, List.nil_append] at he
  have hlen16 : ((List.range 16).map fun i => ((txidLimb e.1.hash i : ℕ) : F)).length =
      ((List.range 16).map fun i => ((txidLimb e'.1.hash i : ℕ) : F)).length := by simp
  obtain ⟨hl, hr⟩ := List.append_inj he hlen16
  simp only [List.cons.injEq] at hr
  obtain ⟨hn1, hn2, hc1, hc2, ha, hb, hcc, hd, hsl1, hctx⟩ := hr
  -- the txid
  have hh : e.1.hash = e'.1.hash := by
    apply txidLimb_inj h32 h32'
    intro i hi
    have := congrArg (fun l => l[i]?) hl
    simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some, Option.some.injEq] at this
    have b1 := txidLimb_lt e.1.hash i
    have b2 := txidLimb_lt e'.1.hash i
    exact natCast_inj_of_lt (lt_of_lt_of_le b1 (by unfold P; norm_num)) (lt_of_lt_of_le b2 (by unfold P; norm_num)) this
  have hnn : e.1.n = e'.1.n := limbs_inj hn hn' hn1 hn2
  have hcode : e.2.1.1 = e'.2.1.1 := limbs_inj hc hc' hc1 hc2
  -- the bytes
  have hlen : e.2.1.2.length = e'.2.1.2.length := natCast_inj_of_lt hsl hsl' hsl1
  have hfp : FpWalk.horner γ (e.2.1.2.map fun b => emb ((b.toNat : ℕ) : F)) =
      FpWalk.horner γ (e'.2.1.2.map fun b => emb ((b.toNat : ℕ) : F)) := by
    rw [← toQ_coordsOf (FpWalk.horner γ (e.2.1.2.map fun b => emb ((b.toNat : ℕ) : F))),
      ← toQ_coordsOf (FpWalk.horner γ (e'.2.1.2.map fun b => emb ((b.toNat : ℕ) : F)))]
    congr 1; exact Circuit.Q.ext ha hb hcc hd
  rw [horner_bytesF, horner_bytesF] at hfp
  have hbF := fp_separates hγ hs hs' (by simp [bytesF, hlen]) hfp
  have hser : e.2.1.2 = e'.2.1.2 := by
    apply List.ext_getElem hlen
    intro k h1 h2
    have := congrArg (fun l => l[k]?) hbF
    simp only [bytesF, List.getElem?_map, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.map_some,
      Option.some.injEq] at this
    exact UInt8.toNat_inj.mp (natCast_inj_of_lt (by have := UInt8.toNat_lt (e.2.1.2[k]); unfold P; omega)
      (by have := UInt8.toNat_lt (e'.2.1.2[k]); unfold P; omega) this)
  -- the index
  have hct2 := natCast_inj_of_lt hct hct' hctx.1
  rw [hcode] at hct2 hix
  have hidx : e.2.2 = e'.2.2 := by omega
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, c1⟩ := e
  obtain ⟨⟨a1', a2'⟩, ⟨b1', b2'⟩, c1'⟩ := e'
  simp only at hh hnn hcode hser hidx
  subst hh hnn hcode hser hidx; rfl

end StarkedAir.Block
