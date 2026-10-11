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

/-! ### Sums over lists, as range sums -/

theorem zipIdx_sum {α : Type} (l : List α) (g : α → ℕ → QM) (c : ℕ) :
    ((l.zipIdx c).map fun p => g p.1 p.2).sum = ∑ k ∈ Finset.range l.length, (match l[k]? with
      | some a => g a (c + k) | none => 0) := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Nat.add_zero, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show x + (c + 1) = c + (x + 1) by omega]

theorem zipIdx_filter_sum {α : Type} (l : List α) (P : α → Bool) (g : α → ℕ → QM) (c : ℕ) :
    (((l.zipIdx c).filter fun p => P p.1).map fun p => g p.1 p.2).sum = ∑ k ∈ Finset.range l.length, (match l[k]? with
      | some a => if P a then g a (c + k) else 0 | none => 0) := by
  induction l generalizing c with
  | nil => simp
  | cons a l ih =>
    rw [List.zipIdx_cons, List.filter_cons, List.length_cons, Finset.sum_range_succ']
    have hs : ∑ x ∈ Finset.range l.length, (match (a :: l)[x + 1]? with
        | some a => if P a then g a (c + (x + 1)) else 0 | none => 0) =
        (((l.zipIdx (c + 1)).filter fun p => P p.1).map fun p => g p.1 p.2).sum := by
      rw [ih]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [List.getElem?_cons_succ, show c + 1 + x = c + (x + 1) by omega]
    rw [hs]
    by_cases hp : P a <;> simp [hp, add_comm]

/-- A sum over created coins, transaction by transaction. -/
theorem created_sum (f : CEv → QM) : ∀ (g : ℕ) (ts : List (Spec.Utxo.Tx Spec.Block.OutPoint Val)),
    ((created g ts).map f).sum = ∑ k ∈ Finset.range ts.length, (match ts[k]? with
      | some t => (t.outs.map fun kv => f (kv.1, kv.2, g + k)).sum | none => 0)
  | g, [] => by simp [created]
  | g, t :: ts => by
    rw [created, Multiset.map_add, Multiset.sum_add, created_sum f (g + 1) ts, List.length_cons,
      Finset.sum_range_succ', add_comm]
    simp only [outsT, Multiset.map_coe, Multiset.sum_coe, List.map_map, List.getElem?_cons_succ,
      List.getElem?_cons_zero, Nat.add_zero]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show g + 1 + x = g + (x + 1) by omega]

theorem spent_sum (f : CEv → QM) : ∀ (ts : List (Spec.Utxo.Tx Spec.Block.OutPoint Val)),
    ((spent ts).map f).sum = (ts.map fun t => (t.ins.map f).sum).sum
  | [] => by simp [spent]
  | t :: ts => by
    rw [spent, Multiset.map_add, Multiset.sum_add, spent_sum f ts, List.map_cons, List.sum_cons]
    simp

/-- Claim `c` is input row `j`'s undo record: the row is an input, its record is URec row `rj`, and the
claim's `serTxOut`, code and creating-transaction index are that record's undo bytes. -/
def ClaimAt (inst : ℕ → Inst) (pub : ℕ → F) (L j : ℕ) (c : Claim) : Prop :=
  (inst 14).main Coin.KI j = 1 ∧ ∃ rj < 2 ^ L, (inst 13).main URec.ON rj = 1 ∧
    (inst 14).main Coin.J j = (inst 13).main URec.J rj ∧
    ∃ u0 : ℕ, (inst 13).main URec.S rj + 7 = (u0 : F) ∧ 7 ≤ u0 ∧ u0 + c.ser.length ≤ (pub 8).val ∧
      c.ser = (List.range c.ser.length).map (fun k => (Ub inst pub).getD (u0 + k) 0) ∧
      c.code = Spec.Block.le ((List.range 4).map fun k => (Ub inst pub).getD (u0 - 7 + k) 0) ∧
      c.ctx = Spec.Block.le ((List.range 3).map fun k => (Ub inst pub).getD (u0 - 3 + k) 0)

theorem le3_lt (f : ℕ → UInt8) : Spec.Block.le ((List.range 3).map f) < 2 ^ 24 := by
  have := UInt8.toNat_lt (f 0); have := UInt8.toNat_lt (f 1); have := UInt8.toNat_lt (f 2)
  simp [Spec.Block.le, List.range_succ]; omega

section System

variable {inst : ℕ → Inst} {pub : ℕ → F} {L : ℕ}
  (hL : ∀ i < 15, (inst i).logSize = L) (hsat : hashSys.SatisfiedExt inst pub []) (hL24 : L ≤ 23)
include hL hsat hL24

/-- **An input's claim is earlier**: with the claim's code below `2^26` and its `ctx` below `2^25`,
`(code / 2, ctx) < (height, t)` lexicographically (the circuit's `ORD`/`OB` check). -/
theorem coin_in_lex {j : ℕ} (hj : j < 2 ^ L) (hki : (inst 14).main Coin.KI j = 1) {h t code : ℕ}
    (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23) (htxi : (inst 14).main Coin.TXI j = (t : F)) (ht : t < 2 ^ 23)
    (hcode : (inst 14).main Coin.CLO j + 65536 * (inst 14).main Coin.CHI j = (code : F)) (hc26 : code < 2 ^ 26)
    (hctx : ((inst 14).main Coin.CTX j).val < 2 ^ 25) :
    code / 2 < h ∨ (code / 2 = h ∧ ((inst 14).main Coin.CTX j).val < t) := by
  have cs := coin_sat hL hsat hL24
  obtain ⟨hc1, hhc, hord0, hord1, -, -, -, -⟩ := Coin.in_spec cs hj hki
  have ek : (Coin.k Coin.KI).eval (2 ^ L) Coin.preCols pub (inst 14).main j = 1 := by rw [Coin.ev_k hj]; exact hki
  have hhb : ∀ i < 3, ((inst 14).main (Coin.HB i) j).val < 256 := by
    intro i hi
    have fam : Coin.lookups.getD (52 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.HB i)) (Coin.k Coin.KI) := by
      interval_cases i <;> rfl
    exact coin_r8 hL hsat hL24 (k := 52 + i) (by omega) (by omega) fam hj ek
  have hob : ∀ i < 3, ((inst 14).main (Coin.OB i) j).val < 256 := by
    intro i hi
    have fam : Coin.lookups.getD (55 + i) ⟨0, .const 0, []⟩ = Coin.r8 (Coin.k (Coin.OB i)) (Coin.k Coin.KI) := by
      interval_cases i <;> rfl
    exact coin_r8 hL hsat hL24 (k := 55 + i) (by omega) (by omega) fam hj ek
  have hb3h := Coin.b3N_lt hhb
  have hb3o := Coin.b3N_lt hob
  have hP := Coin.P_big
  have hHC : (inst 14).main Coin.HC j = ((Coin.b3N (inst 14).main Coin.HB j : ℕ) : F) := by rw [hhc, Coin.b3V_eq]
  set hc := Coin.b3N (inst 14).main Coin.HB j with hcdef
  have cbc := Coin.bool_col cs (c := Coin.CBC) (by simp) hj
  have ord := Coin.bool_col cs (c := Coin.ORD) (by simp) hj
  -- the code is 2·HC + CBC
  have hcodeN : code = 2 * hc + ((inst 14).main Coin.CBC j).val := by
    have hcv : ((inst 14).main Coin.CBC j).val ≤ 1 := by rcases cbc with e | e <;> rw [e] <;> decide
    apply Coin.lift _ (by omega) (by omega)
    push_cast; rw [Coin.cast_val, ← hHC, ← hcode, hc1]
  have hdiv : code / 2 = hc := by
    have hcv : ((inst 14).main Coin.CBC j).val ≤ 1 := by rcases cbc with e | e <;> rw [e] <;> decide
    omega
  rw [hdiv]
  rcases ord with o | o
  · -- same height: an earlier transaction
    obtain ⟨hhe, hob'⟩ := hord0 o
    rw [hHC, hp2] at hhe
    have hhv : hc = h := Coin.lift hhe (by omega) (by omega)
    rw [Coin.b3V_eq, htxi] at hob'
    have := Coin.lift (a := Coin.b3N (inst 14).main Coin.OB j + ((inst 14).main Coin.CTX j).val + 1) (b := t)
      (by push_cast; rw [Coin.cast_val, hob']; ring) (by omega) (by omega)
    right; exact ⟨hhv, by omega⟩
  · -- an earlier height
    have hob' := hord1 o
    rw [Coin.b3V_eq, hHC, hp2] at hob'
    have := Coin.lift (a := Coin.b3N (inst 14).main Coin.OB j + hc + 1) (b := h)
      (by push_cast; rw [hob']; ring) (by omega) (by omega)
    left; omega

/-- **The block's claims.** A claim per (transaction, input) whose tuple is that input row's, earlier when
small, with `ctx` below `P`. -/
theorem block_claims (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23) :
    ∃ claim : ℕ → ℕ → Claim, ∀ (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
      ∀ (k : ℕ) (i : Spec.Block.TxIn), tx.vin[k]? = some i →
        rowTuple inst pub L (((parts.take t).map List.length).sum + k) =
          tupleOf (FpWalk.gQ pub) i.prevout.hash i.prevout.n (claim t k).code (claim t k).ser (claim t k).ctx ∧
        ((claim t k).code < 2 ^ 26 → (claim t k).ctx < 2 ^ 25 →
          ((claim t k).code / 2 < h ∨ ((claim t k).code / 2 = h ∧ (claim t k).ctx < t))) ∧ (claim t k).ctx < 2 ^ 24 ∧
        ClaimAt inst pub L (((parts.take t).map List.length).sum + k) (claim t k) := by
  have cs := coin_sat hL hsat hL24
  have key : ∀ t k, ∃ c : Claim, ∀ (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
      ∀ (i : Spec.Block.TxIn), tx.vin[k]? = some i →
        rowTuple inst pub L (((parts.take t).map List.length).sum + k) =
          tupleOf (FpWalk.gQ pub) i.prevout.hash i.prevout.n c.code c.ser c.ctx ∧
        (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < h ∨ (c.code / 2 = h ∧ c.ctx < t))) ∧ c.ctx < 2 ^ 24 ∧
        ClaimAt inst pub L (((parts.take t).map List.length).sum + k) c := by
    intro t k
    by_cases hv : ∃ tx i, S.b.txs[t]? = some tx ∧ 1 ≤ t ∧ tx.vin[k]? = some i
    · obtain ⟨tx, i, htx, ht1, hi⟩ := hv
      obtain ⟨hpl, hpe⟩ := part_len hf htx
      have hk : k < tx.vin.length := (List.getElem?_eq_some_iff.mp hi).1
      set j := ((parts.take t).map List.length).sum + k with hjdef
      have hj : j < e := by
        have := pre_succ parts hpl
        have := pre_mono parts (t := t + 1) (t' := parts.length) (by omega) le_rfl
        have hft := fields_tagged hL hsat hL24 S
        rw [htg] at hft
        have he' : e = (parts.map List.length).sum := by rw [hlen, ← Spec.Block.tagParts_length 0, hft, List.length_map]
        have htot : ((parts.take parts.length).map List.length).sum = (parts.map List.length).sum := by
          rw [List.take_length]
        omega
      have hj2 : j < 2 ^ L := by omega
      have hq : k < tx.vin.length + tx.vout.length := by omega
      have hki := (coin_kind_pos hL hsat hL24 S he hon hlen hst hf htg hj htx hjdef hq).2.1.mpr ⟨hk, ht1⟩
      obtain ⟨rj, hrj, honj, hJ, code, ser, ctx, htu, hcode, hctx, u0, hu0, hu07, hu0l, hser, hcodeb, hctxb⟩ :=
        coin_in_tuple hL hsat hL24 S he hon hlen hst hf htg hj hki htx hjdef hq hi
      obtain ⟨t0, q0, tx0, htx0, htxi, hjq0, hq0, -, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
      obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
      obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjdef.symm.trans hjq0)
      have hc24 : ctx < 2 ^ 24 := by rw [hctxb]; exact le3_lt _
      have hcv : ((inst 14).main Coin.CTX j).val = ctx := by
        rw [hctx, ZMod.val_natCast_of_lt (lt_of_lt_of_le hc24 (by unfold P; norm_num))]
      refine ⟨⟨code, ser, ctx⟩, fun tx' htx' _ i' hi' => ?_⟩
      rw [htx] at htx'; obtain rfl := Option.some.inj htx'
      rw [hi] at hi'; obtain rfl := Option.some.inj hi'
      have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
      have htN : t < 2 ^ 23 := by have := (List.getElem?_eq_some_iff.mp htx).1; have := S.hN25; omega
      refine ⟨htu, fun hc26 hc25 => ?_, hc24, hki, rj, hrj, honj, hJ, u0, hu0, hu07, hu0l, hser, hcodeb, hctxb⟩
      have := coin_in_lex hL hsat hL24 hj2 hki hp2 hh htxi htN hcode hc26 (by rw [hcv]; exact hc25)
      rwa [hcv] at this
    · exact ⟨default, fun tx htx ht1 i hi => absurd ⟨tx, i, htx, ht1, hi⟩ hv⟩
  choose claim hclaim using key
  exact ⟨claim, fun t tx htx ht1 k i hi => hclaim t k tx htx ht1 i hi⟩

/-- **The block's partial sum, as epoch events.** With a claim function giving each input row's tuple,
the public partial sum is the block's created events' `1/(z − φ(encE))` minus its spent events'. -/
theorem block_event_sum (S : Setup inst pub L) {e : ℕ} (he : e < 2 ^ L)
    (hon : ∀ j < 2 ^ L, Coin.onV (inst 14).main j = 1 ↔ j < e) (hlen : e = (ioRows inst S.m).length)
    (hst : ∀ j < e, (inst 14).main Coin.START j = (inst 1).main Fields.START ((ioRows inst S.m).getD j 0))
    {parts : List (List Spec.Block.Tok)} (hf : List.Forall₂ Spec.Block.IoTx S.b.txs parts)
    (htg : Spec.Block.tagged 0 (Fields.toksFrom (inst 1).main (Rb inst pub) S.m 0) = Spec.Block.tagParts 0 parts)
    {h : ℕ} (hp2 : pub 2 = (h : F)) (hh : h < 2 ^ 23) {lost : Bool} (hlost : pub Coin.PUB_LOST = if lost then 1 else 0)
    (N : ℕ → ℕ) (claim : ℕ → ℕ → Claim)
    (hcl : ∀ (t : ℕ) (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
      ∀ (k : ℕ) (i : Spec.Block.TxIn), tx.vin[k]? = some i →
        rowTuple inst pub L (((parts.take t).map List.length).sum + k) =
          tupleOf (FpWalk.gQ pub) i.prevout.hash i.prevout.n (claim t k).code (claim t k).ser (claim t k).ctx) :
    let F' := fun ev : CEv => (RunSum.pQ pub Coin.PUB_Z - phiOf pub (encE N (FpWalk.gQ pub) ev))⁻¹
    let B : BlockC := ⟨h, S.b.txs, lost, claim⟩
    RunSum.pQ pub Coin.PUB_S = ((created (N h) (blockTxs N B)).map F').sum - ((spent (blockTxs N B)).map F').sum := by
  intro F' B
  rw [coin_block_sum hL hsat hL24 S he hon hlen hst hf htg hp2 hh hlost, created_sum, spent_sum,
    blockTxs_length]
  have hsp : ((blockTxs N B).map fun t => (t.ins.map F').sum).sum = ∑ t ∈ Finset.range S.b.txs.length,
      (match S.b.txs[t]? with | some tx => ((txIns N B t tx).map F').sum | none => 0) := by
    unfold blockTxs
    rw [List.map_map]
    exact zipIdx_sum S.b.txs (fun tx t => ((txIns N B t tx).map F').sum) 0 |>.trans (Finset.sum_congr rfl fun x _ => by cases S.b.txs[x]? <;> simp)
  rw [hsp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hbt : (blockTxs N B)[t]? = (S.b.txs[t]?).map fun tx => (⟨txIns N B t tx, txOuts B t tx⟩ : Spec.Utxo.Tx _ _) := by
    simp [blockTxs, List.getElem?_zipIdx]
    cases S.b.txs[t]? <;> rfl
  rw [hbt]
  cases htx : S.b.txs[t]? with
  | none => simp [blockTerm, htx]
  | some tx =>
    simp only [Option.map_some]
    rw [(part_len hf htx).2, Finset.sum_range_add, sub_eq_add_neg, add_comm]
    congr 1
    · -- the outputs
      have hr : ((txOuts B t tx).map fun kv => F' (kv.1, kv.2, N h + t)).sum = ∑ k ∈ Finset.range tx.vout.length,
          (match tx.vout[k]? with
            | some o => if live lost t o then F' (⟨Spec.Block.txid tx, k⟩, (codeOf h t, Spec.Block.serTxOut o), N h + t) else 0
            | none => 0) := by
        simp only [txOuts, List.map_map]
        exact (zipIdx_filter_sum tx.vout (live lost t) (fun o k =>
          F' (⟨Spec.Block.txid tx, k⟩, (codeOf h t, Spec.Block.serTxOut o), N h + t)) 0).trans
          (Finset.sum_congr rfl fun x _ => by cases tx.vout[x]? <;> simp)
      rw [hr]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [List.getElem?_eq_getElem hk']
      simp only [blockTerm, htx, if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left, List.getElem?_eq_getElem hk']
      have hF : F' (⟨Spec.Block.txid tx, k⟩, (codeOf h t, Spec.Block.serTxOut tx.vout[k]), N h + t) =
          (RunSum.pQ pub Coin.PUB_Z - phiOf pub (tupleOf (FpWalk.gQ pub) (Spec.Block.txid tx) k (codeOf h t)
            (Spec.Block.serTxOut tx.vout[k]) t))⁻¹ := by
        simp only [F', encE, codeOf_div, Nat.add_sub_cancel_left]
      rw [hF, show live lost t tx.vout[k] = (!Spec.Coins.unspendable tx.vout[k] && !(t == 0 && lost)) from rfl]
      rfl
    · -- the inputs
      by_cases ht0 : t = 0
      · subst ht0
        rw [Finset.sum_eq_zero (fun q hq => by simp [blockTerm, htx, not_le.mpr (Finset.mem_range.mp hq)])]
        simp [txIns]
      · have ht1 : 1 ≤ t := by omega
        have hr : ((txIns N B t tx).map F').sum = ∑ k ∈ Finset.range tx.vin.length, (match tx.vin[k]? with
            | some i => F' (i.prevout, ((claim t k).code, (claim t k).ser), N ((claim t k).code / 2) + (claim t k).ctx)
            | none => 0) := by
          simp only [txIns, if_neg ht0, List.map_map]
          exact (zipIdx_sum tx.vin (fun i k => F' (i.prevout, ((claim t k).code, (claim t k).ser),
            N ((claim t k).code / 2) + (claim t k).ctx)) 0).trans
            (Finset.sum_congr rfl fun x _ => by cases tx.vin[x]? <;> simp)
        rw [hr, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun q hq => ?_
        have hq' := Finset.mem_range.mp hq
        rw [List.getElem?_eq_getElem hq']
        simp only [blockTerm, htx, if_neg (not_le.mpr hq'), if_pos ht1]
        rw [hcl t tx htx ht1 q _ (List.getElem?_eq_getElem hq')]
        simp only [F', encE, Nat.add_sub_cancel_left]

end System

/-! ### The epoch sum -/

/-- An event's fraction at `(α, z)`: `1/(z − φ)`, `φ` its encoding's polynomial at `α`. -/
noncomputable def efrac (N : ℕ → ℕ) (γ α z : QM) (e : CEv) : QM := (z - (tuplePoly (K := QM) (encE N γ e)).eval α)⁻¹

theorem toList_map_sum {β : Type} (m : Multiset β) (f : β → QM) : (m.toList.map f).sum = (m.map f).sum := by
  conv_rhs => rw [← Multiset.coe_toList m]
  rw [Multiset.map_coe, Multiset.sum_coe]

theorem list_sum_map_neg {β : Type} (l : List β) (f : β → QM) : (l.map fun x => -f x).sum = -(l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem msum_map_neg {β : Type} (m : Multiset β) (f : β → QM) : (m.map fun x => -f x).sum = -(m.map f).sum := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons a m ih => simp only [Multiset.map_cons, Multiset.sum_cons, ih]; ring

theorem spent_append : ∀ (l1 l2 : List (Spec.Utxo.Tx Spec.Block.OutPoint Val)), spent (l1 ++ l2) = spent l1 + spent l2
  | [], l2 => by simp [spent]
  | t :: l1, l2 => by simp only [List.cons_append, spent, spent_append l1 l2, add_assoc]

/-- The block's term in the epoch sum: its created events' fractions minus its spent events'. -/
noncomputable def blockSum (N : ℕ → ℕ) (f : CEv → QM) (B : BlockC) : QM :=
  ((created (N B.h) (blockTxs N B)).map f).sum - ((spent (blockTxs N B)).map f).sum

/-- **The epoch's sums are the blocks' sums**, with each block's creation indices starting at its first
transaction's global position. -/
theorem epoch_sums (N : ℕ → ℕ) (f : CEv → QM) : ∀ (blocks : List BlockC) (g : ℕ),
    (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g + ((blocks.take i).map (·.txs.length)).sum) →
    ((created g (allTxs N blocks)).map f).sum - ((spent (allTxs N blocks)).map f).sum =
      (blocks.map (blockSum N f)).sum
  | [], g, _ => by simp [allTxs, created, spent]
  | B :: bs, g, hpos => by
    have h0 : N B.h = g := by simpa using hpos 0 B rfl
    have ha : allTxs N (B :: bs) = blockTxs N B ++ allTxs N bs := by simp [allTxs]
    have ih := epoch_sums N f bs (g + B.txs.length) (fun i B' hB' => by
      have := hpos (i + 1) B' (by simpa using hB')
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons] at this; omega)
    rw [ha, created_append, spent_append, List.map_cons, List.sum_cons, blockTxs_length, ← ih]
    simp only [Multiset.map_add, Multiset.sum_add, blockSum, h0]
    ring

/-- **A balanced epoch sum is a zero LogUp sum.** If the blocks' sums plus the initial set's fractions
equal the final set's, the epoch's LogUp sum (initial and created `+1`, spent and final `−1`) is zero. -/
theorem epoch_frac_zero (N : ℕ → ℕ) (γ α z : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv)
    (hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum)
    (hsum : (blocks.map (blockSum N (efrac N γ α z))).sum + (init.map (efrac N γ α z)).sum =
      (fin.map (efrac N γ α z)).sum) :
    fracSum (pnEntries (𝕂 := QM) (encE N γ) (init ++ (created g0 (allTxs N blocks)).toList)
      ((spent (allTxs N blocks)).toList ++ fin)) α z = 0 := by
  have hp : ∀ e : CEv, (1 : QM) / ((tuplePoly (K := QM) (encE N γ e)).eval α - z) = -efrac N γ α z e := by
    intro e; unfold efrac; rw [one_div, ← inv_neg, neg_sub]
  have hn : ∀ e : CEv, (-1 : QM) / ((tuplePoly (K := QM) (encE N γ e)).eval α - z) = efrac N γ α z e := by
    intro e; rw [neg_div, hp, neg_neg]
  have hs := epoch_sums N (efrac N γ α z) blocks g0 hpos
  unfold fracSum pnEntries
  simp only [List.map_append, List.map_map, Function.comp_def, List.sum_append, hp, hn, list_sum_map_neg,
    toList_map_sum, msum_map_neg]
  linear_combination -hs - hsum

/-- The epoch's LogUp entries: initial and created `+1`, spent and final `−1`. -/
noncomputable def epochPN (N : ℕ → ℕ) (γ : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv) :
    List (Entry QM) :=
  pnEntries (𝕂 := QM) (encE N γ) (init ++ (created g0 (allTxs N blocks)).toList) ((spent (allTxs N blocks)).toList ++ fin)

/-- **The epoch balances** outside a bad set of `(α, z)` fixed by the epoch's events: with the encoding
injective on them and fewer than `P` events, a balanced epoch sum gives
`init + created = spent + final` as multisets of events. -/
theorem epoch_balance (N : ℕ → ℕ) (γ : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv) :
    ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys (epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
        2 * (polys (epochPN N γ blocks g0 init fin)).card) * Fintype.card QM ∧
      ∀ az ∉ Bad,
        (∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
          ∀ e' ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
            encE N γ e = encE N γ e' → e = e') →
        init.length + Multiset.card (created g0 (allTxs N blocks)) + Multiset.card (spent (allTxs N blocks)) +
          fin.length < P →
        (∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum) →
        (blocks.map (blockSum N (efrac N γ az.1 az.2))).sum + (init.map (efrac N γ az.1 az.2)).sum =
          (fin.map (efrac N γ az.1 az.2)).sum →
        (init : Multiset CEv) + created g0 (allTxs N blocks) = spent (allTxs N blocks) + fin := by
  obtain ⟨Bad, hcard, hb⟩ := balance_of_sum (𝕂 := QM) (encE N γ) 26 (encE_length N γ)
    (init ++ (created g0 (allTxs N blocks)).toList) ((spent (allTxs N blocks)).toList ++ fin)
  refine ⟨Bad, hcard, fun az haz hinj hlen hpos hsum => ?_⟩
  have h := hb az haz hinj (by simp only [List.length_append, Multiset.length_toList]; omega)
    (epoch_frac_zero N γ az.1 az.2 blocks g0 init fin hpos hsum)
  rw [← Multiset.coe_add, ← Multiset.coe_add, Multiset.coe_toList, Multiset.coe_toList] at h
  exact h

/-- **The epoch runs to the final set.** For `γ` outside the fingerprint bad set of the epoch's byte
strings `S`, then `(α, z)` outside a bad set fixed by the epoch's events: with the events well formed,
the circuit's ordering checks, distinct created outpoints and fewer than `P` events, a balanced epoch sum
means Core's sequential update from the initial set succeeds and ends holding exactly the final set. -/
theorem epoch_coin_run (N : ℕ → ℕ) (γ : QM) (blocks : List BlockC) (g0 : ℕ) (init fin : List CEv)
    {S : Finset (List F)} (hγ : γ ∉ fpBad (𝕂 := QM) S)
    (hwf : ∀ e ∈ init ++ (created g0 (allTxs N blocks)).toList ++ ((spent (allTxs N blocks)).toList ++ fin),
      WFE N e ∧ bytesF e ∈ S)
    (hpos : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → N B.h = g0 + ((blocks.take i).map (·.txs.length)).sum)
    (hinc : ∀ (i i' : ℕ) (B B' : BlockC), blocks[i]? = some B → blocks[i']? = some B' → (B.h < B'.h ↔ i < i'))
    (hbnd : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25)
    (hlex : ∀ (i : ℕ) (B : BlockC), blocks[i]? = some B → ∀ (t : ℕ) (tx : Spec.Block.Tx), B.txs[t]? = some tx →
      ∀ e ∈ txIns N B t tx, ∃ c : Claim, e = (e.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
        (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < B.h ∨ (c.code / 2 = B.h ∧ c.ctx < t))))
    (hinit : ∀ e ∈ init, e.2.2 < g0)
    (hnd : (((init : Multiset CEv) + created g0 (allTxs N blocks)).map Prod.fst).Nodup) :
    ∃ Bad : Finset (QM × QM), Bad.card ≤ ((polys (epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
        2 * (polys (epochPN N γ blocks g0 init fin)).card) * Fintype.card QM ∧
      ∀ az ∉ Bad,
        init.length + Multiset.card (created g0 (allTxs N blocks)) + Multiset.card (spent (allTxs N blocks)) +
          fin.length < P →
        (blocks.map (blockSum N (efrac N γ az.1 az.2))).sum + (init.map (efrac N γ az.1 az.2)).sum =
          (fin.map (efrac N γ az.1 az.2)).sum →
        ∃ m, run g0 (viewOf init) (allTxs N blocks) = some m ∧ ∀ k v j, m k = some (v, j) ↔ (k, v, j) ∈ fin := by
  obtain ⟨Bad, hcard, hb⟩ := epoch_balance N γ blocks g0 init fin
  refine ⟨Bad, hcard, fun az haz hlen hsum => ?_⟩
  have hbal := hb az haz (fun e he e' he' h =>
    encE_inj N hγ (hwf e he).1 (hwf e' he').1 (hwf e he).2 (hwf e' he').2 h) hlen hpos hsum
  exact epoch_run N blocks g0 init fin hpos hinc hbnd hlex hinit hnd hbal

end StarkedAir.Block
