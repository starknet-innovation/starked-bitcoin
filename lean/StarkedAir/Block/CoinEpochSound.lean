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
          ((claim t k).code / 2 < h ∨ ((claim t k).code / 2 = h ∧ (claim t k).ctx < t))) ∧ (claim t k).ctx < P := by
  have cs := coin_sat hL hsat hL24
  have key : ∀ t k, ∃ c : Claim, ∀ (tx : Spec.Block.Tx), S.b.txs[t]? = some tx → 1 ≤ t →
      ∀ (i : Spec.Block.TxIn), tx.vin[k]? = some i →
        rowTuple inst pub L (((parts.take t).map List.length).sum + k) =
          tupleOf (FpWalk.gQ pub) i.prevout.hash i.prevout.n c.code c.ser c.ctx ∧
        (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → (c.code / 2 < h ∨ (c.code / 2 = h ∧ c.ctx < t))) ∧ c.ctx < P := by
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
      obtain ⟨-, -, -, -, code, ser, ctx, htu, hcode, hctx, -⟩ :=
        coin_in_tuple hL hsat hL24 S he hon hlen hst hf htg hj hki htx hjdef hq hi
      obtain ⟨t0, q0, tx0, htx0, htxi, hjq0, hq0, -, -⟩ := coin_row_tx hL hsat hL24 S he hon hlen hst hf htg hj
      obtain ⟨hpl0, hpe0⟩ := part_len hf htx0
      obtain ⟨rfl, rfl⟩ := decomp_unique parts hpl hpl0 (by omega) (by omega) (hjdef.symm.trans hjq0)
      refine ⟨⟨code, ser, ((inst 14).main Coin.CTX j).val⟩, fun tx' htx' _ i' hi' => ?_⟩
      rw [htx] at htx'; obtain rfl := Option.some.inj htx'
      rw [hi] at hi'; obtain rfl := Option.some.inj hi'
      have hLb : 2 ^ L ≤ 2 ^ 23 := Nat.pow_le_pow_right (by norm_num) hL24
      have htN : t < 2 ^ 23 := by have := (List.getElem?_eq_some_iff.mp htx).1; have := S.hN25; omega
      refine ⟨?_, fun hc26 hc25 => coin_in_lex hL hsat hL24 hj2 hki hp2 hh htxi htN hcode hc26 hc25,
        show ((inst 14).main Coin.CTX j).val < P from ZMod.val_lt _⟩
      rw [htu]
      unfold tupleOf
      simp only [Coin.cast_val, hctx]
    · exact ⟨default, fun tx htx ht1 i hi => absurd ⟨tx, i, htx, ht1, hi⟩ hv⟩
  choose claim hclaim using key
  exact ⟨claim, fun t tx htx ht1 k i hi => hclaim t k tx htx ht1 i hi⟩

end System

end StarkedAir.Block
