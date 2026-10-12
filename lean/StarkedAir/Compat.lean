import StarkedAir.Block.AggregateBlocks
import StarkedAir.Block.AncSound
import StarkedAir.Block.B2Link
import StarkedAir.Block.B2MsgSound
import StarkedAir.Block.BlockAnc
import StarkedAir.Block.BlockSound
import StarkedAir.Block.Bytes
import StarkedAir.Block.CoinClaims
import StarkedAir.Block.CoinEpochCore
import StarkedAir.Block.CoinEpochSound
import StarkedAir.Block.CoinWFE
import StarkedAir.Block.ExtSum
import StarkedAir.Block.FieldsSound
import StarkedAir.Block.FpWalk
import StarkedAir.Block.MerkleLink
import StarkedAir.Block.RunSum
import StarkedAir.Block.ShaSound
import StarkedAir.Block.URec
import StarkedAir.Block.WMerkleLink
import StarkedAir.Circuit.Balance
import StarkedAir.Circuit.BlakeSound
import StarkedAir.Circuit.BlockCtx
import StarkedAir.Circuit.BlockLeaf
import StarkedAir.Circuit.BlockNode
import StarkedAir.Circuit.BlockRec
import StarkedAir.Circuit.BlockTree
import StarkedAir.Circuit.Channel
import StarkedAir.Circuit.Composition
import StarkedAir.Circuit.CompositionLogUp
import StarkedAir.Circuit.CompositionSound
import StarkedAir.Circuit.Deep
import StarkedAir.Circuit.EndToEnd
import StarkedAir.Circuit.HeaderRec
import StarkedAir.Circuit.LeafHash
import StarkedAir.Circuit.Merkle
import StarkedAir.Circuit.NodeSound
import StarkedAir.Circuit.Oods
import StarkedAir.Circuit.Pow
import StarkedAir.Circuit.Statement

/-!
# Compatibility gate for per-component trace sizes (D-045, c1)

Everything proven on `2196ba3` (one shared log size `L`) must stay proven after the generalization to a
per-component size vector. This file is the gate:

1. **Statements.** Each `compat_*` theorem restates, verbatim, the statement of an exported theorem as
   elaborated on `2196ba3` (printed with full names and typed coercions). The statements must not
   change. After the generalization each is proven from the new general theorem at the constant
   vector `fun _ => L` (or still by `exact` where the theorem is untouched).
2. **Definitions.** `pins` lists a structural hash of every non-theorem constant (definitions,
   structures, inductives) that the statements above reach, transitively, as on `2196ba3`. The check
   below fails the build if any of them changes, so no statement can change meaning through a
   definition it mentions. Generalized definitions get new names (`BlockPubOk'`, `StarkSoundV`, …);
   an old one may only be re-pinned together with a proven equality to its old body.
-/

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace StarkedAir.Compat

/-- StarkedAir.Block.BlockPubOk.mtp -/
theorem compat_Block_BlockPubOk_mtp : ∀ {p : ℕ → StarkedAir.F},
  StarkedAir.Block.BlockPubOk p →
    p StarkedAir.Block.Anc.PUB_CSV = 0 ∧ p StarkedAir.Block.Anc.PUB_MLO = 0 ∧ p StarkedAir.Block.Anc.PUB_MHI = 0 ∨
      p StarkedAir.Block.Anc.PUB_CSV = 1 ∧
        ∃ (inst : ℕ → StarkedAir.Inst) (b : StarkedAir.Spec.Block.Blk) (hw : ℕ → ℕ → StarkedAir.Spec.Sha256.Word),
          StarkedAir.Spec.Block.parseBlock (StarkedAir.Block.Rb inst p) = Option.some b ∧
            StarkedAir.Spec.Block.stateBytes (StarkedAir.Spec.Bitcoin.sha256d (hw StarkedAir.Block.Anc.NANC)) =
                StarkedAir.Spec.Block.sha256d b.header ∧
              (∀ (j : ℕ),
                  1 ≤ j →
                    j ≤ StarkedAir.Block.Anc.NANC →
                      StarkedAir.Spec.Bitcoin.prevHash (hw j) = StarkedAir.Spec.Bitcoin.sha256d (hw (j - 1))) ∧
                ZMod.val (p StarkedAir.Block.Anc.PUB_MLO) < 65536 ∧
                  ZMod.val (p StarkedAir.Block.Anc.PUB_MHI) < 65536 ∧
                    StarkedAir.Block.Anc.mtpOf p =
                      StarkedAir.Spec.Bitcoin.medianTimePast
                        (List.map (fun (k : ℕ) => StarkedAir.Spec.Bitcoin.timeOf (hw k))
                            (List.range StarkedAir.Block.Anc.NANC)).reverse :=
  @StarkedAir.Block.BlockPubOk.mtp

/-- StarkedAir.Block.Anc.anc_sound -/
theorem compat_Block_Anc_anc_sound : ∀ {L : ℕ} {pub : ℕ → StarkedAir.F} {main : ℕ → ℕ → StarkedAir.F},
  StarkedAir.Block.Anc.anc.air.Satisfied L pub main →
    8 ≤ L →
      pub StarkedAir.Block.Anc.PUB_CSV = 0 ∧
          pub StarkedAir.Block.Anc.PUB_MLO = 0 ∧ pub StarkedAir.Block.Anc.PUB_MHI = 0 ∨
        pub StarkedAir.Block.Anc.PUB_CSV = 1 ∧
          12 ≤ L ∧
            (∀ j ≤ StarkedAir.Block.Anc.NANC,
                StarkedAir.Spec.Bitcoin.sha256d (StarkedAir.HeaderChain.headerWord main j) =
                  StarkedAir.HeaderChain.hashAt main j) ∧
              (∀ (j : ℕ),
                  1 ≤ j →
                    j ≤ StarkedAir.Block.Anc.NANC →
                      StarkedAir.Spec.Bitcoin.prevHash (StarkedAir.HeaderChain.headerWord main j) =
                        StarkedAir.HeaderChain.hashAt main (j - 1)) ∧
                (∀ w < 8,
                    ∀ h ≤ 1,
                      pub (StarkedAir.Block.Anc.PUB_HASH + 2 * w + h) =
                        (↑(StarkedAir.Sha256.half16
                              (StarkedAir.Spec.Bitcoin.stateWord
                                (StarkedAir.HeaderChain.hashAt main StarkedAir.Block.Anc.NANC) w)
                              h) :
                          StarkedAir.F)) ∧
                  (ZMod.val (pub StarkedAir.Block.Anc.PUB_MLO) < 65536 ∧
                      ZMod.val (pub StarkedAir.Block.Anc.PUB_MHI) < 65536) ∧
                    StarkedAir.Block.Anc.mtpOf pub =
                      StarkedAir.Spec.Bitcoin.medianTimePast
                        (List.map
                            (fun (k : ℕ) => StarkedAir.Spec.Bitcoin.timeOf (StarkedAir.HeaderChain.headerWord main k))
                            (List.range StarkedAir.Block.Anc.NANC)).reverse :=
  @StarkedAir.Block.Anc.anc_sound

/-- StarkedAir.Block.commit_sound -/
theorem compat_Block_commit_sound : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 15, (inst i).logSize = L) →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        8 ≤ L →
          ∀ i < 8,
            ∀ h ≤ 1,
              pub (9 + 2 * i + h) = (↑(StarkedAir.Sha256.half16 (StarkedAir.Block.hwords inst pub i) h) : StarkedAir.F) :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.commit_sound (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Block.B2Msg.walker_sound -/
theorem compat_Block_B2Msg_walker_sound : ∀ {n : ℕ} {pub : ℕ → StarkedAir.F} {M : ℕ → ℕ → StarkedAir.F},
  (∀ r < n,
      ∀ c ∈ StarkedAir.Block.B2Msg.constraints, StarkedAir.Expr.eval n StarkedAir.Block.B2Msg.preCols pub M r c = 0) →
    0 < n →
      n ≤ 2 ^ 25 →
        ∀ (S : StarkedAir.Spec.Block.Bytes),
          pub StarkedAir.Block.Undo.PUB_LEN = (↑(List.length S) : StarkedAir.F) →
            List.length S < StarkedAir.P →
              (∀ r < n,
                  ∀ j < 4,
                    M (StarkedAir.Block.B2Msg.A j) r = 1 →
                      ∃ (q : ℕ),
                        M StarkedAir.Block.B2Msg.POS r + (↑j : StarkedAir.F) = (↑q : StarkedAir.F) ∧
                          q < List.length S ∧
                            ZMod.val (M (StarkedAir.Block.B2Msg.B j) r) = StarkedAir.Block.B2Msg.sbyte S q) →
                ∀ r < n,
                  M StarkedAir.Block.B2Msg.ON r = 1 →
                    ∃ (b : ℕ),
                      M StarkedAir.Block.B2Msg.BLK r = (↑b : StarkedAir.F) ∧
                        b < StarkedAir.Block.B2Msg.nbOf (List.length S) ∧
                          (∀ j < 4,
                              ZMod.val (M (StarkedAir.Block.B2Msg.B j) r) =
                                StarkedAir.Block.B2Msg.sbyte S (64 * b + 4 * (r % 16) + j)) ∧
                            (r % 16 = 0 →
                              (M StarkedAir.Block.B2Msg.LASTF r = 1 ↔
                                  b + 1 = StarkedAir.Block.B2Msg.nbOf (List.length S)) ∧
                                (M StarkedAir.Block.B2Msg.LASTF r = 0 ∨ M StarkedAir.Block.B2Msg.LASTF r = 1) ∧
                                  M StarkedAir.Block.B2Msg.T r =
                                    (↑(if b + 1 = StarkedAir.Block.B2Msg.nbOf (List.length S) then List.length S
                                        else 64 * (b + 1)) :
                                      StarkedAir.F)) :=
  @StarkedAir.Block.B2Msg.walker_sound

/-- StarkedAir.Block.blockSys_sat -/
theorem compat_Block_blockSys_sat : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F},
  StarkedAir.Block.blockSys.SatisfiedExt inst pub [] →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] ∧
      StarkedAir.Block.Anc.anc.air.Satisfied (inst 15).logSize pub (inst 15).main :=
  @StarkedAir.Block.blockSys_sat

/-- StarkedAir.Block.block_mtp -/
theorem compat_Block_block_mtp : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 16, (inst i).logSize = L) →
    StarkedAir.Block.blockSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        8 ≤ L →
          pub StarkedAir.Block.Anc.PUB_CSV = 0 ∧
              pub StarkedAir.Block.Anc.PUB_MLO = 0 ∧ pub StarkedAir.Block.Anc.PUB_MHI = 0 ∨
            pub StarkedAir.Block.Anc.PUB_CSV = 1 ∧
              ∃ (b : StarkedAir.Spec.Block.Blk) (hw : ℕ → ℕ → StarkedAir.Spec.Sha256.Word),
                StarkedAir.Spec.Block.parseBlock (StarkedAir.Block.Rb inst pub) = Option.some b ∧
                  StarkedAir.Spec.Block.stateBytes (StarkedAir.Spec.Bitcoin.sha256d (hw StarkedAir.Block.Anc.NANC)) =
                      StarkedAir.Spec.Block.sha256d b.header ∧
                    (∀ (j : ℕ),
                        1 ≤ j →
                          j ≤ StarkedAir.Block.Anc.NANC →
                            StarkedAir.Spec.Bitcoin.prevHash (hw j) = StarkedAir.Spec.Bitcoin.sha256d (hw (j - 1))) ∧
                      ZMod.val (pub StarkedAir.Block.Anc.PUB_MLO) < 65536 ∧
                        ZMod.val (pub StarkedAir.Block.Anc.PUB_MHI) < 65536 ∧
                          StarkedAir.Block.Anc.mtpOf pub =
                            StarkedAir.Spec.Bitcoin.medianTimePast
                              (List.map (fun (k : ℕ) => StarkedAir.Spec.Bitcoin.timeOf (hw k))
                                  (List.range StarkedAir.Block.Anc.NANC)).reverse :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.block_mtp (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Block.block_sound -/
theorem compat_Block_block_sound : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 15, (inst i).logSize = L) →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        8 ≤ L →
          ∀ {c : StarkedAir.Spec.Block.Ctx},
            c.height < 2 ^ 23 →
              c.prevMtp < 2 ^ 32 →
                StarkedAir.Block.BlockPubs c pub →
                  ∃ (b : StarkedAir.Spec.Block.Blk),
                    StarkedAir.Spec.Block.parseBlock (StarkedAir.Block.Rb inst pub) = Option.some b ∧
                      ((∀ t ∈ b.txs,
                          StarkedAir.Spec.Block.nodupBy
                              (List.map (fun (x : StarkedAir.Spec.Block.TxIn) => x.prevout) t.vin) =
                            Bool.true) →
                        StarkedAir.Spec.Block.checkBlock c (StarkedAir.Block.Rb inst pub) = Option.none) :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.block_sound (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Block.yield_sound -/
theorem compat_Block_yield_sound : ∀ {n : ℕ} {pub : ℕ → StarkedAir.F} {main : ℕ → ℕ → StarkedAir.F},
  (∀ r < n, ∀ c ∈ StarkedAir.Block.constraints, StarkedAir.Expr.eval n StarkedAir.Block.preCols pub main r c = 0) →
    n < StarkedAir.P →
      ∀ {r : ℕ},
        r < n →
          StarkedAir.Expr.eval n StarkedAir.Block.preCols pub main r
                ((StarkedAir.Sha256.col StarkedAir.Block.ACTIVE).mul (StarkedAir.Sha256.col StarkedAir.Block.MULT)) ≠
              0 →
            r < ZMod.val (pub 0) ∧
              List.map (StarkedAir.Expr.eval n StarkedAir.Block.preCols pub main r)
                  [StarkedAir.Sha256.col StarkedAir.Block.POS, StarkedAir.Sha256.col StarkedAir.Block.BYTE] =
                [(↑r : StarkedAir.F), main StarkedAir.Block.BYTE r] :=
  @StarkedAir.Block.yield_sound

/-- StarkedAir.Block.tx_claims_ok -/
theorem compat_Block_tx_claims_ok : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 15, (inst i).logSize = L) →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        ∀ (S : StarkedAir.Block.Setup inst pub L) {e : ℕ},
          e < 2 ^ L →
            (∀ j < 2 ^ L, StarkedAir.Block.Coin.onV (inst 14).main j = 1 ↔ j < e) →
              e = (StarkedAir.Block.ioRows inst S.m).length →
                (∀ j < e,
                    (inst 14).main StarkedAir.Block.Coin.START j =
                      (inst 1).main StarkedAir.Block.Fields.START ((StarkedAir.Block.ioRows inst S.m).getD j 0)) →
                  ∀ {parts : List (List StarkedAir.Spec.Block.Tok)},
                    List.Forall₂ StarkedAir.Spec.Block.IoTx S.b.txs parts →
                      StarkedAir.Spec.Block.tagged 0
                            (StarkedAir.Block.Fields.toksFrom (inst 1).main (StarkedAir.Block.Rb inst pub) S.m 0) =
                          StarkedAir.Spec.Block.tagParts 0 parts →
                        (∀ (t' : ℕ) (tx' : StarkedAir.Spec.Block.Tx),
                            S.b.txs[t']? = Option.some tx' → tx'.vin ≠ [] ∧ tx'.vout ≠ []) →
                          ∀ {h : ℕ},
                            pub 2 = (↑h : StarkedAir.F) →
                              h < 2 ^ 23 →
                                ∀ (N : ℕ → ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                  B.h = h →
                                    ∀ {t : ℕ} {tx : StarkedAir.Spec.Block.Tx},
                                      S.b.txs[t]? = Option.some tx →
                                        1 ≤ t →
                                          (∀ k < tx.vin.length,
                                              StarkedAir.Block.ClaimAt inst pub L
                                                ((List.map List.length (List.take t parts)).sum + k) (B.claim t k)) →
                                            (∀ k < tx.vin.length,
                                                8 ≤ List.length (B.claim t k).ser ∧
                                                  StarkedAir.Spec.Block.le (List.take 8 (B.claim t k).ser) ≤
                                                      StarkedAir.Block.Fields.MAXHI * 2 ^ 24 +
                                                        StarkedAir.Block.Fields.MAXLO ∧
                                                    (B.claim t k).code < 2 ^ 30) →
                                              StarkedAir.Spec.Coins.outSum tx ≤ StarkedAir.Spec.Block.MAX_MONEY →
                                                StarkedAir.Spec.Coins.ClaimsOK
                                                  (StarkedAir.Spec.CoinEpoch.txcOf N B t tx) :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.tx_claims_ok (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Block.epoch_block_valid -/
theorem compat_Block_epoch_block_valid : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 15, (inst i).logSize = L) →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        8 ≤ L →
          ∀ (S : StarkedAir.Block.Setup inst pub L) {c : StarkedAir.Spec.Block.Ctx},
            c.height < 2 ^ 23 →
              c.prevMtp < 2 ^ 32 →
                StarkedAir.Block.BlockPubs c pub →
                  (∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                      S.b.txs[t]? = Option.some tx →
                        1 ≤ t →
                          StarkedAir.Spec.Block.nodupBy
                              (List.map (fun (x : StarkedAir.Spec.Block.TxIn) => x.prevout) tx.vin) =
                            Bool.true) →
                    StarkedAir.Spec.Block.checkBlock c (StarkedAir.Block.Rb inst pub) = Option.none :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.epoch_block_valid (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Block.epoch_systems_core -/
theorem compat_Block_epoch_systems_core : ∀ (nb : ℕ) (inst : ℕ → ℕ → StarkedAir.Inst) (pub : ℕ → ℕ → StarkedAir.F) (L : ℕ → ℕ),
  (∀ i < nb, ∀ c < 15, (inst i c).logSize = L i) →
    (∀ i < nb, StarkedAir.Block.hashSys.SatisfiedExt (inst i) (pub i) []) →
      (∀ i < nb, L i ≤ 23) →
        ∀ (S : (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)) (h0 : ℕ),
          h0 + nb ≤ 2 ^ 23 →
            (∀ i < nb, pub i 2 = (↑(h0 + i) : StarkedAir.F)) →
              (∀ i < nb,
                  pub i StarkedAir.Block.Coin.PUB_LOST =
                    if StarkedAir.Spec.Coins.bip30Lost (h0 + i) = Bool.true then 1 else 0) →
                ∀ (γ α z : StarkedAir.Spec.QM31.QM),
                  (∀ i < nb, StarkedAir.Block.FpWalk.gQ (pub i) = γ) →
                    (∀ i < nb, StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_Z = z) →
                      (∀ i < nb,
                          ∀ k < StarkedAir.Block.Coin.W,
                            StarkedAir.Block.RunSum.pQ (pub i) (StarkedAir.Block.Coin.PUB_ALPHA k) = α ^ k) →
                        ∃ (blocks : List StarkedAir.Spec.CoinEpoch.BlockC),
                          blocks.length = nb ∧
                            (∀ i < nb,
                                ∃ (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                  blocks[i]? = Option.some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs) ∧
                              (∀ (N : ℕ → ℕ) (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                  blocks[i]? = Option.some B →
                                    ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                      B.txs[t]? = Option.some tx →
                                        ∀ ev ∈ StarkedAir.Spec.CoinEpoch.txIns N B t tx,
                                          ∃ (c : StarkedAir.Spec.CoinEpoch.Claim),
                                            ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
                                              c.code < 2 ^ 32 ∧ c.ctx < 2 ^ 24 ∧ List.length c.ser < StarkedAir.P) ∧
                                ∀ (N : ℕ → ℕ) (g0 : ℕ) (init fin : List StarkedAir.Spec.CoinEpoch.CEv)
                                  (Sb : Finset (List StarkedAir.F)),
                                  γ ∉ StarkedAir.Spec.Utxo.fpBad Sb →
                                    (∀
                                        e ∈
                                          init ++
                                              (StarkedAir.Spec.Utxo.created g0
                                                  (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
                                            ((StarkedAir.Spec.Utxo.spent
                                                  (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
                                              fin),
                                        StarkedAir.Block.WFE N e ∧ StarkedAir.Block.bytesF e ∈ Sb) →
                                      (∀ i < nb, N (h0 + i) = g0 + ∑ i' ∈ Finset.range i, (S i').b.txs.length) →
                                        (∀ e ∈ init, e.2.2 < g0) →
                                          (∀ e ∈ init, StarkedAir.Block.RealVal e.2.1) →
                                            (Multiset.map Prod.fst
                                                  ((↑init : Multiset StarkedAir.Spec.CoinEpoch.CEv) +
                                                    StarkedAir.Spec.Utxo.created g0
                                                      (StarkedAir.Spec.CoinEpoch.allTxs N blocks))).Nodup →
                                              ∃ (Bad : Finset (StarkedAir.Spec.QM31.QM × StarkedAir.Spec.QM31.QM)),
                                                Bad.card ≤
                                                    ((StarkedAir.LogUpSZ.polys
                                                                (StarkedAir.Block.epochPN N γ blocks g0 init
                                                                  fin)).card ^
                                                            2 *
                                                          27 +
                                                        2 *
                                                          (StarkedAir.LogUpSZ.polys
                                                              (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card) *
                                                      Fintype.card StarkedAir.Spec.QM31.QM ∧
                                                  ((α, z) ∉ Bad →
                                                    init.length +
                                                              (StarkedAir.Spec.Utxo.created g0
                                                                  (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                                            (StarkedAir.Spec.Utxo.spent
                                                                (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                                          fin.length <
                                                        StarkedAir.P →
                                                      ∑ i ∈ Finset.range nb,
                                                              StarkedAir.Block.RunSum.pQ (pub i)
                                                                StarkedAir.Block.Coin.PUB_S +
                                                            (List.map (StarkedAir.Block.efrac N γ α z) init).sum =
                                                          (List.map (StarkedAir.Block.efrac N γ α z) fin).sum →
                                                        (∃ (m :
                                                            StarkedAir.Spec.Utxo.View StarkedAir.Spec.Block.OutPoint
                                                              StarkedAir.Spec.CoinEpoch.Val),
                                                            StarkedAir.Spec.Coins.connectTxs
                                                                  (StarkedAir.Spec.Coins.untag
                                                                    (StarkedAir.Spec.Utxo.vmap
                                                                      StarkedAir.Spec.CoinEpoch.coinOfVal
                                                                      (StarkedAir.Spec.Utxo.viewOf init)))
                                                                  (StarkedAir.Spec.CoinEpoch.allTxC N blocks) =
                                                                Option.some
                                                                  (StarkedAir.Spec.Coins.untag
                                                                      (StarkedAir.Spec.Utxo.vmap
                                                                        StarkedAir.Spec.CoinEpoch.coinOfVal m),
                                                                    List.map StarkedAir.Spec.Coins.claimFee
                                                                      (StarkedAir.Spec.CoinEpoch.allTxC N blocks)) ∧
                                                              ∀ (k : StarkedAir.Spec.Block.OutPoint)
                                                                (v : StarkedAir.Spec.CoinEpoch.Val) (j : ℕ),
                                                                m k = Option.some (v, j) ↔ (k, v, j) ∈ fin) ∧
                                                          ∀ i < nb,
                                                            ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                                              (S i).b.txs[t]? = Option.some tx →
                                                                1 ≤ t →
                                                                  StarkedAir.Spec.Block.nodupBy
                                                                      (List.map
                                                                        (fun (x : StarkedAir.Spec.Block.TxIn) =>
                                                                          x.prevout)
                                                                        tx.vin) =
                                                                    Bool.true) :=
  fun nb inst pub L hL hsat hL24 => StarkedAir.Block.epoch_systems_core nb inst pub (fun i _ => L i) hL hsat
    (fun i hi _ _ => hL24 i hi)

/-- StarkedAir.Block.ExtSum.extsum_sound -/
theorem compat_Block_ExtSum_extsum_sound : ∀ {L : ℕ} {pub : ℕ → StarkedAir.F} {M : ℕ → ℕ → StarkedAir.F},
  (∀ r < 2 ^ L,
      ∀ c ∈ StarkedAir.Block.ExtSum.constraints,
        StarkedAir.Expr.eval (2 ^ L) StarkedAir.Block.ExtSum.preCols pub M r c = 0) →
    StarkedAir.Block.ExtSum.pQ pub StarkedAir.Block.ExtSum.PUB_S =
        ∑ r ∈ Finset.range (2 ^ L), StarkedAir.Block.ExtSum.fQ M r ∧
      ∀ r < 2 ^ L,
        (M StarkedAir.Block.ExtSum.MC r = 0 ∨
            M StarkedAir.Block.ExtSum.MC r = 1 ∨ M StarkedAir.Block.ExtSum.MC r = -1) ∧
          (StarkedAir.Block.ExtSum.pQ pub StarkedAir.Block.ExtSum.PUB_Z ≠ StarkedAir.Block.ExtSum.phiQ pub M r →
            StarkedAir.Block.ExtSum.fQ M r =
              StarkedAir.Spec.QM31.emb (M StarkedAir.Block.ExtSum.MC r) /
                (StarkedAir.Block.ExtSum.pQ pub StarkedAir.Block.ExtSum.PUB_Z - StarkedAir.Block.ExtSum.phiQ pub M r)) :=
  @StarkedAir.Block.ExtSum.extsum_sound

/-- StarkedAir.Block.Fields.fields_sound_gen -/
theorem compat_Block_Fields_fields_sound_gen : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  L ≤ 25 →
    (∀ r < 2 ^ L,
        ∀ c ∈ StarkedAir.Block.Fields.constraints,
          StarkedAir.Expr.eval (2 ^ L) StarkedAir.Block.Fields.preCols pub (inst 1).main r c = 0) →
      StarkedAir.Block.bytes.air.Satisfied L pub (inst 0).main →
        (∀ {r : ℕ},
            r < 2 ^ L →
              ∀ {kk : ℕ},
                kk < 7 →
                  StarkedAir.Expr.eval (2 ^ L) StarkedAir.Block.Fields.preCols pub (inst 1).main r
                        (StarkedAir.Block.Fields.lookups.getD kk
                            { rel := 0, mult := StarkedAir.Expr.const 0, vals := [] }).mult =
                      -1 →
                    ∃ r0 < ZMod.val (pub 0),
                      List.map (StarkedAir.Expr.eval (2 ^ L) StarkedAir.Block.Fields.preCols pub (inst 1).main r)
                          (StarkedAir.Block.Fields.lookups.getD kk
                              { rel := 0, mult := StarkedAir.Expr.const 0, vals := [] }).vals =
                        [(↑r0 : StarkedAir.F), (inst 0).main StarkedAir.Block.BYTE r0]) →
          ∃ (b : StarkedAir.Spec.Block.Blk),
            StarkedAir.Spec.Block.parseBlock (StarkedAir.Block.Fields.blockBytes (inst 0).main (ZMod.val (pub 0))) =
              Option.some b :=
  fun {inst pub L} hL => StarkedAir.Block.Fields.fields_sound_gen (inst := inst) (pub := pub) (L := L) (L0 := L) hL

/-- StarkedAir.Block.FpWalk.seg_sound -/
theorem compat_Block_FpWalk_seg_sound : ∀ {n : ℕ} {pub : ℕ → StarkedAir.F} {M : ℕ → ℕ → StarkedAir.F},
  (∀ r < n,
      ∀ c ∈ StarkedAir.Block.FpWalk.constraints, StarkedAir.Expr.eval n StarkedAir.Block.FpWalk.preCols pub M r c = 0) →
    ∀ {e : ℕ},
      e < n →
        M StarkedAir.Block.FpWalk.LST e = 1 →
          ∃ s ≤ e,
            M StarkedAir.Block.FpWalk.FST s = 1 ∧
              (∀ (r : ℕ),
                  s ≤ r →
                    r ≤ e →
                      M StarkedAir.Block.FpWalk.ON r = 1 ∧
                        M StarkedAir.Block.FpWalk.STR r = M StarkedAir.Block.FpWalk.STR e ∧
                          M StarkedAir.Block.FpWalk.SID r = M StarkedAir.Block.FpWalk.SID e ∧
                            M StarkedAir.Block.FpWalk.LEN r = M StarkedAir.Block.FpWalk.LEN e ∧
                              M StarkedAir.Block.FpWalk.POS r =
                                M StarkedAir.Block.FpWalk.POS s + (↑(r - s) : StarkedAir.F)) ∧
                M StarkedAir.Block.FpWalk.REM s = (↑(e - s + 1) : StarkedAir.F) ∧
                  M StarkedAir.Block.FpWalk.LEN e = (↑(e - s + 1) : StarkedAir.F) ∧
                    StarkedAir.Block.FpWalk.hQ M e =
                      StarkedAir.Block.FpWalk.horner (StarkedAir.Block.FpWalk.gQ pub)
                        (List.map (fun (j : ℕ) => StarkedAir.Spec.QM31.emb (M StarkedAir.Block.FpWalk.B (s + j)))
                          (List.range (e - s + 1))) :=
  @StarkedAir.Block.FpWalk.seg_sound

/-- StarkedAir.Block.merkle_sound -/
theorem compat_Block_merkle_sound : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 15, (inst i).logSize = L) →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        ∃ (b : StarkedAir.Spec.Block.Blk),
          StarkedAir.Spec.Block.parseBlock (StarkedAir.Block.Fields.blockBytes (inst 0).main (ZMod.val (pub 0))) =
              Option.some b ∧
            StarkedAir.Spec.Block.merkleRoot (List.map StarkedAir.Spec.Block.txid b.txs) =
              (StarkedAir.Spec.Block.headerMerkle b, Bool.false) :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.merkle_sound (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Block.RunSum.runsum_sound -/
theorem compat_Block_RunSum_runsum_sound : ∀ {n : ℕ} {pub : ℕ → StarkedAir.F} {M : ℕ → ℕ → StarkedAir.F} {fc acc pz ps : ℕ} {phi : StarkedAir.Block.ExtSum.QE}
  {m : StarkedAir.Expr},
  (∀ r < n,
      ∀
        c ∈
          StarkedAir.Block.RunSum.fracC fc pz phi m ++ StarkedAir.Block.RunSum.zeroC fc m ++
              StarkedAir.Block.RunSum.accC fc acc ++
            StarkedAir.Block.RunSum.lastC acc ps,
        StarkedAir.Expr.eval n StarkedAir.Block.RunSum.preCols pub M r c = 0) →
    0 < n →
      StarkedAir.Block.RunSum.pQ pub ps = ∑ r ∈ Finset.range n, StarkedAir.Block.RunSum.cQ M fc r ∧
        ∀ r < n,
          (StarkedAir.Block.RunSum.pQ pub pz -
                  StarkedAir.Spec.QM31.toQ
                    (StarkedAir.Block.ExtSum.QE.ev n StarkedAir.Block.RunSum.preCols pub M r phi)) *
                StarkedAir.Block.RunSum.cQ M fc r =
              StarkedAir.Spec.QM31.emb (StarkedAir.Expr.eval n StarkedAir.Block.RunSum.preCols pub M r m) ∧
            (StarkedAir.Expr.eval n StarkedAir.Block.RunSum.preCols pub M r m = 0 →
              StarkedAir.Block.RunSum.cQ M fc r = 0) :=
  @StarkedAir.Block.RunSum.runsum_sound

/-- StarkedAir.Block.Sha.digest_sound -/
theorem compat_Block_Sha_digest_sound : ∀ {n : ℕ} {pub : ℕ → StarkedAir.F} {M : ℕ → ℕ → StarkedAir.F},
  (∀ r < n, ∀ c ∈ StarkedAir.Block.Sha.constraints, StarkedAir.Expr.eval n StarkedAir.Block.Sha.preCols pub M r c = 0) →
    ∀ {q : ℕ},
      1 ≤ q →
        72 * q + 72 ≤ n →
          M StarkedAir.Block.Sha.DBL (72 * q) = 1 →
            M StarkedAir.Block.Sha.NODE (72 * (q - 1)) = 0 →
              M StarkedAir.Block.Sha.NPAD (72 * (q - 1)) = 0 →
                ∃ q0 < q,
                  M StarkedAir.Block.Sha.FST (72 * q0) = 1 ∧
                    (∀ (j : ℕ), q0 < j → j < q → M StarkedAir.Block.Sha.CHN (72 * j) = 1) ∧
                      (∀ (j : ℕ),
                          q0 ≤ j →
                            j < q →
                              M StarkedAir.Block.Sha.MID (72 * j) = M StarkedAir.Block.Sha.MID (72 * q) ∧
                                M StarkedAir.Block.Sha.BLKI (72 * j) = (↑(j - q0) : StarkedAir.F)) ∧
                        StarkedAir.Sha256.outputAt M (72 * q) =
                          StarkedAir.Spec.Sha256.compress StarkedAir.Spec.Sha256.IV
                            (StarkedAir.Block.Sha.dblBlock (StarkedAir.Block.Sha.fold M (72 * q0) (q - q0))) :=
  @StarkedAir.Block.Sha.digest_sound

/-- StarkedAir.Block.URec.rows_sound -/
theorem compat_Block_URec_rows_sound : ∀ {n : ℕ} {pub : ℕ → StarkedAir.F} {M : ℕ → ℕ → StarkedAir.F},
  (∀ r < n,
      ∀ c ∈ StarkedAir.Block.URec.constraints, StarkedAir.Expr.eval n StarkedAir.Block.URec.preCols pub M r c = 0) →
    0 < n →
      ∃ e < n,
        (∀ r < n, M StarkedAir.Block.URec.ON r = 1 ↔ r < e) ∧
          (∀ r < e, M StarkedAir.Block.URec.J r = (↑r : StarkedAir.F)) ∧
            M StarkedAir.Block.URec.S 0 = 1 ∧
              (∀ (r : ℕ),
                  r + 1 < e →
                    M StarkedAir.Block.URec.S (r + 1) =
                      M StarkedAir.Block.URec.S r + 9 + M StarkedAir.Block.URec.TL r) ∧
                (e = 0 → pub StarkedAir.Block.Undo.PUB_LEN = 1) ∧
                  (0 < e →
                    M StarkedAir.Block.URec.S (e - 1) + 9 + M StarkedAir.Block.URec.TL (e - 1) =
                      pub StarkedAir.Block.Undo.PUB_LEN) :=
  @StarkedAir.Block.URec.rows_sound

/-- StarkedAir.Block.wmerkle_sound -/
theorem compat_Block_wmerkle_sound : ∀ {inst : ℕ → StarkedAir.Inst} {pub : ℕ → StarkedAir.F} {L : ℕ},
  (∀ i < 15, (inst i).logSize = L) →
    StarkedAir.Block.hashSys.SatisfiedExt inst pub [] →
      L ≤ 23 →
        256 ≤ 2 ^ L →
          ∀ {b : StarkedAir.Spec.Block.Blk},
            StarkedAir.Spec.Block.parseBlock (StarkedAir.Block.Fields.blockBytes (inst 0).main (ZMod.val (pub 0))) =
                Option.some b →
              pub 1 = (↑b.txs.length : StarkedAir.F) →
                1 ≤ b.txs.length →
                  b.txs.length < 2 ^ L →
                    (inst 7).main StarkedAir.Block.Ctx.HC 0 = 1 →
                      ∃ (oN : StarkedAir.Spec.Sha256.State) (oC : StarkedAir.Spec.Sha256.State),
                        StarkedAir.Block.stLimbs oN =
                            List.map (StarkedAir.Block.ctxLimb (inst 7).main 79) (List.range 16) ∧
                          StarkedAir.Block.stLimbs oC =
                              List.map (StarkedAir.Block.ctxLimb (inst 7).main 117) (List.range 16) ∧
                            StarkedAir.Spec.Block.stateBytes oC =
                              StarkedAir.Spec.Block.sha256d
                                ((StarkedAir.Spec.Block.merkleRoot (StarkedAir.Block.wleaves b)).1 ++
                                  StarkedAir.Spec.Block.stateBytes oN) :=
  fun {inst pub L} hL hsat hL24 => StarkedAir.Block.wmerkle_sound (inst := inst) (pub := pub) (Ls := fun _ => L) hL hsat
    (fun _ _ => hL24)

/-- StarkedAir.Circuit.Composition.balance_sound -/
theorem compat_Circuit_Composition_balance_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {claimed : List ℕ} {ext : List StarkedAir.Circuit.Composition.ExtE}
  {z alpha : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.balanceProg n claimed ext z alpha) →
    (List.map (StarkedAir.Circuit.Composition.val ρ) claimed).sum +
        (List.map (StarkedAir.Circuit.Composition.entryFrac ρ z alpha) ext).sum =
      0 :=
  @StarkedAir.Circuit.Composition.balance_sound

/-- StarkedAir.Circuit.Composition.entFold_sound -/
theorem compat_Circuit_Composition_entFold_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {z alpha : ℕ} (ext : List StarkedAir.Circuit.Composition.ExtE)
  (s : List StarkedAir.Circuit.Op × ℕ × ℕ),
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.entFold z alpha ext s).1 →
    StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.entFold z alpha ext s).2.1 =
      StarkedAir.Circuit.Composition.val ρ s.2.1 +
        (List.map (StarkedAir.Circuit.Composition.entryFrac ρ z alpha) ext).sum :=
  @StarkedAir.Circuit.Composition.entFold_sound

/-- StarkedAir.Circuit.Composition.entry_sound -/
theorem compat_Circuit_Composition_entry_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n acc z alpha : ℕ} {e : StarkedAir.Circuit.Composition.ExtE},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.entryOps n acc z alpha e).ops →
    StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.entryOps n acc z alpha e).res =
        StarkedAir.Circuit.Composition.val ρ acc + StarkedAir.Circuit.Composition.entryFrac ρ z alpha e ∧
      StarkedAir.Circuit.Composition.fingerprint (StarkedAir.Circuit.Composition.val ρ alpha)
            (StarkedAir.Spec.QM31.emb (↑e.rel : StarkedAir.F))
            (List.map (StarkedAir.Circuit.Composition.val ρ) e.vals) -
          StarkedAir.Circuit.Composition.val ρ z ≠
        0 :=
  @StarkedAir.Circuit.Composition.entry_sound

/-- StarkedAir.Circuit.blake2s_sound -/
theorem compat_Circuit_blake2s_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {msg : List ℕ} {nBytes : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.blake2s n msg nBytes).ops →
    nBytes < 2 ^ 32 →
      ∀ i < 8,
        (ρ ((StarkedAir.Circuit.blake2s n msg nBytes).res.getD i 0)).word =
          StarkedAir.Circuit.hashW (fun (j : ℕ) => (ρ (msg.getD j n)).word) nBytes (StarkedAir.Circuit.nBlocks nBytes) i :=
  @StarkedAir.Circuit.blake2s_sound

/-- StarkedAir.Circuit.block_sound -/
theorem compat_Circuit_block_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {msg : ℕ → ℕ} {nBytes nb b : ℕ} {H : ℕ → StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.blockOps n msg nBytes nb b) →
    nBytes < 2 ^ 32 →
      (∀ i < 8, (ρ (StarkedAir.Circuit.chain n b i)).word = H i) →
        ∀ i < 8,
          (ρ (StarkedAir.Circuit.chain n (b + 1) i)).word =
            StarkedAir.Spec.Blake2s.compress H (fun (j : ℕ) => (ρ (msg (16 * b + j))).word)
              (Min.min nBytes (64 * (b + 1))) (Decidable.decide (b + 1 = nb)) i :=
  @StarkedAir.Circuit.block_sound

/-- StarkedAir.Circuit.pubsDigest_sound -/
theorem compat_Circuit_pubsDigest_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {key pubs : List ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.pubsDigest n key pubs).ops →
    4 * (key.length + pubs.length) < 2 ^ 32 →
      ∀ i < 8,
        (ρ ((StarkedAir.Circuit.pubsDigest n key pubs).res.getD i 0)).word =
          StarkedAir.Circuit.blake2sWords
            (List.map (StarkedAir.Circuit.Q.word ∘ ρ) key ++
              List.map (fun (p : ℕ) => BitVec.ofNat 32 (ZMod.val (ρ p).a)) pubs)
            (4 * (key.length + pubs.length)) i :=
  @StarkedAir.Circuit.pubsDigest_sound

/-- StarkedAir.Circuit.BlockCtx.ctx_sound -/
theorem compat_Circuit_BlockCtx_ctx_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {H : ℕ},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.BlockCtx.ctxOps →
    H < 2 ^ 30 →
      ρ 0 = { a := (↑H : StarkedAir.F), b := 0, c := 0, d := 0 } →
        (∀ j < 4, 1 ≤ j → (ρ j).IsBase) →
          ((ρ 1).a = if StarkedAir.Spec.Block.BIP34_HEIGHT ≤ H then 1 else 0) ∧
            ((ρ 2).a = if StarkedAir.Spec.Block.CSV_HEIGHT ≤ H then 1 else 0) ∧
              ((ρ 3).a = if StarkedAir.Spec.Block.SEGWIT_HEIGHT ≤ H then 1 else 0) ∧
                (ρ 4).a = (((StarkedAir.Circuit.BlockCtx.subsidy H % 2 ^ 24 : ℕ)) : StarkedAir.F) ∧
                  (ρ 5).a = (((StarkedAir.Circuit.BlockCtx.subsidy H / 2 ^ 24 : ℕ)) : StarkedAir.F) :=
  @StarkedAir.Circuit.BlockCtx.ctx_sound

/-- StarkedAir.Circuit.BlockCtx.flag_sound -/
theorem compat_Circuit_BlockCtx_flag_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {m fr c H : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.BlockCtx.flagOps m fr c) →
    c < 2 ^ 30 →
      1 ≤ c →
        H < 2 ^ 30 →
          ρ 0 = { a := (↑H : StarkedAir.F), b := 0, c := 0, d := 0 } →
            (ρ fr).IsBase →
              ρ StarkedAir.Circuit.BlockCtx.ONE = StarkedAir.Circuit.Q.lit 1 0 0 0 → (ρ fr).a = if c ≤ H then 1 else 0 :=
  @StarkedAir.Circuit.BlockCtx.flag_sound

/-- StarkedAir.Circuit.BlockCtx.sub_sound -/
theorem compat_Circuit_BlockCtx_sub_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {m H : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.BlockCtx.subOps m) →
    H < 2 ^ 30 →
      ρ 0 = { a := (↑H : StarkedAir.F), b := 0, c := 0, d := 0 } →
        ρ StarkedAir.Circuit.BlockCtx.ONE = StarkedAir.Circuit.Q.lit 1 0 0 0 →
          (ρ 4).a = (((StarkedAir.Circuit.BlockCtx.subsidy H % 2 ^ 24 : ℕ)) : StarkedAir.F) ∧
            (ρ 5).a = (((StarkedAir.Circuit.BlockCtx.subsidy H / 2 ^ 24 : ℕ)) : StarkedAir.F) :=
  @StarkedAir.Circuit.BlockCtx.sub_sound

/-- StarkedAir.Circuit.BlockLeaf.checks_sound -/
theorem compat_Circuit_BlockLeaf_checks_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.BlockLeaf.checksOps →
    (∀ j < StarkedAir.Circuit.BlockLeaf.N_IN, (ρ j).IsBase) →
      ∀ {H : ℕ},
        H < StarkedAir.P →
          (ρ 0).a = (↑H : StarkedAir.F) →
            (∀ k < StarkedAir.Circuit.BlockLeaf.NW,
                StarkedAir.Spec.QM31.toQ
                    { a := (ρ (2 + 4 * k)).a, b := (ρ (3 + 4 * k)).a, c := (ρ (4 + 4 * k)).a, d := (ρ (5 + 4 * k)).a } =
                  StarkedAir.Spec.QM31.toQ { a := (ρ 6).a, b := (ρ 7).a, c := (ρ 8).a, d := (ρ 9).a } ^ k) ∧
              (ρ 1).a = if StarkedAir.Spec.Coins.bip30Lost H = Bool.true then 1 else 0 :=
  @StarkedAir.Circuit.BlockLeaf.checks_sound

/-- StarkedAir.Circuit.BlockLeaf.seedLeaf_sound -/
theorem compat_Circuit_BlockLeaf_seedLeaf_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.BlockLeaf.seedLeafProg.ops →
    ∀ {a b : StarkedAir.Spec.Sha256.State},
      (StarkedAir.HeaderTree.pubT fun (k : ℕ) => (ρ (k - StarkedAir.Circuit.TB)).a) = StarkedAir.HeaderTree.limbsOf a →
        (StarkedAir.HeaderTree.pubT fun (k : ℕ) => (ρ (16 + (k - StarkedAir.Circuit.TB))).a) =
            StarkedAir.HeaderTree.limbsOf b →
          ∀ j < 16,
            (ρ (StarkedAir.Circuit.BlockLeaf.seedLeafProg.res.getD j 0)).a =
              (StarkedAir.HeaderTree.limbsOf (StarkedAir.Spec.HeaderTree.hnode a b)).getD j 0 :=
  @StarkedAir.Circuit.BlockLeaf.seedLeaf_sound

/-- StarkedAir.Circuit.BlockNode.lt30_sound -/
theorem compat_Circuit_BlockNode_lt30_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {m x : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.BlockNode.lt30 m x) → (ρ x).IsBase ∧ ZMod.val (ρ x).a < 2 ^ 30 :=
  @StarkedAir.Circuit.BlockNode.lt30_sound

/-- StarkedAir.Circuit.BlockNode.node_sound -/
theorem compat_Circuit_BlockNode_node_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {pl pr : ℕ → ℕ} {b : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.BlockNode.nodeOut pl pr b).ops →
    ρ (pr StarkedAir.Circuit.BlockNode.NN) = ρ (pl StarkedAir.Circuit.BlockNode.NN) ∧
      ρ (pr StarkedAir.Circuit.BlockNode.LO) =
          ρ (pl StarkedAir.Circuit.BlockNode.LO) + ρ (pl StarkedAir.Circuit.BlockNode.NN) ∧
        (∀ i < 12, ρ (pr (StarkedAir.Circuit.BlockNode.CH + i)) = ρ (pl (StarkedAir.Circuit.BlockNode.CH + i))) ∧
          ρ (b + 1) = ρ (pl StarkedAir.Circuit.BlockNode.NN) + ρ (pl StarkedAir.Circuit.BlockNode.NN) ∧
            (∀ i < 4,
                ρ (b + 2 + i) =
                  ρ (pl (StarkedAir.Circuit.BlockNode.SS + i)) + ρ (pr (StarkedAir.Circuit.BlockNode.SS + i))) ∧
              ρ (b + 6) = ρ (pl StarkedAir.Circuit.BlockNode.NIN) + ρ (pr StarkedAir.Circuit.BlockNode.NIN) ∧
                ((ρ (pl StarkedAir.Circuit.BlockNode.LO)).IsBase ∧
                    ZMod.val (ρ (pl StarkedAir.Circuit.BlockNode.LO)).a < 2 ^ 30) ∧
                  ((ρ (b + 1)).IsBase ∧ ZMod.val (ρ (b + 1)).a < 2 ^ 30) ∧
                    ((ρ (b + 6)).IsBase ∧ ZMod.val (ρ (b + 6)).a < 2 ^ 30) ∧
                      (∀ {x y : StarkedAir.Spec.Sha256.State},
                          (StarkedAir.HeaderTree.pubT fun (k : ℕ) =>
                                (ρ (pl (StarkedAir.Circuit.BlockNode.HR + (k - StarkedAir.Circuit.TB)))).a) =
                              StarkedAir.HeaderTree.limbsOf x →
                            (StarkedAir.HeaderTree.pubT fun (k : ℕ) =>
                                  (ρ (pr (StarkedAir.Circuit.BlockNode.HR + (k - StarkedAir.Circuit.TB)))).a) =
                                StarkedAir.HeaderTree.limbsOf y →
                              ∀ j < 16,
                                (ρ ((StarkedAir.Circuit.BlockNode.hrNode pl pr (b + 34)).res.getD j 0)).a =
                                  (StarkedAir.HeaderTree.limbsOf (StarkedAir.Spec.HeaderTree.hnode x y)).getD j 0) ∧
                        ∀ {x y : StarkedAir.Spec.Sha256.State},
                          (StarkedAir.HeaderTree.pubT fun (k : ℕ) =>
                                (ρ (pl (StarkedAir.Circuit.BlockNode.SR + (k - StarkedAir.Circuit.TB)))).a) =
                              StarkedAir.HeaderTree.limbsOf x →
                            (StarkedAir.HeaderTree.pubT fun (k : ℕ) =>
                                  (ρ (pr (StarkedAir.Circuit.BlockNode.SR + (k - StarkedAir.Circuit.TB)))).a) =
                                StarkedAir.HeaderTree.limbsOf y →
                              ∀ j < 16,
                                (ρ
                                      ((StarkedAir.Circuit.BlockNode.srNode pl pr
                                              (StarkedAir.Circuit.BlockNode.hrNode pl pr (b + 34)).next).res.getD
                                        j 0)).a =
                                  (StarkedAir.HeaderTree.limbsOf (StarkedAir.Spec.HeaderTree.hnode x y)).getD j 0 :=
  @StarkedAir.Circuit.BlockNode.node_sound

/-- StarkedAir.Circuit.BlockRec.block_node_sound -/
theorem compat_Circuit_BlockRec_block_node_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.BlockNode.blockNodeProgram.ops →
    StarkedAir.Circuit.BlockTree.SumOk (StarkedAir.Circuit.BlockRec.childSum ρ StarkedAir.Circuit.BlockNode.bC0) →
      StarkedAir.Circuit.BlockTree.SumOk (StarkedAir.Circuit.BlockRec.childSum ρ StarkedAir.Circuit.BlockNode.bC1) →
        StarkedAir.Circuit.BlockTree.SumOk (StarkedAir.Circuit.BlockRec.outSum ρ) ∧
          StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.blockNodeProgram.results =
              StarkedAir.Circuit.BlockRec.sumDigest
                (StarkedAir.Circuit.BlockRec.keyOf
                  (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC0.res.chash)
                  (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC0.res.key)
                  (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC1.res.chash)
                  (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC1.res.key))
                (StarkedAir.Circuit.BlockRec.outSum ρ) ∧
            StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC0.res.digest =
                StarkedAir.Circuit.BlockRec.sumDigest
                  (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC0.res.key)
                  (StarkedAir.Circuit.BlockRec.childSum ρ StarkedAir.Circuit.BlockNode.bC0) ∧
              StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC1.res.digest =
                StarkedAir.Circuit.BlockRec.sumDigest
                  (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockNode.bC1.res.key)
                  (StarkedAir.Circuit.BlockRec.childSum ρ StarkedAir.Circuit.BlockNode.bC1) :=
  @StarkedAir.Circuit.BlockRec.block_node_sound

/-- StarkedAir.Circuit.BlockRec.forest_epoch -/
theorem compat_Circuit_BlockRec_forest_epoch : ∀ {Acc SatC : List StarkedAir.Spec.Blake2s.Word → List StarkedAir.Spec.Blake2s.Word → Prop}
  {VGates : (ℕ → StarkedAir.Circuit.Q) → ℕ → List ℕ → List ℕ → Prop} {leafH : ℕ → List StarkedAir.Spec.Blake2s.Word}
  {nodeH : List StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.BlockRec.Trust Acc SatC VGates leafH nodeH StarkedAir.Circuit.BlockNode.blockNodeProgram
      StarkedAir.Circuit.BlockRec.LeafOut →
    (∀ (L : ℕ), (leafH L).length = 8) →
      nodeH.length = 8 →
        ∀ (t0 : StarkedAir.Circuit.BlockRec.Tree) (v0 : ℕ → StarkedAir.F)
          (rest : List (StarkedAir.Circuit.BlockRec.Tree × (ℕ → StarkedAir.F))),
          Acc (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH t0)
              (StarkedAir.Circuit.BlockRec.sumDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH t0) v0) →
            (∀ tv ∈ rest,
                Acc (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH tv.1)
                  (StarkedAir.Circuit.BlockRec.sumDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH tv.1)
                    tv.2)) →
              StarkedAir.Circuit.BlockTree.Linked' v0 (List.map Prod.snd rest) →
                (∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) →
                  (∃ (n : ℕ),
                      0 < n ∧
                        ∃ (pub : ℕ → ℕ → StarkedAir.F) (inst : ℕ → ℕ → StarkedAir.Inst) (L : ℕ → ℕ) (x :
                          (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)),
                          (∀ i < n, ∀ c < 15, (inst i c).logSize = L i) ∧
                            (∀ i < n, StarkedAir.Block.hashSys.SatisfiedExt (inst i) (pub i) []) ∧
                              (∀ i < n, L i ≤ 23) ∧
                                (∀ i < n, pub i 2 = (↑(ZMod.val (v0 0) + i) : StarkedAir.F)) ∧
                                  (∀ i < n,
                                      pub i StarkedAir.Block.Coin.PUB_LOST =
                                        if StarkedAir.Spec.Coins.bip30Lost (ZMod.val (v0 0) + i) = Bool.true then 1
                                        else 0) ∧
                                    (∀ i < n, StarkedAir.Block.FpWalk.gQ (pub i) = StarkedAir.Block.RunSum.pQ v0 7) ∧
                                      (∀ i < n,
                                          StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_Z =
                                            StarkedAir.Block.RunSum.pQ v0 11) ∧
                                        (∀ i < n,
                                            ∀ k < StarkedAir.Block.Coin.W,
                                              StarkedAir.Block.RunSum.pQ (pub i) (StarkedAir.Block.Coin.PUB_ALPHA k) =
                                                StarkedAir.Block.RunSum.pQ v0 15 ^ k) ∧
                                          ∑ i ∈ Finset.range n,
                                              StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_S =
                                            StarkedAir.Block.RunSum.pQ v0 2 +
                                              (List.map (fun (v : ℕ → StarkedAir.F) => StarkedAir.Block.RunSum.pQ v 2)
                                                  (List.map Prod.snd rest)).sum) ∨
                    StarkedAir.Circuit.BlockRec.Collision :=
  @StarkedAir.Circuit.BlockRec.forest_epoch

/-- StarkedAir.Circuit.BlockRec.forest_sound -/
theorem compat_Circuit_BlockRec_forest_sound : ∀ {Acc SatC : List StarkedAir.Spec.Blake2s.Word → List StarkedAir.Spec.Blake2s.Word → Prop}
  {VGates : (ℕ → StarkedAir.Circuit.Q) → ℕ → List ℕ → List ℕ → Prop} {leafH : ℕ → List StarkedAir.Spec.Blake2s.Word}
  {nodeH : List StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.BlockRec.Trust Acc SatC VGates leafH nodeH StarkedAir.Circuit.BlockNode.blockNodeProgram
      StarkedAir.Circuit.BlockRec.LeafOut →
    (∀ (L : ℕ), (leafH L).length = 8) →
      nodeH.length = 8 →
        ∀ (t0 : StarkedAir.Circuit.BlockRec.Tree) (v0 : ℕ → StarkedAir.F)
          (rest : List (StarkedAir.Circuit.BlockRec.Tree × (ℕ → StarkedAir.F))),
          Acc (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH t0)
              (StarkedAir.Circuit.BlockRec.sumDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH t0) v0) →
            (∀ tv ∈ rest,
                Acc (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH tv.1)
                  (StarkedAir.Circuit.BlockRec.sumDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH tv.1)
                    tv.2)) →
              StarkedAir.Circuit.BlockTree.Linked' v0 (List.map Prod.snd rest) →
                (∀ tv ∈ rest, ∀ i < 12, tv.2 (7 + i) = v0 (7 + i)) →
                  (∃ (n : ℕ),
                      0 < n ∧
                        StarkedAir.Block.RngOk
                          { lo := ZMod.val (v0 0), n := n,
                            s :=
                              StarkedAir.Block.RunSum.pQ v0 2 +
                                (List.map (fun (v : ℕ → StarkedAir.F) => StarkedAir.Block.RunSum.pQ v 2)
                                    (List.map Prod.snd rest)).sum,
                            nin :=
                              ZMod.val (v0 6) +
                                (List.map (fun (v : ℕ → StarkedAir.F) => ZMod.val (v 6)) (List.map Prod.snd rest)).sum,
                            γ := StarkedAir.Block.RunSum.pQ v0 7, z := StarkedAir.Block.RunSum.pQ v0 11,
                            α := StarkedAir.Block.RunSum.pQ v0 15 }) ∨
                    StarkedAir.Circuit.BlockRec.Collision :=
  @StarkedAir.Circuit.BlockRec.forest_sound

/-- StarkedAir.Circuit.BlockRec.leafOut_sound -/
theorem compat_Circuit_BlockRec_leafOut_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.BlockRec.leafOutOps →
    (StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockRec.blockLeafOut.results =
        StarkedAir.Circuit.BlockRec.sumDigest StarkedAir.Circuit.BlockRec.zeroKey fun (i : ℕ) =>
          (ρ (StarkedAir.Circuit.BlockRec.sReg i)).a) ∧
      ((ρ 2).IsBase ∧ ZMod.val (ρ 2).a < 2 ^ 30) ∧
        ((ρ StarkedAir.Block.Coin.PUB_NIN).IsBase ∧ ZMod.val (ρ StarkedAir.Block.Coin.PUB_NIN).a < 2 ^ 30) ∧
          ρ (StarkedAir.Circuit.BlockRec.LIN + 18) = StarkedAir.Circuit.Q.lit 1 0 0 0 :=
  @StarkedAir.Circuit.BlockRec.leafOut_sound

/-- StarkedAir.Circuit.BlockRec.tree_sound -/
theorem compat_Circuit_BlockRec_tree_sound : ∀ {Acc SatC : List StarkedAir.Spec.Blake2s.Word → List StarkedAir.Spec.Blake2s.Word → Prop}
  {VGates : (ℕ → StarkedAir.Circuit.Q) → ℕ → List ℕ → List ℕ → Prop} {leafH : ℕ → List StarkedAir.Spec.Blake2s.Word}
  {nodeH : List StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.BlockRec.Trust Acc SatC VGates leafH nodeH StarkedAir.Circuit.BlockNode.blockNodeProgram
      StarkedAir.Circuit.BlockRec.LeafOut →
    (∀ (L : ℕ), (leafH L).length = 8) →
      nodeH.length = 8 →
        ∀ (t : StarkedAir.Circuit.BlockRec.Tree) (v : ℕ → StarkedAir.F),
          SatC (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH t)
              (StarkedAir.Circuit.BlockRec.sumDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH t) v) →
            StarkedAir.Circuit.BlockTree.SumOk v ∨ StarkedAir.Circuit.BlockRec.Collision :=
  @StarkedAir.Circuit.BlockRec.tree_sound

/-- StarkedAir.Circuit.BlockTree.sumOk_leaf -/
theorem compat_Circuit_BlockTree_sumOk_leaf : ∀ {p : ℕ → StarkedAir.F},
  StarkedAir.Block.BlockPubOk p →
    ∀ {H : ℕ},
      H < 2 ^ 30 →
        p 2 = (↑H : StarkedAir.F) →
          (p StarkedAir.Block.Coin.PUB_LOST = if StarkedAir.Spec.Coins.bip30Lost H = Bool.true then 1 else 0) →
            (∀ k < StarkedAir.Block.Coin.W,
                StarkedAir.Block.RunSum.pQ p (StarkedAir.Block.Coin.PUB_ALPHA k) =
                  StarkedAir.Block.RunSum.pQ p (StarkedAir.Block.Coin.PUB_ALPHA 1) ^ k) →
              ZMod.val (p StarkedAir.Block.Coin.PUB_NIN) < 2 ^ 30 →
                (∀ j < 16, ZMod.val (p (25 + j)) < 65536) →
                  StarkedAir.Circuit.BlockTree.SumOk (StarkedAir.Circuit.BlockTree.leafVec p) :=
  @StarkedAir.Circuit.BlockTree.sumOk_leaf

/-- StarkedAir.Circuit.BlockTree.sumOk_node -/
theorem compat_Circuit_BlockTree_sumOk_node : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {pl pr : ℕ → ℕ} {b : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.BlockNode.nodeOut pl pr b).ops →
    (StarkedAir.Circuit.BlockTree.SumOk fun (i : ℕ) => (ρ (pl i)).a) →
      (StarkedAir.Circuit.BlockTree.SumOk fun (i : ℕ) => (ρ (pr i)).a) →
        StarkedAir.Circuit.BlockTree.SumOk fun (i : ℕ) => (ρ (StarkedAir.Circuit.BlockNode.outReg pl pr b i)).a :=
  @StarkedAir.Circuit.BlockTree.sumOk_node

/-- StarkedAir.Circuit.Channel.absorb_sound -/
theorem compat_Circuit_Channel_absorb_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {xs vs : List ℕ} {nBytes : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.absorb n xs vs nBytes).ops →
    nBytes < 2 ^ 32 →
      ρ (StarkedAir.Circuit.Channel.absorb n xs vs nBytes).res.1 =
          StarkedAir.Circuit.Channel.qOf
            (StarkedAir.Circuit.Channel.Spec.absorb (List.map ρ xs) (List.map (StarkedAir.Circuit.Q.word ∘ ρ) vs)
              nBytes)
            0 ∧
        ρ (StarkedAir.Circuit.Channel.absorb n xs vs nBytes).res.2 =
          StarkedAir.Circuit.Channel.qOf
            (StarkedAir.Circuit.Channel.Spec.absorb (List.map ρ xs) (List.map (StarkedAir.Circuit.Q.word ∘ ρ) vs)
              nBytes)
            4 :=
  @StarkedAir.Circuit.Channel.absorb_sound

/-- StarkedAir.Circuit.Channel.drawPoint_sound -/
theorem compat_Circuit_Channel_drawPoint_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {s : StarkedAir.Circuit.Channel.Spec.St} {n lo hi : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.drawPointP n lo hi).ops →
    s.nDraws = 0 →
      ρ lo = s.lo →
        ρ hi = s.hi →
          have T := StarkedAir.Spec.QM31.toQ (StarkedAir.Circuit.Channel.Spec.drawTwo s).1;
          1 + T ^ 2 ≠ 0 ∧
            StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Channel.drawPointP n lo hi).res.1) =
                (1 - T ^ 2) / (1 + T ^ 2) ∧
              StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Channel.drawPointP n lo hi).res.2) = 2 * T / (1 + T ^ 2) :=
  @StarkedAir.Circuit.Channel.drawPoint_sound

/-- StarkedAir.Circuit.Channel.drawQm31_sound -/
theorem compat_Circuit_Channel_drawQm31_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {s : StarkedAir.Circuit.Channel.Spec.St} {n lo hi : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.drawQm31P n lo hi).ops →
    s.nDraws = 0 →
      ρ lo = s.lo →
        ρ hi = s.hi →
          ρ (StarkedAir.Circuit.Channel.drawQm31P n lo hi).res = (StarkedAir.Circuit.Channel.Spec.drawTwo s).1 :=
  @StarkedAir.Circuit.Channel.drawQm31_sound

/-- StarkedAir.Circuit.Channel.draw_sound -/
theorem compat_Circuit_Channel_draw_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {s : StarkedAir.Circuit.Channel.Spec.St} {n lo hi : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.drawP n lo hi).ops →
    s.nDraws = 0 →
      ρ lo = s.lo →
        ρ hi = s.hi →
          ρ (StarkedAir.Circuit.Channel.drawP n lo hi).res.1 = (StarkedAir.Circuit.Channel.Spec.drawTwo s).1 ∧
            ρ (StarkedAir.Circuit.Channel.drawP n lo hi).res.2 = (StarkedAir.Circuit.Channel.Spec.drawTwo s).2.1 :=
  @StarkedAir.Circuit.Channel.draw_sound

/-- StarkedAir.Circuit.Channel.fpe_sound -/
theorem compat_Circuit_Channel_fpe_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {q v0 v1 v2 v3 : ℕ} {f0 f1 f2 f3 : StarkedAir.F},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.fpe q v0 v1 v2 v3) →
    ρ v0 = { a := f0, b := 0, c := 0, d := 0 } →
      ρ v1 = { a := f1, b := 0, c := 0, d := 0 } →
        ρ v2 = { a := f2, b := 0, c := 0, d := 0 } →
          ρ v3 = { a := f3, b := 0, c := 0, d := 0 } → ρ (q + 8) = { a := f0, b := f1, c := f2, d := f3 } :=
  @StarkedAir.Circuit.Channel.fpe_sound

/-- StarkedAir.Circuit.Channel.mixQm31s_sound -/
theorem compat_Circuit_Channel_mixQm31s_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {s : StarkedAir.Circuit.Channel.Spec.St} {n lo hi : ℕ} {xs : List ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.mixQm31sP n lo hi xs).ops →
    16 * (2 + xs.length) < 2 ^ 32 →
      ρ lo = s.lo →
        ρ hi = s.hi →
          ρ (StarkedAir.Circuit.Channel.mixQm31sP n lo hi xs).res.1 =
              (StarkedAir.Circuit.Channel.Spec.mixQm31s s (List.map ρ xs)).lo ∧
            ρ (StarkedAir.Circuit.Channel.mixQm31sP n lo hi xs).res.2 =
              (StarkedAir.Circuit.Channel.Spec.mixQm31s s (List.map ρ xs)).hi :=
  @StarkedAir.Circuit.Channel.mixQm31s_sound

/-- StarkedAir.Circuit.Channel.mixU32s_sound -/
theorem compat_Circuit_Channel_mixU32s_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {s : StarkedAir.Circuit.Channel.Spec.St} {n lo hi : ℕ} {vs : List ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.mixU32sP n lo hi vs).ops →
    4 * (8 + vs.length) < 2 ^ 32 →
      ρ lo = s.lo →
        ρ hi = s.hi →
          ρ (StarkedAir.Circuit.Channel.mixU32sP n lo hi vs).res.1 =
              (StarkedAir.Circuit.Channel.Spec.mixU32s s (List.map (StarkedAir.Circuit.Q.word ∘ ρ) vs)).lo ∧
            ρ (StarkedAir.Circuit.Channel.mixU32sP n lo hi vs).res.2 =
              (StarkedAir.Circuit.Channel.Spec.mixU32s s (List.map (StarkedAir.Circuit.Q.word ∘ ρ) vs)).hi :=
  @StarkedAir.Circuit.Channel.mixU32s_sound

/-- StarkedAir.Circuit.Channel.point_sound -/
theorem compat_Circuit_Channel_point_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n t : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.pointOps n t).ops →
    1 + StarkedAir.Spec.QM31.toQ (ρ t) ^ 2 ≠ 0 ∧
      StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Channel.pointOps n t).res.1) =
          (1 - StarkedAir.Spec.QM31.toQ (ρ t) ^ 2) / (1 + StarkedAir.Spec.QM31.toQ (ρ t) ^ 2) ∧
        StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Channel.pointOps n t).res.2) =
          2 * StarkedAir.Spec.QM31.toQ (ρ t) / (1 + StarkedAir.Spec.QM31.toQ (ρ t) ^ 2) :=
  @StarkedAir.Circuit.Channel.point_sound

/-- StarkedAir.Circuit.Channel.powMix_sound -/
theorem compat_Circuit_Channel_powMix_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {s : StarkedAir.Circuit.Channel.Spec.St} {n lo hi nonce : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.powMixP n lo hi nonce).ops →
    ρ lo = s.lo →
      ρ hi = s.hi →
        ρ (StarkedAir.Circuit.Channel.powMixP n lo hi nonce).res.1 =
            (StarkedAir.Circuit.Channel.Spec.powMix s (ρ nonce)).lo ∧
          ρ (StarkedAir.Circuit.Channel.powMixP n lo hi nonce).res.2 =
            (StarkedAir.Circuit.Channel.Spec.powMix s (ρ nonce)).hi :=
  @StarkedAir.Circuit.Channel.powMix_sound

/-- StarkedAir.Circuit.Channel.redWord_sound -/
theorem compat_Circuit_Channel_redWord_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {m w two16 : ℕ} {W : StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.redWord m w two16) →
    ρ two16 = StarkedAir.Circuit.Q.lit 65536 0 0 0 →
      ρ w = StarkedAir.Circuit.Q.pack W →
        ρ (m + 7) = { a := (↑(BitVec.toNat W) : StarkedAir.F), b := 0, c := 0, d := 0 } :=
  @StarkedAir.Circuit.Channel.redWord_sound

/-- StarkedAir.Circuit.Channel.reduce_sound -/
theorem compat_Circuit_Channel_reduce_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {ws : List ℕ} {W : ℕ → StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.reduceOps n ws).ops →
    (∀ k < 8, ρ (ws.getD k 0) = StarkedAir.Circuit.Q.pack (W k)) →
      ρ (StarkedAir.Circuit.Channel.reduceOps n ws).res.1 =
          StarkedAir.Circuit.Channel.qOf (StarkedAir.Circuit.Channel.reduce W) 0 ∧
        ρ (StarkedAir.Circuit.Channel.reduceOps n ws).res.2 =
          StarkedAir.Circuit.Channel.qOf (StarkedAir.Circuit.Channel.reduce W) 4 :=
  @StarkedAir.Circuit.Channel.reduce_sound

/-- StarkedAir.Circuit.Channel.unpack1_sound -/
theorem compat_Circuit_Channel_unpack1_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n x : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.unpack1 n x).ops →
    List.map (StarkedAir.Circuit.Q.word ∘ ρ) (StarkedAir.Circuit.Channel.unpack1 n x).res =
      StarkedAir.Circuit.Channel.qWords (ρ x) :=
  @StarkedAir.Circuit.Channel.unpack1_sound

/-- StarkedAir.Circuit.Channel.unpack_sound -/
theorem compat_Circuit_Channel_unpack_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {xs : List ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Channel.unpack n xs).ops →
    List.map (StarkedAir.Circuit.Q.word ∘ ρ) (StarkedAir.Circuit.Channel.unpack n xs).res =
      List.flatMap (StarkedAir.Circuit.Channel.qWords ∘ ρ) xs :=
  @StarkedAir.Circuit.Channel.unpack_sound

/-- StarkedAir.Circuit.Composition.constraints_sound -/
theorem compat_Circuit_Composition_constraints_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {base accIn hb coeff : ℕ} {air : StarkedAir.Air}
  {ci : StarkedAir.Circuit.Composition.Inputs},
  StarkedAir.Circuit.Composition.WF air.toDag.1 →
    (∀ id ∈ air.toDag.2, id < air.toDag.1.size) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.constraintOps base accIn hb coeff air ci) →
        StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Composition.accReg accIn hb air.toDag.2.length)) =
          StarkedAir.Circuit.Composition.horner (StarkedAir.Spec.QM31.toQ (ρ coeff))
            (StarkedAir.Spec.QM31.toQ (ρ accIn))
            (List.map
              (StarkedAir.Expr.evalR StarkedAir.Circuit.Composition.cstQ (StarkedAir.Circuit.Composition.leafQ ρ ci)
                (StarkedAir.Circuit.Composition.pubQ ρ ci))
              air.constraints) :=
  @StarkedAir.Circuit.Composition.constraints_sound

/-- StarkedAir.Circuit.Composition.program_sound -/
theorem compat_Circuit_Composition_program_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {air : StarkedAir.Air} {lay : StarkedAir.Circuit.Composition.Layout},
  StarkedAir.Circuit.Composition.WF air.toDag.1 →
    (∀ id ∈ air.toDag.2, id < air.toDag.1.size) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.program air lay).1 →
        StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Composition.program air lay).2) =
          StarkedAir.Circuit.Composition.horner (StarkedAir.Spec.QM31.toQ (ρ lay.coeff)) 0
              (List.map
                (StarkedAir.Expr.evalR StarkedAir.Circuit.Composition.cstQ
                  (StarkedAir.Circuit.Composition.leafQ ρ lay.inputs)
                  (StarkedAir.Circuit.Composition.pubQ ρ lay.inputs))
                air.constraints) *
            StarkedAir.Spec.QM31.toQ (ρ (lay.nIn + 1 + 2 * air.toDag.1.size + 2 * air.toDag.2.length)) :=
  @StarkedAir.Circuit.Composition.program_sound

/-- StarkedAir.Circuit.Composition.batch_sound -/
theorem compat_Circuit_Composition_batch_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n acc coeff b : ℕ} {x : StarkedAir.Circuit.Composition.BatchIn},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.batchOps n acc coeff b x).ops →
    StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.batchOps n acc coeff b x).res =
      StarkedAir.Circuit.Composition.val ρ acc * StarkedAir.Circuit.Composition.val ρ coeff +
        StarkedAir.Circuit.Composition.batchTerm (fun (i : ℕ) => StarkedAir.Circuit.Composition.val ρ (x.m i))
          (fun (i : ℕ) => StarkedAir.Circuit.Composition.val ρ (x.d i))
          (fun (i : ℕ) => StarkedAir.Circuit.Composition.val ρ (x.S i)) (StarkedAir.Circuit.Composition.val ρ x.sprev)
          (StarkedAir.Circuit.Composition.val ρ x.shift) x.L x.B b :=
  @StarkedAir.Circuit.Composition.batch_sound

/-- StarkedAir.Circuit.Composition.den_sound -/
theorem compat_Circuit_Composition_den_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n rel z alpha : ℕ} {vals : List ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.denOps n rel z alpha vals).ops →
    StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.denOps n rel z alpha vals).res =
      StarkedAir.Circuit.Composition.fingerprint (StarkedAir.Circuit.Composition.val ρ alpha)
          (StarkedAir.Spec.QM31.emb (↑rel : StarkedAir.F)) (List.map (StarkedAir.Circuit.Composition.val ρ) vals) -
        StarkedAir.Circuit.Composition.val ρ z :=
  @StarkedAir.Circuit.Composition.den_sound

/-- StarkedAir.Circuit.Composition.secure_sound -/
theorem compat_Circuit_Composition_secure_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {l : ℕ → ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.secureOps n l).ops →
    StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.secureOps n l).res =
      StarkedAir.Circuit.Composition.val ρ (l 0) +
            StarkedAir.Circuit.Composition.val ρ (l 1) * StarkedAir.Circuit.Composition.e1 +
          StarkedAir.Circuit.Composition.val ρ (l 2) * StarkedAir.Circuit.Composition.e2 +
        StarkedAir.Circuit.Composition.val ρ (l 3) * StarkedAir.Circuit.Composition.e3 :=
  @StarkedAir.Circuit.Composition.secure_sound

/-- StarkedAir.Circuit.Composition.batchFold_sound -/
theorem compat_Circuit_Composition_batchFold_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {coeff : ℕ} {bx : StarkedAir.Circuit.Composition.BatchIn} {acc1 q : ℕ} (B : ℕ),
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.batchFold coeff bx acc1 q B).1 →
    StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.batchFold coeff bx acc1 q B).2.1 =
      StarkedAir.Circuit.Composition.horner (StarkedAir.Circuit.Composition.val ρ coeff)
        (StarkedAir.Circuit.Composition.val ρ acc1)
        (List.map
          (fun (b : ℕ) =>
            StarkedAir.Circuit.Composition.batchTerm (fun (i : ℕ) => StarkedAir.Circuit.Composition.val ρ (bx.m i))
              (fun (i : ℕ) => StarkedAir.Circuit.Composition.val ρ (bx.d i))
              (fun (i : ℕ) => StarkedAir.Circuit.Composition.val ρ (bx.S i))
              (StarkedAir.Circuit.Composition.val ρ bx.sprev) (StarkedAir.Circuit.Composition.val ρ bx.shift) bx.L bx.B
              b)
          (List.range B)) :=
  @StarkedAir.Circuit.Composition.batchFold_sound

/-- StarkedAir.Circuit.Composition.cops_sound -/
theorem compat_Circuit_Composition_cops_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {c : StarkedAir.Comp} {pr : StarkedAir.Circuit.Composition.PartRegs}
  {sh : StarkedAir.Circuit.Composition.Shared} {n accIn : ℕ},
  StarkedAir.Circuit.Composition.WF (StarkedAir.Circuit.Composition.pNodes c) →
    (∀ id ∈ StarkedAir.Circuit.Composition.pIds c, id < (StarkedAir.Circuit.Composition.pNodes c).size) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.pCOps c pr sh n accIn) →
        StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.pAcc1 c n accIn) =
          StarkedAir.Circuit.Composition.horner (StarkedAir.Circuit.Composition.val ρ sh.coeff)
            (StarkedAir.Circuit.Composition.val ρ accIn)
            (List.map (StarkedAir.Circuit.Composition.rootVal ρ pr) c.air.constraints) :=
  @StarkedAir.Circuit.Composition.cops_sound

/-- StarkedAir.Circuit.Composition.partFold_sound -/
theorem compat_Circuit_Composition_partFold_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} (sh : StarkedAir.Circuit.Composition.Shared)
  (parts : List (StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs)) (s : List StarkedAir.Circuit.Op × ℕ × ℕ),
  (∀ p ∈ parts,
      StarkedAir.Circuit.Composition.WF (StarkedAir.Circuit.Composition.pNodes p.1) ∧
        ∀ id ∈ StarkedAir.Circuit.Composition.pIds p.1, id < (StarkedAir.Circuit.Composition.pNodes p.1).size) →
    (∀ (q : ℕ),
        StarkedAir.Circuit.Op.hook 2 [] [q] ∈ (StarkedAir.Circuit.Composition.partFold sh parts s).1 →
          StarkedAir.Circuit.Composition.val ρ q =
            StarkedAir.Spec.QM31.emb (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F)) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.partFold sh parts s).1 →
        StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.partFold sh parts s).2.1 =
          StarkedAir.Circuit.Composition.horner (StarkedAir.Circuit.Composition.val ρ sh.coeff)
            (StarkedAir.Circuit.Composition.val ρ s.2.1)
            (List.flatMap
              (fun (p : StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs) =>
                StarkedAir.Circuit.Composition.partTerms ρ p.1 p.2 sh)
              parts) :=
  @StarkedAir.Circuit.Composition.partFold_sound

/-- StarkedAir.Circuit.Composition.part_sound -/
theorem compat_Circuit_Composition_part_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {c : StarkedAir.Comp} {pr : StarkedAir.Circuit.Composition.PartRegs}
  {sh : StarkedAir.Circuit.Composition.Shared} {n accIn : ℕ},
  StarkedAir.Circuit.Composition.WF (StarkedAir.Circuit.Composition.pNodes c) →
    (∀ id ∈ StarkedAir.Circuit.Composition.pIds c, id < (StarkedAir.Circuit.Composition.pNodes c).size) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.partProg c pr sh n accIn).ops →
        (c.lookups.isEmpty = Bool.false →
            StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.pQ c pr sh n) =
              StarkedAir.Spec.QM31.emb (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F)) →
          StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.partProg c pr sh n accIn).res =
            StarkedAir.Circuit.Composition.horner (StarkedAir.Circuit.Composition.val ρ sh.coeff)
              (StarkedAir.Circuit.Composition.val ρ accIn) (StarkedAir.Circuit.Composition.partTerms ρ c pr sh) :=
  @StarkedAir.Circuit.Composition.part_sound

/-- StarkedAir.Circuit.Composition.seqOuts_sound -/
theorem compat_Circuit_Composition_seqOuts_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {spec : ℕ → StarkedAir.Spec.QM31.QM} (fs : List (ℕ → StarkedAir.Circuit.Out ℕ))
  (n j0 : ℕ),
  (∀ (j : ℕ) (hj : j < fs.length) (m : ℕ),
      StarkedAir.Circuit.Holds ρ (fs[j] m).ops → StarkedAir.Circuit.Composition.val ρ (fs[j] m).res = spec (j0 + j)) →
    StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.seqOuts n fs).1 →
      ∀ j < fs.length,
        StarkedAir.Circuit.Composition.val ρ ((StarkedAir.Circuit.Composition.seqOuts n fs).2.1.getD j 0) =
          spec (j0 + j) :=
  @StarkedAir.Circuit.Composition.seqOuts_sound

/-- StarkedAir.Circuit.Composition.sys_sound -/
theorem compat_Circuit_Composition_sys_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {parts : List (StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs)}
  {sh : StarkedAir.Circuit.Composition.Shared} {nIn oodsX : ℕ},
  (∀ p ∈ parts,
      StarkedAir.Circuit.Composition.WF (StarkedAir.Circuit.Composition.pNodes p.1) ∧
        ∀ id ∈ StarkedAir.Circuit.Composition.pIds p.1, id < (StarkedAir.Circuit.Composition.pNodes p.1).size) →
    (∀ (q : ℕ),
        StarkedAir.Circuit.Op.hook 2 [] [q] ∈ (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).1 →
          StarkedAir.Circuit.Composition.val ρ q =
            StarkedAir.Spec.QM31.emb (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F)) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).1 →
        StarkedAir.Circuit.Composition.val ρ (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).2 =
          StarkedAir.Circuit.Composition.horner (StarkedAir.Circuit.Composition.val ρ sh.coeff) 0
              (List.flatMap
                (fun (p : StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs) =>
                  StarkedAir.Circuit.Composition.partTerms ρ p.1 p.2 sh)
                parts) *
            StarkedAir.Circuit.Composition.val ρ
              (StarkedAir.Circuit.Composition.partFold sh parts ([], nIn, nIn + 1)).2.2 :=
  @StarkedAir.Circuit.Composition.sys_sound

/-- StarkedAir.Circuit.Deep.colResps_sound -/
theorem compat_Circuit_Deep_colResps_sound : ∀ {t c base : ℕ} {offs : List ℤ} {L : List StarkedAir.Circuit.Deep.Label},
  (∀ (k : ℕ) (h : k < offs.length), L[base + k]? = Option.some (t, c, offs[k])) →
    ∀ r ∈ StarkedAir.Circuit.Deep.colResps t c base offs, L[r.idx]? = Option.some r.label :=
  @StarkedAir.Circuit.Deep.colResps_sound

/-- StarkedAir.Circuit.Deep.deepFrom_sound -/
theorem compat_Circuit_Deep_deepFrom_sound : ∀ {L : List StarkedAir.Circuit.Deep.Label} (tc : List (ℕ × List (List ℤ))) (base : ℕ),
  (∀ (i : ℕ) (h : i < (StarkedAir.Circuit.Deep.samples tc).length),
      L[base + i]? = Option.some (StarkedAir.Circuit.Deep.samples tc)[i]) →
    ∀ r ∈ StarkedAir.Circuit.Deep.deepFrom tc base, L[r.idx]? = Option.some r.label :=
  @StarkedAir.Circuit.Deep.deepFrom_sound

/-- StarkedAir.Circuit.Deep.deep_sound -/
theorem compat_Circuit_Deep_deep_sound : ∀ (tc : List (ℕ × List (List ℤ))),
  ∀ r ∈ StarkedAir.Circuit.Deep.deepList tc, (StarkedAir.Circuit.Deep.samples tc)[r.idx]? = Option.some r.label :=
  @StarkedAir.Circuit.Deep.deep_sound

/-- StarkedAir.Circuit.Deep.treeResps_sound -/
theorem compat_Circuit_Deep_treeResps_sound : ∀ (t : ℕ) {L : List StarkedAir.Circuit.Deep.Label} (cols : List (List ℤ)) (c base : ℕ),
  (∀ (i : ℕ) (h : i < (StarkedAir.Circuit.Deep.labelsFrom t cols c).length),
      L[base + i]? = Option.some (StarkedAir.Circuit.Deep.labelsFrom t cols c)[i]) →
    ∀ r ∈ StarkedAir.Circuit.Deep.treeResps t cols c base, L[r.idx]? = Option.some r.label :=
  @StarkedAir.Circuit.Deep.treeResps_sound

/-- StarkedAir.Circuit.EndToEnd.plain_leaf_valid -/
theorem compat_Circuit_EndToEnd_plain_leaf_valid : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} [inst : DecidableEq StarkedAir.Spec.QM31.QM]
  (parts : List (StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs))
  (sh : StarkedAir.Circuit.Composition.Shared) (nIn oodsX nB : ℕ) (xs : List StarkedAir.Circuit.Composition.ExtE)
  (pub : ℕ → StarkedAir.F) (C : StarkedAir.Spec.QM31.QM),
  parts.length = 2 →
    (∀ (i : ℕ) (hi : i < parts.length), parts[i].1 = StarkedAir.HeaderTree.sys.comp i) →
      8 ≤ sh.logSize →
        sh.logSize ≤ 28 →
          StarkedAir.Circuit.EndToEnd.extRaw ρ xs =
              [(StarkedAir.HeaderTree.REL_NODE,
                  (↑(sh.logSize - 8) : StarkedAir.F) :: 0 :: StarkedAir.HeaderTree.pubT pub, -1)] →
            (∀ p ∈ parts,
                ∀ (j : ℕ), StarkedAir.Circuit.Composition.val ρ (p.2.ci.pub j) = StarkedAir.Spec.QM31.emb (pub j)) →
              (∀ e ∈ xs, ∀ r ∈ e.vals, StarkedAir.Circuit.Composition.val ρ r = StarkedAir.Spec.QM31.emb (ρ r).a) →
                (∀ p ∈ parts,
                    StarkedAir.Circuit.Composition.WF (StarkedAir.Circuit.Composition.pNodes p.1) ∧
                      ∀ id ∈ StarkedAir.Circuit.Composition.pIds p.1,
                        id < (StarkedAir.Circuit.Composition.pNodes p.1).size) →
                  (∀ (q : ℕ),
                      StarkedAir.Circuit.Op.hook 2 [] [q] ∈
                          (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).1 →
                        StarkedAir.Circuit.Composition.val ρ q =
                          StarkedAir.Spec.QM31.emb (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F)) →
                    StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).1 →
                      StarkedAir.Circuit.Composition.val ρ
                            (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).2 =
                          C →
                        StarkedAir.Circuit.Holds ρ
                            (StarkedAir.Circuit.Composition.balanceProg nB
                              (List.map
                                (fun (x : StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs) => x.2.claimed)
                                parts)
                              xs sh.z sh.alpha) →
                          StarkedAir.Circuit.EndToEnd.StarkSound sh.logSize pub
                              (StarkedAir.Circuit.Composition.val ρ sh.alpha)
                              (StarkedAir.Circuit.Composition.val ρ sh.z)
                              (StarkedAir.Circuit.Composition.val ρ sh.coeff)
                              (StarkedAir.Circuit.Composition.val ρ
                                (StarkedAir.Circuit.Composition.partFold sh parts ([], nIn, nIn + 1)).2.2)
                              C
                              (List.map
                                (fun (p : StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs) =>
                                  (p.1,
                                    StarkedAir.Circuit.Composition.val ρ p.2.claimed *
                                      StarkedAir.Spec.QM31.emb
                                        (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F),
                                    StarkedAir.Circuit.EndToEnd.oodsVal ρ p.1 p.2))
                                parts) →
                            ∃ (main : ℕ → ℕ → ℕ → StarkedAir.F),
                              StarkedAir.Circuit.EndToEnd.SZGood
                                  (List.map StarkedAir.LogUpSZ.toEntry
                                    (StarkedAir.LogUpSZ.siteRaw StarkedAir.HeaderTree.sys
                                        (StarkedAir.Circuit.EndToEnd.instOf sh.logSize main) pub ++
                                      StarkedAir.Circuit.EndToEnd.extRaw ρ xs))
                                  (StarkedAir.Circuit.Composition.val ρ sh.alpha)
                                  (StarkedAir.Circuit.Composition.val ρ sh.z) →
                                StarkedAir.HeaderTree.PubValidT pub :=
  @StarkedAir.Circuit.EndToEnd.plain_leaf_valid

/-- StarkedAir.Circuit.EndToEnd.plain_sound -/
theorem compat_Circuit_EndToEnd_plain_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} [inst : DecidableEq StarkedAir.Spec.QM31.QM] (sys : StarkedAir.System)
  (parts : List (StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs))
  (sh : StarkedAir.Circuit.Composition.Shared) (nIn oodsX nB : ℕ) (xs : List StarkedAir.Circuit.Composition.ExtE)
  (pub : ℕ → StarkedAir.F) (C : StarkedAir.Spec.QM31.QM),
  parts.length = sys.m →
    (∀ (i : ℕ) (hi : i < parts.length), parts[i].1 = sys.comp i) →
      (∀ i < sys.m, (sys.comp i).lookups ≠ []) →
        StarkedAir.LogUpSZ.StaticOk sys = Bool.true →
          (∀ e ∈ StarkedAir.Circuit.EndToEnd.extRaw ρ xs, (e.1, e.2.1.length) ∈ StarkedAir.LogUpSZ.shapes sys) →
            (∀ p ∈ parts,
                ∀ (j : ℕ), StarkedAir.Circuit.Composition.val ρ (p.2.ci.pub j) = StarkedAir.Spec.QM31.emb (pub j)) →
              (∀ e ∈ xs, ∀ r ∈ e.vals, StarkedAir.Circuit.Composition.val ρ r = StarkedAir.Spec.QM31.emb (ρ r).a) →
                (∀ p ∈ parts,
                    StarkedAir.Circuit.Composition.WF (StarkedAir.Circuit.Composition.pNodes p.1) ∧
                      ∀ id ∈ StarkedAir.Circuit.Composition.pIds p.1,
                        id < (StarkedAir.Circuit.Composition.pNodes p.1).size) →
                  (∀ (q : ℕ),
                      StarkedAir.Circuit.Op.hook 2 [] [q] ∈
                          (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).1 →
                        StarkedAir.Circuit.Composition.val ρ q =
                          StarkedAir.Spec.QM31.emb (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F)) →
                    StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).1 →
                      StarkedAir.Circuit.Composition.val ρ
                            (StarkedAir.Circuit.Composition.sysProg parts sh nIn oodsX).2 =
                          C →
                        StarkedAir.Circuit.Holds ρ
                            (StarkedAir.Circuit.Composition.balanceProg nB
                              (List.map
                                (fun (x : StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs) => x.2.claimed)
                                parts)
                              xs sh.z sh.alpha) →
                          StarkedAir.Circuit.EndToEnd.StarkSound sh.logSize pub
                              (StarkedAir.Circuit.Composition.val ρ sh.alpha)
                              (StarkedAir.Circuit.Composition.val ρ sh.z)
                              (StarkedAir.Circuit.Composition.val ρ sh.coeff)
                              (StarkedAir.Circuit.Composition.val ρ
                                (StarkedAir.Circuit.Composition.partFold sh parts ([], nIn, nIn + 1)).2.2)
                              C
                              (List.map
                                (fun (p : StarkedAir.Comp × StarkedAir.Circuit.Composition.PartRegs) =>
                                  (p.1,
                                    StarkedAir.Circuit.Composition.val ρ p.2.claimed *
                                      StarkedAir.Spec.QM31.emb
                                        (↑(StarkedAir.Circuit.Composition.ninv sh.logSize) : StarkedAir.F),
                                    StarkedAir.Circuit.EndToEnd.oodsVal ρ p.1 p.2))
                                parts) →
                            ∃ (main : ℕ → ℕ → ℕ → StarkedAir.F),
                              (∀ i < sys.m, (sys.comp i).air.Satisfied sh.logSize pub (main i)) ∧
                                (StarkedAir.Circuit.EndToEnd.SZGood
                                    (List.map StarkedAir.LogUpSZ.toEntry
                                      (StarkedAir.LogUpSZ.siteRaw sys
                                          (StarkedAir.Circuit.EndToEnd.instOf sh.logSize main) pub ++
                                        StarkedAir.Circuit.EndToEnd.extRaw ρ xs))
                                    (StarkedAir.Circuit.Composition.val ρ sh.alpha)
                                    (StarkedAir.Circuit.Composition.val ρ sh.z) →
                                  sys.SatisfiedExt (StarkedAir.Circuit.EndToEnd.instOf sh.logSize main) pub
                                    (StarkedAir.Circuit.EndToEnd.extRaw ρ xs)) :=
  @StarkedAir.Circuit.EndToEnd.plain_sound

/-- StarkedAir.Circuit.HeaderRec.header_root_sound -/
theorem compat_Circuit_HeaderRec_header_root_sound : ∀ {Acc SatC : List StarkedAir.Spec.Blake2s.Word → List StarkedAir.Spec.Blake2s.Word → Prop}
  {VGates : (ℕ → StarkedAir.Circuit.Q) → ℕ → List ℕ → List ℕ → Prop} {leafH : ℕ → List StarkedAir.Spec.Blake2s.Word}
  {nodeH : List StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.BlockRec.Trust Acc SatC VGates leafH nodeH StarkedAir.Circuit.nodeProgram
      StarkedAir.Circuit.HeaderRec.LeafOutH →
    (∀ (L : ℕ), (leafH L).length = 8) →
      nodeH.length = 8 →
        ∀ (t : StarkedAir.Circuit.BlockRec.Tree) (p : ℕ → StarkedAir.F),
          Acc (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH t)
              (StarkedAir.Circuit.HeaderRec.pubDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH t) p) →
            (∀ c ∈ StarkedAir.HeaderTree.genesisChecks, ZMod.val (p c.1) = c.2) →
              (∃ (n : ℕ) (hs : ℕ → ℕ → StarkedAir.Spec.Sha256.Word),
                  StarkedAir.Spec.Bitcoin.SegmentValid n hs
                      { prevHash := StarkedAir.HeaderChain.pubState p 0, height := 0,
                        prevNBits := StarkedAir.HeaderChain.leN (StarkedAir.HeaderChain.pubWord p 34),
                        prevTime := StarkedAir.HeaderChain.leN (StarkedAir.HeaderChain.pubWord p 44),
                        prevPst := StarkedAir.HeaderChain.leN (StarkedAir.HeaderChain.pubWord p 36), window := [],
                        work := 0 }
                      (StarkedAir.HeaderChain.decodeOut p) ∧
                    StarkedAir.HeaderChain.pubState p 0 = StarkedAir.HeaderChain.pubState (fun (x : ℕ) => 0) 0 ∧
                      ∃ (t : StarkedAir.Spec.HeaderTree.HTree),
                        t.leaves = List.map (fun (j : ℕ) => StarkedAir.Spec.Bitcoin.sha256d (hs j)) (List.range n) ∧
                          StarkedAir.HeaderTree.pubT p = StarkedAir.HeaderTree.limbsOf t.root) ∨
                StarkedAir.Circuit.BlockRec.Collision :=
  @StarkedAir.Circuit.HeaderRec.header_root_sound

/-- StarkedAir.Circuit.HeaderRec.htree_sound -/
theorem compat_Circuit_HeaderRec_htree_sound : ∀ {Acc SatC : List StarkedAir.Spec.Blake2s.Word → List StarkedAir.Spec.Blake2s.Word → Prop}
  {VGates : (ℕ → StarkedAir.Circuit.Q) → ℕ → List ℕ → List ℕ → Prop} {leafH : ℕ → List StarkedAir.Spec.Blake2s.Word}
  {nodeH : List StarkedAir.Spec.Blake2s.Word},
  StarkedAir.Circuit.BlockRec.Trust Acc SatC VGates leafH nodeH StarkedAir.Circuit.nodeProgram
      StarkedAir.Circuit.HeaderRec.LeafOutH →
    (∀ (L : ℕ), (leafH L).length = 8) →
      nodeH.length = 8 →
        ∀ (t : StarkedAir.Circuit.BlockRec.Tree) (p : ℕ → StarkedAir.F),
          SatC (StarkedAir.Circuit.BlockRec.Tree.hash leafH nodeH t)
              (StarkedAir.Circuit.HeaderRec.pubDigest (StarkedAir.Circuit.BlockRec.Tree.key leafH nodeH t) p) →
            StarkedAir.HeaderTree.PubValidT p ∨ StarkedAir.Circuit.BlockRec.Collision :=
  @StarkedAir.Circuit.HeaderRec.htree_sound

/-- StarkedAir.Circuit.leaf_sound -/
theorem compat_Circuit_leaf_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {vals : List ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.leafHash n vals).ops →
    4 * vals.length < 2 ^ 32 →
      ∀ i < 8,
        (ρ ((StarkedAir.Circuit.leafHash n vals).res.getD i 0)).word =
          StarkedAir.Circuit.blake2sWords (List.map (fun (r : ℕ) => BitVec.ofNat 32 (ZMod.val (ρ r).a)) vals)
            (4 * vals.length) i :=
  @StarkedAir.Circuit.leaf_sound

/-- StarkedAir.Circuit.Merkle.flip_sound -/
theorem compat_Circuit_Merkle_flip_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n bit a b : ℕ} {β : Bool},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Merkle.flipOps n bit a b) →
    ρ bit = StarkedAir.Circuit.Merkle.bitQ β →
      (ρ (n + 2) = if β = Bool.true then ρ b else ρ a) ∧ ρ (n + 3) = if β = Bool.true then ρ a else ρ b :=
  @StarkedAir.Circuit.Merkle.flip_sound

/-- StarkedAir.Circuit.Merkle.node_sound -/
theorem compat_Circuit_Merkle_node_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {cur sib : List ℕ} {bit : ℕ} {β : Bool},
  cur.length = 8 →
    sib.length = 8 →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Merkle.node n cur sib bit).ops →
        ρ bit = StarkedAir.Circuit.Merkle.bitQ β →
          List.map (StarkedAir.Circuit.Q.word ∘ ρ) (StarkedAir.Circuit.Merkle.node n cur sib bit).res =
            StarkedAir.Circuit.Merkle.specNode (List.map (StarkedAir.Circuit.Q.word ∘ ρ) cur)
              (List.map (StarkedAir.Circuit.Q.word ∘ ρ) sib) β :=
  @StarkedAir.Circuit.Merkle.node_sound

/-- StarkedAir.Circuit.Merkle.path_check_sound -/
theorem compat_Circuit_Merkle_path_check_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} (β : ℕ → Bool) {n : ℕ} {leaf root : List ℕ} {levels : List (ℕ × List ℕ)},
  leaf.length = 8 →
    root.length = 8 →
      (∀ p ∈ levels, p.2.length = 8 ∧ ρ p.1 = StarkedAir.Circuit.Merkle.bitQ (β p.1)) →
        StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Merkle.pathCheck n leaf levels root).ops →
          List.map (StarkedAir.Circuit.Q.word ∘ ρ) root =
            StarkedAir.Circuit.Merkle.specRoot (List.map (StarkedAir.Circuit.Q.word ∘ ρ) leaf)
              (List.map (fun (p : ℕ × List ℕ) => (β p.1, List.map (StarkedAir.Circuit.Q.word ∘ ρ) p.2)) levels) :=
  @StarkedAir.Circuit.Merkle.path_check_sound

/-- StarkedAir.Circuit.Merkle.path_sound -/
theorem compat_Circuit_Merkle_path_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} (β : ℕ → Bool) (n : ℕ) (cur : List ℕ) (levels : List (ℕ × List ℕ)),
  cur.length = 8 →
    (∀ p ∈ levels, p.2.length = 8 ∧ ρ p.1 = StarkedAir.Circuit.Merkle.bitQ (β p.1)) →
      StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Merkle.path n cur levels).ops →
        List.map (StarkedAir.Circuit.Q.word ∘ ρ) (StarkedAir.Circuit.Merkle.path n cur levels).res =
          StarkedAir.Circuit.Merkle.specRoot (List.map (StarkedAir.Circuit.Q.word ∘ ρ) cur)
            (List.map (fun (p : ℕ × List ℕ) => (β p.1, List.map (StarkedAir.Circuit.Q.word ∘ ρ) p.2)) levels) :=
  @StarkedAir.Circuit.Merkle.path_sound

/-- StarkedAir.Circuit.link_sound -/
theorem compat_Circuit_link_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {pl pr : ℕ → ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.linkChecks n pl pr).ops →
    StarkedAir.HeaderChain.PubLink (fun (k : ℕ) => (ρ (pl k)).a) fun (k : ℕ) => (ρ (pr k)).a :=
  @StarkedAir.Circuit.link_sound

/-- StarkedAir.Circuit.node_sound -/
theorem compat_Circuit_node_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.nodeProgram.ops →
    StarkedAir.HeaderChain.PubLink (StarkedAir.Circuit.nodePL ρ) (StarkedAir.Circuit.nodePR ρ) ∧
      StarkedAir.HeaderTree.NodeOut (StarkedAir.Circuit.nodePL ρ) (StarkedAir.Circuit.nodePR ρ)
        (StarkedAir.Circuit.nodeOut ρ) :=
  @StarkedAir.Circuit.node_sound

/-- StarkedAir.Circuit.range16_sound -/
theorem compat_Circuit_range16_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n x : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.range16 n x) → (ρ x).IsBase ∧ ZMod.val (ρ x).a < 65536 :=
  @StarkedAir.Circuit.range16_sound

/-- StarkedAir.Circuit.treeNode_sound -/
theorem compat_Circuit_treeNode_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {pl pr : ℕ → ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.treeNode n pl pr).ops →
    ∀ {a b : StarkedAir.Spec.Sha256.State},
      (StarkedAir.HeaderTree.pubT fun (k : ℕ) => (ρ (pl k)).a) = StarkedAir.HeaderTree.limbsOf a →
        (StarkedAir.HeaderTree.pubT fun (k : ℕ) => (ρ (pr k)).a) = StarkedAir.HeaderTree.limbsOf b →
          ∀ j < 16,
            (ρ ((StarkedAir.Circuit.treeNode n pl pr).res.getD j 0)).a =
              (StarkedAir.HeaderTree.limbsOf (StarkedAir.Spec.HeaderTree.hnode a b)).getD j 0 :=
  @StarkedAir.Circuit.treeNode_sound

/-- StarkedAir.Circuit.Oods.shift_sound -/
theorem compat_Circuit_Oods_shift_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n ox oy L : ℕ} {off : ℤ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Oods.shiftP n ox oy L off).ops →
    StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Oods.shiftP n ox oy L off).res.1) =
        StarkedAir.Spec.QM31.toQ (ρ ox) * StarkedAir.Spec.QM31.emb (StarkedAir.Circuit.Oods.shiftPt L off).x -
          StarkedAir.Spec.QM31.toQ (ρ oy) * StarkedAir.Spec.QM31.emb (StarkedAir.Circuit.Oods.shiftPt L off).y ∧
      StarkedAir.Spec.QM31.toQ (ρ (StarkedAir.Circuit.Oods.shiftP n ox oy L off).res.2) =
        StarkedAir.Spec.QM31.toQ (ρ ox) * StarkedAir.Spec.QM31.emb (StarkedAir.Circuit.Oods.shiftPt L off).y +
          StarkedAir.Spec.QM31.toQ (ρ oy) * StarkedAir.Spec.QM31.emb (StarkedAir.Circuit.Oods.shiftPt L off).x :=
  @StarkedAir.Circuit.Oods.shift_sound

/-- StarkedAir.Circuit.Pow.assertBit_sound -/
theorem compat_Circuit_Pow_assertBit_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {m x z : ℕ},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Pow.assertBit m x z) →
    ρ z = StarkedAir.Circuit.Q.lit 0 0 0 0 → (ρ x).a = 0 ∨ (ρ x).a = 1 :=
  @StarkedAir.Circuit.Pow.assertBit_sound

/-- StarkedAir.Circuit.Pow.powCheck_sound -/
theorem compat_Circuit_Pow_powCheck_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n lo hi nonce nBits : ℕ} {s : StarkedAir.Circuit.Channel.Spec.St},
  StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Pow.powCheckP n lo hi nonce nBits) →
    ρ lo = s.lo → ρ hi = s.hi → nBits ≤ 30 → StarkedAir.Circuit.Pow.Spec.powOk s (ρ nonce) nBits :=
  @StarkedAir.Circuit.Pow.powCheck_sound

/-- StarkedAir.Circuit.Pow.rounds_sound -/
theorem compat_Circuit_Pow_rounds_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {z inv2 : ℕ},
  ρ z = StarkedAir.Circuit.Q.lit 0 0 0 0 →
    ρ inv2 = StarkedAir.Circuit.Q.lit StarkedAir.Circuit.Pow.INV2 0 0 0 →
      ∀ (k n v : ℕ),
        StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Pow.rounds z inv2 k n v).1 →
          (∀ b ∈ (StarkedAir.Circuit.Pow.rounds z inv2 k n v).2.1, (ρ b).a = 0 ∨ (ρ b).a = 1) ∧
            (StarkedAir.Circuit.Pow.rounds z inv2 k n v).2.1.length = k ∧
              (ρ v).a =
                StarkedAir.Circuit.Pow.fold
                  (List.map (fun (b : ℕ) => (ρ b).a) (StarkedAir.Circuit.Pow.rounds z inv2 k n v).2.1)
                  (ρ (StarkedAir.Circuit.Pow.rounds z inv2 k n v).2.2.1).a :=
  @StarkedAir.Circuit.Pow.rounds_sound

/-- StarkedAir.Circuit.Statement.statement_sound -/
theorem compat_Circuit_Statement_statement_sound : ∀ {ρ : ℕ → StarkedAir.Circuit.Q} {n : ℕ} {system : Bool} {parts : List StarkedAir.Circuit.Statement.PartSt} {L : ℕ},
  L < 2 ^ 32 →
    (∀ p ∈ parts, (∀ w ∈ p.digest, w < 2 ^ 32) ∧ p.digest.length = 8 ∧ p.pubs.length < 2 ^ 32) →
      parts.length < 2 ^ 32 →
        (∀ (r : ℕ),
            StarkedAir.Circuit.Op.hook 4 [] [r] ∈ StarkedAir.Circuit.Statement.stmtOps n system parts →
              StarkedAir.Circuit.Statement.wv ρ r = L) →
          StarkedAir.Circuit.Holds ρ (StarkedAir.Circuit.Statement.stmtOps n system parts) →
            List.map (List.map (StarkedAir.Circuit.Statement.wv ρ))
                (StarkedAir.Circuit.Statement.mixArgs (StarkedAir.Circuit.Statement.stmtOps n system parts)) =
              StarkedAir.Circuit.Statement.stmtWords system L (StarkedAir.Circuit.Statement.stmtSpec ρ parts) :=
  @StarkedAir.Circuit.Statement.statement_sound

/-- StarkedAir.Block.epoch_coin_run -/
theorem compat_Block_epoch_coin_run : ∀ (N : ℕ → ℕ) (γ : StarkedAir.Spec.QM31.QM) (blocks : List StarkedAir.Spec.CoinEpoch.BlockC) (g0 : ℕ)
  (init fin : List StarkedAir.Spec.CoinEpoch.CEv) {S : Finset (List StarkedAir.F)},
  γ ∉ StarkedAir.Spec.Utxo.fpBad S →
    (∀
        e ∈
          init ++ (StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
            ((StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++ fin),
        StarkedAir.Block.WFE N e ∧ StarkedAir.Block.bytesF e ∈ S) →
      (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
          blocks[i]? = Option.some B →
            N B.h =
              g0 + (List.map (fun (x : StarkedAir.Spec.CoinEpoch.BlockC) => x.txs.length) (List.take i blocks)).sum) →
        (∀ (i i' : ℕ) (B B' : StarkedAir.Spec.CoinEpoch.BlockC),
            blocks[i]? = Option.some B → blocks[i']? = Option.some B' → (B.h < B'.h ↔ i < i')) →
          (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
              blocks[i]? = Option.some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25) →
            (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                blocks[i]? = Option.some B →
                  ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                    B.txs[t]? = Option.some tx →
                      ∀ e ∈ StarkedAir.Spec.CoinEpoch.txIns N B t tx,
                        ∃ (c : StarkedAir.Spec.CoinEpoch.Claim),
                          e = (e.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
                            (c.code < 2 ^ 26 → c.ctx < 2 ^ 25 → c.code / 2 < B.h ∨ c.code / 2 = B.h ∧ c.ctx < t)) →
              (∀ e ∈ init, e.2.2 < g0) →
                (Multiset.map Prod.fst
                      ((↑init : Multiset StarkedAir.Spec.CoinEpoch.CEv) +
                        StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks))).Nodup →
                  ∃ (Bad : Finset (StarkedAir.Spec.QM31.QM × StarkedAir.Spec.QM31.QM)),
                    Bad.card ≤
                        ((StarkedAir.LogUpSZ.polys (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
                            2 * (StarkedAir.LogUpSZ.polys (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card) *
                          Fintype.card StarkedAir.Spec.QM31.QM ∧
                      ∀ az ∉ Bad,
                        init.length +
                                  (StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                (StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                              fin.length <
                            StarkedAir.P →
                          (List.map (StarkedAir.Block.blockSum N (StarkedAir.Block.efrac N γ az.1 az.2)) blocks).sum +
                                (List.map (StarkedAir.Block.efrac N γ az.1 az.2) init).sum =
                              (List.map (StarkedAir.Block.efrac N γ az.1 az.2) fin).sum →
                            ∃ (m :
                              StarkedAir.Spec.Utxo.View StarkedAir.Spec.Block.OutPoint StarkedAir.Spec.CoinEpoch.Val),
                              StarkedAir.Spec.Utxo.run g0 (StarkedAir.Spec.Utxo.viewOf init)
                                    (StarkedAir.Spec.CoinEpoch.allTxs N blocks) =
                                  Option.some m ∧
                                ∀ (k : StarkedAir.Spec.Block.OutPoint) (v : StarkedAir.Spec.CoinEpoch.Val) (j : ℕ),
                                  m k = Option.some (v, j) ↔ (k, v, j) ∈ fin :=
  @StarkedAir.Block.epoch_coin_run

/-- StarkedAir.Block.epoch_balance -/
theorem compat_Block_epoch_balance : ∀ (N : ℕ → ℕ) (γ : StarkedAir.Spec.QM31.QM) (blocks : List StarkedAir.Spec.CoinEpoch.BlockC) (g0 : ℕ)
  (init fin : List StarkedAir.Spec.CoinEpoch.CEv),
  ∃ (Bad : Finset (StarkedAir.Spec.QM31.QM × StarkedAir.Spec.QM31.QM)),
    Bad.card ≤
        ((StarkedAir.LogUpSZ.polys (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card ^ 2 * 27 +
            2 * (StarkedAir.LogUpSZ.polys (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card) *
          Fintype.card StarkedAir.Spec.QM31.QM ∧
      ∀ az ∉ Bad,
        (∀
            e ∈
              init ++ (StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
                ((StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++ fin),
            ∀
              e' ∈
                init ++ (StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
                  ((StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++ fin),
              StarkedAir.Block.encE N γ e = StarkedAir.Block.encE N γ e' → e = e') →
          init.length + (StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                  (StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                fin.length <
              StarkedAir.P →
            (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                blocks[i]? = Option.some B →
                  N B.h =
                    g0 +
                      (List.map (fun (x : StarkedAir.Spec.CoinEpoch.BlockC) => x.txs.length)
                          (List.take i blocks)).sum) →
              (List.map (StarkedAir.Block.blockSum N (StarkedAir.Block.efrac N γ az.1 az.2)) blocks).sum +
                    (List.map (StarkedAir.Block.efrac N γ az.1 az.2) init).sum =
                  (List.map (StarkedAir.Block.efrac N γ az.1 az.2) fin).sum →
                (↑init : Multiset StarkedAir.Spec.CoinEpoch.CEv) +
                    StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks) =
                  StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks) +
                    (↑fin : Multiset StarkedAir.Spec.CoinEpoch.CEv) :=
  @StarkedAir.Block.epoch_balance

/-- StarkedAir.Block.epoch_sums -/
theorem compat_Block_epoch_sums : ∀ (N : ℕ → ℕ) (f : StarkedAir.Spec.CoinEpoch.CEv → StarkedAir.Spec.QM31.QM)
  (blocks : List StarkedAir.Spec.CoinEpoch.BlockC) (g : ℕ),
  (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
      blocks[i]? = Option.some B →
        N B.h = g + (List.map (fun (x : StarkedAir.Spec.CoinEpoch.BlockC) => x.txs.length) (List.take i blocks)).sum) →
    (Multiset.map f (StarkedAir.Spec.Utxo.created g (StarkedAir.Spec.CoinEpoch.allTxs N blocks))).sum -
        (Multiset.map f (StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks))).sum =
      (List.map (StarkedAir.Block.blockSum N f) blocks).sum :=
  @StarkedAir.Block.epoch_sums

/-- StarkedAir.Block.epoch_systems_wf -/
theorem compat_Block_epoch_systems_wf : ∀ (nb : ℕ) (inst : ℕ → ℕ → StarkedAir.Inst) (pub : ℕ → ℕ → StarkedAir.F) (L : ℕ → ℕ),
  (∀ i < nb, ∀ c < 15, (inst i c).logSize = L i) →
    (∀ i < nb, StarkedAir.Block.hashSys.SatisfiedExt (inst i) (pub i) []) →
      (∀ i < nb, L i ≤ 23) →
        ∀ (S : (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)) (h0 : ℕ),
          h0 + nb ≤ 2 ^ 23 →
            (∀ i < nb, pub i 2 = (↑(h0 + i) : StarkedAir.F)) →
              (∀ i < nb,
                  pub i StarkedAir.Block.Coin.PUB_LOST =
                    if StarkedAir.Spec.Coins.bip30Lost (h0 + i) = Bool.true then 1 else 0) →
                ∀ (γ α z : StarkedAir.Spec.QM31.QM),
                  (∀ i < nb, StarkedAir.Block.FpWalk.gQ (pub i) = γ) →
                    (∀ i < nb, StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_Z = z) →
                      (∀ i < nb,
                          ∀ k < StarkedAir.Block.Coin.W,
                            StarkedAir.Block.RunSum.pQ (pub i) (StarkedAir.Block.Coin.PUB_ALPHA k) = α ^ k) →
                        ∃ (blocks : List StarkedAir.Spec.CoinEpoch.BlockC),
                          blocks.length = nb ∧
                            (∀ i < nb,
                                ∃ (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                  blocks[i]? = Option.some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs) ∧
                              ∀ (N : ℕ → ℕ) (g0 : ℕ) (init fin : List StarkedAir.Spec.CoinEpoch.CEv)
                                (Sb : Finset (List StarkedAir.F)),
                                γ ∉ StarkedAir.Spec.Utxo.fpBad Sb →
                                  (∀ e ∈ init ++ fin, StarkedAir.Block.WFE N e) →
                                    (∀
                                        e ∈
                                          init ++
                                              (StarkedAir.Spec.Utxo.created g0
                                                  (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
                                            ((StarkedAir.Spec.Utxo.spent
                                                  (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
                                              fin),
                                        StarkedAir.Block.bytesF e ∈ Sb) →
                                      (∀ i < nb, N (h0 + i) = g0 + ∑ i' ∈ Finset.range i, (S i').b.txs.length) →
                                        (∀ e ∈ init, e.2.2 < g0) →
                                          (∀ e ∈ init, StarkedAir.Block.RealVal e.2.1) →
                                            (Multiset.map Prod.fst
                                                  ((↑init : Multiset StarkedAir.Spec.CoinEpoch.CEv) +
                                                    StarkedAir.Spec.Utxo.created g0
                                                      (StarkedAir.Spec.CoinEpoch.allTxs N blocks))).Nodup →
                                              ∃ (Bad : Finset (StarkedAir.Spec.QM31.QM × StarkedAir.Spec.QM31.QM)),
                                                Bad.card ≤
                                                    ((StarkedAir.LogUpSZ.polys
                                                                (StarkedAir.Block.epochPN N γ blocks g0 init
                                                                  fin)).card ^
                                                            2 *
                                                          27 +
                                                        2 *
                                                          (StarkedAir.LogUpSZ.polys
                                                              (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card) *
                                                      Fintype.card StarkedAir.Spec.QM31.QM ∧
                                                  ((α, z) ∉ Bad →
                                                    init.length +
                                                              (StarkedAir.Spec.Utxo.created g0
                                                                  (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                                            (StarkedAir.Spec.Utxo.spent
                                                                (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                                          fin.length <
                                                        StarkedAir.P →
                                                      ∑ i ∈ Finset.range nb,
                                                              StarkedAir.Block.RunSum.pQ (pub i)
                                                                StarkedAir.Block.Coin.PUB_S +
                                                            (List.map (StarkedAir.Block.efrac N γ α z) init).sum =
                                                          (List.map (StarkedAir.Block.efrac N γ α z) fin).sum →
                                                        (∃ (m :
                                                            StarkedAir.Spec.Utxo.View StarkedAir.Spec.Block.OutPoint
                                                              StarkedAir.Spec.CoinEpoch.Val),
                                                            StarkedAir.Spec.Coins.connectTxs
                                                                  (StarkedAir.Spec.Coins.untag
                                                                    (StarkedAir.Spec.Utxo.vmap
                                                                      StarkedAir.Spec.CoinEpoch.coinOfVal
                                                                      (StarkedAir.Spec.Utxo.viewOf init)))
                                                                  (StarkedAir.Spec.CoinEpoch.allTxC N blocks) =
                                                                Option.some
                                                                  (StarkedAir.Spec.Coins.untag
                                                                      (StarkedAir.Spec.Utxo.vmap
                                                                        StarkedAir.Spec.CoinEpoch.coinOfVal m),
                                                                    List.map StarkedAir.Spec.Coins.claimFee
                                                                      (StarkedAir.Spec.CoinEpoch.allTxC N blocks)) ∧
                                                              ∀ (k : StarkedAir.Spec.Block.OutPoint)
                                                                (v : StarkedAir.Spec.CoinEpoch.Val) (j : ℕ),
                                                                m k = Option.some (v, j) ↔ (k, v, j) ∈ fin) ∧
                                                          ∀ i < nb,
                                                            ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                                              (S i).b.txs[t]? = Option.some tx →
                                                                1 ≤ t →
                                                                  StarkedAir.Spec.Block.nodupBy
                                                                      (List.map
                                                                        (fun (x : StarkedAir.Spec.Block.TxIn) =>
                                                                          x.prevout)
                                                                        tx.vin) =
                                                                    Bool.true) :=
  fun nb inst pub L hL hsat hL24 => StarkedAir.Block.epoch_systems_wf nb inst pub (fun i _ => L i) hL hsat
    (fun i hi _ _ => hL24 i hi)

/-- StarkedAir.Block.created_wfe_systems -/
theorem compat_Block_created_wfe_systems : ∀ {nb : ℕ} {inst : ℕ → ℕ → StarkedAir.Inst} {pub : ℕ → ℕ → StarkedAir.F} {L : ℕ → ℕ}
  (S : (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)) {h0 : ℕ},
  h0 + nb ≤ 2 ^ 23 →
    ∀ {blocks : List StarkedAir.Spec.CoinEpoch.BlockC},
      blocks.length = nb →
        (∀ i < nb,
            ∃ (B : StarkedAir.Spec.CoinEpoch.BlockC), blocks[i]? = Option.some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs) →
          ∀ (N : ℕ → ℕ) (g0 : ℕ),
            (∀ i < nb, N (h0 + i) = g0 + ∑ i' ∈ Finset.range i, (S i').b.txs.length) →
              ∀ e ∈ StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks),
                StarkedAir.Block.WFE N e :=
  @StarkedAir.Block.created_wfe_systems

/-- StarkedAir.Block.epoch_hyps_of_rng -/
theorem compat_Block_epoch_hyps_of_rng : ∀ {r : StarkedAir.Block.Rng},
  StarkedAir.Block.RngOk r →
    0 < r.n →
      ∃ (pub : ℕ → ℕ → StarkedAir.F) (inst : ℕ → ℕ → StarkedAir.Inst) (L : ℕ → ℕ) (x :
        (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)),
        (∀ i < r.n, ∀ c < 15, (inst i c).logSize = L i) ∧
          (∀ i < r.n, StarkedAir.Block.hashSys.SatisfiedExt (inst i) (pub i) []) ∧
            (∀ i < r.n, L i ≤ 23) ∧
              (∀ i < r.n, pub i 2 = (↑(r.lo + i) : StarkedAir.F)) ∧
                (∀ i < r.n,
                    pub i StarkedAir.Block.Coin.PUB_LOST =
                      if StarkedAir.Spec.Coins.bip30Lost (r.lo + i) = Bool.true then 1 else 0) ∧
                  (∀ i < r.n, StarkedAir.Block.FpWalk.gQ (pub i) = r.γ) ∧
                    (∀ i < r.n, StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_Z = r.z) ∧
                      (∀ i < r.n,
                          ∀ k < StarkedAir.Block.Coin.W,
                            StarkedAir.Block.RunSum.pQ (pub i) (StarkedAir.Block.Coin.PUB_ALPHA k) = r.α ^ k) ∧
                        ∑ i ∈ Finset.range r.n, StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_S = r.s :=
  @StarkedAir.Block.epoch_hyps_of_rng

/-- StarkedAir.Block.rng_leaf -/
theorem compat_Block_rng_leaf : ∀ {h : ℕ} {p : ℕ → StarkedAir.F},
  StarkedAir.Block.BlockPubOk p →
    p 2 = (↑h : StarkedAir.F) →
      (p StarkedAir.Block.Coin.PUB_LOST = if StarkedAir.Spec.Coins.bip30Lost h = Bool.true then 1 else 0) →
        (∀ k < StarkedAir.Block.Coin.W,
            StarkedAir.Block.RunSum.pQ p (StarkedAir.Block.Coin.PUB_ALPHA k) =
              StarkedAir.Block.RunSum.pQ p (StarkedAir.Block.Coin.PUB_ALPHA 1) ^ k) →
          StarkedAir.Block.RngOk (StarkedAir.Block.leafRng h p) :=
  @StarkedAir.Block.rng_leaf

/-- StarkedAir.Block.rng_node -/
theorem compat_Block_rng_node : ∀ {l r : StarkedAir.Block.Rng},
  StarkedAir.Block.RngOk l →
    StarkedAir.Block.RngOk r →
      r.lo = l.lo + l.n → r.γ = l.γ → r.z = l.z → r.α = l.α → StarkedAir.Block.RngOk (StarkedAir.Block.joinRng l r) :=
  @StarkedAir.Block.rng_node

/-- StarkedAir.Block.epoch_core -/
theorem compat_Block_epoch_core : ∀ (N : ℕ → ℕ) (γ : StarkedAir.Spec.QM31.QM) (blocks : List StarkedAir.Spec.CoinEpoch.BlockC) (g0 : ℕ)
  (init fin : List StarkedAir.Spec.CoinEpoch.CEv) {S : Finset (List StarkedAir.F)},
  γ ∉ StarkedAir.Spec.Utxo.fpBad S →
    (∀
        e ∈
          init ++ (StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++
            ((StarkedAir.Spec.Utxo.spent (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).toList ++ fin),
        StarkedAir.Block.WFE N e ∧ StarkedAir.Block.bytesF e ∈ S) →
      (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
          blocks[i]? = Option.some B →
            N B.h =
              g0 + (List.map (fun (x : StarkedAir.Spec.CoinEpoch.BlockC) => x.txs.length) (List.take i blocks)).sum) →
        (∀ (i i' : ℕ) (B B' : StarkedAir.Spec.CoinEpoch.BlockC),
            blocks[i]? = Option.some B → blocks[i']? = Option.some B' → (B.h < B'.h ↔ i < i')) →
          (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
              blocks[i]? = Option.some B → B.h < 2 ^ 24 ∧ B.txs.length < 2 ^ 25) →
            (∀ e ∈ init, e.2.2 < g0) →
              (∀ e ∈ init, StarkedAir.Block.RealVal e.2.1) →
                (Multiset.map Prod.fst
                      ((↑init : Multiset StarkedAir.Spec.CoinEpoch.CEv) +
                        StarkedAir.Spec.Utxo.created g0 (StarkedAir.Spec.CoinEpoch.allTxs N blocks))).Nodup →
                  (∀ B ∈ blocks, ∀ tx ∈ B.txs, ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ StarkedAir.Spec.Block.MAX_MONEY) →
                    (∀ B ∈ blocks, B.lost = StarkedAir.Spec.Coins.bip30Lost B.h) →
                      (∀ B ∈ blocks, ∀ tx ∈ B.txs, StarkedAir.Spec.Coins.outSum tx ≤ StarkedAir.Spec.Block.MAX_MONEY) →
                        (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                            blocks[i]? = Option.some B →
                              ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                B.txs[t]? = Option.some tx →
                                  ∀ ev ∈ StarkedAir.Spec.CoinEpoch.txIns N B t tx,
                                    ∃ (c : StarkedAir.Spec.CoinEpoch.Claim),
                                      ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
                                        (c.code < 2 ^ 26 →
                                          c.ctx < 2 ^ 25 → c.code / 2 < B.h ∨ c.code / 2 = B.h ∧ c.ctx < t)) →
                          (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                              blocks[i]? = Option.some B →
                                ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                  B.txs[t]? = Option.some tx →
                                    1 ≤ t →
                                      (∀ k < tx.vin.length,
                                          StarkedAir.Block.RealVal ((B.claim t k).code, (B.claim t k).ser)) →
                                        StarkedAir.Spec.Coins.outSum tx ≤ StarkedAir.Spec.Block.MAX_MONEY →
                                          StarkedAir.Spec.Coins.ClaimsOK (StarkedAir.Spec.CoinEpoch.txcOf N B t tx)) →
                            ∃ (Bad : Finset (StarkedAir.Spec.QM31.QM × StarkedAir.Spec.QM31.QM)),
                              Bad.card ≤
                                  ((StarkedAir.LogUpSZ.polys (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card ^
                                          2 *
                                        27 +
                                      2 *
                                        (StarkedAir.LogUpSZ.polys
                                            (StarkedAir.Block.epochPN N γ blocks g0 init fin)).card) *
                                    Fintype.card StarkedAir.Spec.QM31.QM ∧
                                ∀ az ∉ Bad,
                                  init.length +
                                            (StarkedAir.Spec.Utxo.created g0
                                                (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                          (StarkedAir.Spec.Utxo.spent
                                              (StarkedAir.Spec.CoinEpoch.allTxs N blocks)).card +
                                        fin.length <
                                      StarkedAir.P →
                                    (List.map (StarkedAir.Block.blockSum N (StarkedAir.Block.efrac N γ az.1 az.2))
                                              blocks).sum +
                                          (List.map (StarkedAir.Block.efrac N γ az.1 az.2) init).sum =
                                        (List.map (StarkedAir.Block.efrac N γ az.1 az.2) fin).sum →
                                      (∃ (m :
                                          StarkedAir.Spec.Utxo.View StarkedAir.Spec.Block.OutPoint
                                            StarkedAir.Spec.CoinEpoch.Val),
                                          StarkedAir.Spec.Coins.connectTxs
                                                (StarkedAir.Spec.Coins.untag
                                                  (StarkedAir.Spec.Utxo.vmap StarkedAir.Spec.CoinEpoch.coinOfVal
                                                    (StarkedAir.Spec.Utxo.viewOf init)))
                                                (StarkedAir.Spec.CoinEpoch.allTxC N blocks) =
                                              Option.some
                                                (StarkedAir.Spec.Coins.untag
                                                    (StarkedAir.Spec.Utxo.vmap StarkedAir.Spec.CoinEpoch.coinOfVal m),
                                                  List.map StarkedAir.Spec.Coins.claimFee
                                                    (StarkedAir.Spec.CoinEpoch.allTxC N blocks)) ∧
                                            ∀ (k : StarkedAir.Spec.Block.OutPoint) (v : StarkedAir.Spec.CoinEpoch.Val)
                                              (j : ℕ), m k = Option.some (v, j) ↔ (k, v, j) ∈ fin) ∧
                                        ∀ B ∈ blocks,
                                          ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                            B.txs[t]? = Option.some tx →
                                              1 ≤ t →
                                                StarkedAir.Spec.Block.nodupBy
                                                    (List.map (fun (x : StarkedAir.Spec.Block.TxIn) => x.prevout)
                                                      tx.vin) =
                                                  Bool.true :=
  @StarkedAir.Block.epoch_core

/-- StarkedAir.Block.epoch_blocks -/
theorem compat_Block_epoch_blocks : ∀ (nb : ℕ) (inst : ℕ → ℕ → StarkedAir.Inst) (pub : ℕ → ℕ → StarkedAir.F) (L : ℕ → ℕ),
  (∀ i < nb, ∀ c < 15, (inst i c).logSize = L i) →
    (∀ i < nb, StarkedAir.Block.hashSys.SatisfiedExt (inst i) (pub i) []) →
      (∀ i < nb, L i ≤ 23) →
        ∀ (S : (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)) (h0 : ℕ),
          h0 + nb ≤ 2 ^ 23 →
            (∀ i < nb, pub i 2 = (↑(h0 + i) : StarkedAir.F)) →
              ∀ (lost : ℕ → Bool),
                (∀ i < nb, pub i StarkedAir.Block.Coin.PUB_LOST = if lost i = Bool.true then 1 else 0) →
                  ∀ (γ α z : StarkedAir.Spec.QM31.QM),
                    (∀ i < nb, StarkedAir.Block.FpWalk.gQ (pub i) = γ) →
                      (∀ i < nb, StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_Z = z) →
                        (∀ i < nb,
                            ∀ k < StarkedAir.Block.Coin.W,
                              StarkedAir.Block.RunSum.pQ (pub i) (StarkedAir.Block.Coin.PUB_ALPHA k) = α ^ k) →
                          ∃ (blocks : List StarkedAir.Spec.CoinEpoch.BlockC),
                            blocks.length = nb ∧
                              (∀ i < nb,
                                  ∃ (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                    blocks[i]? = Option.some B ∧ B.h = h0 + i ∧ B.txs = (S i).b.txs ∧ B.lost = lost i) ∧
                                (∀ B ∈ blocks,
                                    ∀ tx ∈ B.txs,
                                      (∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ StarkedAir.Spec.Block.MAX_MONEY) ∧
                                        StarkedAir.Spec.Coins.outSum tx ≤ StarkedAir.Spec.Block.MAX_MONEY) ∧
                                  ∀ (N : ℕ → ℕ),
                                    ∑ i ∈ Finset.range nb,
                                          StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_S =
                                        (List.map (StarkedAir.Block.blockSum N (StarkedAir.Block.efrac N γ α z))
                                            blocks).sum ∧
                                      (∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                          blocks[i]? = Option.some B →
                                            ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                              B.txs[t]? = Option.some tx →
                                                ∀ ev ∈ StarkedAir.Spec.CoinEpoch.txIns N B t tx,
                                                  ∃ (c : StarkedAir.Spec.CoinEpoch.Claim),
                                                    ev = (ev.1, (c.code, c.ser), N (c.code / 2) + c.ctx) ∧
                                                      (c.code < 2 ^ 26 →
                                                          c.ctx < 2 ^ 25 →
                                                            c.code / 2 < B.h ∨ c.code / 2 = B.h ∧ c.ctx < t) ∧
                                                        c.code < 2 ^ 32 ∧
                                                          c.ctx < 2 ^ 24 ∧ List.length c.ser < StarkedAir.P) ∧
                                        ∀ (i : ℕ) (B : StarkedAir.Spec.CoinEpoch.BlockC),
                                          blocks[i]? = Option.some B →
                                            ∀ (t : ℕ) (tx : StarkedAir.Spec.Block.Tx),
                                              B.txs[t]? = Option.some tx →
                                                1 ≤ t →
                                                  (∀ k < tx.vin.length,
                                                      StarkedAir.Block.RealVal
                                                        ((B.claim t k).code, (B.claim t k).ser)) →
                                                    StarkedAir.Spec.Coins.outSum tx ≤ StarkedAir.Spec.Block.MAX_MONEY →
                                                      StarkedAir.Spec.Coins.ClaimsOK
                                                        (StarkedAir.Spec.CoinEpoch.txcOf N B t tx) :=
  fun nb inst pub L hL hsat hL24 => StarkedAir.Block.epoch_blocks nb inst pub (fun i _ => L i) hL hsat
    (fun i hi _ _ => hL24 i hi)

/-- StarkedAir.Circuit.BlockTree.epoch_hyps_of_sum -/
theorem compat_Circuit_BlockTree_epoch_hyps_of_sum : ∀ {v : ℕ → StarkedAir.F},
  StarkedAir.Circuit.BlockTree.SumOk v →
    ∃ (ℓ : ℕ),
      ZMod.val (v 1) = 2 ^ ℓ ∧
        ∃ (pub : ℕ → ℕ → StarkedAir.F) (inst : ℕ → ℕ → StarkedAir.Inst) (L : ℕ → ℕ) (x :
          (i : ℕ) → StarkedAir.Block.Setup (inst i) (pub i) (L i)),
          (∀ i < 2 ^ ℓ, ∀ c < 15, (inst i c).logSize = L i) ∧
            (∀ i < 2 ^ ℓ, StarkedAir.Block.hashSys.SatisfiedExt (inst i) (pub i) []) ∧
              (∀ i < 2 ^ ℓ, L i ≤ 23) ∧
                (∀ i < 2 ^ ℓ, pub i 2 = (↑(ZMod.val (v 0) + i) : StarkedAir.F)) ∧
                  (∀ i < 2 ^ ℓ,
                      pub i StarkedAir.Block.Coin.PUB_LOST =
                        if StarkedAir.Spec.Coins.bip30Lost (ZMod.val (v 0) + i) = Bool.true then 1 else 0) ∧
                    (∀ i < 2 ^ ℓ, StarkedAir.Block.FpWalk.gQ (pub i) = StarkedAir.Block.RunSum.pQ v 7) ∧
                      (∀ i < 2 ^ ℓ,
                          StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_Z =
                            StarkedAir.Block.RunSum.pQ v 11) ∧
                        (∀ i < 2 ^ ℓ,
                            ∀ k < StarkedAir.Block.Coin.W,
                              StarkedAir.Block.RunSum.pQ (pub i) (StarkedAir.Block.Coin.PUB_ALPHA k) =
                                StarkedAir.Block.RunSum.pQ v 15 ^ k) ∧
                          ∑ i ∈ Finset.range (2 ^ ℓ), StarkedAir.Block.RunSum.pQ (pub i) StarkedAir.Block.Coin.PUB_S =
                            StarkedAir.Block.RunSum.pQ v 2 :=
  @StarkedAir.Circuit.BlockTree.epoch_hyps_of_sum

/-- StarkedAir.Circuit.BlockTree.forest_rng -/
theorem compat_Circuit_BlockTree_forest_rng : ∀ (vs : List (ℕ → StarkedAir.F)) (v0 : ℕ → StarkedAir.F),
  StarkedAir.Circuit.BlockTree.SumOk v0 →
    (∀ v ∈ vs, StarkedAir.Circuit.BlockTree.SumOk v) →
      StarkedAir.Circuit.BlockTree.Linked' v0 vs →
        (∀ v ∈ vs, ∀ i < 12, v (7 + i) = v0 (7 + i)) →
          ∃ (n : ℕ),
            StarkedAir.Block.RngOk
              { lo := ZMod.val (v0 0), n := n,
                s :=
                  StarkedAir.Block.RunSum.pQ v0 2 +
                    (List.map (fun (v : ℕ → StarkedAir.F) => StarkedAir.Block.RunSum.pQ v 2) vs).sum,
                nin := ZMod.val (v0 6) + (List.map (fun (v : ℕ → StarkedAir.F) => ZMod.val (v 6)) vs).sum,
                γ := StarkedAir.Block.RunSum.pQ v0 7, z := StarkedAir.Block.RunSum.pQ v0 11,
                α := StarkedAir.Block.RunSum.pQ v0 15 } :=
  @StarkedAir.Circuit.BlockTree.forest_rng

/-- StarkedAir.Circuit.BlockTree.rng_forest -/
theorem compat_Circuit_BlockTree_rng_forest : ∀ (rs : List StarkedAir.Block.Rng) (r0 : StarkedAir.Block.Rng),
  StarkedAir.Block.RngOk r0 →
    (∀ r ∈ rs, StarkedAir.Block.RngOk r) →
      StarkedAir.Circuit.BlockTree.Linked r0 rs →
        (∀ r ∈ rs, r.γ = r0.γ ∧ r.z = r0.z ∧ r.α = r0.α) →
          StarkedAir.Block.RngOk
            { lo := r0.lo, n := r0.n + (List.map (fun (x : StarkedAir.Block.Rng) => x.n) rs).sum,
              s := r0.s + (List.map (fun (x : StarkedAir.Block.Rng) => x.s) rs).sum,
              nin := r0.nin + (List.map (fun (x : StarkedAir.Block.Rng) => x.nin) rs).sum, γ := r0.γ, z := r0.z,
              α := r0.α } :=
  @StarkedAir.Circuit.BlockTree.rng_forest

/-- StarkedAir.Circuit.BlockRec.forest_rng' -/
theorem compat_Circuit_BlockRec_forest_rng' : ∀ (vs : List (ℕ → StarkedAir.F)) (v0 : ℕ → StarkedAir.F),
  StarkedAir.Circuit.BlockTree.SumOk v0 →
    (∀ v ∈ vs, StarkedAir.Circuit.BlockTree.SumOk v) →
      StarkedAir.Circuit.BlockTree.Linked' v0 vs →
        (∀ v ∈ vs, ∀ i < 12, v (7 + i) = v0 (7 + i)) →
          ∃ (n : ℕ),
            0 < n ∧
              StarkedAir.Block.RngOk
                { lo := ZMod.val (v0 0), n := n,
                  s :=
                    StarkedAir.Block.RunSum.pQ v0 2 +
                      (List.map (fun (v : ℕ → StarkedAir.F) => StarkedAir.Block.RunSum.pQ v 2) vs).sum,
                  nin := ZMod.val (v0 6) + (List.map (fun (v : ℕ → StarkedAir.F) => ZMod.val (v 6)) vs).sum,
                  γ := StarkedAir.Block.RunSum.pQ v0 7, z := StarkedAir.Block.RunSum.pQ v0 11,
                  α := StarkedAir.Block.RunSum.pQ v0 15 } :=
  @StarkedAir.Circuit.BlockRec.forest_rng'

/-- StarkedAir.Circuit.BlockRec.leafOut_vec -/
theorem compat_Circuit_BlockRec_leafOut_vec : ∀ {ρ : ℕ → StarkedAir.Circuit.Q},
  StarkedAir.Circuit.Holds ρ StarkedAir.Circuit.BlockRec.leafOutOps →
    ∀ {p : ℕ → StarkedAir.F},
      (∀ j < StarkedAir.Circuit.BlockRec.LSEED, (ρ j).a = p j) →
        (∀ j < 16,
            (ρ (StarkedAir.Circuit.BlockRec.LSEED + j)).a =
              (StarkedAir.HeaderTree.limbsOf (StarkedAir.Circuit.BlockTree.seedOf p)).getD j 0) →
          StarkedAir.Circuit.wordsOf ρ StarkedAir.Circuit.BlockRec.blockLeafOut.results =
            StarkedAir.Circuit.BlockRec.sumDigest StarkedAir.Circuit.BlockRec.zeroKey
              (StarkedAir.Circuit.BlockTree.leafVec p) :=
  @StarkedAir.Circuit.BlockRec.leafOut_vec

open Lean in
/-- Structural hash of a constant's type and value (constructors for inductives). -/
def pinHash (env : Environment) (c : Name) : Option UInt64 :=
  match env.find? c with
  | some (.defnInfo d) => some (mixHash d.type.hash d.value.hash)
  | some (.inductInfo i) => some (i.ctors.foldl (fun h k => match env.find? k with
      | some ci => mixHash h ci.type.hash | none => h) i.type.hash)
  | some (.ctorInfo c) => some c.type.hash
  | some (.opaqueInfo o) => some (mixHash o.type.hash o.value.hash)
  | some (.axiomInfo a) => some a.type.hash
  | some (.recInfo r) => some r.type.hash
  | _ => none

/-- The pinned constants and their hashes on `2196ba3`, one `name hash` per line. -/
def pinTable : String := "
StarkedAir.Air 370992439935339461
StarkedAir.Air.Satisfied 3555047645679353822
StarkedAir.Air.constraints 3195494350647499192
StarkedAir.Air.mk 3076634626
StarkedAir.Air.pre 10704772784783188780
StarkedAir.Air.toDag 11074718001047600086
StarkedAir.BalancedExt 6417201821001504529
StarkedAir.Blake2s.CA1_HI 12508926887679710735
StarkedAir.Blake2s.CA1_LO 11125588122290141182
StarkedAir.Blake2s.CA2_HI 10616793124281915399
StarkedAir.Blake2s.CA2_LO 13403305893303433831
StarkedAir.Blake2s.CC1_HI 5026493321673071272
StarkedAir.Blake2s.CC1_LO 18444604699847171585
StarkedAir.Blake2s.CC2_HI 1129545177923845729
StarkedAir.Blake2s.CC2_LO 7270170836753777704
StarkedAir.Blake2s.ML 5173250534863897990
StarkedAir.Blake2s.MSG 15290883838485526649
StarkedAir.Blake2s.PERIOD 5860101780672588214
StarkedAir.Blake2s.P_COPY 13937052351939933727
StarkedAir.Blake2s.P_FIN 9489224394318221991
StarkedAir.Blake2s.P_G 9008973590095614055
StarkedAir.Blake2s.P_INIT 9333288226061687284
StarkedAir.Blake2s.P_ISG 4667950421468529655
StarkedAir.Blake2s.P_XSEL 4274287032599217858
StarkedAir.Blake2s.P_YSEL 12086097043009658104
StarkedAir.Blake2s.WB 7423908779547554199
StarkedAir.Blake2s.bitsEq 650513264979676046
StarkedAir.Blake2s.booleans 6160639244590136786
StarkedAir.Blake2s.constraints 14844483445217614473
StarkedAir.Blake2s.copy 9114118812164392778
StarkedAir.Blake2s.finOff 6812538121028890468
StarkedAir.Blake2s.final 6800744713019940090
StarkedAir.Blake2s.gFirst 15157586443367680230
StarkedAir.Blake2s.gSecond 17123006847870164465
StarkedAir.Blake2s.init 2708378328975679777
StarkedAir.Blake2s.ivBit 17529549904224252578
StarkedAir.Blake2s.limb 14058424478190202289
StarkedAir.Blake2s.msgLimb 3651997685513970954
StarkedAir.Blake2s.outW 18329628573680846351
StarkedAir.Blake2s.outW.match_1 17867045463899273768
StarkedAir.Blake2s.preCols 13200615374789044903
StarkedAir.Blake2s.preQ 15725036107441224105
StarkedAir.Blake2s.rotXor 12297011085085677577
StarkedAir.Blake2s.src 18175958492849263011
StarkedAir.Blake2s.src.match_1 9921439537099186262
StarkedAir.Blake2s.srcOff 15798331942558134764
StarkedAir.Blake2s.xorC 10614046002499631260
StarkedAir.Block.ACTIVE 7200184553213182899
StarkedAir.Block.Anc.FCOPY 16993442085808736178
StarkedAir.Block.Anc.NANC 12679747259330932428
StarkedAir.Block.Anc.PUB_CSV 9619963949715690370
StarkedAir.Block.Anc.PUB_HASH 5130555358687355332
StarkedAir.Block.Anc.PUB_MHI 6734708282103567336
StarkedAir.Block.Anc.PUB_MLO 4752661515056156754
StarkedAir.Block.Anc.act 11509978770161209219
StarkedAir.Block.Anc.anc 10125080559040480986
StarkedAir.Block.Anc.ancCs 9783626794407537417
StarkedAir.Block.Anc.ancHi 16832182175689144932
StarkedAir.Block.Anc.ancLo 12020684667279038173
StarkedAir.Block.Anc.cmpSel 15442877157780501681
StarkedAir.Block.Anc.constraints 7621159090655947378
StarkedAir.Block.Anc.countSum 16809981087988357060
StarkedAir.Block.Anc.counts 14836816230479200725
StarkedAir.Block.Anc.flagAt 16901033523947780528
StarkedAir.Block.Anc.gates 1794441568831358114
StarkedAir.Block.Anc.hashOut 3402835509522086075
StarkedAir.Block.Anc.linkNF 2278687305262311651
StarkedAir.Block.Anc.mpub 9633930507314077591
StarkedAir.Block.Anc.mtpOf 2854684066532649576
StarkedAir.Block.Anc.operands 15065240937598222149
StarkedAir.Block.B2Msg.A 16728725346606875127
StarkedAir.Block.B2Msg.B 11558983466567915884
StarkedAir.Block.B2Msg.BLK 17101530479978464024
StarkedAir.Block.B2Msg.CNT 12679747259330932428
StarkedAir.Block.B2Msg.END 13687919700108124114
StarkedAir.Block.B2Msg.LASTF 644735488301855163
StarkedAir.Block.B2Msg.N_MAIN 13937052351939933727
StarkedAir.Block.B2Msg.ON 12621482290909172116
StarkedAir.Block.B2Msg.POS 11239342436784068239
StarkedAir.Block.B2Msg.P_FIRST 12621482290909172116
StarkedAir.Block.B2Msg.P_K 11239342436784068239
StarkedAir.Block.B2Msg.P_K0 4752661515056156754
StarkedAir.Block.B2Msg.P_K15 110532540116317034
StarkedAir.Block.B2Msg.P_NOTLAST 17101530479978464024
StarkedAir.Block.B2Msg.REL_B2B 2246386411152602517
StarkedAir.Block.B2Msg.REL_B2W 4393090879460539949
StarkedAir.Block.B2Msg.SM 4177543070365710692
StarkedAir.Block.B2Msg.T 10911675690963571469
StarkedAir.Block.B2Msg.b2msg 12872004703626126351
StarkedAir.Block.B2Msg.boolCols 12962393568995793720
StarkedAir.Block.B2Msg.constraints 853764476663276609
StarkedAir.Block.B2Msg.ends 1232628437164361533
StarkedAir.Block.B2Msg.first 6701522690554443113
StarkedAir.Block.B2Msg.hi 1898861421523231785
StarkedAir.Block.B2Msg.isLast 11736501313645815607
StarkedAir.Block.B2Msg.k 4215733963973134624
StarkedAir.Block.B2Msg.kn 10932140884916001105
StarkedAir.Block.B2Msg.kp 14591804336548626625
StarkedAir.Block.B2Msg.lenS 4430758931116920785
StarkedAir.Block.B2Msg.lo 16860806919675652179
StarkedAir.Block.B2Msg.lookups 14149163265150312061
StarkedAir.Block.B2Msg.nbOf 16995390180492155233
StarkedAir.Block.B2Msg.notFirst 6194261800078472236
StarkedAir.Block.B2Msg.om 2321827168386594119
StarkedAir.Block.B2Msg.one 1633976985673480194
StarkedAir.Block.B2Msg.p 13632788622925991193
StarkedAir.Block.B2Msg.per16 1418100152035227764
StarkedAir.Block.B2Msg.preCols 8115278215687686764
StarkedAir.Block.B2Msg.sbyte 14407112270505172705
StarkedAir.Block.B2Msg.sumA 9227164329517314162
StarkedAir.Block.B2s.BLKI 10785627192811993227
StarkedAir.Block.B2s.CHN 15017452174536805530
StarkedAir.Block.B2s.FST 16635232050084475590
StarkedAir.Block.B2s.LASTF 17292395879646336484
StarkedAir.Block.B2s.MU0 6305988514913448063
StarkedAir.Block.B2s.MU1 11371828430506203534
StarkedAir.Block.B2s.NIL 9079680652827673749
StarkedAir.Block.B2s.N_MAIN 8521955296787166820
StarkedAir.Block.B2s.PUB_OUT 6851467553259871396
StarkedAir.Block.B2s.P_KR 16134696242039045869
StarkedAir.Block.B2s.P_LT16 17358607272618789953
StarkedAir.Block.B2s.P_OUT8 8217079625019891863
StarkedAir.Block.B2s.P_R0 16591784325937161225
StarkedAir.Block.B2s.P_RK 1136009154564510988
StarkedAir.Block.B2s.REL_B2D 4122579724926651454
StarkedAir.Block.B2s.T 12018727679059400609
StarkedAir.Block.B2s.USEW 2120695554121013105
StarkedAir.Block.B2s.WHI 8390020435547715311
StarkedAir.Block.B2s.WLO 3056932898449465091
StarkedAir.Block.B2s.YD 17955972273041342551
StarkedAir.Block.B2s.b2s 10394044494526180455
StarkedAir.Block.B2s.bidx 7264734933810758034
StarkedAir.Block.B2s.bitSum 12538228827719192982
StarkedAir.Block.B2s.chainC 16104978792375946464
StarkedAir.Block.B2s.constraints 17188743921160810934
StarkedAir.Block.B2s.flagC 4638411387374695908
StarkedAir.Block.B2s.h0 9650489794048259978
StarkedAir.Block.B2s.h0Bit 7278460103385350657
StarkedAir.Block.B2s.initC 5061456873264661473
StarkedAir.Block.B2s.k 4215733963973134624
StarkedAir.Block.B2s.kp 14591804336548626625
StarkedAir.Block.B2s.kq 8432732418962188793
StarkedAir.Block.B2s.lookups 16044857007118128591
StarkedAir.Block.B2s.om 15361604658823865837
StarkedAir.Block.B2s.one 1633976985673480194
StarkedAir.Block.B2s.p 13632788622925991193
StarkedAir.Block.B2s.per88 11034636970774260185
StarkedAir.Block.B2s.perConst 16852131396777348017
StarkedAir.Block.B2s.preCols 7101630440915934272
StarkedAir.Block.B2s.pubLimb 15654500309238305474
StarkedAir.Block.B2s.tfC 12881203133123654823
StarkedAir.Block.B2s.wordC 6642334980010801513
StarkedAir.Block.BIT0 11239342436784068239
StarkedAir.Block.BYTE 17101530479978464024
StarkedAir.Block.BlockAt 1954791157267639417
StarkedAir.Block.BlockPubOk 10210431950510644760
StarkedAir.Block.BlockPubs 5207504306574123012
StarkedAir.Block.ClaimAt 6696442704788940435
StarkedAir.Block.Coin.ACC 8897190996565932596
StarkedAir.Block.Coin.BIG 9562720865119475955
StarkedAir.Block.Coin.BR1 10674809079763322373
StarkedAir.Block.Coin.BR3 13331762052517343641
StarkedAir.Block.Coin.CB 15638948555482515816
StarkedAir.Block.Coin.CBC 13858858957942268285
StarkedAir.Block.Coin.CBH 2184941676350844251
StarkedAir.Block.Coin.CBI 11239342436784068239
StarkedAir.Block.Coin.CBL 9440403996689931779
StarkedAir.Block.Coin.CBO 4393090879460539949
StarkedAir.Block.Coin.CHI 1518844136755050564
StarkedAir.Block.Coin.CLO 4914398126782852037
StarkedAir.Block.Coin.CTX 18100021416754734682
StarkedAir.Block.Coin.CY 10749535602551813547
StarkedAir.Block.Coin.D 12480503310037593863
StarkedAir.Block.Coin.FB 7219797621819445579
StarkedAir.Block.Coin.FC 632558657101528159
StarkedAir.Block.Coin.FCY 6729837763028667006
StarkedAir.Block.Coin.FEH 3908560419702505228
StarkedAir.Block.Coin.FEL 9466735686970830579
StarkedAir.Block.Coin.FH 5860101780672588214
StarkedAir.Block.Coin.GB 1872110660523164010
StarkedAir.Block.Coin.H1 12151129222638441331
StarkedAir.Block.Coin.H1C 697298089060678933
StarkedAir.Block.Coin.H2 14727568655513083124
StarkedAir.Block.Coin.H2C 8437815397017188386
StarkedAir.Block.Coin.H3 4370707133555971447
StarkedAir.Block.Coin.H3C 17405313595899184622
StarkedAir.Block.Coin.HB 10983968840588092850
StarkedAir.Block.Coin.HC 7253451167642400172
StarkedAir.Block.Coin.INH 3683350701089354875
StarkedAir.Block.Coin.INL 9522473875335708282
StarkedAir.Block.Coin.INVB 15369429412751102520
StarkedAir.Block.Coin.J 13937052351939933727
StarkedAir.Block.Coin.KI 17101530479978464024
StarkedAir.Block.Coin.KN 15257867343500937718
StarkedAir.Block.Coin.KO 12621482290909172116
StarkedAir.Block.Coin.KP 11915824346916814960
StarkedAir.Block.Coin.LEN 9619963949715690370
StarkedAir.Block.Coin.MB 10478199059826735215
StarkedAir.Block.Coin.MC1 10209490872791271168
StarkedAir.Block.Coin.MLO 8020736631586362313
StarkedAir.Block.Coin.MM 5580780264887204875
StarkedAir.Block.Coin.MNB 12456454333311047599
StarkedAir.Block.Coin.NB 8646764002683721668
StarkedAir.Block.Coin.N_MAIN 6085311629211475663
StarkedAir.Block.Coin.OB 721389358932291958
StarkedAir.Block.Coin.ORD 5454922851969046533
StarkedAir.Block.Coin.OUH 8076550275599354812
StarkedAir.Block.Coin.OUL 1061646650389532803
StarkedAir.Block.Coin.PB 13763848869307909864
StarkedAir.Block.Coin.PUB_ALPHA 3707048847286038001
StarkedAir.Block.Coin.PUB_LOST 12190039271130089235
StarkedAir.Block.Coin.PUB_NIN 1257017251801583450
StarkedAir.Block.Coin.PUB_S 697298089060678933
StarkedAir.Block.Coin.PUB_SUBH 11729151763962993750
StarkedAir.Block.Coin.PUB_SUBL 4987549681831757402
StarkedAir.Block.Coin.PUB_Z 15379246830983459820
StarkedAir.Block.Coin.Q1 9936580920851359796
StarkedAir.Block.Coin.Q2 13041627532983354747
StarkedAir.Block.Coin.Q3 1125561973254504697
StarkedAir.Block.Coin.REL_INT 5130555358687355332
StarkedAir.Block.Coin.REL_OUTT 1015439597935339062
StarkedAir.Block.Coin.SB 11886692268979065078
StarkedAir.Block.Coin.SIDC 4765000530389825132
StarkedAir.Block.Coin.SINV 5981168852429598106
StarkedAir.Block.Coin.SLEN 11436649988442595329
StarkedAir.Block.Coin.SSC 13752328820276602557
StarkedAir.Block.Coin.START 110532540116317034
StarkedAir.Block.Coin.SVAL 6734708282103567336
StarkedAir.Block.Coin.TEND 3651293100378858203
StarkedAir.Block.Coin.TLB 8870046071047273995
StarkedAir.Block.Coin.TXI 4752661515056156754
StarkedAir.Block.Coin.U6A 10795676046289485695
StarkedAir.Block.Coin.U6Z 11445925570022971888
StarkedAir.Block.Coin.UNSP 11437002141770042747
StarkedAir.Block.Coin.VB 2843141533488432785
StarkedAir.Block.Coin.VH 13079535155315776488
StarkedAir.Block.Coin.VHI 10911675690963571469
StarkedAir.Block.Coin.VL 8195331293974438075
StarkedAir.Block.Coin.VLO 644735488301855163
StarkedAir.Block.Coin.VOUT 12679747259330932428
StarkedAir.Block.Coin.W 11208987806306150437
StarkedAir.Block.Coin.ZI 195973943113694959
StarkedAir.Block.Coin.ZS 1580254171466077270
StarkedAir.Block.Coin.accC 17338440577039351490
StarkedAir.Block.Coin.amountC 16455570758616584428
StarkedAir.Block.Coin.b3 1543431860124293618
StarkedAir.Block.Coin.b4 2327974905121133907
StarkedAir.Block.Coin.coin 8326980354223559378
StarkedAir.Block.Coin.constraints 11015623120550571891
StarkedAir.Block.Coin.first 15453146726949858975
StarkedAir.Block.Coin.fracC 17833657597395715562
StarkedAir.Block.Coin.height 3487460431781878574
StarkedAir.Block.Coin.isLast 9524697876664787951
StarkedAir.Block.Coin.k 4215733963973134624
StarkedAir.Block.Coin.kn 10932140884916001105
StarkedAir.Block.Coin.kp 14591804336548626625
StarkedAir.Block.Coin.lastC 4686876359968818310
StarkedAir.Block.Coin.lastOn 11618261464159590984
StarkedAir.Block.Coin.localC 11861545920249534897
StarkedAir.Block.Coin.lookups 1993625935316010669
StarkedAir.Block.Coin.mE 16749810043131797124
StarkedAir.Block.Coin.notFirst 1322236294483047389
StarkedAir.Block.Coin.notLast 17856571357075250639
StarkedAir.Block.Coin.om 16835927748042026538
StarkedAir.Block.Coin.on 4288727325737415452
StarkedAir.Block.Coin.onV 18130292760651592672
StarkedAir.Block.Coin.one 1633976985673480194
StarkedAir.Block.Coin.onn 2470409987339317604
StarkedAir.Block.Coin.onp 4734937668218819411
StarkedAir.Block.Coin.pair 15576528077312850479
StarkedAir.Block.Coin.phi 10317016122995768845
StarkedAir.Block.Coin.preCols 2484850527752626642
StarkedAir.Block.Coin.prevLimb 11129681111510200445
StarkedAir.Block.Coin.r8 11503876311102383167
StarkedAir.Block.Coin.tf 15374759760975450968
StarkedAir.Block.Coin.tuple 10058641763961070265
StarkedAir.Block.Coin.two24 9233243156309046089
StarkedAir.Block.Coin.zeroC 7231081858608859870
StarkedAir.Block.Ctx.A0 15021439758854435811
StarkedAir.Block.Ctx.ACC 4752661515056156754
StarkedAir.Block.Ctx.ACTR 11239342436784068239
StarkedAir.Block.Ctx.ADDR 12621482290909172116
StarkedAir.Block.Ctx.B 17101530479978464024
StarkedAir.Block.Ctx.CHI 1073657718774685624
StarkedAir.Block.Ctx.CID 1789953865269236795
StarkedAir.Block.Ctx.CLEN 17657334438023227186
StarkedAir.Block.Ctx.CLO 14140254281272384383
StarkedAir.Block.Ctx.CPOS 2528803397246198985
StarkedAir.Block.Ctx.HASC 9465160240525125549
StarkedAir.Block.Ctx.HC 18342781002210354705
StarkedAir.Block.Ctx.L0 5130555358687355332
StarkedAir.Block.Ctx.LG 4526833116419246417
StarkedAir.Block.Ctx.MHI 7310214899571200254
StarkedAir.Block.Ctx.MLO 11094188613630540670
StarkedAir.Block.Ctx.MZ 3378581462597066800
StarkedAir.Block.Ctx.NONCE_ID 3053612009897865308
StarkedAir.Block.Ctx.NSEG 11024855835016570353
StarkedAir.Block.Ctx.N_MAIN 6552061845898070580
StarkedAir.Block.Ctx.PACC 9619963949715690370
StarkedAir.Block.Ctx.PUB_HASH 5130555358687355332
StarkedAir.Block.Ctx.P_CAPM0 5130555358687355332
StarkedAir.Block.Ctx.P_CAPM1 11208987806306150437
StarkedAir.Block.Ctx.P_CAPT0 11605307065553852467
StarkedAir.Block.Ctx.P_CAPT1 1015439597935339062
StarkedAir.Block.Ctx.P_CHKH 11024855835016570353
StarkedAir.Block.Ctx.P_CHKL 9465160240525125549
StarkedAir.Block.Ctx.P_CHKS 2528803397246198985
StarkedAir.Block.Ctx.P_CHKW 14757724169269328703
StarkedAir.Block.Ctx.P_EXP 644735488301855163
StarkedAir.Block.Ctx.P_FIRST 12621482290909172116
StarkedAir.Block.Ctx.P_FLIP 4122579724926651454
StarkedAir.Block.Ctx.P_HEXP 10911675690963571469
StarkedAir.Block.Ctx.P_HI 15965332230801424257
StarkedAir.Block.Ctx.P_LO 15021439758854435811
StarkedAir.Block.Ctx.P_LT117 110532540116317034
StarkedAir.Block.Ctx.P_LT118 9619963949715690370
StarkedAir.Block.Ctx.P_LT79 11239342436784068239
StarkedAir.Block.Ctx.P_LT80 4752661515056156754
StarkedAir.Block.Ctx.P_OFF 13752328820276602557
StarkedAir.Block.Ctx.P_RST 4177543070365710692
StarkedAir.Block.Ctx.P_SB34 6851467553259871396
StarkedAir.Block.Ctx.P_SC 12679747259330932428
StarkedAir.Block.Ctx.P_SC1 4393090879460539949
StarkedAir.Block.Ctx.P_SC2 2246386411152602517
StarkedAir.Block.Ctx.P_SCB 15608481590008836421
StarkedAir.Block.Ctx.P_SHDR 6734708282103567336
StarkedAir.Block.Ctx.P_SRCB 13937052351939933727
StarkedAir.Block.Ctx.P_SRCR 195973943113694959
StarkedAir.Block.Ctx.P_SW 7200184553213182899
StarkedAir.Block.Ctx.P_WGT 13687919700108124114
StarkedAir.Block.Ctx.RA 110532540116317034
StarkedAir.Block.Ctx.REL_WCID 13937052351939933727
StarkedAir.Block.Ctx.Role 8437306099191888508
StarkedAir.Block.Ctx.Role.base 14691926915907483594
StarkedAir.Block.Ctx.Role.capM0 13133037678653388542
StarkedAir.Block.Ctx.Role.capM1 11641469161874473887
StarkedAir.Block.Ctx.Role.capT0 16873748360553722347
StarkedAir.Block.Ctx.Role.capT1 12749753778004214979
StarkedAir.Block.Ctx.Role.chkH 10038772302045002863
StarkedAir.Block.Ctx.Role.chkL 5887510768262020193
StarkedAir.Block.Ctx.Role.chkS 370959607190686474
StarkedAir.Block.Ctx.Role.chkW 17296114647376516215
StarkedAir.Block.Ctx.Role.exp 8212958956489750780
StarkedAir.Block.Ctx.Role.flip 11589694147069334836
StarkedAir.Block.Ctx.Role.hi 13416450303288937268
StarkedAir.Block.Ctx.Role.lo 8857938936145464680
StarkedAir.Block.Ctx.Role.mk 2218483454
StarkedAir.Block.Ctx.Role.off 10394025388486694025
StarkedAir.Block.Ctx.Role.rst 17328264461567792661
StarkedAir.Block.Ctx.Role.sc1 7260937364983867678
StarkedAir.Block.Ctx.Role.sc2 6143856557339050196
StarkedAir.Block.Ctx.Role.srcB 2255197470206256247
StarkedAir.Block.Ctx.Role.srcR 11474258552943377847
StarkedAir.Block.Ctx.Role.wgt 3848470217633948977
StarkedAir.Block.Ctx.SEG0 11605307065553852467
StarkedAir.Block.Ctx.SIGS 14757724169269328703
StarkedAir.Block.Ctx.TH16 16444331713195875192
StarkedAir.Block.Ctx.TL16 17750663069614403632
StarkedAir.Block.Ctx.W0 1015439597935339062
StarkedAir.Block.Ctx.WT 11208987806306150437
StarkedAir.Block.Ctx.ZERO_ID 15766393040424645665
StarkedAir.Block.Ctx.bn 1211540856924898373
StarkedAir.Block.Ctx.constraints 17620595603992092776
StarkedAir.Block.Ctx.consts 7392833621229240773
StarkedAir.Block.Ctx.ctx 17055706767271233458
StarkedAir.Block.Ctx.k 4215733963973134624
StarkedAir.Block.Ctx.kp 14591804336548626625
StarkedAir.Block.Ctx.limbs 17801573404424114319
StarkedAir.Block.Ctx.lookups 1726404177418135180
StarkedAir.Block.Ctx.notFirst 7756826477428127892
StarkedAir.Block.Ctx.om 1092795982528353786
StarkedAir.Block.Ctx.one 1633976985673480194
StarkedAir.Block.Ctx.p 13632788622925991193
StarkedAir.Block.Ctx.preCols 14705492555517531885
StarkedAir.Block.Ctx.role 14954000010187050443
StarkedAir.Block.Ctx.tabR 6710618105624616634
StarkedAir.Block.ExtSum.ACC 15608481590008836421
StarkedAir.Block.ExtSum.FC 110532540116317034
StarkedAir.Block.ExtSum.MC 4752661515056156754
StarkedAir.Block.ExtSum.PUB_ALPHA 14748385564778810097
StarkedAir.Block.ExtSum.PUB_S 13937052351939933727
StarkedAir.Block.ExtSum.PUB_Z 12621482290909172116
StarkedAir.Block.ExtSum.QE 147769867411210062
StarkedAir.Block.ExtSum.QE.a 2515325547990469605
StarkedAir.Block.ExtSum.QE.add 12275927629589590086
StarkedAir.Block.ExtSum.QE.b 10034251958524381128
StarkedAir.Block.ExtSum.QE.base 2788066374282878831
StarkedAir.Block.ExtSum.QE.c 13996862104506790077
StarkedAir.Block.ExtSum.QE.cmulE 14339539115287149343
StarkedAir.Block.ExtSum.QE.colQ 14056992675567635140
StarkedAir.Block.ExtSum.QE.coords 10738954254855211425
StarkedAir.Block.ExtSum.QE.d 17667162040479213406
StarkedAir.Block.ExtSum.QE.ev 7396600609376117218
StarkedAir.Block.ExtSum.QE.mk 1048894055
StarkedAir.Block.ExtSum.QE.mul 12392442004984085308
StarkedAir.Block.ExtSum.QE.pubQ 10990291398810164900
StarkedAir.Block.ExtSum.QE.sub 1835268478383605983
StarkedAir.Block.ExtSum.TC 9333288226061687284
StarkedAir.Block.ExtSum.W 4752661515056156754
StarkedAir.Block.ExtSum.accC 3339837065685215793
StarkedAir.Block.ExtSum.constraints 8249022061065022541
StarkedAir.Block.ExtSum.fQ 14857244784389321966
StarkedAir.Block.ExtSum.fracC 9587529306868243677
StarkedAir.Block.ExtSum.isLast 7445015741484464927
StarkedAir.Block.ExtSum.lastC 5061490595216234202
StarkedAir.Block.ExtSum.mC 13035795177074848450
StarkedAir.Block.ExtSum.mE 7580706890209409632
StarkedAir.Block.ExtSum.notFirst 7658284369446234937
StarkedAir.Block.ExtSum.one 1633976985673480194
StarkedAir.Block.ExtSum.pQ 9419764949612812891
StarkedAir.Block.ExtSum.phi 3323396769934388546
StarkedAir.Block.ExtSum.phiQ 5845461185445873749
StarkedAir.Block.ExtSum.preCols 2484850527752626642
StarkedAir.Block.ExtSum.zeroC 14137551363218363913
StarkedAir.Block.Fields.AFT 3549963017473870078
StarkedAir.Block.Fields.AQ 9101128833897120425
StarkedAir.Block.Fields.B2 14112197795987423530
StarkedAir.Block.Fields.BASEC 3908560419702505228
StarkedAir.Block.Fields.BOR 8437815397017188386
StarkedAir.Block.Fields.BQ 2700747840432739824
StarkedAir.Block.Fields.BRW 9134718571879620143
StarkedAir.Block.Fields.BY 4751906410701708568
StarkedAir.Block.Fields.C4B0 314272252700577665
StarkedAir.Block.Fields.C4B1 4765000530389825132
StarkedAir.Block.Fields.CAR 697298089060678933
StarkedAir.Block.Fields.CB 4274287032599217858
StarkedAir.Block.Fields.CHI 10820623693314178612
StarkedAir.Block.Fields.CLO 12837673738735876932
StarkedAir.Block.Fields.CP1 4177543070365710692
StarkedAir.Block.Fields.CP3 13687919700108124114
StarkedAir.Block.Fields.CP5 13937052351939933727
StarkedAir.Block.Fields.DW 13773995161130163348
StarkedAir.Block.Fields.E1C 18068838573090174274
StarkedAir.Block.Fields.E2C 14635086819067720673
StarkedAir.Block.Fields.EOC 9054670203840292923
StarkedAir.Block.Fields.ESC 8897190996565932596
StarkedAir.Block.Fields.EXPQ 10674809079763322373
StarkedAir.Block.Fields.FL 8076550275599354812
StarkedAir.Block.Fields.FS 10749535602551813547
StarkedAir.Block.Fields.FZ 1061646650389532803
StarkedAir.Block.Fields.G0 9682705975747838464
StarkedAir.Block.Fields.GIN 15257867343500937718
StarkedAir.Block.Fields.GL0 16407894917998692034
StarkedAir.Block.Fields.GL1 12773739540974081893
StarkedAir.Block.Fields.GS 4860790409758013023
StarkedAir.Block.Fields.GZ 2751803065318331006
StarkedAir.Block.Fields.HASC 12329412102689721863
StarkedAir.Block.Fields.HASW 11445925570022971888
StarkedAir.Block.Fields.INL 9562720865119475955
StarkedAir.Block.Fields.INV1 632558657101528159
StarkedAir.Block.Fields.INV2 11846305455129162963
StarkedAir.Block.Fields.INVN 12456454333311047599
StarkedAir.Block.Fields.INVQ 18257503768710735932
StarkedAir.Block.Fields.INVT 11915824346916814960
StarkedAir.Block.Fields.INVV 17923297191037355554
StarkedAir.Block.Fields.ISC 9260909153828460204
StarkedAir.Block.Fields.ITEML 11437002141770042747
StarkedAir.Block.Fields.K_BLK 12621482290909172116
StarkedAir.Block.Fields.K_IN 11239342436784068239
StarkedAir.Block.Fields.K_LOCK 6734708282103567336
StarkedAir.Block.Fields.K_NOUT 4752661515056156754
StarkedAir.Block.Fields.K_OUT 110532540116317034
StarkedAir.Block.Fields.K_PAD 15608481590008836421
StarkedAir.Block.Fields.K_TXH 17101530479978464024
StarkedAir.Block.Fields.K_WCNT 9619963949715690370
StarkedAir.Block.Fields.K_WITEM 13752328820276602557
StarkedAir.Block.Fields.LEN 7200184553213182899
StarkedAir.Block.Fields.LENPUB 6675951301058138558
StarkedAir.Block.Fields.MAXHI 7794976647393072461
StarkedAir.Block.Fields.MAXLO 2833807799884135824
StarkedAir.Block.Fields.MAXS 17601196584736204622
StarkedAir.Block.Fields.MMB 17739090352072707088
StarkedAir.Block.Fields.MML 17617332127936783150
StarkedAir.Block.Fields.NIN 17470984253759324793
StarkedAir.Block.Fields.NS 5284724056767648695
StarkedAir.Block.Fields.N_MAIN' 13742794323032148329
StarkedAir.Block.Fields.OFF 10911675690963571469
StarkedAir.Block.Fields.OH 13041627532983354747
StarkedAir.Block.Fields.OUTL 1750718438119926672
StarkedAir.Block.Fields.QB 4269591047795432596
StarkedAir.Block.Fields.QH 13363460484354492103
StarkedAir.Block.Fields.RA 1074956584641015118
StarkedAir.Block.Fields.RB 13183320871000412271
StarkedAir.Block.Fields.REL_COMMIT 4177543070365710692
StarkedAir.Block.Fields.REL_CTX 10911675690963571469
StarkedAir.Block.Fields.REL_SCRIPT 12679747259330932428
StarkedAir.Block.Fields.REL_TOT 644735488301855163
StarkedAir.Block.Fields.REL_TX 110532540116317034
StarkedAir.Block.Fields.REQ 2153266645535438764
StarkedAir.Block.Fields.REQC 12043011904445076227
StarkedAir.Block.Fields.RG 1125561973254504697
StarkedAir.Block.Fields.RS 6090778278832877846
StarkedAir.Block.Fields.SEG 644735488301855163
StarkedAir.Block.Fields.SSC 6050329034903606933
StarkedAir.Block.Fields.START 6851467553259871396
StarkedAir.Block.Fields.THI 8020736631586362313
StarkedAir.Block.Fields.TLO 10209490872791271168
StarkedAir.Block.Fields.TXA 8195331293974438075
StarkedAir.Block.Fields.TXI 9522473875335708282
StarkedAir.Block.Fields.TXL 15369429412751102520
StarkedAir.Block.Fields.TXM 3683350701089354875
StarkedAir.Block.Fields.TY 9466735686970830579
StarkedAir.Block.Fields.TxAt 14041695782806371276
StarkedAir.Block.Fields.VAL 12679747259330932428
StarkedAir.Block.Fields.WB 337445974396808168
StarkedAir.Block.Fields.WINL 9393665165638303039
StarkedAir.Block.Fields.WST 13079535155315776488
StarkedAir.Block.Fields.Z1 5580780264887204875
StarkedAir.Block.Fields.Z2 7248905091690107603
StarkedAir.Block.Fields.ZT 13739582799410941959
StarkedAir.Block.Fields.ZV 12486006358225498496
StarkedAir.Block.Fields.bitC 14513382331141017775
StarkedAir.Block.Fields.blockBytes 3362647105931116537
StarkedAir.Block.Fields.by4 928109702473566966
StarkedAir.Block.Fields.c 7398137197751755746
StarkedAir.Block.Fields.chkC 1340301875353697891
StarkedAir.Block.Fields.chkLookups 7211814688263250234
StarkedAir.Block.Fields.commitC 17939344127444849891
StarkedAir.Block.Fields.compactC 5760949608222406565
StarkedAir.Block.Fields.constraints 887555171356707603
StarkedAir.Block.Fields.countC 9761320507809890299
StarkedAir.Block.Fields.e1 6315645682856458953
StarkedAir.Block.Fields.e2 10075862923094640558
StarkedAir.Block.Fields.fields 6499582317579388765
StarkedAir.Block.Fields.finalC 3377919427884971299
StarkedAir.Block.Fields.first 15453146726949858975
StarkedAir.Block.Fields.hasC 13603305468679119935
StarkedAir.Block.Fields.hi16 4521148875920633961
StarkedAir.Block.Fields.isLast 7175143457965580847
StarkedAir.Block.Fields.isZero 7097151901272403092
StarkedAir.Block.Fields.k 4215733963973134624
StarkedAir.Block.Fields.kindC 11706269081297446281
StarkedAir.Block.Fields.kinds 17604250687663591452
StarkedAir.Block.Fields.kp 14591804336548626625
StarkedAir.Block.Fields.le2 15412803654668629242
StarkedAir.Block.Fields.le3 6713872034906061719
StarkedAir.Block.Fields.le4 8205959152885222164
StarkedAir.Block.Fields.lenE 2073812807037109725
StarkedAir.Block.Fields.lo16 404667341693468830
StarkedAir.Block.Fields.locks 2788108230741084760
StarkedAir.Block.Fields.lookups 15797939230126591961
StarkedAir.Block.Fields.modeC 16913633504967601591
StarkedAir.Block.Fields.notFirst 7743742685527701712
StarkedAir.Block.Fields.offE 3796264667135795787
StarkedAir.Block.Fields.ohSum 3089668273034562312
StarkedAir.Block.Fields.one 1633976985673480194
StarkedAir.Block.Fields.oneMinus 9233604868208270565
StarkedAir.Block.Fields.pat 9084117554932748549
StarkedAir.Block.Fields.preCols 2484850527752626642
StarkedAir.Block.Fields.pref 5960655931378127860
StarkedAir.Block.Fields.prefOf 13207927753107707229
StarkedAir.Block.Fields.prevoutC 13602525699288173970
StarkedAir.Block.Fields.pubC 16146507305773893285
StarkedAir.Block.Fields.qE 15597169146787769620
StarkedAir.Block.Fields.rg 2936836401487920943
StarkedAir.Block.Fields.same 1019193136548579725
StarkedAir.Block.Fields.segC 13109145802674227011
StarkedAir.Block.Fields.slice 567132871137622237
StarkedAir.Block.Fields.tileC 9483385469064967170
StarkedAir.Block.Fields.tokOf 6194309918656515234
StarkedAir.Block.Fields.toksFrom 12716148988464879622
StarkedAir.Block.Fields.totalsC 13697947197982863534
StarkedAir.Block.Fields.trans 10617737885257594734
StarkedAir.Block.Fields.transC 14023597682513581801
StarkedAir.Block.Fields.txC 6392821058622529058
StarkedAir.Block.Fields.valE 10369112164646255249
StarkedAir.Block.Fields.valueC 12462423409342365395
StarkedAir.Block.Fields.vhi 18294084325602165591
StarkedAir.Block.Fields.vlo 2956203929671963707
StarkedAir.Block.Fields.zeroC 10320465777670589175
StarkedAir.Block.FpWalk.B 110532540116317034
StarkedAir.Block.FpWalk.FST 9619963949715690370
StarkedAir.Block.FpWalk.H 7200184553213182899
StarkedAir.Block.FpWalk.LEN 6851467553259871396
StarkedAir.Block.FpWalk.LINV 15608481590008836421
StarkedAir.Block.FpWalk.LST 13752328820276602557
StarkedAir.Block.FpWalk.N_MAIN 4177543070365710692
StarkedAir.Block.FpWalk.ON 12621482290909172116
StarkedAir.Block.FpWalk.POS 4752661515056156754
StarkedAir.Block.FpWalk.PUB_G 6552061845898070580
StarkedAir.Block.FpWalk.REL_FP 15021439758854435811
StarkedAir.Block.FpWalk.REL_SEG 15965332230801424257
StarkedAir.Block.FpWalk.REM 6734708282103567336
StarkedAir.Block.FpWalk.SID 11239342436784068239
StarkedAir.Block.FpWalk.STR 17101530479978464024
StarkedAir.Block.FpWalk.constraints 13013764606119335660
StarkedAir.Block.FpWalk.cont 3242263415734511268
StarkedAir.Block.FpWalk.first 15453146726949858975
StarkedAir.Block.FpWalk.fpwalk 3867794570120447737
StarkedAir.Block.FpWalk.gQ 7700316102455386843
StarkedAir.Block.FpWalk.hQ 4591210531937172488
StarkedAir.Block.FpWalk.horner 10972267240396326222
StarkedAir.Block.FpWalk.hornerQE 2263943911133627455
StarkedAir.Block.FpWalk.isLast 9977756212372776516
StarkedAir.Block.FpWalk.k 4215733963973134624
StarkedAir.Block.FpWalk.kn 10932140884916001105
StarkedAir.Block.FpWalk.kp 14591804336548626625
StarkedAir.Block.FpWalk.lookups 16738366044155682979
StarkedAir.Block.FpWalk.nl 9889822956787777429
StarkedAir.Block.FpWalk.om 2404492044571925028
StarkedAir.Block.FpWalk.one 1633976985673480194
StarkedAir.Block.FpWalk.preCols 2484850527752626642
StarkedAir.Block.LEN 6675951301058138558
StarkedAir.Block.MULT 12679747259330932428
StarkedAir.Block.Merkle.ACTN 12621482290909172116
StarkedAir.Block.Merkle.BASE 6851467553259871396
StarkedAir.Block.Merkle.C1 13937052351939933727
StarkedAir.Block.Merkle.C1INV 195973943113694959
StarkedAir.Block.Merkle.CNT 13752328820276602557
StarkedAir.Block.Merkle.DUP 13687919700108124114
StarkedAir.Block.Merkle.FIRST 12621482290909172116
StarkedAir.Block.Merkle.FIRSTL 11239342436784068239
StarkedAir.Block.Merkle.FS 1015439597935339062
StarkedAir.Block.Merkle.I 9619963949715690370
StarkedAir.Block.Merkle.L1 12679747259330932428
StarkedAir.Block.Merkle.LAST 4752661515056156754
StarkedAir.Block.Merkle.LEFT 10911675690963571469
StarkedAir.Block.Merkle.LINV 110532540116317034
StarkedAir.Block.Merkle.MMC 15965332230801424257
StarkedAir.Block.Merkle.NB 5990581102698132738
StarkedAir.Block.Merkle.NF 11605307065553852467
StarkedAir.Block.Merkle.NM 4122579724926651454
StarkedAir.Block.Merkle.NOTLAST 17101530479978464024
StarkedAir.Block.Merkle.NTX 9642947143088483524
StarkedAir.Block.Merkle.N_MAIN 6552061845898070580
StarkedAir.Block.Merkle.ODD 15608481590008836421
StarkedAir.Block.Merkle.PBASE 7200184553213182899
StarkedAir.Block.Merkle.PCNT 6734708282103567336
StarkedAir.Block.Merkle.PINV 2246386411152602517
StarkedAir.Block.Merkle.RIDC 15021439758854435811
StarkedAir.Block.Merkle.RIGHT 4177543070365710692
StarkedAir.Block.Merkle.RIX 644735488301855163
StarkedAir.Block.Merkle.RL 6826526909334274157
StarkedAir.Block.Merkle.RN 4393090879460539949
StarkedAir.Block.Merkle.RT 17101530479978464024
StarkedAir.Block.Merkle.childC 5143711500392341527
StarkedAir.Block.Merkle.constraints 13615782428049790339
StarkedAir.Block.Merkle.flagC 2380550699163399147
StarkedAir.Block.Merkle.k 4215733963973134624
StarkedAir.Block.Merkle.kindC 14953317086415851577
StarkedAir.Block.Merkle.kp 14591804336548626625
StarkedAir.Block.Merkle.levelC 11355571162866751827
StarkedAir.Block.Merkle.lookups 3682744502492224325
StarkedAir.Block.Merkle.merkle 2992387126925459017
StarkedAir.Block.Merkle.nodeId 3188837490937368345
StarkedAir.Block.Merkle.notFirst 2673087246662498707
StarkedAir.Block.Merkle.om 1880781539155610484
StarkedAir.Block.Merkle.one 1633976985673480194
StarkedAir.Block.Merkle.preCols 2484850527752626642
StarkedAir.Block.Msg.BIT0 15965332230801424257
StarkedAir.Block.Msg.BYTE 4122579724926651454
StarkedAir.Block.Msg.CONT 14140254281272384383
StarkedAir.Block.Msg.D 12621482290909172116
StarkedAir.Block.Msg.DLC 16444331713195875192
StarkedAir.Block.Msg.ENDD 17750663069614403632
StarkedAir.Block.Msg.EZ 14757724169269328703
StarkedAir.Block.Msg.FIRST 12621482290909172116
StarkedAir.Block.Msg.FIRSTM 9619963949715690370
StarkedAir.Block.Msg.HDR 7200184553213182899
StarkedAir.Block.Msg.IDX 4393090879460539949
StarkedAir.Block.Msg.INV 17657334438023227186
StarkedAir.Block.Msg.IS0 11239342436784068239
StarkedAir.Block.Msg.IS3 4752661515056156754
StarkedAir.Block.Msg.IS56 6734708282103567336
StarkedAir.Block.Msg.IS63 9619963949715690370
StarkedAir.Block.Msg.LN 4752661515056156754
StarkedAir.Block.Msg.LZ 13752328820276602557
StarkedAir.Block.Msg.MID 195973943113694959
StarkedAir.Block.Msg.MM 7310214899571200254
StarkedAir.Block.Msg.MT 6851467553259871396
StarkedAir.Block.Msg.NIL 110532540116317034
StarkedAir.Block.Msg.NOTLAST 17101530479978464024
StarkedAir.Block.Msg.N_MAIN 18342781002210354705
StarkedAir.Block.Msg.P80 17101530479978464024
StarkedAir.Block.Msg.PC0 13752328820276602557
StarkedAir.Block.Msg.PC1 6734708282103567336
StarkedAir.Block.Msg.PC2 15608481590008836421
StarkedAir.Block.Msg.POS 2246386411152602517
StarkedAir.Block.Msg.REL_MLEN 13752328820276602557
StarkedAir.Block.Msg.REL_MSGW 9619963949715690370
StarkedAir.Block.Msg.SEG 644735488301855163
StarkedAir.Block.Msg.SW 1073657718774685624
StarkedAir.Block.Msg.TA 4177543070365710692
StarkedAir.Block.Msg.TI 10911675690963571469
StarkedAir.Block.Msg.TL 13937052351939933727
StarkedAir.Block.Msg.TW 13687919700108124114
StarkedAir.Block.Msg.WM 11094188613630540670
StarkedAir.Block.Msg.WTX 12679747259330932428
StarkedAir.Block.Msg.Z 2528803397246198985
StarkedAir.Block.Msg.ZR 11239342436784068239
StarkedAir.Block.Msg.byteE 134405968211506128
StarkedAir.Block.Msg.constraints 15174100950869230581
StarkedAir.Block.Msg.ezE 14869823075395025940
StarkedAir.Block.Msg.k 4215733963973134624
StarkedAir.Block.Msg.kindC 5684811304822234986
StarkedAir.Block.Msg.kinds 7672823797541516882
StarkedAir.Block.Msg.kp 14591804336548626625
StarkedAir.Block.Msg.lookups 3533917296128141515
StarkedAir.Block.Msg.msg 15341973700162635113
StarkedAir.Block.Msg.msgC 3045106842292104347
StarkedAir.Block.Msg.notFirst 12663156859211837596
StarkedAir.Block.Msg.om 12441653587333723642
StarkedAir.Block.Msg.one 1633976985673480194
StarkedAir.Block.Msg.padC 6466892410866391750
StarkedAir.Block.Msg.per64 8367195531656906142
StarkedAir.Block.Msg.preCols 13640927822775926323
StarkedAir.Block.Msg.transC 4927832362509663645
StarkedAir.Block.POS 12621482290909172116
StarkedAir.Block.REL_BYTE 4752661515056156754
StarkedAir.Block.Rb 10984875201770313777
StarkedAir.Block.RealVal 17816587417522568435
StarkedAir.Block.Rng 11356591986143134850
StarkedAir.Block.Rng.lo 4957958980706581513
StarkedAir.Block.Rng.mk 792509985
StarkedAir.Block.Rng.n 8510243369086010538
StarkedAir.Block.Rng.nin 10939497676155635290
StarkedAir.Block.Rng.s 1404007880977387120
StarkedAir.Block.Rng.z 2109780470536028108
StarkedAir.Block.Rng.α 8059692874848964411
StarkedAir.Block.Rng.γ 8835453168127845186
StarkedAir.Block.RngOk 10320902993185117089
StarkedAir.Block.RunSum.accC 7323125106130689268
StarkedAir.Block.RunSum.cQ 16481101670845435649
StarkedAir.Block.RunSum.fracC 18052887548377219002
StarkedAir.Block.RunSum.isLast 4155549906625837474
StarkedAir.Block.RunSum.lastC 10581436997468906820
StarkedAir.Block.RunSum.notFirst 12957777571371124953
StarkedAir.Block.RunSum.one 1633976985673480194
StarkedAir.Block.RunSum.pQ 9419764949612812891
StarkedAir.Block.RunSum.preCols 2484850527752626642
StarkedAir.Block.RunSum.zeroC 15065765611479224596
StarkedAir.Block.Setup 13441758473109685040
StarkedAir.Block.Setup.b 2184830600205238768
StarkedAir.Block.Setup.m 844058681661882047
StarkedAir.Block.Setup.mk 3997582544
StarkedAir.Block.Sha.ALLEQ 18160893256249230201
StarkedAir.Block.Sha.BLKI 2184941676350844251
StarkedAir.Block.Sha.CHN 10299845546680833332
StarkedAir.Block.Sha.CMPF 2528803397246198985
StarkedAir.Block.Sha.CMPR 17657334438023227186
StarkedAir.Block.Sha.DBL 6622370624862463869
StarkedAir.Block.Sha.DCONST 195973943113694959
StarkedAir.Block.Sha.DC_LO 4393090879460539949
StarkedAir.Block.Sha.DLR 9465160240525125549
StarkedAir.Block.Sha.DMSG 10961464290490724482
StarkedAir.Block.Sha.DRR 14757724169269328703
StarkedAir.Block.Sha.FIN3 1015439597935339062
StarkedAir.Block.Sha.FIRST 5130555358687355332
StarkedAir.Block.Sha.FST 3651293100378858203
StarkedAir.Block.Sha.IH 8527695832703923635
StarkedAir.Block.Sha.IL 7548803592384816321
StarkedAir.Block.Sha.INIT 13752328820276602557
StarkedAir.Block.Sha.IVA_LO 4122579724926651454
StarkedAir.Block.Sha.IVE_LO 15021439758854435811
StarkedAir.Block.Sha.LID 10674809079763322373
StarkedAir.Block.Sha.MID 9440403996689931779
StarkedAir.Block.Sha.MSGROW 6734708282103567336
StarkedAir.Block.Sha.NDUP 14930426411805578633
StarkedAir.Block.Sha.NILS 11073764770086698345
StarkedAir.Block.Sha.NNE 17010543522489585975
StarkedAir.Block.Sha.NODE 2700747840432739824
StarkedAir.Block.Sha.NPAD 18257503768710735932
StarkedAir.Block.Sha.NP_LO 11208987806306150437
StarkedAir.Block.Sha.N_MAIN 9687707573945904981
StarkedAir.Block.Sha.REL_DIGEST 6734708282103567336
StarkedAir.Block.Sha.REL_NODE 15608481590008836421
StarkedAir.Block.Sha.RID 13363460484354492103
StarkedAir.Block.Sha.ROW0 9619963949715690370
StarkedAir.Block.Sha.ROWIDX 15608481590008836421
StarkedAir.Block.Sha.USEW 13157210405237361235
StarkedAir.Block.Sha.YM 9101128833897120425
StarkedAir.Block.Sha.ZH 11049598832614110269
StarkedAir.Block.Sha.ZL 18302911713765037329
StarkedAir.Block.Sha.ZZ 11596352625421794144
StarkedAir.Block.Sha.constraints 9944545127670452536
StarkedAir.Block.Sha.dLimb 186394966660386660
StarkedAir.Block.Sha.dblBlock 18235785426816597303
StarkedAir.Block.Sha.dblC 12269998498490092480
StarkedAir.Block.Sha.dblWord 15663431719187665571
StarkedAir.Block.Sha.digestLimbs 413146587691331122
StarkedAir.Block.Sha.flagC 2540374969561202630
StarkedAir.Block.Sha.fold 15268446542026920843
StarkedAir.Block.Sha.fold._f 9212492706979392108
StarkedAir.Block.Sha.fold.match_1 17830781580792491215
StarkedAir.Block.Sha.initC 729820454724207230
StarkedAir.Block.Sha.k 4215733963973134624
StarkedAir.Block.Sha.kp 14591804336548626625
StarkedAir.Block.Sha.lookups 15364042914350174159
StarkedAir.Block.Sha.mutC 8043662553986443408
StarkedAir.Block.Sha.nodeFlagC 311955755424418221
StarkedAir.Block.Sha.nodeOrderC 16243970031612096044
StarkedAir.Block.Sha.nodeWordLimbs 4815749958411105094
StarkedAir.Block.Sha.npadC 14131504765698362207
StarkedAir.Block.Sha.npadWord 8104525988631809917
StarkedAir.Block.Sha.om 8801113726808236209
StarkedAir.Block.Sha.one 1633976985673480194
StarkedAir.Block.Sha.orderC 3230901070438501449
StarkedAir.Block.Sha.per72 12744749193189339864
StarkedAir.Block.Sha.preCols 16520564967922278494
StarkedAir.Block.Sha.sha 14195976782634997835
StarkedAir.Block.Tables.M8 12621482290909172116
StarkedAir.Block.Tables.MO 17101530479978464024
StarkedAir.Block.Tables.REL_OPC 7200184553213182899
StarkedAir.Block.Tables.REL_R8 6851467553259871396
StarkedAir.Block.Tables.isK 17043310659461992685
StarkedAir.Block.Tables.nzp 9921142537180359164
StarkedAir.Block.Tables.preCols 6623534308864229351
StarkedAir.Block.Tables.pushN 7698814410318517584
StarkedAir.Block.Tables.sigN 11168280518748509007
StarkedAir.Block.Tables.tab 7375536557753390365
StarkedAir.Block.Tables.tables 17386151214833498562
StarkedAir.Block.URec.C 9008973590095614055
StarkedAir.Block.URec.HDR 6851467553259871396
StarkedAir.Block.URec.J 17101530479978464024
StarkedAir.Block.URec.N_MAIN 15965332230801424257
StarkedAir.Block.URec.ON 12621482290909172116
StarkedAir.Block.URec.REL_UREC 11605307065553852467
StarkedAir.Block.URec.S 11239342436784068239
StarkedAir.Block.URec.T 13763848869307909864
StarkedAir.Block.URec.TL 4752661515056156754
StarkedAir.Block.URec.V 12480503310037593863
StarkedAir.Block.URec.X 3974326331376613517
StarkedAir.Block.URec.constraints 4614390995059804876
StarkedAir.Block.URec.endE 1615782864753567404
StarkedAir.Block.URec.first 15453146726949858975
StarkedAir.Block.URec.isLast 10838763449130032985
StarkedAir.Block.URec.k 4215733963973134624
StarkedAir.Block.URec.kn 10932140884916001105
StarkedAir.Block.URec.kp 14591804336548626625
StarkedAir.Block.URec.lastOn 18115899815943002436
StarkedAir.Block.URec.limb 7512756407812944505
StarkedAir.Block.URec.lookups 17719792941515026862
StarkedAir.Block.URec.notFirst 14162281473066790946
StarkedAir.Block.URec.notLast 17856571357075250639
StarkedAir.Block.URec.om 15132569984123850130
StarkedAir.Block.URec.one 1633976985673480194
StarkedAir.Block.URec.preCols 2484850527752626642
StarkedAir.Block.URec.urec 7723182547553762947
StarkedAir.Block.Ub 16040643627717686085
StarkedAir.Block.Undo.PUB_LEN 15608481590008836421
StarkedAir.Block.Undo.REL_UBYTE 195973943113694959
StarkedAir.Block.Undo.constraints 10188151374478713314
StarkedAir.Block.Undo.remap 439311791927941543
StarkedAir.Block.Undo.undo 1506964699588883944
StarkedAir.Block.WFE 7891082374178490326
StarkedAir.Block.WMerkle.ACTN 12621482290909172116
StarkedAir.Block.WMerkle.BASE 6851467553259871396
StarkedAir.Block.WMerkle.C1 13937052351939933727
StarkedAir.Block.WMerkle.C1INV 195973943113694959
StarkedAir.Block.WMerkle.CNT 13752328820276602557
StarkedAir.Block.WMerkle.DUP 13687919700108124114
StarkedAir.Block.WMerkle.FIRST 12621482290909172116
StarkedAir.Block.WMerkle.FIRSTL 11239342436784068239
StarkedAir.Block.WMerkle.FS 1015439597935339062
StarkedAir.Block.WMerkle.I 9619963949715690370
StarkedAir.Block.WMerkle.L1 12679747259330932428
StarkedAir.Block.WMerkle.LAST 4752661515056156754
StarkedAir.Block.WMerkle.LEFT 10911675690963571469
StarkedAir.Block.WMerkle.LINV 110532540116317034
StarkedAir.Block.WMerkle.LRAW 11208987806306150437
StarkedAir.Block.WMerkle.MMC 15965332230801424257
StarkedAir.Block.WMerkle.NBW 17318146846279119450
StarkedAir.Block.WMerkle.NF 11605307065553852467
StarkedAir.Block.WMerkle.NM 4122579724926651454
StarkedAir.Block.WMerkle.NOTLAST 17101530479978464024
StarkedAir.Block.WMerkle.NTX 9642947143088483524
StarkedAir.Block.WMerkle.N_MAIN 11024855835016570353
StarkedAir.Block.WMerkle.ODD 15608481590008836421
StarkedAir.Block.WMerkle.PBASE 7200184553213182899
StarkedAir.Block.WMerkle.PCNT 6734708282103567336
StarkedAir.Block.WMerkle.PINV 2246386411152602517
StarkedAir.Block.WMerkle.RIDC 15021439758854435811
StarkedAir.Block.WMerkle.RIGHT 4177543070365710692
StarkedAir.Block.WMerkle.RIX 644735488301855163
StarkedAir.Block.WMerkle.RN 4393090879460539949
StarkedAir.Block.WMerkle.RT 17101530479978464024
StarkedAir.Block.WMerkle.WON 5130555358687355332
StarkedAir.Block.WMerkle.childC 14241975368517138060
StarkedAir.Block.WMerkle.constraints 9199785549638680403
StarkedAir.Block.WMerkle.flagC 10478816294227075334
StarkedAir.Block.WMerkle.k 4215733963973134624
StarkedAir.Block.WMerkle.kindC 4746229293207201066
StarkedAir.Block.WMerkle.kp 14591804336548626625
StarkedAir.Block.WMerkle.levelC 16629053809691182882
StarkedAir.Block.WMerkle.lookups 12448327123115323187
StarkedAir.Block.WMerkle.nodeId 7869743490077633928
StarkedAir.Block.WMerkle.notFirst 15705400698702898974
StarkedAir.Block.WMerkle.om 7815351948821725316
StarkedAir.Block.WMerkle.one 1633976985673480194
StarkedAir.Block.WMerkle.preCols 2484850527752626642
StarkedAir.Block.WMerkle.wmerkle 9029726546138988457
StarkedAir.Block.Walk.ACC2 1015439597935339062
StarkedAir.Block.Walk.ACT 12621482290909172116
StarkedAir.Block.Walk.B 110532540116317034
StarkedAir.Block.Walk.DR 11605307065553852467
StarkedAir.Block.Walk.DT 6734708282103567336
StarkedAir.Block.Walk.ENDC 5130555358687355332
StarkedAir.Block.Walk.FS 17101530479978464024
StarkedAir.Block.Walk.GC 8217079625019891863
StarkedAir.Block.Walk.INF 15608481590008836421
StarkedAir.Block.Walk.INVA 17657334438023227186
StarkedAir.Block.Walk.INVD 1073657718774685624
StarkedAir.Block.Walk.INVR 16444331713195875192
StarkedAir.Block.Walk.K1 7200184553213182899
StarkedAir.Block.Walk.K2 12679747259330932428
StarkedAir.Block.Walk.K4 644735488301855163
StarkedAir.Block.Walk.L4 14757724169269328703
StarkedAir.Block.Walk.LACC 15021439758854435811
StarkedAir.Block.Walk.LE 11208987806306150437
StarkedAir.Block.Walk.LEF 11024855835016570353
StarkedAir.Block.Walk.LI 8529384104522857804
StarkedAir.Block.Walk.LK1 2246386411152602517
StarkedAir.Block.Walk.LK2 4122579724926651454
StarkedAir.Block.Walk.LK4 15965332230801424257
StarkedAir.Block.Walk.LN 13752328820276602557
StarkedAir.Block.Walk.NDR 3378581462597066800
StarkedAir.Block.Walk.NDT 18342781002210354705
StarkedAir.Block.Walk.NINF 1789953865269236795
StarkedAir.Block.Walk.NLACC 6552061845898070580
StarkedAir.Block.Walk.NLI 7386756880137863153
StarkedAir.Block.Walk.NLK1 11124677409355023995
StarkedAir.Block.Walk.NLK2 7671841968229473692
StarkedAir.Block.Walk.NLK4 4725656910573684349
StarkedAir.Block.Walk.NLN 7310214899571200254
StarkedAir.Block.Walk.NOP 11094188613630540670
StarkedAir.Block.Walk.NZP 4177543070365710692
StarkedAir.Block.Walk.N_MAIN 16591784325937161225
StarkedAir.Block.Walk.OP 9619963949715690370
StarkedAir.Block.Walk.PN 6851467553259871396
StarkedAir.Block.Walk.POS 11239342436784068239
StarkedAir.Block.Walk.REL_SIGOPS 13687919700108124114
StarkedAir.Block.Walk.REM 4752661515056156754
StarkedAir.Block.Walk.SG 10911675690963571469
StarkedAir.Block.Walk.SUMS 4667950421468529655
StarkedAir.Block.Walk.TOPF 9465160240525125549
StarkedAir.Block.Walk.ZA 2528803397246198985
StarkedAir.Block.Walk.ZD 14140254281272384383
StarkedAir.Block.Walk.ZR 17750663069614403632
StarkedAir.Block.Walk.bools 14564466877597105042
StarkedAir.Block.Walk.constraints 11119068869024587802
StarkedAir.Block.Walk.first 15453146726949858975
StarkedAir.Block.Walk.isLast 772695947456970895
StarkedAir.Block.Walk.isZero 11628486450963550751
StarkedAir.Block.Walk.k 4215733963973134624
StarkedAir.Block.Walk.kp 14591804336548626625
StarkedAir.Block.Walk.localC 15257636934503895075
StarkedAir.Block.Walk.lookups 11597809144117538848
StarkedAir.Block.Walk.notFirst 17680546512045641737
StarkedAir.Block.Walk.om 7075645198861469997
StarkedAir.Block.Walk.one 1633976985673480194
StarkedAir.Block.Walk.preCols 2484850527752626642
StarkedAir.Block.Walk.scriptC 13871278657413447844
StarkedAir.Block.Walk.stepC 3935738588002480548
StarkedAir.Block.Walk.walk 4745805336571270262
StarkedAir.Block.blockSum 15472004464258823465
StarkedAir.Block.blockSys 17098779988574179132
StarkedAir.Block.bytes 9319963975173897965
StarkedAir.Block.bytesF 28550661201329685
StarkedAir.Block.constraints 3942616370523363441
StarkedAir.Block.ctxLimb 3228652565816505189
StarkedAir.Block.efrac 5129865901931290193
StarkedAir.Block.encE 2957823032590111893
StarkedAir.Block.epochPN 11377319080096614489
StarkedAir.Block.hashSys 13770380171803703161
StarkedAir.Block.hwords 7437227654724474065
StarkedAir.Block.ioRows 16077129653267624513
StarkedAir.Block.isLast 7175143457965580847
StarkedAir.Block.joinRng 9110440607303968726
StarkedAir.Block.leafRng 17667669819815642652
StarkedAir.Block.notFirst 7743742685527701712
StarkedAir.Block.preCols 2484850527752626642
StarkedAir.Block.stLimbs 14828536308225470673
StarkedAir.Block.tupleOf 155604424351560432
StarkedAir.Block.txidLimb 3680338214155519578
StarkedAir.Block.wleaves 10934019511373310052
StarkedAir.Circuit.BLOCK 2266981284532208154
StarkedAir.Circuit.BlockCtx.ONE 13752328820276602557
StarkedAir.Circuit.BlockCtx.ctxOps 8173901774492177399
StarkedAir.Circuit.BlockCtx.flagOps 17386122578640767119
StarkedAir.Circuit.BlockCtx.highOf 6815284001888050469
StarkedAir.Circuit.BlockCtx.hotOps 17761476511628414518
StarkedAir.Circuit.BlockCtx.lowOf 17078375189495075926
StarkedAir.Circuit.BlockCtx.subOps 5255892617030581978
StarkedAir.Circuit.BlockCtx.subsidy 9181283964555168919
StarkedAir.Circuit.BlockLeaf.M0 577624025665939290
StarkedAir.Circuit.BlockLeaf.M1 8005197264031571867
StarkedAir.Circuit.BlockLeaf.NW 11208987806306150437
StarkedAir.Circuit.BlockLeaf.N_IN 7248905091690107603
StarkedAir.Circuit.BlockLeaf.checksOps 1678819291968320715
StarkedAir.Circuit.BlockLeaf.seedLeafProg 12482771802738935419
StarkedAir.Circuit.BlockLeaf.wReg 18249744232310871857
StarkedAir.Circuit.BlockNode.CH 6734708282103567336
StarkedAir.Circuit.BlockNode.EXT_B 6988241736356003233
StarkedAir.Circuit.BlockNode.HR 2246386411152602517
StarkedAir.Circuit.BlockNode.LO 12621482290909172116
StarkedAir.Circuit.BlockNode.NIN 13752328820276602557
StarkedAir.Circuit.BlockNode.NN 17101530479978464024
StarkedAir.Circuit.BlockNode.NSUM 16591784325937161225
StarkedAir.Circuit.BlockNode.SR 16444331713195875192
StarkedAir.Circuit.BlockNode.SS 11239342436784068239
StarkedAir.Circuit.BlockNode.bC0 13131678934347788534
StarkedAir.Circuit.BlockNode.bC1 4696562365929605953
StarkedAir.Circuit.BlockNode.bDigest 17512482334674815631
StarkedAir.Circuit.BlockNode.bJoin 10968571320711267197
StarkedAir.Circuit.BlockNode.bKey 7627566071258952299
StarkedAir.Circuit.BlockNode.bchild 16496504444927550787
StarkedAir.Circuit.BlockNode.blockNodeProgram 2271701620495671223
StarkedAir.Circuit.BlockNode.hrNode 9060706749725943293
StarkedAir.Circuit.BlockNode.linkOps 15290662392419397248
StarkedAir.Circuit.BlockNode.lt30 3193099617412676091
StarkedAir.Circuit.BlockNode.nodeOut 13056200302010838690
StarkedAir.Circuit.BlockNode.outReg 3886741016630133958
StarkedAir.Circuit.BlockNode.srNode 8797161592527138075
StarkedAir.Circuit.BlockRec.Collision 6658132553732922983
StarkedAir.Circuit.BlockRec.H 17524520411747960331
StarkedAir.Circuit.BlockRec.HookGates 9484072683139874268
StarkedAir.Circuit.BlockRec.LIN 5284724056767648695
StarkedAir.Circuit.BlockRec.LSEED 2581427263304555304
StarkedAir.Circuit.BlockRec.LeafOut 18163894594969511925
StarkedAir.Circuit.BlockRec.Tree 4947258123697059603
StarkedAir.Circuit.BlockRec.Tree.below 14078527054675433867
StarkedAir.Circuit.BlockRec.Tree.brecOn 1112724162927945635
StarkedAir.Circuit.BlockRec.Tree.brecOn.go 12309796470323851053
StarkedAir.Circuit.BlockRec.Tree.casesOn 8213067016065973666
StarkedAir.Circuit.BlockRec.Tree.hash 9661502848745365310
StarkedAir.Circuit.BlockRec.Tree.hash.match_1 11738060744849569152
StarkedAir.Circuit.BlockRec.Tree.key 7060301032900919718
StarkedAir.Circuit.BlockRec.Tree.key._f 798001553337652429
StarkedAir.Circuit.BlockRec.Tree.leaf 2292278552
StarkedAir.Circuit.BlockRec.Tree.node 3310300566
StarkedAir.Circuit.BlockRec.Tree.rec 2909502127
StarkedAir.Circuit.BlockRec.Trust 10991053124077016908
StarkedAir.Circuit.BlockRec.Trust.mk 1649151361
StarkedAir.Circuit.BlockRec.blockLeafOut 14717586490366668372
StarkedAir.Circuit.BlockRec.childSum 10592627854440986644
StarkedAir.Circuit.BlockRec.keyOf 2627845629955930997
StarkedAir.Circuit.BlockRec.leafDg 13613718150793361946
StarkedAir.Circuit.BlockRec.leafKey 15926553737258759112
StarkedAir.Circuit.BlockRec.leafOutOps 14319629601296192938
StarkedAir.Circuit.BlockRec.outSum 6669954708479048515
StarkedAir.Circuit.BlockRec.sReg 8004558542974073844
StarkedAir.Circuit.BlockRec.sumDigest 820596514008726166
StarkedAir.Circuit.BlockRec.vals 1234930350653819936
StarkedAir.Circuit.BlockRec.zeroKey 9508251696432073109
StarkedAir.Circuit.BlockTree.Linked 16394057694338774871
StarkedAir.Circuit.BlockTree.Linked' 3256882141208732589
StarkedAir.Circuit.BlockTree.Linked'._f 15290029933395370290
StarkedAir.Circuit.BlockTree.Linked'.match_1 8500139157461062078
StarkedAir.Circuit.BlockTree.Linked._f 1904985142174776658
StarkedAir.Circuit.BlockTree.Linked.match_1 6685034172563296092
StarkedAir.Circuit.BlockTree.SumOk 15757349759364808582
StarkedAir.Circuit.BlockTree.hashOf 3084769588635683389
StarkedAir.Circuit.BlockTree.leafVec 17466280146285499594
StarkedAir.Circuit.BlockTree.rngOf 9164303772093635433
StarkedAir.Circuit.BlockTree.rootFrom 17988772817446457183
StarkedAir.Circuit.BlockTree.rootFrom._f 17516563571882526196
StarkedAir.Circuit.BlockTree.rootFrom.match_1 1157926029087303457
StarkedAir.Circuit.BlockTree.seedOf 1905480411647156886
StarkedAir.Circuit.BlockTree.stateAt 2562386272838010965
StarkedAir.Circuit.Channel.Spec.St 14870965665879628945
StarkedAir.Circuit.Channel.Spec.St.hi 6093575539738547650
StarkedAir.Circuit.Channel.Spec.St.lo 5372431178483419547
StarkedAir.Circuit.Channel.Spec.St.mk 2010183340
StarkedAir.Circuit.Channel.Spec.St.nDraws 16905757211733172986
StarkedAir.Circuit.Channel.Spec.absorb 9334779080177306843
StarkedAir.Circuit.Channel.Spec.drawTwo 14368680158520855617
StarkedAir.Circuit.Channel.Spec.mixQm31s 1140842578617454683
StarkedAir.Circuit.Channel.Spec.mixU32s 6124216658174345234
StarkedAir.Circuit.Channel.Spec.ofLimbs 16093054325219868319
StarkedAir.Circuit.Channel.Spec.powMix 6400160597404482674
StarkedAir.Circuit.Channel.absorb 12541180052087171299
StarkedAir.Circuit.Channel.drawP 5280383573049786148
StarkedAir.Circuit.Channel.drawPointP 3446747584424957154
StarkedAir.Circuit.Channel.drawQm31P 13718828224659287931
StarkedAir.Circuit.Channel.fpe 12824354522227460215
StarkedAir.Circuit.Channel.fw 7829372039259022578
StarkedAir.Circuit.Channel.mixQm31sP 8928062366249484435
StarkedAir.Circuit.Channel.mixU32sP 1495375716091415802
StarkedAir.Circuit.Channel.pointOps 6465050662826680377
StarkedAir.Circuit.Channel.powMixP 9087547083183419352
StarkedAir.Circuit.Channel.qOf 7312336910814682686
StarkedAir.Circuit.Channel.qWords 3059936033555332653
StarkedAir.Circuit.Channel.redWord 12573267932007809527
StarkedAir.Circuit.Channel.reduce 13712147881035451047
StarkedAir.Circuit.Channel.reduceOps 38171792973616860
StarkedAir.Circuit.Channel.unpack 6654523416323150443
StarkedAir.Circuit.Channel.unpack._f 11878476426798246216
StarkedAir.Circuit.Channel.unpack.match_1 16298679511601174868
StarkedAir.Circuit.Channel.unpack1 2973672416842661030
StarkedAir.Circuit.ChildRegs 801756190693788312
StarkedAir.Circuit.ChildRegs.chash 10421710273523295572
StarkedAir.Circuit.ChildRegs.digest 583090933423697645
StarkedAir.Circuit.ChildRegs.key 3564382033286475132
StarkedAir.Circuit.ChildRegs.mk 1822012691
StarkedAir.Circuit.ChildRegs.pubs 2629256251295335543
StarkedAir.Circuit.Composition.BatchIn 14715750547515248546
StarkedAir.Circuit.Composition.BatchIn.B 13333787900487597189
StarkedAir.Circuit.Composition.BatchIn.L 3939105380649452958
StarkedAir.Circuit.Composition.BatchIn.S 11465693637119184357
StarkedAir.Circuit.Composition.BatchIn.d 10453550878090445225
StarkedAir.Circuit.Composition.BatchIn.m 5297486056837483032
StarkedAir.Circuit.Composition.BatchIn.mk 3522230436
StarkedAir.Circuit.Composition.BatchIn.shift 1899926804583661015
StarkedAir.Circuit.Composition.BatchIn.sprev 3003712246480597057
StarkedAir.Circuit.Composition.ExtE 5886141264934551965
StarkedAir.Circuit.Composition.ExtE.mk 1756408910
StarkedAir.Circuit.Composition.ExtE.mult 14277568955138595649
StarkedAir.Circuit.Composition.ExtE.rel 17293238036466975501
StarkedAir.Circuit.Composition.ExtE.vals 8215717461683618602
StarkedAir.Circuit.Composition.Inputs 9301388653950648712
StarkedAir.Circuit.Composition.Inputs.leaf 11637364497030278274
StarkedAir.Circuit.Composition.Inputs.mk 352226347
StarkedAir.Circuit.Composition.Inputs.pub 4404490459332071618
StarkedAir.Circuit.Composition.Layout 428005373984804403
StarkedAir.Circuit.Composition.Layout.coeff 12001981200754405635
StarkedAir.Circuit.Composition.Layout.inputs 17553846387995048584
StarkedAir.Circuit.Composition.Layout.inputs.match_1 10773035983448041582
StarkedAir.Circuit.Composition.Layout.mainStart 5904124344195912622
StarkedAir.Circuit.Composition.Layout.mk 1052431907
StarkedAir.Circuit.Composition.Layout.nIn 18410162976060723631
StarkedAir.Circuit.Composition.Layout.nMain 1772922268854913599
StarkedAir.Circuit.Composition.Layout.nPre 1464078593886151546
StarkedAir.Circuit.Composition.Layout.nPub 11683693232677680699
StarkedAir.Circuit.Composition.Layout.nSamples 12926523249785452831
StarkedAir.Circuit.Composition.Layout.offs 1332090774372717746
StarkedAir.Circuit.Composition.Layout.oodsX 1077003407758048754
StarkedAir.Circuit.Composition.PartRegs 3185992488584397551
StarkedAir.Circuit.Composition.PartRegs.ci 12798720387612595085
StarkedAir.Circuit.Composition.PartRegs.claimed 5869307890445319076
StarkedAir.Circuit.Composition.PartRegs.inter 4350561813047802409
StarkedAir.Circuit.Composition.PartRegs.mk 1046811121
StarkedAir.Circuit.Composition.Shared 11177214373476681329
StarkedAir.Circuit.Composition.Shared.alpha 9048024617400918828
StarkedAir.Circuit.Composition.Shared.coeff 551544052316774660
StarkedAir.Circuit.Composition.Shared.logSize 7196366530637227406
StarkedAir.Circuit.Composition.Shared.mk 3585770968
StarkedAir.Circuit.Composition.Shared.z 10050045699922157427
StarkedAir.Circuit.Composition.WF 3736747117525544904
StarkedAir.Circuit.Composition.WF._sparseCasesOn_1 4391421646640567022
StarkedAir.Circuit.Composition.WF.match_1 820862950561885854
StarkedAir.Circuit.Composition.accReg 8845687263633199147
StarkedAir.Circuit.Composition.accReg.match_1 17830781580792491215
StarkedAir.Circuit.Composition.balanceProg 8266423689689969449
StarkedAir.Circuit.Composition.batchFold 2416995431445833104
StarkedAir.Circuit.Composition.batchOps 1570592308441631922
StarkedAir.Circuit.Composition.batchTerm 11418777745778417119
StarkedAir.Circuit.Composition.compDag 15769890894564629430
StarkedAir.Circuit.Composition.compRoots 99881185596997212
StarkedAir.Circuit.Composition.constraintOps 17731626181191986257
StarkedAir.Circuit.Composition.cstQ 759271158595774983
StarkedAir.Circuit.Composition.dagOps 11855118253220609547
StarkedAir.Circuit.Composition.denOps 8585936511608724843
StarkedAir.Circuit.Composition.e1 7015390422203283650
StarkedAir.Circuit.Composition.e2 1736085738790426401
StarkedAir.Circuit.Composition.e3 4301816810775433352
StarkedAir.Circuit.Composition.entFold 2934109831876315104
StarkedAir.Circuit.Composition.entryFrac 12546696150951736044
StarkedAir.Circuit.Composition.entryOps 2764713398509730310
StarkedAir.Circuit.Composition.fingerprint 1006723930965589556
StarkedAir.Circuit.Composition.horner 4094878049250242369
StarkedAir.Circuit.Composition.horner._f 14500449045191669424
StarkedAir.Circuit.Composition.horner.match_1 14906355249352815004
StarkedAir.Circuit.Composition.hornerOps 2638082702217822538
StarkedAir.Circuit.Composition.hornerRegs 8276446116990694724
StarkedAir.Circuit.Composition.leafQ 18153650394000870596
StarkedAir.Circuit.Composition.lk 14364659762861923201
StarkedAir.Circuit.Composition.lookupAt 3205347305146134673
StarkedAir.Circuit.Composition.ninv 8443993624714126878
StarkedAir.Circuit.Composition.nodeOps 15257005610887904165
StarkedAir.Circuit.Composition.nodeOps._sparseCasesOn_1 10377985166193111434
StarkedAir.Circuit.Composition.nodeOps.match_1 8099887552912192265
StarkedAir.Circuit.Composition.nodeReg 14477735834547910360
StarkedAir.Circuit.Composition.nodeReg._sparseCasesOn_1 5523436881708479340
StarkedAir.Circuit.Composition.nodeReg._sparseCasesOn_2 5944029986163308501
StarkedAir.Circuit.Composition.nodeReg.match_1 10881366926323990897
StarkedAir.Circuit.Composition.pAcc1 400954720466459261
StarkedAir.Circuit.Composition.pB 9917498087579750546
StarkedAir.Circuit.Composition.pBt 10575057013189542578
StarkedAir.Circuit.Composition.pBx 7231679099989509194
StarkedAir.Circuit.Composition.pCOps 17286360437081027560
StarkedAir.Circuit.Composition.pDens 12875875519056683258
StarkedAir.Circuit.Composition.pHb 11243726781996344451
StarkedAir.Circuit.Composition.pIdAt 17378561665186751340
StarkedAir.Circuit.Composition.pIds 8177223864457333757
StarkedAir.Circuit.Composition.pL 1819004945939297764
StarkedAir.Circuit.Composition.pMults 2396955470203319464
StarkedAir.Circuit.Composition.pNc 11382249464386626447
StarkedAir.Circuit.Composition.pNodes 17668812118990184322
StarkedAir.Circuit.Composition.pP0 9098959911933708996
StarkedAir.Circuit.Composition.pQ 6507385239489458567
StarkedAir.Circuit.Composition.pReg 3049373289683261633
StarkedAir.Circuit.Composition.pSS 11497349043275770635
StarkedAir.Circuit.Composition.pShOps 12347229061187177326
StarkedAir.Circuit.Composition.pSp 2530699814215659344
StarkedAir.Circuit.Composition.pValsOf 14921813816069662072
StarkedAir.Circuit.Composition.partFold 12003537114460758367
StarkedAir.Circuit.Composition.partProg 8615096737866414666
StarkedAir.Circuit.Composition.partTerms 610978132259804453
StarkedAir.Circuit.Composition.program 6499478608379858693
StarkedAir.Circuit.Composition.pubQ 14445045997566793115
StarkedAir.Circuit.Composition.rootVal 4239904452000097125
StarkedAir.Circuit.Composition.secureOps 12969376139240875882
StarkedAir.Circuit.Composition.secureVal 12116376378467215410
StarkedAir.Circuit.Composition.seqOuts 12538606210675465234
StarkedAir.Circuit.Composition.seqOuts._f 13238500845588798584
StarkedAir.Circuit.Composition.seqOuts.match_1 4108144251202984113
StarkedAir.Circuit.Composition.sysProg 11155960401102091752
StarkedAir.Circuit.Composition.val 12326014692794801461
StarkedAir.Circuit.Deep.Label 12914792989764896688
StarkedAir.Circuit.Deep.Resp 17277317144516056197
StarkedAir.Circuit.Deep.Resp.col 5987798404146563329
StarkedAir.Circuit.Deep.Resp.idx 1027461836996302770
StarkedAir.Circuit.Deep.Resp.label 1949321250598197982
StarkedAir.Circuit.Deep.Resp.mk 1977973966
StarkedAir.Circuit.Deep.Resp.off 1711571134613908103
StarkedAir.Circuit.Deep.Resp.tree 15404968862788212477
StarkedAir.Circuit.Deep.colResps 10495086588280564174
StarkedAir.Circuit.Deep.colResps.match_1 3286681864404384245
StarkedAir.Circuit.Deep.deepFrom 2183136656390733447
StarkedAir.Circuit.Deep.deepFrom._f 17622248980285551265
StarkedAir.Circuit.Deep.deepFrom.match_1 16714435412701038491
StarkedAir.Circuit.Deep.deepList 14959397304438109320
StarkedAir.Circuit.Deep.labelsFrom 13000781317707038824
StarkedAir.Circuit.Deep.samples 1976266510393776008
StarkedAir.Circuit.Deep.samples.match_1 556179357428633914
StarkedAir.Circuit.Deep.treeLabels 7130361264474102892
StarkedAir.Circuit.Deep.treeLabels.match_1 7088792031154317659
StarkedAir.Circuit.Deep.treeResps 7182210563088297364
StarkedAir.Circuit.Deep.treeResps._f 5198511361343001644
StarkedAir.Circuit.Deep.treeResps.match_1 15086997072960536622
StarkedAir.Circuit.EXT_CHILD 7860539317984281379
StarkedAir.Circuit.EndToEnd.SZGood 18352844139312371512
StarkedAir.Circuit.EndToEnd.StarkSound 529158102843186867
StarkedAir.Circuit.EndToEnd.Val 2185048477082411819
StarkedAir.Circuit.EndToEnd.Val.inter 9504016385185686536
StarkedAir.Circuit.EndToEnd.Val.leaf 15006689456435999434
StarkedAir.Circuit.EndToEnd.Val.mk 458122756
StarkedAir.Circuit.EndToEnd.extRaw 10327054474987048797
StarkedAir.Circuit.EndToEnd.instOf 12809486802045288378
StarkedAir.Circuit.EndToEnd.oodsVal 17309261907849537650
StarkedAir.Circuit.EndToEnd.rowVal 13120459701159018747
StarkedAir.Circuit.EndToEnd.rowVal.match_1 10773035983448041582
StarkedAir.Circuit.EndToEnd.terms 10067851135228764959
StarkedAir.Circuit.HeaderRec.LeafOutH 17517245393575776171
StarkedAir.Circuit.HeaderRec.pubDigest 7713460709577242129
StarkedAir.Circuit.HeaderRec.valsH 554762761996347895
StarkedAir.Circuit.Hint 10883925531545511745
StarkedAir.Circuit.Hint.coord 3993040705
StarkedAir.Circuit.Hint.divC 4220142516
StarkedAir.Circuit.Hint.ext 1776514523
StarkedAir.Circuit.Hint.invOrZero 1767036328
StarkedAir.Circuit.Hint.isEq 4220142516
StarkedAir.Circuit.Hint.lsb 1767036328
StarkedAir.Circuit.Hint.modC 4220142516
StarkedAir.Circuit.Hint.reg 1776514523
StarkedAir.Circuit.Holds 7759549839738483855
StarkedAir.Circuit.Merkle.bitQ 4353626027171053197
StarkedAir.Circuit.Merkle.flipOps 8211335302662799128
StarkedAir.Circuit.Merkle.node 14553213103564785863
StarkedAir.Circuit.Merkle.path 7965881436418530023
StarkedAir.Circuit.Merkle.path._f 6536771774386094591
StarkedAir.Circuit.Merkle.path.match_1 10445048938170710851
StarkedAir.Circuit.Merkle.pathCheck 16171520047214828074
StarkedAir.Circuit.Merkle.specNode 8328092890168391852
StarkedAir.Circuit.Merkle.specRoot 7443041379894333325
StarkedAir.Circuit.Merkle.specRoot._f 15842107767200962969
StarkedAir.Circuit.Merkle.specRoot.match_1 762905883319870752
StarkedAir.Circuit.N_PUB 9440403996689931779
StarkedAir.Circuit.ONE 7501865748563843868
StarkedAir.Circuit.Oods.CP 16406594007887124817
StarkedAir.Circuit.Oods.CP.mk 602698947
StarkedAir.Circuit.Oods.CP.x 17602935971983765913
StarkedAir.Circuit.Oods.CP.y 4745201592462269206
StarkedAir.Circuit.Oods.cpAdd 14904667537469353598
StarkedAir.Circuit.Oods.cpConj 13430196488649086337
StarkedAir.Circuit.Oods.cpMul 11757237610489184675
StarkedAir.Circuit.Oods.cpMul._unary 16713668119793871098
StarkedAir.Circuit.Oods.cpZero 9299040298505208174
StarkedAir.Circuit.Oods.gen 8100818964401316267
StarkedAir.Circuit.Oods.shiftP 16813842372193527947
StarkedAir.Circuit.Oods.shiftPt 1731875666507367954
StarkedAir.Circuit.Oods.traceGen 9756552185855644605
StarkedAir.Circuit.Op 15609717420484994063
StarkedAir.Circuit.Op.add 2107003531
StarkedAir.Circuit.Op.blakeG 1252721175
StarkedAir.Circuit.Op.casesOn 8723563409963323079
StarkedAir.Circuit.Op.const 397137086
StarkedAir.Circuit.Op.ctorIdx 2162560457380491373
StarkedAir.Circuit.Op.eq 2653336952
StarkedAir.Circuit.Op.guess 667962532
StarkedAir.Circuit.Op.guessM31 667962532
StarkedAir.Circuit.Op.guessU16 667962532
StarkedAir.Circuit.Op.holds 15005958803080094625
StarkedAir.Circuit.Op.holds.match_1 11774505667930496762
StarkedAir.Circuit.Op.hook 586283538
StarkedAir.Circuit.Op.inv 2653336952
StarkedAir.Circuit.Op.m2u 2653336952
StarkedAir.Circuit.Op.mul 2107003531
StarkedAir.Circuit.Op.one 4143624950
StarkedAir.Circuit.Op.pmul 2107003531
StarkedAir.Circuit.Op.rec 3536317442
StarkedAir.Circuit.Op.sub 2107003531
StarkedAir.Circuit.Op.unused 4143624950
StarkedAir.Circuit.Op.xor3 4153048111
StarkedAir.Circuit.Op.zero 4143624950
StarkedAir.Circuit.Out 6381523859689538064
StarkedAir.Circuit.Out.mk 3739296005
StarkedAir.Circuit.Out.next 2236598584845518504
StarkedAir.Circuit.Out.ops 12014415191654859905
StarkedAir.Circuit.Out.res 1843976474017931169
StarkedAir.Circuit.Pow.INV2 15652643747451977402
StarkedAir.Circuit.Pow.Spec.powOk 6044462759406079246
StarkedAir.Circuit.Pow.assertBit 2367513788852509767
StarkedAir.Circuit.Pow.fold 13078221845642581861
StarkedAir.Circuit.Pow.fold._f 2878128473326935579
StarkedAir.Circuit.Pow.fold.match_1 5062619832248392733
StarkedAir.Circuit.Pow.powCheckP 11696778036014390520
StarkedAir.Circuit.Pow.rounds 15317398985362763165
StarkedAir.Circuit.Pow.rounds._f 9687721206978988898
StarkedAir.Circuit.Pow.rounds.match_1 2671473151025538475
StarkedAir.Circuit.Program 11439221476885187046
StarkedAir.Circuit.Program.mk 1818042546
StarkedAir.Circuit.Program.ops 14208735230604175799
StarkedAir.Circuit.Program.results 11172861970204655687
StarkedAir.Circuit.Q 9098138277342538836
StarkedAir.Circuit.Q.IsBase 16629948589798936924
StarkedAir.Circuit.Q.IsU32 8358206132960107673
StarkedAir.Circuit.Q.a 43667141081517737
StarkedAir.Circuit.Q.b 9297466026164580387
StarkedAir.Circuit.Q.c 1328046544913643865
StarkedAir.Circuit.Q.cmul 17843718473493918599
StarkedAir.Circuit.Q.d 4473606135408106087
StarkedAir.Circuit.Q.instAdd 9345365565197297525
StarkedAir.Circuit.Q.instMul 9126815787530812474
StarkedAir.Circuit.Q.instSub 9600226158627746356
StarkedAir.Circuit.Q.lit 9093227186846416887
StarkedAir.Circuit.Q.m2u 4531148191197652871
StarkedAir.Circuit.Q.mk 1349904058
StarkedAir.Circuit.Q.pack 2667224906681567483
StarkedAir.Circuit.Q.word 349992850032676142
StarkedAir.Circuit.Statement.PartSt 4323526383414184580
StarkedAir.Circuit.Statement.PartSt.digest 595426825512847547
StarkedAir.Circuit.Statement.PartSt.mk 287567121
StarkedAir.Circuit.Statement.PartSt.pubs 13773973774123016114
StarkedAir.Circuit.Statement.headerOps 14369789062222918000
StarkedAir.Circuit.Statement.mixArgs 16280347228723805260
StarkedAir.Circuit.Statement.mixArgs._f 17763516859341213800
StarkedAir.Circuit.Statement.mixArgs._sparseCasesOn_1 18349320414959255277
StarkedAir.Circuit.Statement.mixArgs.match_1 15228396954952142574
StarkedAir.Circuit.Statement.partOps 17132919821229068003
StarkedAir.Circuit.Statement.partSize 10126457959504709697
StarkedAir.Circuit.Statement.pubOps 15893805708713956005
StarkedAir.Circuit.Statement.stmtOps 1754303163613710147
StarkedAir.Circuit.Statement.stmtSpec 16037032646094920566
StarkedAir.Circuit.Statement.stmtWords 1324114834228966001
StarkedAir.Circuit.Statement.wv 9019150367316828704
StarkedAir.Circuit.TB 9054670203840292923
StarkedAir.Circuit.blake2s 12974119943927785471
StarkedAir.Circuit.blake2sWords 5813635051977919992
StarkedAir.Circuit.blockOps 12571548478556091813
StarkedAir.Circuit.chain 3106821790314753209
StarkedAir.Circuit.child 15885927822640158072
StarkedAir.Circuit.constU32 8765009318883924631
StarkedAir.Circuit.gOp 1944017324182395886
StarkedAir.Circuit.gState 4762834525757568322
StarkedAir.Circuit.gState._f 163551446896171393
StarkedAir.Circuit.gState.match_1 5966486410946897557
StarkedAir.Circuit.gState.match_3 17830781580792491215
StarkedAir.Circuit.guessHash 4362310521980358143
StarkedAir.Circuit.guessU32 4451267533534090042
StarkedAir.Circuit.hashW 16910600231871796217
StarkedAir.Circuit.hashWL 15257391447322716164
StarkedAir.Circuit.hashWL._f 12793169667412255196
StarkedAir.Circuit.hashWL.match_1 17830781580792491215
StarkedAir.Circuit.isIn 8871226720599635189
StarkedAir.Circuit.ivWord 8699278922701816089
StarkedAir.Circuit.leafHash 9544363267300149143
StarkedAir.Circuit.linkChecks 17372773408014343570
StarkedAir.Circuit.nBlocks 16995390180492155233
StarkedAir.Circuit.nodeC0 6955861439903790630
StarkedAir.Circuit.nodeC1 15051979811667793673
StarkedAir.Circuit.nodeDigest 5845075575738975382
StarkedAir.Circuit.nodeKey 7383761549956317456
StarkedAir.Circuit.nodeLink 11028562739400034738
StarkedAir.Circuit.nodeOut 1252707278368474233
StarkedAir.Circuit.nodeOuts 7081313207152509604
StarkedAir.Circuit.nodePL 15047486060983019854
StarkedAir.Circuit.nodePR 15665534129193560859
StarkedAir.Circuit.nodeProgram 10607728342108394991
StarkedAir.Circuit.nodeTree 17590694313239338477
StarkedAir.Circuit.pubsDigest 15951677723916669388
StarkedAir.Circuit.range16 16323179013711604896
StarkedAir.Circuit.treeNode 13582299647825869679
StarkedAir.Circuit.wordsOf 3369815413737908708
StarkedAir.Comp 14284233726971471820
StarkedAir.Comp.air 18030797575459134624
StarkedAir.Comp.lookups 18093185417665623275
StarkedAir.Comp.mk 1065119481
StarkedAir.DagState 8284028335400666191
StarkedAir.DagState.ids 6073289342293710819
StarkedAir.DagState.mk 731054495
StarkedAir.DagState.out 8597311620065896912
StarkedAir.Expr 11303857423613885392
StarkedAir.Expr.add 1506004216
StarkedAir.Expr.add.elim 2726342248804429446
StarkedAir.Expr.add.noConfusion 13888250454099682139
StarkedAir.Expr.below 14876219523557409339
StarkedAir.Expr.brecOn 14485461535669957328
StarkedAir.Expr.brecOn.go 10348790448317438063
StarkedAir.Expr.casesOn 4740705637082787768
StarkedAir.Expr.col 2763396940
StarkedAir.Expr.col.elim 7356316903394189567
StarkedAir.Expr.col.noConfusion 159200535215894501
StarkedAir.Expr.const 2808486231
StarkedAir.Expr.const.elim 16376827102137908159
StarkedAir.Expr.const.noConfusion 10394435373359977134
StarkedAir.Expr.ctorElim 11088614868491195410
StarkedAir.Expr.ctorElimType 14806985455672980748
StarkedAir.Expr.ctorIdx 68445167361828633
StarkedAir.Expr.eval 16540112575261618751
StarkedAir.Expr.eval._f 18341306552219918402
StarkedAir.Expr.eval.match_1 13402520789550799716
StarkedAir.Expr.evalR 14282506435975487159
StarkedAir.Expr.evalR._f 3332868460736066848
StarkedAir.Expr.evalR.match_1 7789081745509938674
StarkedAir.Expr.mapPub 2555473558108782902
StarkedAir.Expr.mapPub._f 16501981040216101608
StarkedAir.Expr.mapPub.match_1 7789081745509938674
StarkedAir.Expr.mul 1506004216
StarkedAir.Expr.mul.elim 8678194778470701112
StarkedAir.Expr.mul.noConfusion 10446489674583001174
StarkedAir.Expr.neg 2568028563
StarkedAir.Expr.neg.elim 4929527908148918233
StarkedAir.Expr.neg.noConfusion 10881983251429189206
StarkedAir.Expr.noConfusion 18281477468488913940
StarkedAir.Expr.noConfusionType 8566969317399440150
StarkedAir.Expr.pub 2808486231
StarkedAir.Expr.pub.elim 2671612112649071007
StarkedAir.Expr.pub.noConfusion 15182894208015690170
StarkedAir.Expr.rec 2019465717
StarkedAir.Expr.sub 1506004216
StarkedAir.Expr.sub.elim 12263762533571692898
StarkedAir.Expr.sub.noConfusion 10840179214799121523
StarkedAir.F 2817563682531933181
StarkedAir.HeaderChain.FIRST 2528803397246198985
StarkedAir.HeaderChain.IS_CHAIN 7200184553213182899
StarkedAir.HeaderChain.IS_IV 9619963949715690370
StarkedAir.HeaderChain.IS_WCONST 12679747259330932428
StarkedAir.HeaderChain.IVA_LO 13752328820276602557
StarkedAir.HeaderChain.IVE_LO 15608481590008836421
StarkedAir.HeaderChain.LAST 17657334438023227186
StarkedAir.HeaderChain.LINK0 15021439758854435811
StarkedAir.HeaderChain.MSG0 4177543070365710692
StarkedAir.HeaderChain.MTP0 3378581462597066800
StarkedAir.HeaderChain.MTPC 16591784325937161225
StarkedAir.HeaderChain.OUT0 14140254281272384383
StarkedAir.HeaderChain.PERIOD 15290883838485526649
StarkedAir.HeaderChain.POW 11094188613630540670
StarkedAir.HeaderChain.PREV 18342781002210354705
StarkedAir.HeaderChain.PubLink 8060745836110740875
StarkedAir.HeaderChain.PubSeg 13156186872308997123
StarkedAir.HeaderChain.RT 1789953865269236795
StarkedAir.HeaderChain.STATE 7310214899571200254
StarkedAir.HeaderChain.VER 16134696242039045869
StarkedAir.HeaderChain.WC_LO 644735488301855163
StarkedAir.HeaderChain.WORK 17358607272618789953
StarkedAir.HeaderChain.WorkInOk 14867828103447052957
StarkedAir.HeaderChain.WorkOutOk 8176366721924981697
StarkedAir.HeaderChain.air 8180987952272132056
StarkedAir.HeaderChain.bE 3440987716652270973
StarkedAir.HeaderChain.baseConstraints 600795976340805943
StarkedAir.HeaderChain.beByte 1988520916280814040
StarkedAir.HeaderChain.bitR 9413891950057526308
StarkedAir.HeaderChain.bitsAt 2273673461444948731
StarkedAir.HeaderChain.bitsR 5631840304227659421
StarkedAir.HeaderChain.byD 2613323654537007715
StarkedAir.HeaderChain.cE 17433024447040540931
StarkedAir.HeaderChain.capCol 14703717435146063707
StarkedAir.HeaderChain.capE 4027525449115037345
StarkedAir.HeaderChain.capHead 8820893280945330839
StarkedAir.HeaderChain.capThr25 2163004147523785251
StarkedAir.HeaderChain.capThr26 6174084734642035318
StarkedAir.HeaderChain.ccE 11315216546900631942
StarkedAir.HeaderChain.cmpHi 17409346116677690193
StarkedAir.HeaderChain.cmpLo 12949266900563098461
StarkedAir.HeaderChain.combine 7956136821152417249
StarkedAir.HeaderChain.constraints 5114797134794706323
StarkedAir.HeaderChain.copyCs 3541804947166804990
StarkedAir.HeaderChain.copyFam 16361412338970727757
StarkedAir.HeaderChain.copySelF 3582460128131964992
StarkedAir.HeaderChain.copySelNF 18354356115459244814
StarkedAir.HeaderChain.countC 14678075344906192840
StarkedAir.HeaderChain.dAny 13674052526063946517
StarkedAir.HeaderChain.dE 13146612724675507578
StarkedAir.HeaderChain.dE' 8633174746004580276
StarkedAir.HeaderChain.dHead 513031717489925804
StarkedAir.HeaderChain.dLimb 16271843793703144266
StarkedAir.HeaderChain.dcE 6119429842609075500
StarkedAir.HeaderChain.decodeIn 2496346533194636297
StarkedAir.HeaderChain.decodeOut 359361157635210037
StarkedAir.HeaderChain.divBytes 18052075622250967196
StarkedAir.HeaderChain.divBytes.match_1 17163099491768297178
StarkedAir.HeaderChain.divCol 14116288370320079306
StarkedAir.HeaderChain.divM1Bytes 17295959079359461544
StarkedAir.HeaderChain.ecE 9782398683456622820
StarkedAir.HeaderChain.eqLimbs 15025720526037775873
StarkedAir.HeaderChain.expE 4495682090723344171
StarkedAir.HeaderChain.fieldOf 13327543892820489146
StarkedAir.HeaderChain.fieldOf.match_1 18268961221940264838
StarkedAir.HeaderChain.flagAt 16215424667896235753
StarkedAir.HeaderChain.flagE 6871410122546097225
StarkedAir.HeaderChain.g2E 17503751203047609780
StarkedAir.HeaderChain.gE 7780219590135362721
StarkedAir.HeaderChain.hCarryE 5630214158829806560
StarkedAir.HeaderChain.hashAt 3248726366147370693
StarkedAir.HeaderChain.hashBit 5677977874921523162
StarkedAir.HeaderChain.hashByteE 17255526207293809328
StarkedAir.HeaderChain.headerWord 9198664546473903170
StarkedAir.HeaderChain.heightE 17907105144863030976
StarkedAir.HeaderChain.hiE 3760923307499868660
StarkedAir.HeaderChain.isIn 8871226720599635189
StarkedAir.HeaderChain.isPadRow 3079505627036640913
StarkedAir.HeaderChain.ivWords 3139897311156775666
StarkedAir.HeaderChain.knE 15714983440360763181
StarkedAir.HeaderChain.kpE 7266077759299952513
StarkedAir.HeaderChain.lE 14616074537989564128
StarkedAir.HeaderChain.leN 17866407100205875312
StarkedAir.HeaderChain.linkSrc 858674302209517468
StarkedAir.HeaderChain.linkage 17953321128751094940
StarkedAir.HeaderChain.loE 17382895766896336679
StarkedAir.HeaderChain.ltE 6871410122546097225
StarkedAir.HeaderChain.m1E 764048108957203363
StarkedAir.HeaderChain.mB 4969491885480171824
StarkedAir.HeaderChain.mainCol 1573503209459212468
StarkedAir.HeaderChain.mantBit 15089596165242867784
StarkedAir.HeaderChain.mantE 1560047261902740286
StarkedAir.HeaderChain.mcE 3848064181767233546
StarkedAir.HeaderChain.mcE' 17527688029323214165
StarkedAir.HeaderChain.mcSlots 8352471995269280721
StarkedAir.HeaderChain.midE 11195836295178857998
StarkedAir.HeaderChain.midE' 15264971645618457030
StarkedAir.HeaderChain.msgSrc 1378948838445813992
StarkedAir.HeaderChain.mtpCs 12921166899656013503
StarkedAir.HeaderChain.mtpRegion 12179577469604324067
StarkedAir.HeaderChain.nbBit 16915110564456469537
StarkedAir.HeaderChain.nbitsFirst 11082551947465708663
StarkedAir.HeaderChain.nbitsLink 1925242735202667591
StarkedAir.HeaderChain.notFirst 4509123803590566038
StarkedAir.HeaderChain.nzE 8777298313016716070
StarkedAir.HeaderChain.ohE 14647393842910814665
StarkedAir.HeaderChain.ohP 16351123973345901159
StarkedAir.HeaderChain.ohS 15327507842441392527
StarkedAir.HeaderChain.ohSum 18143259899380809455
StarkedAir.HeaderChain.ohWeighted 7953362925244352848
StarkedAir.HeaderChain.oneRow 8452536140812483212
StarkedAir.HeaderChain.outHeight 9816877624299826049
StarkedAir.HeaderChain.outNBits 17431127396491412807
StarkedAir.HeaderChain.outPst 14885412151553191668
StarkedAir.HeaderChain.outputs 943565937322263991
StarkedAir.HeaderChain.ownMant 13031545394202503766
StarkedAir.HeaderChain.ownMantE 17982937969595940817
StarkedAir.HeaderChain.ownOhWeighted 3966335064752426723
StarkedAir.HeaderChain.ownTime 15562874314406486202
StarkedAir.HeaderChain.p0Byte 939795529842635434
StarkedAir.HeaderChain.p0Col 9234028091947908164
StarkedAir.HeaderChain.padWord 6094433912547519554
StarkedAir.HeaderChain.pcE 16673355147306965939
StarkedAir.HeaderChain.pcSlots 4170268860157358179
StarkedAir.HeaderChain.periodic256 16853729448712093251
StarkedAir.HeaderChain.plumbing 14164059044672710200
StarkedAir.HeaderChain.powCs 9738010087423538289
StarkedAir.HeaderChain.preCols 3325405409371164083
StarkedAir.HeaderChain.prefixE 15102700723232139188
StarkedAir.HeaderChain.prevExp 7576690768198245734
StarkedAir.HeaderChain.prevMant 2492842341609769887
StarkedAir.HeaderChain.prodCol 7539335182674860941
StarkedAir.HeaderChain.pstCarry 3908286958249595322
StarkedAir.HeaderChain.pstFirst 10490656906110712114
StarkedAir.HeaderChain.pstReset 5320852106974134565
StarkedAir.HeaderChain.pubState 9905730181127918845
StarkedAir.HeaderChain.pubWindow 6020767201776733723
StarkedAir.HeaderChain.pubWord 10215680606308399041
StarkedAir.HeaderChain.pubWork 633232560383393307
StarkedAir.HeaderChain.qAt 601826647370068485
StarkedAir.HeaderChain.qB 1166011532164892221
StarkedAir.HeaderChain.qE 6465380814454220022
StarkedAir.HeaderChain.qL 16668295082617708069
StarkedAir.HeaderChain.qSlots 4807500441320456984
StarkedAir.HeaderChain.rB 14642256938873028072
StarkedAir.HeaderChain.rSlots 1633096838479252867
StarkedAir.HeaderChain.remCol 1026101694030393980
StarkedAir.HeaderChain.remCompE 5326383590545518574
StarkedAir.HeaderChain.remE 8238337364068584619
StarkedAir.HeaderChain.remM1E 14511903996539756459
StarkedAir.HeaderChain.retargetCs 5563225904695143884
StarkedAir.HeaderChain.rhoB 3975683938029198960
StarkedAir.HeaderChain.rhoByte 399460291275947465
StarkedAir.HeaderChain.rhoSlots 9172597676909731186
StarkedAir.HeaderChain.rsCol 11338083432112171079
StarkedAir.HeaderChain.rtBase 374604869222770112
StarkedAir.HeaderChain.rtE 12634280999827829143
StarkedAir.HeaderChain.rtSel 8619081091144111444
StarkedAir.HeaderChain.sMin 13777812732257816549
StarkedAir.HeaderChain.scE 1638834584293677208
StarkedAir.HeaderChain.selectE 14822014721260086073
StarkedAir.HeaderChain.shaSel 7647897455486709254
StarkedAir.HeaderChain.sigB 14564510862287047576
StarkedAir.HeaderChain.sigByte 1493745291816179408
StarkedAir.HeaderChain.sigSlots 16838488416147734562
StarkedAir.HeaderChain.slotSel 224820158861254792
StarkedAir.HeaderChain.spanByte 7090912067572226885
StarkedAir.HeaderChain.spanE 2732372924201698425
StarkedAir.HeaderChain.spanHi 4703582141949359313
StarkedAir.HeaderChain.spanLo 14989218931779596123
StarkedAir.HeaderChain.stateBase 10301370996776083359
StarkedAir.HeaderChain.stateCs 13228916422863355749
StarkedAir.HeaderChain.stateFam 17144503240498949951
StarkedAir.HeaderChain.stateSel 12168455595389990711
StarkedAir.HeaderChain.suffixE 16456687524057801987
StarkedAir.HeaderChain.sumCol 10346191457176516383
StarkedAir.HeaderChain.sumE 17261073220073438166
StarkedAir.HeaderChain.tauByte 7389276886897787849
StarkedAir.HeaderChain.timeLimb 8988304375296660568
StarkedAir.HeaderChain.verC 1569600996120868634
StarkedAir.HeaderChain.verD 4012184634381427147
StarkedAir.HeaderChain.verE 14021421809643702718
StarkedAir.HeaderChain.verF 16821132709531358465
StarkedAir.HeaderChain.verFlag 12923166004955200797
StarkedAir.HeaderChain.verHeight 17266363063814028871
StarkedAir.HeaderChain.verHi 12876225015656139812
StarkedAir.HeaderChain.verLo 9924485986541802560
StarkedAir.HeaderChain.verMin 13076542941818261129
StarkedAir.HeaderChain.verSel 7012019687039155138
StarkedAir.HeaderChain.verSign 8738522812956327478
StarkedAir.HeaderChain.verT 17187340014212013931
StarkedAir.HeaderChain.versionCs 8457564437612441349
StarkedAir.HeaderChain.wB 18158459492838738020
StarkedAir.HeaderChain.wL 6262288631440932416
StarkedAir.HeaderChain.wSlots 6971444143672406366
StarkedAir.HeaderChain.wcE 3119660799641391650
StarkedAir.HeaderChain.wctl 14575685672044472756
StarkedAir.HeaderChain.window 10390437824688841870
StarkedAir.HeaderChain.windowOut 18292247181134132249
StarkedAir.HeaderChain.workAdd 9761855263144251323
StarkedAir.HeaderChain.workCs 8024142113880833005
StarkedAir.HeaderChain.workFam 14214234989400267723
StarkedAir.HeaderChain.workOff 10519968067724277198
StarkedAir.HeaderChain.workSel 7853301277133936984
StarkedAir.HeaderTree.HMULT 16993442085808736178
StarkedAir.HeaderTree.LVL 10785627192811993227
StarkedAir.HeaderTree.LVLB 2656514626884365964
StarkedAir.HeaderTree.LVL_INV 8390020435547715311
StarkedAir.HeaderTree.Low 3616170921489205324
StarkedAir.HeaderTree.N_MAIN 17955972273041342551
StarkedAir.HeaderTree.NodeOut 6415462674877726922
StarkedAir.HeaderTree.POS 15017452174536805530
StarkedAir.HeaderTree.PubValidT 10368995644358915361
StarkedAir.HeaderTree.REL_NODE 11239342436784068239
StarkedAir.HeaderTree.TMULT 2120695554121013105
StarkedAir.HeaderTree.bOf 7264734933810758034
StarkedAir.HeaderTree.bitsConst 16824188438167282511
StarkedAir.HeaderTree.constIn 7706463302831762560
StarkedAir.HeaderTree.genesisChecks 2655491511713704456
StarkedAir.HeaderTree.h0Nat 9650489794048259978
StarkedAir.HeaderTree.hashLimbs 413146587691331122
StarkedAir.HeaderTree.headers 16916867811456694848
StarkedAir.HeaderTree.levelCs 7230612894701879222
StarkedAir.HeaderTree.limbsOf 2084530650338146052
StarkedAir.HeaderTree.msgLimbs 9567996631326553158
StarkedAir.HeaderTree.outLimbs 10062696445739749644
StarkedAir.HeaderTree.pubT 14264734224977827624
StarkedAir.HeaderTree.relHeight 1536650547384375958
StarkedAir.HeaderTree.sys 9675387801452162188
StarkedAir.HeaderTree.tree 156568386173223244
StarkedAir.HeaderTree.treeConstraints 7363958883327904358
StarkedAir.HeaderTree.treeLookups 11966391967409978299
StarkedAir.HeaderTree.windowIndex 142546850631024727
StarkedAir.Inst 7025466638451465156
StarkedAir.Inst.logSize 8991157092722038686
StarkedAir.Inst.main 16523730767809465881
StarkedAir.Inst.mk 3206954254
StarkedAir.LogUpSZ.Entry 14452012310861970551
StarkedAir.LogUpSZ.PolyBalanced 16169659885551650957
StarkedAir.LogUpSZ.Raw 14949551345347162005
StarkedAir.LogUpSZ.StaticOk 14516097472743826527
StarkedAir.LogUpSZ.collSet 13163959593070603523
StarkedAir.LogUpSZ.fracSum 4576434722453238840
StarkedAir.LogUpSZ.mult 11580441281911957303
StarkedAir.LogUpSZ.polys 3830712794850528456
StarkedAir.LogUpSZ.shapes 16278955831244148761
StarkedAir.LogUpSZ.siteRaw 1243804745517749898
StarkedAir.LogUpSZ.toEntry 11070817434019526550
StarkedAir.LogUpSZ.tuplePoly 5992642180446623655
StarkedAir.Lookup 7803626126871354549
StarkedAir.Lookup.mk 4156052722
StarkedAir.Lookup.mult 7041463134209492021
StarkedAir.Lookup.rel 11188719335142618448
StarkedAir.Lookup.vals 5880368897517555952
StarkedAir.Node 231950750079802956
StarkedAir.Node.add 2621412388
StarkedAir.Node.casesOn 860107716745376140
StarkedAir.Node.col 608194105
StarkedAir.Node.const 246605875
StarkedAir.Node.ctorIdx 5020633993024796376
StarkedAir.Node.mul 2621412388
StarkedAir.Node.neg 246605875
StarkedAir.Node.pub 246605875
StarkedAir.Node.rec 2020798397
StarkedAir.Node.sub 2621412388
StarkedAir.P 16041972504898226365
StarkedAir.PreCol 11442295935212003612
StarkedAir.PreCol.casesOn 15124837736459233963
StarkedAir.PreCol.eval 14459156391039858412
StarkedAir.PreCol.eval.match_1 1060910033389622266
StarkedAir.PreCol.isFirst 1254745529
StarkedAir.PreCol.notLast 1254745529
StarkedAir.PreCol.periodic 4161355810
StarkedAir.PreCol.rec 1499479518
StarkedAir.PreCol.rowGeEnd 3578822226
StarkedAir.PreCol.rowLt 3578822226
StarkedAir.PubEntries 8306077080412797439
StarkedAir.Sha256.A 12621482290909172116
StarkedAir.Sha256.CA_HI 14635086819067720673
StarkedAir.Sha256.CA_LO 9054670203840292923
StarkedAir.Sha256.CE_HI 3683350701089354875
StarkedAir.Sha256.CE_LO 8195331293974438075
StarkedAir.Sha256.CH 1750718438119926672
StarkedAir.Sha256.CW_HI 3908560419702505228
StarkedAir.Sha256.CW_LO 10749535602551813547
StarkedAir.Sha256.E 14140254281272384383
StarkedAir.Sha256.IS_FINAL 11239342436784068239
StarkedAir.Sha256.IS_ROUND 12621482290909172116
StarkedAir.Sha256.IS_SCHED 17101530479978464024
StarkedAir.Sha256.K 10064386731235677263
StarkedAir.Sha256.K_LO 4752661515056156754
StarkedAir.Sha256.MJ 11437002141770042747
StarkedAir.Sha256.N_MAIN 9440403996689931779
StarkedAir.Sha256.PERIOD 1518844136755050564
StarkedAir.Sha256.S0 10795676046289485695
StarkedAir.Sha256.S1 9562720865119475955
StarkedAir.Sha256.W 7081778986160262171
StarkedAir.Sha256.addC 2414061205805544134
StarkedAir.Sha256.bigSigmaBit 8219529129346999975
StarkedAir.Sha256.bit 16015351397544042199
StarkedAir.Sha256.bitsOf 6281966409277294330
StarkedAir.Sha256.bitwise 8656070666238383149
StarkedAir.Sha256.boolC 660787826473308685
StarkedAir.Sha256.booleans 2626303518137298078
StarkedAir.Sha256.chE 3477385481221200837
StarkedAir.Sha256.col 3807634473904907899
StarkedAir.Sha256.constraints 7944731736830857711
StarkedAir.Sha256.cst 5278941036133109659
StarkedAir.Sha256.defineLimbs 18402172018319443821
StarkedAir.Sha256.finalAdds 7563518686606733470
StarkedAir.Sha256.half16 16460371134213216557
StarkedAir.Sha256.half16.match_1 10809900262045307389
StarkedAir.Sha256.limb 13445529349150759381
StarkedAir.Sha256.limbOf 11881063350252816425
StarkedAir.Sha256.majE 11433690644182030264
StarkedAir.Sha256.messageAt 2021809064057880924
StarkedAir.Sha256.outputAt 685655477282819404
StarkedAir.Sha256.pre 899571968731205473
StarkedAir.Sha256.preCols 7198962098991239353
StarkedAir.Sha256.roundAdds 4028226998620025040
StarkedAir.Sha256.s0 5580780264887204875
StarkedAir.Sha256.s1 7248905091690107603
StarkedAir.Sha256.scheduleAdds 9117426749025657825
StarkedAir.Sha256.smallSigmaBit 7893902910943369425
StarkedAir.Sha256.stAt 15541212213389900680
StarkedAir.Sha256.sumPow 18299937407984118295
StarkedAir.Sha256.sumPow._f 14772345721419670349
StarkedAir.Sha256.sumPow.match_1 17830781580792491215
StarkedAir.Sha256.word 8049171349227360006
StarkedAir.Sha256.xor2 15483279024267784122
StarkedAir.Sha256.xor3 13632097124755267244
StarkedAir.Site 1771541150299346305
StarkedAir.Spec.Bitcoin.SegIn 7763272757341114924
StarkedAir.Spec.Bitcoin.SegIn.height 9587466680300723929
StarkedAir.Spec.Bitcoin.SegIn.mk 1152659404
StarkedAir.Spec.Bitcoin.SegIn.prevHash 5185569799388303637
StarkedAir.Spec.Bitcoin.SegIn.prevNBits 10705663347249220690
StarkedAir.Spec.Bitcoin.SegIn.prevPst 3277521104194093491
StarkedAir.Spec.Bitcoin.SegIn.prevTime 7475092868513845658
StarkedAir.Spec.Bitcoin.SegIn.window 11684572407500340357
StarkedAir.Spec.Bitcoin.SegIn.work 2988810364181225620
StarkedAir.Spec.Bitcoin.SegOut 2191247780888238535
StarkedAir.Spec.Bitcoin.SegOut.height 13512153121428379947
StarkedAir.Spec.Bitcoin.SegOut.mk 323098327
StarkedAir.Spec.Bitcoin.SegOut.nBits 6884975968386832673
StarkedAir.Spec.Bitcoin.SegOut.pst 17952214264508491094
StarkedAir.Spec.Bitcoin.SegOut.time 6491827669331187907
StarkedAir.Spec.Bitcoin.SegOut.tip 18058867218971820283
StarkedAir.Spec.Bitcoin.SegOut.window 6354467699873153307
StarkedAir.Spec.Bitcoin.SegOut.work 1528932603087660052
StarkedAir.Spec.Bitcoin.SegmentValid 11395036100457507544
StarkedAir.Spec.Bitcoin.block0 13701244606936639781
StarkedAir.Spec.Bitcoin.block1 5205801141909716366
StarkedAir.Spec.Bitcoin.blockProof 14977088718433034383
StarkedAir.Spec.Bitcoin.blockProof.match_1 4241432415214483146
StarkedAir.Spec.Bitcoin.compactTarget 15669337089988284311
StarkedAir.Spec.Bitcoin.compactValue 15427094226541616736
StarkedAir.Spec.Bitcoin.digestBlock 13963182590972426119
StarkedAir.Spec.Bitcoin.getCompact 14755142728659646895
StarkedAir.Spec.Bitcoin.hashByte 418211963250631551
StarkedAir.Spec.Bitcoin.hashNat 10080341498276608708
StarkedAir.Spec.Bitcoin.medianTimePast 11827271290880686719
StarkedAir.Spec.Bitcoin.mtpOk 7379952796441239840
StarkedAir.Spec.Bitcoin.nBitsOf 3083721522197336310
StarkedAir.Spec.Bitcoin.nextWork 17433356544386581487
StarkedAir.Spec.Bitcoin.powLimit 11425922263640630605
StarkedAir.Spec.Bitcoin.powOk 3206722561502681899
StarkedAir.Spec.Bitcoin.prevHash 15811780676478674933
StarkedAir.Spec.Bitcoin.prevTimes 14054019878953368594
StarkedAir.Spec.Bitcoin.pstOf 13956694953683744543
StarkedAir.Spec.Bitcoin.pstOf._f 8978940440550568527
StarkedAir.Spec.Bitcoin.pstOf.match_1 17830781580792491215
StarkedAir.Spec.Bitcoin.sentinel 6618379776126743265
StarkedAir.Spec.Bitcoin.sha256d 13785171852235319867
StarkedAir.Spec.Bitcoin.stateWord 10829685561984185510
StarkedAir.Spec.Bitcoin.stateWord.match_1 2133660230195602849
StarkedAir.Spec.Bitcoin.targetTimespan 13494239461004615983
StarkedAir.Spec.Bitcoin.timeOf 16227043122203097958
StarkedAir.Spec.Bitcoin.versionInt 17246866424420851397
StarkedAir.Spec.Bitcoin.versionOf 7238408430541584916
StarkedAir.Spec.Bitcoin.versionOk 578271651124274073
StarkedAir.Spec.Blake2s.IV 1413596999589485702
StarkedAir.Spec.Blake2s.IVn 3139897311156775666
StarkedAir.Spec.Blake2s.SIGMA 5375860584763766100
StarkedAir.Spec.Blake2s.Word 10648194333372659550
StarkedAir.Spec.Blake2s.compress 13199894164096123740
StarkedAir.Spec.Blake2s.gIdx 10466722882121797774
StarkedAir.Spec.Blake2s.gIdx.match_1 2133660230195602849
StarkedAir.Spec.Blake2s.gStep 4349550160195733965
StarkedAir.Spec.Blake2s.gStep.match_1 15007910408180600292
StarkedAir.Spec.Blake2s.gStep.match_3 5966486410946897557
StarkedAir.Spec.Blake2s.h0 14296180187461398653
StarkedAir.Spec.Blake2s.hashBlocks 18101667264012246283
StarkedAir.Spec.Blake2s.hashBlocks._sparseCasesOn_1 8053240399280998920
StarkedAir.Spec.Blake2s.hashBlocks._unary 15602407407999534695
StarkedAir.Spec.Blake2s.hashBlocks.match_1 3053927846933542526
StarkedAir.Spec.Blake2s.initV 6496089739398119043
StarkedAir.Spec.Blake2s.leWord 12602025423843975422
StarkedAir.Spec.Blake2s.mix 220855499362022128
StarkedAir.Spec.Blake2s.sigma 4638162625857485937
StarkedAir.Spec.Blake2s.steps 9134756126496715338
StarkedAir.Spec.Blake2s.steps._f 10835645767857014805
StarkedAir.Spec.Blake2s.steps.match_1 17830781580792491215
StarkedAir.Spec.Block.BIP34_HEIGHT 4028863373844725641
StarkedAir.Spec.Block.Blk 12858256961024494880
StarkedAir.Spec.Block.Blk.header 17805235892981134901
StarkedAir.Spec.Block.Blk.mk 2079361985
StarkedAir.Spec.Block.Blk.time 5994097009086317760
StarkedAir.Spec.Block.Blk.txs 8788057254449958637
StarkedAir.Spec.Block.Bytes 11075956118847885829
StarkedAir.Spec.Block.CSV_HEIGHT 16719004532436727807
StarkedAir.Spec.Block.Ctx 17412155797014888286
StarkedAir.Spec.Block.Ctx.height 13411501623825391312
StarkedAir.Spec.Block.Ctx.mk 2427923131
StarkedAir.Spec.Block.Ctx.prevMtp 8066535049812394561
StarkedAir.Spec.Block.InTok 14239751044440772731
StarkedAir.Spec.Block.InTok._sparseCasesOn_1 18014883322842696046
StarkedAir.Spec.Block.InTok.match_1 2136604979474395654
StarkedAir.Spec.Block.IoTx 8322390500240075964
StarkedAir.Spec.Block.MAX_BLOCK_SIGOPS_COST 16027835322841022662
StarkedAir.Spec.Block.MAX_BLOCK_WEIGHT 10673846267733248525
StarkedAir.Spec.Block.MAX_MONEY 9182304222035658935
StarkedAir.Spec.Block.MAX_SIZE 17601196584736204622
StarkedAir.Spec.Block.OutPoint 16695991636995116324
StarkedAir.Spec.Block.OutPoint.casesOn 14950177952662121574
StarkedAir.Spec.Block.OutPoint.hash 7297630275844906741
StarkedAir.Spec.Block.OutPoint.isNull 1652520506959091380
StarkedAir.Spec.Block.OutPoint.mk 4148989647
StarkedAir.Spec.Block.OutPoint.n 3148950032910307532
StarkedAir.Spec.Block.OutPoint.rec 3801693791
StarkedAir.Spec.Block.OutTok 5274417410404823361
StarkedAir.Spec.Block.OutTok._sparseCasesOn_1 5812410066980625719
StarkedAir.Spec.Block.OutTok.match_1 1645490313234059227
StarkedAir.Spec.Block.Parser 6746877443796157884
StarkedAir.Spec.Block.SEGWIT_HEIGHT 8728409502814171483
StarkedAir.Spec.Block.Tok 8457977130312311932
StarkedAir.Spec.Block.Tok.blk 3495367860
StarkedAir.Spec.Block.Tok.bytes 7612969834334289235
StarkedAir.Spec.Block.Tok.bytes.match_1 6088674065726577083
StarkedAir.Spec.Block.Tok.casesOn 13018049596740347301
StarkedAir.Spec.Block.Tok.ctorIdx 3305854802195169394
StarkedAir.Spec.Block.Tok.inp 166844674
StarkedAir.Spec.Block.Tok.isIo 8095607700187652720
StarkedAir.Spec.Block.Tok.isIo._sparseCasesOn_1 12881375818955976714
StarkedAir.Spec.Block.Tok.isIo.match_1 9461808684765269517
StarkedAir.Spec.Block.Tok.isLock 5687648839375947542
StarkedAir.Spec.Block.Tok.isLock._sparseCasesOn_1 8175470807216815183
StarkedAir.Spec.Block.Tok.isLock.match_1 11034949434386291736
StarkedAir.Spec.Block.Tok.lock 829666695
StarkedAir.Spec.Block.Tok.nout 2040566526
StarkedAir.Spec.Block.Tok.out 989865985
StarkedAir.Spec.Block.Tok.rec 1328937050
StarkedAir.Spec.Block.Tok.txh 3201144043
StarkedAir.Spec.Block.Tok.wcnt 2040566526
StarkedAir.Spec.Block.Tok.witem 829666695
StarkedAir.Spec.Block.Tx 4339370925971111522
StarkedAir.Spec.Block.Tx.hasWitness 13291097490327931420
StarkedAir.Spec.Block.Tx.isCoinbase 596105010244532746
StarkedAir.Spec.Block.Tx.isCoinbase.match_1 7483647121533381336
StarkedAir.Spec.Block.Tx.lockTime 13500099535187580001
StarkedAir.Spec.Block.Tx.mk 1879632243
StarkedAir.Spec.Block.Tx.version 2724097691566118227
StarkedAir.Spec.Block.Tx.vin 14447410339907522265
StarkedAir.Spec.Block.Tx.vout 11874410405193398038
StarkedAir.Spec.Block.TxIn 18269700046331160455
StarkedAir.Spec.Block.TxIn.mk 2390822353
StarkedAir.Spec.Block.TxIn.prevout 15371725574791616530
StarkedAir.Spec.Block.TxIn.scriptSig 16392072436774655371
StarkedAir.Spec.Block.TxIn.sequence 2668975772045951283
StarkedAir.Spec.Block.TxIn.witness 15203619055130795758
StarkedAir.Spec.Block.TxOut 3098813356776983034
StarkedAir.Spec.Block.TxOut.mk 2632025775
StarkedAir.Spec.Block.TxOut.scriptPubKey 2536333561798102307
StarkedAir.Spec.Block.TxOut.value 4498954940064602675
StarkedAir.Spec.Block.beBytes 16992283686157585825
StarkedAir.Spec.Block.byte 3636446209278313147
StarkedAir.Spec.Block.checkBlock 2252381177902748400
StarkedAir.Spec.Block.checkBlock.match_1 3391665985181815143
StarkedAir.Spec.Block.checkBlockContextual 5309192794802972463
StarkedAir.Spec.Block.checkBlockContextual.match_1 3075246270922173880
StarkedAir.Spec.Block.checkBlockContextual.match_3 16423590567247396340
StarkedAir.Spec.Block.checkBlockCtxFree 6053066597272779199
StarkedAir.Spec.Block.checkBlockCtxFree.match_1 4878531987157868930
StarkedAir.Spec.Block.checkTx 2653192963899672141
StarkedAir.Spec.Block.checkTx.match_1 5687402000427711948
StarkedAir.Spec.Block.chunkWords 15765386581162716621
StarkedAir.Spec.Block.commitmentIndex 14206056427566596883
StarkedAir.Spec.Block.compactSize 15366942956650926507
StarkedAir.Spec.Block.compressAll 10930666801711289112
StarkedAir.Spec.Block.compressAll._unary 7134599208894622502
StarkedAir.Spec.Block.compressAll.match_1 15772991566443888788
StarkedAir.Spec.Block.count 8067391007100629135
StarkedAir.Spec.Block.count._f 13177880889113405306
StarkedAir.Spec.Block.count.match_1 17830781580792491215
StarkedAir.Spec.Block.dupPair 3650691974937233383
StarkedAir.Spec.Block.dupPair._f 11300494326521760357
StarkedAir.Spec.Block.dupPair._sparseCasesOn_1 16926720736584672822
StarkedAir.Spec.Block.dupPair.match_1 13254959314225676073
StarkedAir.Spec.Block.headerMerkle 4377745974086907751
StarkedAir.Spec.Block.insT 1414941550242810734
StarkedAir.Spec.Block.insT._f 13595365800863284276
StarkedAir.Spec.Block.insT._sparseCasesOn_1 16926720736584672822
StarkedAir.Spec.Block.insT._sparseCasesOn_2 18014883322842696046
StarkedAir.Spec.Block.insT.match_1 16356338623466030258
StarkedAir.Spec.Block.instDecidableEqOutPoint 2925425969080261431
StarkedAir.Spec.Block.instDecidableEqOutPoint.decEq 10370019363495218998
StarkedAir.Spec.Block.instDecidableEqOutPoint.decEq.match_1 10047479604205956389
StarkedAir.Spec.Block.isFinal 8302074319518120553
StarkedAir.Spec.Block.itemsT 7390111375068911753
StarkedAir.Spec.Block.itemsT._f 8006606738655742169
StarkedAir.Spec.Block.itemsT._sparseCasesOn_1 15811253998808482325
StarkedAir.Spec.Block.itemsT.match_1 2257987947137968285
StarkedAir.Spec.Block.le 16657223789361146471
StarkedAir.Spec.Block.leBytes 15550488722306033649
StarkedAir.Spec.Block.legacySigOps 5649182481167593071
StarkedAir.Spec.Block.level 15114535155709993445
StarkedAir.Spec.Block.level._f 5761007178400096127
StarkedAir.Spec.Block.level.match_1 9585274522691694140
StarkedAir.Spec.Block.merkleRoot 14119840990440507902
StarkedAir.Spec.Block.merkleRoot.match_1 628586799557272793
StarkedAir.Spec.Block.nodupBy 53166391871310354
StarkedAir.Spec.Block.nodupBy._f 2991912486047397936
StarkedAir.Spec.Block.nodupBy.match_1 13495824627730616609
StarkedAir.Spec.Block.ops 12130293492398098162
StarkedAir.Spec.Block.ops.match_1 11219528800764264065
StarkedAir.Spec.Block.outsT 10336163081766682178
StarkedAir.Spec.Block.outsT._f 9023884717959982039
StarkedAir.Spec.Block.outsT._sparseCasesOn_1 5812410066980625719
StarkedAir.Spec.Block.outsT.match_1 957228908099219804
StarkedAir.Spec.Block.pad 14851738128251295108
StarkedAir.Spec.Block.parseBlock 16046485837610095561
StarkedAir.Spec.Block.parseBlock._sparseCasesOn_1 5523436881708479340
StarkedAir.Spec.Block.parseBlock._sparseCasesOn_2 8053240399280998920
StarkedAir.Spec.Block.parseBlock.match_1 733360101298454056
StarkedAir.Spec.Block.pushHeight 12978985294042408887
StarkedAir.Spec.Block.scriptNum 7305606228002068706
StarkedAir.Spec.Block.serCompact 185539540605731228
StarkedAir.Spec.Block.serNoWit 18008642955385257480
StarkedAir.Spec.Block.serTxIn 13846404322909513382
StarkedAir.Spec.Block.serTxOut 14767426044285477416
StarkedAir.Spec.Block.serVarBytes 13748956056943977685
StarkedAir.Spec.Block.serWit 1201962898648998148
StarkedAir.Spec.Block.sha256 14128985733959644043
StarkedAir.Spec.Block.sha256d 17188582396832159941
StarkedAir.Spec.Block.sigOps 11106374552073849058
StarkedAir.Spec.Block.signed64 5496491835524159879
StarkedAir.Spec.Block.stateBytes 17394717461031306420
StarkedAir.Spec.Block.strippedSize 8156265802872089563
StarkedAir.Spec.Block.tagParts 18023004369588617022
StarkedAir.Spec.Block.tagParts._f 16745051619534747610
StarkedAir.Spec.Block.tagParts.match_1 18261002440992408554
StarkedAir.Spec.Block.tagged 8242432376530277884
StarkedAir.Spec.Block.tagged._f 17495846887891122019
StarkedAir.Spec.Block.tagged.match_1 15194411249220752823
StarkedAir.Spec.Block.take 6132786565631432833
StarkedAir.Spec.Block.toksBlock 15365563412359561460
StarkedAir.Spec.Block.toksBlock._sparseCasesOn_1 8053240399280998920
StarkedAir.Spec.Block.toksBlock._sparseCasesOn_4 12512813252314628533
StarkedAir.Spec.Block.toksBlock.match_1 16924519757760589994
StarkedAir.Spec.Block.toksBlock.match_4 4567140114113741940
StarkedAir.Spec.Block.totalSize 2546169632728569724
StarkedAir.Spec.Block.tx 13464791669445174505
StarkedAir.Spec.Block.tx.match_1 2942036506594848001
StarkedAir.Spec.Block.tx.match_3 11474243804384304947
StarkedAir.Spec.Block.txIn 17460781482789890128
StarkedAir.Spec.Block.txOut 14997199994532028469
StarkedAir.Spec.Block.txT 10237407472332016254
StarkedAir.Spec.Block.txT._sparseCasesOn_1 5523436881708479340
StarkedAir.Spec.Block.txT._sparseCasesOn_10 5826685134274284422
StarkedAir.Spec.Block.txT._sparseCasesOn_2 8175470807216815183
StarkedAir.Spec.Block.txT._sparseCasesOn_7 14758344913650825667
StarkedAir.Spec.Block.txT.match_1 13297261692373910816
StarkedAir.Spec.Block.txT.match_10 10149014858530757785
StarkedAir.Spec.Block.txT.match_5 3540525245216760869
StarkedAir.Spec.Block.txT.match_7 14622587556070089103
StarkedAir.Spec.Block.txid 13096024885263207779
StarkedAir.Spec.Block.txsT 12122830847165400615
StarkedAir.Spec.Block.txsT._f 5518261584833314362
StarkedAir.Spec.Block.txsT.match_1 11300527159429510561
StarkedAir.Spec.Block.txsT.match_3 16522298213779230085
StarkedAir.Spec.Block.u32 5288198419392834023
StarkedAir.Spec.Block.varBytes 14711293895358592812
StarkedAir.Spec.Block.vec 8791213442885473116
StarkedAir.Spec.Block.weight 3826599561524896940
StarkedAir.Spec.Block.witsT 8895864523761011751
StarkedAir.Spec.Block.witsT._f 13027001460567558919
StarkedAir.Spec.Block.witsT._sparseCasesOn_3 9563657014395001693
StarkedAir.Spec.Block.witsT.match_1 11550372025146627108
StarkedAir.Spec.Block.witsT.match_3 13199725484731363174
StarkedAir.Spec.Block.wtxid 3921214279696907971
StarkedAir.Spec.CoinEpoch.BlockC 14456338635063368187
StarkedAir.Spec.CoinEpoch.BlockC.claim 8712803750282361312
StarkedAir.Spec.CoinEpoch.BlockC.h 16121615897971219088
StarkedAir.Spec.CoinEpoch.BlockC.lost 17423502278169921658
StarkedAir.Spec.CoinEpoch.BlockC.mk 514753636
StarkedAir.Spec.CoinEpoch.BlockC.txs 15214066778408889559
StarkedAir.Spec.CoinEpoch.CEv 12601228195261765465
StarkedAir.Spec.CoinEpoch.Claim 10709958432023055810
StarkedAir.Spec.CoinEpoch.Claim.code 13943299332030891543
StarkedAir.Spec.CoinEpoch.Claim.ctx 3906829304436646342
StarkedAir.Spec.CoinEpoch.Claim.mk 2219967719
StarkedAir.Spec.CoinEpoch.Claim.ser 16411239572079229379
StarkedAir.Spec.CoinEpoch.Val 11336213409295540382
StarkedAir.Spec.CoinEpoch.allTxC 11255003056290846752
StarkedAir.Spec.CoinEpoch.allTxs 16504709450879607639
StarkedAir.Spec.CoinEpoch.blockTxC 14052776608636638335
StarkedAir.Spec.CoinEpoch.blockTxs 7677209196994226452
StarkedAir.Spec.CoinEpoch.codeOf 15444137173859708007
StarkedAir.Spec.CoinEpoch.coinOfVal 1554094844980709378
StarkedAir.Spec.CoinEpoch.compactLen 5283425639208309142
StarkedAir.Spec.CoinEpoch.decSer 2392128966968142838
StarkedAir.Spec.CoinEpoch.live 8518839352653915113
StarkedAir.Spec.CoinEpoch.txIns 14552301860936822765
StarkedAir.Spec.CoinEpoch.txOuts 3806217855556997208
StarkedAir.Spec.CoinEpoch.txcOf 15880558919097651423
StarkedAir.Spec.Coins.COINBASE_MATURITY 1750718438119926672
StarkedAir.Spec.Coins.CView 14422048259023082422
StarkedAir.Spec.Coins.ClaimsOK 16732427554837290106
StarkedAir.Spec.Coins.Coin 7156352327546606248
StarkedAir.Spec.Coins.Coin.coinbase 5916379653909229915
StarkedAir.Spec.Coins.Coin.height 3748438261142021104
StarkedAir.Spec.Coins.Coin.mk 1777266618
StarkedAir.Spec.Coins.Coin.value 7171932944387629054
StarkedAir.Spec.Coins.TxC 10126606798078285838
StarkedAir.Spec.Coins.TxC.cb 8497853924145511399
StarkedAir.Spec.Coins.TxC.claims 10765176900838949209
StarkedAir.Spec.Coins.TxC.h 14726940140714006743
StarkedAir.Spec.Coins.TxC.mk 3393415750
StarkedAir.Spec.Coins.TxC.t 1717098450226929552
StarkedAir.Spec.Coins.TxC.txid 17640238200865195117
StarkedAir.Spec.Coins.addOuts 397662313391895274
StarkedAir.Spec.Coins.addOuts._f 12724297050595848071
StarkedAir.Spec.Coins.addOuts.match_1 5190607678362542548
StarkedAir.Spec.Coins.addOuts.match_3 6940706098995469666
StarkedAir.Spec.Coins.bip30Lost 7662387039758480625
StarkedAir.Spec.Coins.claimFee 13071565905828190405
StarkedAir.Spec.Coins.claimSum 5416718636313328126
StarkedAir.Spec.Coins.connectTx 17040519962116673824
StarkedAir.Spec.Coins.connectTx.match_1 7673108004254053716
StarkedAir.Spec.Coins.connectTxs 5451313167917853579
StarkedAir.Spec.Coins.connectTxs._f 15106546906734848671
StarkedAir.Spec.Coins.connectTxs.match_1 2949775015195812958
StarkedAir.Spec.Coins.created 4407510166700938399
StarkedAir.Spec.Coins.outSum 15189811172226599551
StarkedAir.Spec.Coins.spendIns 2986470802767758179
StarkedAir.Spec.Coins.spendIns._f 3043761895717897579
StarkedAir.Spec.Coins.spendIns.match_1 1971004212473733251
StarkedAir.Spec.Coins.spendIns.match_3 7834745008115653825
StarkedAir.Spec.Coins.unspendable 8559637584558408234
StarkedAir.Spec.Coins.untag 9378541947879382602
StarkedAir.Spec.HeaderTree.HTree 14771354198060332148
StarkedAir.Spec.HeaderTree.HTree.below 7110979675153679776
StarkedAir.Spec.HeaderTree.HTree.brecOn 10273478727793368864
StarkedAir.Spec.HeaderTree.HTree.brecOn.go 10718432997074503223
StarkedAir.Spec.HeaderTree.HTree.casesOn 11014854109792241969
StarkedAir.Spec.HeaderTree.HTree.leaf 2748336908
StarkedAir.Spec.HeaderTree.HTree.leaves 16992840211515136989
StarkedAir.Spec.HeaderTree.HTree.leaves._f 16690654733087131092
StarkedAir.Spec.HeaderTree.HTree.node 3035807650
StarkedAir.Spec.HeaderTree.HTree.rec 2481286706
StarkedAir.Spec.HeaderTree.HTree.root 14098536217465640789
StarkedAir.Spec.HeaderTree.HTree.root._f 2292176852463591289
StarkedAir.Spec.HeaderTree.HTree.root.match_1 1469840580791760063
StarkedAir.Spec.HeaderTree.hnode 5853460773206180856
StarkedAir.Spec.HeaderTree.stWord 14851753154612864056
StarkedAir.Spec.HeaderTree.stWord.match_1 2133660230195602849
StarkedAir.Spec.HeaderTree.toState 18029530402525860783
StarkedAir.Spec.QM31.CM 13252297115704957012
StarkedAir.Spec.QM31.I 15690974894986962285
StarkedAir.Spec.QM31.QM 4208162275715624580
StarkedAir.Spec.QM31.coordsOf 9568856547561516307
StarkedAir.Spec.QM31.emb 970624176615802932
StarkedAir.Spec.QM31.fI 2403214826391021183
StarkedAir.Spec.QM31.fU 14203396311039935503
StarkedAir.Spec.QM31.i 17035549701753084122
StarkedAir.Spec.QM31.instFintypeQM 7060433698901478833
StarkedAir.Spec.QM31.toQ 8388821746784937778
StarkedAir.Spec.QM31.u 7062917002669940034
StarkedAir.Spec.Sha256.IV 1400180686627655505
StarkedAir.Spec.Sha256.K 7291032682076318188
StarkedAir.Spec.Sha256.Kn 14819145379305535726
StarkedAir.Spec.Sha256.State 6282903239374961537
StarkedAir.Spec.Sha256.State.a 3163229233772035078
StarkedAir.Spec.Sha256.State.b 10331375246438410003
StarkedAir.Spec.Sha256.State.c 17895880819075392724
StarkedAir.Spec.Sha256.State.d 10324320719629292000
StarkedAir.Spec.Sha256.State.e 9933281763331499590
StarkedAir.Spec.Sha256.State.f 11324300602638988447
StarkedAir.Spec.Sha256.State.g 10686737821255018418
StarkedAir.Spec.Sha256.State.h 9453641181093306016
StarkedAir.Spec.Sha256.State.mk 1831067637
StarkedAir.Spec.Sha256.Word 10648194333372659550
StarkedAir.Spec.Sha256.bsig0 10939041957790852501
StarkedAir.Spec.Sha256.bsig1 2219230831934964652
StarkedAir.Spec.Sha256.ch 3602715760989860519
StarkedAir.Spec.Sha256.compress 16516085549668379872
StarkedAir.Spec.Sha256.maj 8927769463797574694
StarkedAir.Spec.Sha256.round 17429591917821477108
StarkedAir.Spec.Sha256.rounds 13537105844037028763
StarkedAir.Spec.Sha256.rounds._f 904963260031830557
StarkedAir.Spec.Sha256.rounds.match_1 17830781580792491215
StarkedAir.Spec.Sha256.schedule 9493337843037899494
StarkedAir.Spec.Sha256.ssig0 8461279034887270671
StarkedAir.Spec.Sha256.ssig1 2353049456256099591
StarkedAir.Spec.Utxo.Ev 16651738516892790360
StarkedAir.Spec.Utxo.Tx 6797351659679035562
StarkedAir.Spec.Utxo.Tx.ins 15267163609350522548
StarkedAir.Spec.Utxo.Tx.mk 1176340074
StarkedAir.Spec.Utxo.Tx.outs 12330176750170673964
StarkedAir.Spec.Utxo.View 16542555032696407970
StarkedAir.Spec.Utxo.addOne 5529310002549983197
StarkedAir.Spec.Utxo.applyTx 745388368205354405
StarkedAir.Spec.Utxo.created 16726504039046370833
StarkedAir.Spec.Utxo.created._f 9326293920985185492
StarkedAir.Spec.Utxo.created.match_1 12480486185582744193
StarkedAir.Spec.Utxo.fpBad 18106957491709168876
StarkedAir.Spec.Utxo.outsT 5327599600220480054
StarkedAir.Spec.Utxo.pnEntries 714844905917197770
StarkedAir.Spec.Utxo.run 1311856778970035425
StarkedAir.Spec.Utxo.run._f 3436052598664544523
StarkedAir.Spec.Utxo.run.match_1 10070618387133504117
StarkedAir.Spec.Utxo.spendOne 15958836841149795116
StarkedAir.Spec.Utxo.spent 9119882327584785275
StarkedAir.Spec.Utxo.spent._f 15527182939189159312
StarkedAir.Spec.Utxo.spent.match_1 15580048896604809727
StarkedAir.Spec.Utxo.viewOf 1718824939477769782
StarkedAir.Spec.Utxo.viewOf._f 8795985778225859914
StarkedAir.Spec.Utxo.viewOf.match_1 10040976094875740950
StarkedAir.Spec.Utxo.vmap 11302559319914543714
StarkedAir.System 16935078989527864878
StarkedAir.System.SatisfiedExt 6997009823320861587
StarkedAir.System.comp 8137230553188452336
StarkedAir.System.m 3625954319589727815
StarkedAir.System.mk 3802942812
StarkedAir.Tree 2248565400533747410
StarkedAir.Tree.casesOn 14108082928061633560
StarkedAir.Tree.ctorIdx 13344182023880769712
StarkedAir.Tree.main 2069074539
StarkedAir.Tree.pre 2069074539
StarkedAir.Tree.rec 4064028213
StarkedAir.bv32 589111361643377795
StarkedAir.emitAll 10107290660711647018
StarkedAir.emitAll._f 12453135257616733122
StarkedAir.emitAll.match_1 9757634921942210006
StarkedAir.emitAll.match_3 8341197746542026325
StarkedAir.emitN 17891149624834436137
StarkedAir.emitN._f 2605405415572564348
StarkedAir.emitN.match_1 4241432415214483146
StarkedAir.emitN.match_3 935223470162759528
StarkedAir.emitN.match_5 7582302400224318503
StarkedAir.extTotal 3858907446131053176
StarkedAir.instDecidableEqExpr 16842971545169032722
StarkedAir.instDecidableEqExpr.decEq 12056342383689691627
StarkedAir.instDecidableEqExpr.decEq._f 9516376337111759100
StarkedAir.instDecidableEqExpr.decEq.match_1 15751551843750552775
StarkedAir.instDecidableEqTree 15288971164680935291
StarkedAir.instHashableExpr 17235765127019277428
StarkedAir.instHashableExpr.hash 6486744785894318297
StarkedAir.instHashableExpr.hash._f 7848679507890345500
StarkedAir.instHashableExpr.hash.match_1 7789081745509938674
StarkedAir.instHashableTree 15676050417566214897
StarkedAir.instHashableTree.hash 10985545621561091513
StarkedAir.instHashableTree.hash.match_1 10773035983448041582
StarkedAir.ofBits 10712527101781703908
StarkedAir.ofBits._f 14419614856268764045
StarkedAir.ofBits.match_1 17830781580792491215
StarkedAir.siteEval 18362962079189701400
StarkedAir.siteLookup 16747963074750976883
StarkedAir.siteMult 11801631043917750612
StarkedAir.siteRel 13007826187122215346
StarkedAir.siteVals 17892783906530037613
StarkedAir.sites 11656917440478074565
StarkedAir.total 12178251136757035804
StarkedAir.wrap 4289096975738175335
"

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut bad : Array String := #[]
  let mut n := 0
  for l in pinTable.splitOn "\n" do
    if l.isEmpty then continue
    let ws := l.splitOn " "
    let some c := Syntax.decodeNameLit ("`" ++ ws[0]!) | throwError "bad pin name {ws[0]!}"
    let h := ws[1]!.toNat!.toUInt64
    n := n + 1
    match pinHash env c with
    | some h' => if h' != h then bad := bad.push s!"{c} changed"
    | none => bad := bad.push s!"{c} missing"
  unless bad.isEmpty do throwError "Compat pins: {bad.size} definitions changed:\n{"\n".intercalate bad.toList}"
  if n != 2218 then throwError "Compat pins: expected 2218 pins, read {n}"

end StarkedAir.Compat
