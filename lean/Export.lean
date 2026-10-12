import StarkedAir.Export
import StarkedAir.Circuit.CompositionLogUp
import StarkedAir.Circuit.Balance
import StarkedAir.Circuit.Statement
import StarkedAir.Circuit.LeafHash
import StarkedAir.Circuit.Deep
import StarkedAir.Circuit.Merkle
import StarkedAir.Circuit.Channel
import StarkedAir.Circuit.Transcript
import StarkedAir.Circuit.Pow
import StarkedAir.Circuit.Oods
import StarkedAir.Circuit.BlockLeaf
import StarkedAir.Circuit.BlockNode
import StarkedAir.Circuit.BlockRec
import StarkedAir.Circuit.BlockCtx
import StarkedAir.Block.ExtSum
import StarkedAir.Block.FpWalk
import StarkedAir.Block.URec
import StarkedAir.Block.Coin
import StarkedAir.Gadgets.Add32Chain
import StarkedAir.Testing.Probe
import StarkedAir.Gadgets.Sha256
import StarkedAir.Gadgets.HeaderChain
import StarkedAir.Gadgets.Version
import StarkedAir.Testing.ByteLookup
import StarkedAir.Gadgets.Blake2s
import StarkedAir.Gadgets.HeaderTree
import StarkedAir.Circuit.Gadgets
import StarkedAir.Block.Bytes
import StarkedAir.Block.Fields
import StarkedAir.Block.Msg
import StarkedAir.Block.Sha
import StarkedAir.Block.Merkle
import StarkedAir.Block.WMerkle
import StarkedAir.Block.B2s
import StarkedAir.Testing.BlockReader
import StarkedAir.Gadgets.RootChecks
import StarkedAir.Block.Anc

/-- `lake env lean --run Export.lean <name>` prints canonical JSON. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["add32_chain"] => IO.println StarkedAir.Add32Chain.air.toJson
  | ["sha256_compress"] => IO.println StarkedAir.Sha256.air.toJson
  | ["header_chain"] => IO.println StarkedAir.HeaderChain.air.toJson
  | ["composition_bytesys"] => IO.println (StarkedAir.Circuit.Composition.sysJson
      [StarkedAir.ByteLookup.table, StarkedAir.ByteLookup.user]
      [StarkedAir.Circuit.Composition.compShape StarkedAir.ByteLookup.table 0,
       StarkedAir.Circuit.Composition.compShape StarkedAir.ByteLookup.user 0] 8)
  | ["composition_leaf"] => IO.println (StarkedAir.Circuit.Composition.sysJson
      [StarkedAir.HeaderTree.headers, StarkedAir.HeaderTree.tree]
      [StarkedAir.Circuit.Composition.compShape StarkedAir.HeaderTree.headers 108,
       StarkedAir.Circuit.Composition.compShape StarkedAir.HeaderTree.tree 0] 0)
  | ["deep_leaf"] => IO.println (StarkedAir.Circuit.Deep.deepJson
      [StarkedAir.Circuit.Composition.compShape StarkedAir.HeaderTree.headers 108,
       StarkedAir.Circuit.Composition.compShape StarkedAir.HeaderTree.tree 0])
  | "channel" :: rest => match StarkedAir.Circuit.Channel.channelJson rest with
      | some j => IO.println j
      | none => IO.eprintln "unknown channel op"
  | ["oods_shift_leaf"] => IO.println (StarkedAir.Circuit.Oods.shiftJson (List.range' 8 17)
      (StarkedAir.Circuit.Oods.leafOffsets
        [StarkedAir.Circuit.Composition.compShape StarkedAir.HeaderTree.headers 108,
         StarkedAir.Circuit.Composition.compShape StarkedAir.HeaderTree.tree 0]))
  | ["block_leaf_ctx"] => IO.println StarkedAir.Circuit.BlockCtx.ctxJson
  | ["block_node_glue"] => IO.println StarkedAir.Circuit.BlockNode.nodeJson
  | ["block_leaf_out"] => IO.println StarkedAir.Circuit.BlockRec.leafOutJson
  | ["seed_leaf"] => IO.println StarkedAir.Circuit.BlockLeaf.seedLeafJson
  | ["block_leaf_checks"] => IO.println StarkedAir.Circuit.BlockLeaf.checksJson
  | ["pow_check", k] => IO.println (StarkedAir.Circuit.Pow.powJson k.toNat!)
  | ["transcript", "lookups"] => IO.println (StarkedAir.Circuit.Transcript.json true)
  | ["transcript", "plain"] => IO.println (StarkedAir.Circuit.Transcript.json false)
  | ["merkle_node"] => IO.println StarkedAir.Circuit.Merkle.nodeJson
  | ["leafhash", k] => IO.println (StarkedAir.Circuit.leafHashJson k.toNat!)
  | ["statement_leaf"] => IO.println (StarkedAir.Circuit.Statement.stmtJson true [108, 0])
  | ["balance_leaf"] => IO.println (StarkedAir.Circuit.Composition.balanceJson 2 [(2, 18, 2 ^ 31 - 2)])
  | ["composition_header_chain"] => IO.println (StarkedAir.Circuit.Composition.programJson StarkedAir.HeaderChain.air
      { nPre := StarkedAir.HeaderChain.air.pre.length, nMain := StarkedAir.HeaderChain.air.nMain,
        offs := StarkedAir.Circuit.Composition.mainOffsets StarkedAir.HeaderChain.air.toDag.1, nPub := 108 })
  | ["blake2s_compress"] => IO.println StarkedAir.Blake2s.air.toJson
  | ["extsum_test"] => IO.println StarkedAir.Block.ExtSum.air.toJson
  | ["block_fpwalk"] => IO.println StarkedAir.Block.FpWalk.fpwalk.toJson
  | ["block_urec"] => IO.println StarkedAir.Block.URec.urec.toJson
  | ["block_coin"] => IO.println StarkedAir.Block.Coin.coin.toJson
  | ["blake2s_tree"] => IO.println StarkedAir.HeaderTree.tree.toJson
  | ["header_chain_v7"] => IO.println StarkedAir.HeaderTree.headers.toJson
  | ["byte_table"] => IO.println StarkedAir.ByteLookup.table.toJson
  | ["byte_user"] => IO.println StarkedAir.ByteLookup.user.toJson
  | ["node_glue"] => IO.println StarkedAir.Circuit.nodeProgram.toJson
  | ["leaf_glue"] => IO.println StarkedAir.Circuit.leafProgram.toJson
  | ["block_bytes"] => IO.println StarkedAir.Block.bytes.toJson
  | ["block_fields"] => IO.println StarkedAir.Block.Fields.fields.toJson
  | ["block_msg"] => IO.println StarkedAir.Block.Msg.msg.toJson
  | ["block_sha"] => IO.println StarkedAir.Block.Sha.sha.toJson
  | ["block_merkle"] => IO.println StarkedAir.Block.Merkle.merkle.toJson
  | ["block_tables"] => IO.println StarkedAir.Block.Tables.tables.toJson
  | ["block_walk"] => IO.println StarkedAir.Block.Walk.walk.toJson
  | ["block_ctx"] => IO.println StarkedAir.Block.Ctx.ctx.toJson
  | ["block_wmerkle"] => IO.println StarkedAir.Block.WMerkle.wmerkle.toJson
  | ["block_undo"] => IO.println StarkedAir.Block.Undo.undo.toJson
  | ["block_anc"] => IO.println StarkedAir.Block.Anc.anc.air.toJson
  | ["block_b2msg"] => IO.println StarkedAir.Block.B2Msg.b2msg.toJson
  | ["block_b2s"] => IO.println StarkedAir.Block.B2s.b2s.toJson
  | ["block_reader"] => IO.println StarkedAir.BlockReader.reader.toJson
  | ["genesis_checks"] => IO.println StarkedAir.HeaderTree.genesisChecksJson
  | ["probe_oracle"] => IO.println (StarkedAir.Probe.oracleJson 4 2024)
  | _ => throw <| IO.userError "usage: export-air add32_chain|probe_oracle"
