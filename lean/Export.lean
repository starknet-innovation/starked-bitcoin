import StarkedAir.Export
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
import StarkedAir.Testing.BlockReader
import StarkedAir.Gadgets.RootChecks

/-- `lake env lean --run Export.lean <name>` prints canonical JSON. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["add32_chain"] => IO.println StarkedAir.Add32Chain.air.toJson
  | ["sha256_compress"] => IO.println StarkedAir.Sha256.air.toJson
  | ["header_chain"] => IO.println StarkedAir.HeaderChain.air.toJson
  | ["blake2s_compress"] => IO.println StarkedAir.Blake2s.air.toJson
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
  | ["block_reader"] => IO.println StarkedAir.BlockReader.reader.toJson
  | ["genesis_checks"] => IO.println StarkedAir.HeaderTree.genesisChecksJson
  | ["probe_oracle"] => IO.println (StarkedAir.Probe.oracleJson 4 2024)
  | _ => throw <| IO.userError "usage: export-air add32_chain|probe_oracle"
