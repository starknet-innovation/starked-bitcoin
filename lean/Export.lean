import StarkedAir.Export
import StarkedAir.Gadgets.Add32Chain
import StarkedAir.Testing.Probe
import StarkedAir.Gadgets.Sha256
import StarkedAir.Gadgets.HeaderChain
import StarkedAir.Gadgets.Version
import StarkedAir.Testing.ByteLookup
import StarkedAir.Gadgets.Blake2s

/-- `lake env lean --run Export.lean <name>` prints canonical JSON. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["add32_chain"] => IO.println StarkedAir.Add32Chain.air.toJson
  | ["sha256_compress"] => IO.println StarkedAir.Sha256.air.toJson
  | ["header_chain"] => IO.println StarkedAir.HeaderChain.air.toJson
  | ["blake2s_compress"] => IO.println StarkedAir.Blake2s.air.toJson
  | ["byte_table"] => IO.println StarkedAir.ByteLookup.table.toJson
  | ["byte_user"] => IO.println StarkedAir.ByteLookup.user.toJson
  | ["probe_oracle"] => IO.println (StarkedAir.Probe.oracleJson 4 2024)
  | _ => throw <| IO.userError "usage: export-air add32_chain|probe_oracle"
