import StarkedAir.Export
import StarkedAir.Gadgets.Add32Chain
import StarkedAir.Testing.Probe

/-- `lake env lean --run Export.lean <name>` prints canonical JSON. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["add32_chain"] => IO.println StarkedAir.Add32Chain.air.toJson
  | ["probe_oracle"] => IO.println (StarkedAir.Probe.oracleJson 4 2024)
  | _ => throw <| IO.userError "usage: export-air add32_chain|probe_oracle"
