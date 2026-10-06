import StarkedAir.Export
import StarkedAir.Gadgets.Add32Chain

/-- `lake exe export-air <name>` prints the AIR's canonical JSON. -/
def main (args : List String) : IO Unit := do
  match args with
  | ["add32_chain"] => IO.println StarkedAir.Add32Chain.air.toJson
  | _ => throw <| IO.userError "usage: export-air add32_chain"
