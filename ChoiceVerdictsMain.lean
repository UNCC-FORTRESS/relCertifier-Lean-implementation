import RelCertifier.InstancesV2.Choice.Verdicts

/-- Discharge the choice exhibits' verdict packs with Z3; exit 0 only if every component is
`unsat` and the declared total is met. -/
def main : IO UInt32 := do
  match ← RelCertifier.Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"; pure 2
  | .ok cfg =>
      IO.println s!"z3 = {cfg.binary}"
      if ← RelCertifier.ChoiceVerdicts.runChoice cfg then pure 0 else pure 1
