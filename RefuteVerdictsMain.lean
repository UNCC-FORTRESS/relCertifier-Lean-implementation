import RelCertifier.VerdictsV2.RunRefute

/-- Discharge the refutations' query groups with Z3; exit 0 only if every group is `unsat` and
the declared total is met. -/
def main : IO UInt32 := do
  match ← RelCertifier.Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"; pure 2
  | .ok cfg =>
      IO.println s!"z3 = {cfg.binary}"
      if ← RelCertifier.VerdictsV2.runRefuteV2 cfg then pure 0 else pure 1
