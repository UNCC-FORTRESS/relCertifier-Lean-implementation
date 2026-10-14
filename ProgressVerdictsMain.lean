import RelCertifier.VerdictsV2.RunProgress

/-- Discharge the suite's progress certificates with Z3; exit 0 only if every query is `unsat`
and the declared total is met. -/
def main : IO UInt32 := do
  match ← RelCertifier.Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"; pure 2
  | .ok cfg =>
      IO.println s!"z3 = {cfg.binary}"
      if ← RelCertifier.VerdictsV2.runProgressV2 cfg then pure 0 else pure 1
