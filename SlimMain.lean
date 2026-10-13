/-
`relcert-slim`: the certification path of `relcert` (`relcert <input.txt>…`) without the
verdict-replay and handoff modules, which pull in the per-benchmark proof instances.
`runBatchTally` is copied verbatim from `Main.lean`; the certification calls
(`readProblemStrict`, `WellFormed.certifyWF`) are the same functions.
-/
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.Z3
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Trusted.WellFormedCheck

open RelCertifier DL

open RelCertifier.Oracle in
def runBatchTally (paths : List String) (strict : Option Bool := none) :
    IO (Nat × Nat × Nat) := do
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 2
  | .ok cfg =>
    IO.println s!"z3 = {cfg.binary}  (warm persistent session)"
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3 session: {e}"; IO.Process.exit 2
    | .ok s =>
      let mut cert := 0
      let mut decl := 0
      let mut errs := 0
      for path in paths do
        let t0 ← IO.monoMsNow
        let oc ← try
            match ← RelCertifier.Oracle.readProblemStrict path with
            | .error e => pure (Outcome.error s!"parse: {e}")
            | .ok p =>
                match strict with
                | some b => RelCertifier.WellFormed.certifyWFWith b s p
                | none => RelCertifier.WellFormed.certifyWF s p
          catch e => pure (Outcome.error s!"io: {e}")
        let dt := (← IO.monoMsNow) - t0
        let name := (path.splitOn "/").reverse.getD 1 path
        match oc with
        | .certified => cert := cert + 1; IO.println s!"{name}: CERTIFIED ({dt}ms)"
        | .declined  => decl := decl + 1; IO.println s!"{name}: DECLINED ({dt}ms)"
        | .error m   => errs := errs + 1; IO.println s!"{name}: ERROR [{m}] ({dt}ms)"
      s.close
      IO.println s!"errors={errs}"
      pure (cert, decl, errs)

def main (args : List String) : IO Unit := do
  let (_, _, errs) ← runBatchTally args
  if errs > 0 then IO.Process.exit 1
