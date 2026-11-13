/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The SOS oracle call (TRUSTED harness layer, not verified; `docs/SOS-ORACLE.md`)

The operational side of `sosCheck` / `sos_unsat_sound` (`Trusted/Oracle.lean`). With
`RELCERT_SOS_SECS=S` set, a flow-query level that Z3 answers `unknown` on is written to a file
and given to `scripts/sos_oracle.py QUERY S`: a numerical Putinar certificate (`sos_prove.py`,
cvxpy/Clarabel) followed by the EXACT rational check of that certificate against the printed
query (`sos_check.py`). The oracle's answer is `unsat` only when the script's first line is
`SOS unsat …` (the checker printed VERIFIED); `SOS rejected …` (a certificate was found but did
not check exactly) and `SOS unknown …` (none within the budget) are `unknown`, as is any
spawn / IO failure. With the knob unset nothing here runs and the tool's behaviour is that of
`Z3Session.check` alone.

* `RELCERT_SOS_SECS` — the budget in seconds per call (unset: never called).
* `RELCERT_PYTHON` — the interpreter (default `python3`; cvxpy, clarabel, z3, sympy, numpy,
  scipy must be importable).
* `RELCERT_SOS_SCRIPT` — the driver (default `scripts/sos_oracle.py`, relative to the cwd).
* `RELCERT_SOS_DIR` — where the query files go (default `$TMPDIR` or `/tmp`); with
  `RELCERT_SOS_KEEP=1` they are kept, and with `RELCERT_SOS_CERT_DIR` set the driver keeps the
  certificates (`<query>.cert.json`).
-/
import RelCertifier.Trusted.Z3
import RelCertifier.Trusted.Oracle

namespace RelCertifier

/-- The knob, read once per runner: `RELCERT_SOS_SECS=S` (seconds, a natural number), else
`none`. -/
def sosSecsFromEnv : IO (Option Nat) := do
  pure ((← IO.getEnv "RELCERT_SOS_SECS").bind String.toNat?)

/-- A counter for the query file names. -/
initialize sosQueryCounter : IO.Ref Nat ← IO.mkRef 0

/-- The outcome of one SOS call: the oracle's verdict (`unsat` iff VERIFIED), the script's
status word (`unsat`, `rejected`, `unknown`, `error`) and its statistics line. -/
structure SosOutcome where
  verdict : Z3Verdict
  status : String
  stats : String
  secs : Float

/-- Run the SOS oracle on a printed query (`smt`: the script text as `Z3Session.check` sends it,
without the session's `(reset)`/`(set-option …)`/`(check-sat)` lines). -/
def sosRun (secs : Nat) (smt : String) : IO SosOutcome := do
  let t0 ← IO.monoMsNow
  let py := (← IO.getEnv "RELCERT_PYTHON").getD "python3"
  let script := (← IO.getEnv "RELCERT_SOS_SCRIPT").getD "scripts/sos_oracle.py"
  let dir := (← IO.getEnv "RELCERT_SOS_DIR").getD ((← IO.getEnv "TMPDIR").getD "/tmp")
  let n ← sosQueryCounter.modifyGet (fun k => (k, k + 1))
  let pid ← IO.Process.getPID
  let path : System.FilePath := dir / s!"relcert_sos_{pid}_{n}.smt2"
  let keep := (← IO.getEnv "RELCERT_SOS_KEEP").isSome
  let fail (status : String) (stats : String) : IO SosOutcome := do
    let t1 ← IO.monoMsNow
    pure ⟨.unknown, status, stats, (Float.ofNat (t1 - t0)) / 1000.0⟩
  try
    IO.FS.writeFile path smt
    let out ← IO.Process.output { cmd := py, args := #[script, path.toString, toString secs] }
    if !keep then try IO.FS.removeFile path catch _ => pure ()
    let line := (out.stdout.splitOn "\n").find? (·.startsWith "SOS ") |>.getD ""
    if line.isEmpty then
      let err := (out.stderr.splitOn "\n").filter (· ≠ "") |>.getLast? |>.getD ""
      return ← fail "error" s!"no SOS line (exit {out.exitCode}) {err}"
    let words := line.splitOn " "
    let status := words.getD 1 "error"
    let stats := " ".intercalate (words.drop 2)
    let t1 ← IO.monoMsNow
    let secsF := (Float.ofNat (t1 - t0)) / 1000.0
    if status == "unsat" then pure ⟨.unsat, status, stats, secsF⟩
    else pure ⟨.unknown, status, stats, secsF⟩
  catch e =>
    if !keep then try IO.FS.removeFile path catch _ => pure ()
    fail "error" s!"{e}"

/-- The short size of a stats line for the log: its `cvars=… hyps=… basis0=…` or `vars=… basis=…`
fields when present. -/
def sosSizeOf (stats : String) : String :=
  let ws := stats.splitOn " "
  let pick (k : String) := ws.find? (·.startsWith (k ++ "="))
  " ".intercalate (([pick "cvars", pick "qvars", pick "vars", pick "hyps", pick "basis0", pick "basis",
    pick "deg", pick "maxres", pick "minpivot"].filterMap id).eraseDups)

/-- **Z3, then the SOS oracle on `unknown`** (knob set), with the oracle that answered. The
session's `check` as today when the knob is unset. `ctx` prefixes the SOS log line on stderr:
`{ctx}: sos {status} {size} t={secs}s` (`status` is `unsat` = verified exactly, `rejected`,
`unknown` or `error`). -/
def oracleCheck (s : Z3Session) (sos : Option Nat) (smt : String) (ctx : String) :
    IO (Except String (Z3Verdict × OracleTag)) := do
  match ← s.check smt with
  | .error e => pure (.error e)
  | .ok .unsat => pure (.ok (.unsat, .z3))
  | .ok .sat => pure (.ok (.sat, .z3))
  | .ok .unknown =>
      match sos with
      | none => pure (.ok (.unknown, .z3))
      | some secs =>
          let r ← sosRun secs smt
          -- `unsat`/`unknown`: the size fields; `rejected`/`error`: the checker's reason (truncated)
          let detail := if r.status == "unsat" || r.status == "unknown" then sosSizeOf r.stats
            else (r.stats.take 160).toString
          IO.eprintln s!"{ctx}: sos {r.status} {detail} t={r.secs}s"
          if r.verdict == .unsat then pure (.ok (.unsat, .sos))
          else pure (.ok (.unknown, .z3))

end RelCertifier
