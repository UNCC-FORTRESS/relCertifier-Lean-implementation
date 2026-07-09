/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Hermetic, persistent Z3 session (TRUSTED harness layer, not verified)

The oracle's determinism and honesty depend on this layer:
* **Pinned binary** — the Z3 path is resolved once (env `RELCERT_Z3` or a fixed list of
  absolute paths), NEVER PATH-resolved at spawn. A missing/mis-pathed Z3 is a distinct
  `error`, never a silent "not certified".
* **Persistent process** — one `z3 -in` process serves many queries (warm), so the
  per-query cost is the solve, not a process spawn + SMT round-trip.
* **Three-valued, error-distinct verdict** — `unsat` / `sat` / `unknown`, or an
  `Except.error` for any spawn / IO / EOF / malformed-output failure. The caller must
  keep `error` separate from a sound `sat` (declined).
* **Deterministic** — `(reset)` before every query (no state carryover) and an explicit
  per-query `:timeout`, so the same query yields the same verdict independent of PATH,
  interactive shell, or prior queries.
-/

namespace RelCertifier

/-- Solver configuration: the pinned absolute binary path and per-query timeout (ms). -/
structure Z3Config where
  binary    : String
  timeoutMs : Nat := 10000
  /-- Deterministic solver work-unit bound (machine-independent, unlike a wall timeout):
  a hard NRA query hits it and returns `unknown` at the SAME point on every machine, so
  the verdict is reproducible. This is what actually bounds pathological queries `z3`'s
  `:timeout` may ignore in preprocessing. `0` disables it. -/
  rlimit    : Nat := 8000000
  deriving Repr

/-- Three-valued solver verdict. `error` is carried by `Except`, never conflated here. -/
inductive Z3Verdict | unsat | sat | unknown
  deriving DecidableEq, Repr

/-- Discover a pinned Z3 binary: `RELCERT_Z3` if set and existing, else the first
existing standard path. Resolved once; the result is an absolute path used verbatim at
spawn (not re-resolved through PATH). -/
def Z3Config.discover : IO (Except String Z3Config) := do
  -- optional deterministic per-query timeout override (ms)
  let t := (← IO.getEnv "RELCERT_Z3_TIMEOUT").bind String.toNat? |>.getD 10000
  let rl := (← IO.getEnv "RELCERT_Z3_RLIMIT").bind String.toNat? |>.getD 8000000
  match ← IO.getEnv "RELCERT_Z3" with
  | some p =>
      if ← System.FilePath.pathExists p then return .ok { binary := p, timeoutMs := t, rlimit := rl }
      else return .error s!"RELCERT_Z3 set but not found: {p}"
  | none =>
      for p in ["/opt/homebrew/bin/z3", "/usr/local/bin/z3", "/usr/bin/z3"] do
        if ← System.FilePath.pathExists p then return .ok { binary := p, timeoutMs := t, rlimit := rl }
      return .error "z3 not found (set RELCERT_Z3 to an absolute path)"

/-- A live persistent solver process. -/
structure Z3Session where
  child : IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .piped }
  cfg   : Z3Config

/-- Start a persistent `z3 -in`. A non-existent binary is a distinct `error` (checked
before spawn, so it can never surface as a solver verdict). -/
def Z3Session.start (cfg : Z3Config) : IO (Except String Z3Session) := do
  if !(← System.FilePath.pathExists cfg.binary) then
    return .error s!"z3 binary not found: {cfg.binary}"
  try
    let child ← IO.Process.spawn
      { cmd := cfg.binary, args := #["-in"],
        stdin := .piped, stdout := .piped, stderr := .piped }
    return .ok { child := child, cfg := cfg }
  catch e => return .error s!"z3 spawn failed: {e}"

/-- The per-query sentinel echoed after `(check-sat)`; reading up to it drains exactly
one query's output, keeping the persistent pipe in sync (the key to determinism). -/
private def sentinel : String := "<<RCEND>>"

/-- Read up to the sentinel, capturing the verdict and flagging any `(error …)`.
Returns `(verdict?, sawError, sawEnd)`; `sawEnd=false` with `verdict?=none` ⟹ EOF/crash. -/
private partial def drainToSentinel (h : IO.FS.Handle) (fuel : Nat)
    (v? : Option String) (sawErr : Bool) : IO (Option String × Bool × Bool) := do
  if fuel == 0 then return (v?, sawErr, false)
  let line ← h.getLine
  if line.isEmpty then return (v?, sawErr, false)      -- EOF (crash)
  let t := (line.trim).replace "\"" ""
  if t == sentinel then return (v?, sawErr, true)
  else if t == "unsat" || t == "sat" || t == "unknown" then
    drainToSentinel h (fuel - 1) (some t) sawErr
  else
    drainToSentinel h (fuel - 1) v? (sawErr || t.startsWith "(error")

/-- Run one self-contained query. `(reset)` clears prior state; the pinned `:timeout`
bounds the solve; the full `smt` script is sent, then `(check-sat)` and an `(echo)`
sentinel. Reading to the sentinel resynchronizes the pipe every call — the same query
always yields the same verdict, independent of prior queries. Any `(error …)`, missing
verdict, or EOF ⟹ `Except.error` (never a verdict). -/
def Z3Session.check (s : Z3Session) (smt : String) : IO (Except String Z3Verdict) := do
  try
    let stdin := s.child.stdin
    let rl := if s.cfg.rlimit == 0 then "" else s!"(set-option :rlimit {s.cfg.rlimit})\n"
    stdin.putStr s!"(reset)\n(set-option :timeout {s.cfg.timeoutMs})\n{rl}{smt}\n(check-sat)\n(echo \"{sentinel}\")\n"
    stdin.flush
    let (v?, sawErr, sawEnd) ← drainToSentinel s.child.stdout 256 none false
    if !sawEnd then return .error "z3 produced no sentinel (crash/EOF)"
    else if sawErr then return .error "z3 reported an error before the verdict"
    else match v? with
      | some "unsat" => return .ok .unsat
      | some "sat" => return .ok .sat
      | some "unknown" => return .ok .unknown
      | _ => return .error "z3 gave no verdict before the sentinel"
  catch e => return .error s!"z3 io error: {e}"

/-- Terminate the persistent process. -/
def Z3Session.close (s : Z3Session) : IO Unit := do
  try s.child.stdin.putStr "(exit)\n"; s.child.stdin.flush catch _ => pure ()
  try let _ ← s.child.wait catch _ => pure ()

/-- Convenience: start a session, run `act`, always close. Errors from `start` short-
circuit to `error`. -/
def withZ3 {α} (cfg : Z3Config) (act : Z3Session → IO (Except String α)) :
    IO (Except String α) := do
  match ← Z3Session.start cfg with
  | .error e => return .error e
  | .ok s =>
      let r ← act s
      s.close
      return r

end RelCertifier
