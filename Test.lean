/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Trusted-layer test suite (`relcert-test`)

The verified core is proven; this suite exercises the UNVERIFIED harness — the honesty
boundary, determinism, parser, lowering, Z3 layer, and oracle consistency. Exits nonzero
if any assertion fails. These are the anti-flakiness / anti-masquerade guarantees the
synthesis loop depends on.
-/
import RelCertifier.OracleAPI
import RelCertifier.Z3

open RelCertifier RelCertifier.Parse RelCertifier.Oracle

/-- Global failure counter. -/
initialize failCount : IO.Ref Nat ← IO.mkRef 0

def check (name : String) (ok : Bool) : IO Unit := do
  if ok then IO.println s!"  ok   {name}"
  else do IO.println s!"  FAIL {name}"; failCount.modify (· + 1)

def isErr : Outcome → Bool | .error _ => true | _ => false
def isCert : Outcome → Bool | .certified => true | _ => false
def isDecl : Outcome → Bool | .declined => true | _ => false

/-- Resolve a benchmark path by name from the manifest map (env `BENCH_PATHS`). -/
def benchPath (name : String) : IO (Option String) := do
  match ← IO.getEnv "BENCH_PATHS" with
  | none => return none
  | some f =>
      let txt ← try IO.FS.readFile f catch _ => pure ""
      for line in txt.splitOn "\n" do
        match line.splitOn "\t" with
        | [n, p] => if n == name then return some p
        | _ => pure ()
      return none

def loadProblem (name : String) : IO (Option PProblem) := do
  match ← benchPath name with
  | none => return none
  | some p => do
      let txt ← try IO.FS.readFile p catch _ => pure ""
      return parseProblem txt

/-! ## Z3-layer tests: known verdicts + broken path -/
def testZ3Layer (cfg : Z3Config) : IO Unit := do
  IO.println "[z3-layer]"
  match ← Z3Session.start cfg with
  | .error e => check s!"z3 session start ({e})" false
  | .ok s =>
      let u ← s.check "(declare-const x Real)(assert (and (> x 0)(< x 0)))"
      check "known-UNSAT → unsat" (u == .ok .unsat)
      let sa ← s.check "(declare-const x Real)(assert (> x 0))"
      check "known-SAT → sat" (sa == .ok .sat)
      let bad ← s.check "(declare-const x Real)(assert (nonsense x))"
      check "malformed SMT → error (not a verdict)" (isErrE bad)
      s.close
      let dead ← s.check "(assert true)"
      check "check on closed session → error" (isErrE dead)
  -- broken pinned path → error, never a verdict
  match ← Z3Session.start { binary := "/nonexistent/z3" } with
  | .error _ => check "missing z3 binary → error" true
  | .ok _ => check "missing z3 binary → error" false
where isErrE : Except String Z3Verdict → Bool | .error _ => true | _ => false

/-! ## Parser tests -/
def testParser : IO Unit := do
  IO.println "[parser]"
  check "malformed input → none" ((parseProblem "not an ini file").isNone)
  check "offset atom parses"    ((parseFormula "x[l] <= x[r] + 3").isSome)
  check "quadratic atom parses" ((parseFormula "2*(psi[l]-psi[r])*(psi[l]-psi[r]) <= 0.25").isSome)
  check "product atom parses"   ((parseFormula "v[l]*r[l] <= 1.0").isSome)
  check "smt2 atom parses"      ((parseFormula "smt2:(<= (- L_s R_s) 0.2)").isSome)

/-! ## Invariant-lowering tests: each shape → expected component count -/
def testLowering : IO Unit := do
  IO.println "[lowering]"
  let vs := ["v","s","psi","omega_psi","r","e"]
  let n := vs.length
  let comps (str : String) : Option Nat :=
    (parseFormula str).bind (invComponents vs n) |>.map (·.length)
  check "offset → 1 component"        (comps "v[l] <= v[r] + 3" == some 1)
  check "multi-conjunct → n components" (comps "v[l] <= v[r] and s[l] <= s[r]" == some 2)
  check "quadratic → 1 component"     (comps "v[l]*v[l] <= 0.25" == some 1)
  check "product/bilinear → 1 component" (comps "v[l]*r[l] <= 1.0" == some 1)
  check "unlowerable (division of vars) → none"
        (comps "smt2:(<= (/ v[l] r[l]) 1.0)" == none)

/-! ## Outcome-integrity: environment failures → ERROR, never a verdict -/
def testOutcomeIntegrity (cfg : Z3Config) : IO Unit := do
  IO.println "[outcome-integrity]"
  -- missing z3 → error (never certified/declined)
  let e1 ← certifyFile { binary := "/nonexistent/z3" } "/dev/null"
  check "missing z3 → ERROR" (isErr e1)
  -- unparsed input → error
  IO.FS.writeFile "/tmp/relcert_test_bad.txt" "garbage not ini"
  let e2 ← certifyFile cfg "/tmp/relcert_test_bad.txt"
  check "unparsed input → ERROR" (isErr e2)
  -- unreadable file → error
  let e3 ← certifyFile cfg "/no/such/path/xyz.txt"
  check "unreadable file → ERROR" (isErr e3)

/-! ## Determinism + oracle-consistency: same query → same verdict -/
def testDeterminism (cfg : Z3Config) : IO Unit := do
  IO.println "[determinism / oracle-consistency]"
  match ← Z3Session.start cfg with
  | .error e => check s!"session ({e})" false
  | .ok s =>
      -- a CERTIFIED benchmark, 8× on one warm session
      match ← loadProblem "watertank" with
      | none => IO.println "  (skip: BENCH_PATHS not set)"
      | some p => do
          let mut outs : List Bool := []
          for _ in [0:8] do outs := outs ++ [isCert (← certify s p)]
          check "watertank: 8× identical CERTIFIED" (outs.all id)
      -- a DECLINED benchmark, 8× identical verdict (stability, not the value)
      match ← loadProblem "rover_terrain_M1" with
      | none => pure ()
      | some p => do
          let mut tags : List String := []
          for _ in [0:8] do tags := tags ++ [(← certify s p).tag]
          check "declined benchmark: 8× identical verdict" (tags.eraseDups.length == 1)
      s.close

def main : IO Unit := do
  IO.println "relcert-test — trusted-layer suite\n"
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"cannot discover z3: {e}"; IO.Process.exit 2
  | .ok cfg =>
      testZ3Layer cfg
      testParser
      testLowering
      testOutcomeIntegrity cfg
      testDeterminism cfg
      let fails ← failCount.get
      IO.println s!"\n{if fails == 0 then "ALL PASS" else s!"{fails} FAILED"}"
      if fails > 0 then IO.Process.exit 1
