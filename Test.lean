/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Trusted-layer test suite (`relcert-test`)

The verified core is proven; this suite exercises the UNVERIFIED harness — the honesty
boundary, determinism, parser, lowering, Z3 layer, and oracle consistency. Exits nonzero
if any assertion fails. These are the anti-flakiness / anti-masquerade guarantees the
synthesis loop depends on.
-/
import RelCertifier.Trusted.OracleAPI
import RelCertifier.InstancesV2.BenchIR
import RelCertifier.Trusted.Z3

open RelCertifier RelCertifier.Parse RelCertifier.Oracle

/-- Global failure counter. -/
initialize failCount : IO.Ref Nat ← IO.mkRef 0

/-- Checks that did not run. A suite that prints `ALL PASS` while having quietly
skipped a check is reporting work it did not do — the same failure mode as a verdict
runner that discharges a pack by issuing no query. Skips are counted and named in the
final line so a green run states what it actually covered. -/
initialize skipCount : IO.Ref Nat ← IO.mkRef 0

def skip (name : String) (why : String) : IO Unit := do
  IO.println s!"  SKIP {name} ({why})"
  skipCount.modify (· + 1)

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
  -- strictness: reject, never weaken
  check "empty-arg sexpr rejected"   ((parseFormula "smt2:(<= (-) 0.2)").isNone)
  check "op-dropping (op x) rejected" ((parseExpr "smt2:(* 3)").isNone)
  check "unknown expr op rejected"   ((parseExpr "smt2:(foo 1 2)").isNone)
  check "unknown cmp op rejected"    ((parseFormula "smt2:(sim L_v R_v)").isNone)
  check "(and) not top"              ((parseFormula "smt2:(and)").isNone)
  let skel (inv : String) (evolve : String := "x >= 0.0") (ode : String := "x' = 0;") :=
    "[problem]\nname = t\nlambda_min = 1.0\nlambda_max = 1.0\n" ++
    "[Lsys]\nstate_vars = [x]\nepsilon = 1.0\n" ++
    "[Lsys.mode.A]\node = " ++ ode ++ "\nguard = x >= 0.0\nevolve = " ++ evolve ++
    "\nnext = [A]\n" ++
    "[Rsys]\nstate_vars = [x]\nepsilon = 1.0\n" ++
    "[Rsys.mode.A]\node = x' = 0;\nguard = x >= 0.0\nevolve = x >= 0.0\nnext = [A]\n" ++
    "[relational_invariant]\n" ++ inv ++ "\n"
  let bad (nm : String) (txt : String) : IO Unit :=
    check nm ((parseProblemE txt).toOption.isNone)
  check "minimal skeleton parses" ((parseProblemE (skel "A = x[l] <= x[r]")).toOption.isSome)
  bad "unparsable invariant line → error (was: dropped)"
      (skel "A = x[l] <=")
  bad "pair-keyed invariant row → error (dead syntax)"
      (skel "A/A = x[l] <= x[r]")
  bad "invariant key not a mode → error"
      (skel "B = x[l] <= x[r]")
  bad "unprojected var in invariant → error"
      (skel "A = x <= 1.0")
  bad "undeclared var in evolve → error"
      (skel "A = x[l] <= x[r]" (evolve := "y >= 0.0"))
  bad "missing ode for state var → error"
      ((skel "A = x[l] <= x[r]").replace "ode = x' = 0;\nguard = x >= 0.0\nevolve = x >= 0.0\nnext = [A]\n[relational_invariant]"
        "ode = ;\nguard = x >= 0.0\nevolve = x >= 0.0\nnext = [A]\n[relational_invariant]")
  bad "unresolved next → error"
      ((skel "A = x[l] <= x[r]").replace "next = [A]\n[relational_invariant]" "next = [Z]\n[relational_invariant]")
  bad "duplicate key → error"
      ((skel "A = x[l] <= x[r]").replace "[Lsys]\nstate_vars = [x]" "[Lsys]\nstate_vars = [x]\nstate_vars = [x]")
  bad "junk line → error"
      ((skel "A = x[l] <= x[r]").replace "[problem]" "[problem]\njunk line no equals")
  bad "missing guard → error"
      ((skel "A = x[l] <= x[r]").replace "guard = x >= 0.0\nevolve = x >= 0.0\nnext = [A]\n[relational_invariant]"
        "evolve = x >= 0.0\nnext = [A]\n[relational_invariant]")
  bad "malformed numeral → error"
      (skel "A = x[l] <= 1.2.3")
  bad "ode LHS without prime → error"
      ((skel "A = x[l] <= x[r]").replace "ode = x' = 0;\nguard = x >= 0.0\nevolve = x >= 0.0\nnext = [A]\n[relational_invariant]"
        "ode = x = 0;\nguard = x >= 0.0\nevolve = x >= 0.0\nnext = [A]\n[relational_invariant]")

/-! ## SMT printer tests: golden strings + Z3 behavioral agreement

The printer (`IForm.toSmt`/`toScript`) sits INSIDE the trusted `z3solve` plumbing: a
printing bug is an unsoundness route no Lean proof can see. Golden tests pin the exact
output for each constructor; the behavioral tests hand crafted formulas with known
verdicts to a real Z3 session THROUGH the printer, so an operator/parenthesization slip
flips a known verdict and fails the battery. -/
def testPrinter (cfg : Z3Config) : IO Unit := do
  IO.println "[smt-printer]"
  let coord : Fin 1 → String := fun _ => "x"
  let x : ITerm 1 := .var (Side.L, 0)
  let r (q : ℚ) : ITerm 1 := .rat q
  -- golden strings, one per constructor/op
  check "golden var"  ((ITerm.toSmt coord x) == "L_x")
  check "golden neg-rat" ((ITerm.toSmt coord (r (-2))) == "(- 2)")
  check "golden frac"    ((ITerm.toSmt coord (r (1/3))) == "(/ 1 3)")
  check "golden nested sub"
    ((ITerm.toSmt coord (.bin .sub (.bin .mul (r 2) x) (r 1))) == "(- (* 2 L_x) 1)")
  check "golden ne"
    ((IForm.toSmt coord (.cmp .ne x (r 0))) == "(not (= L_x 0))")
  -- behavioral: known verdicts through the full print→Z3 path
  match ← Z3Session.start cfg with
  | .error e => check s!"z3 session ({e})" false
  | .ok s =>
      let run (nm : String) (f : IForm 1) (expectUnsat : Bool) : IO Unit := do
        let script := IForm.toScript coord f
        let v ← s.check script
        let ok := match v, expectUnsat with
          | .ok .unsat, true => true
          | .ok .sat, false => true
          | _, _ => false
        check nm ok
      let eq (a b : ITerm 1) : IForm 1 := .cmp .eq a b
      -- x = 3 ∧ 2x − 1 = 5 : SAT (a sub/mul precedence slip breaks it)
      run "2x−1 arithmetic (sat)"
        (.and (eq x (r 3)) (eq (.bin .sub (.bin .mul (r 2) x) (r 1)) (r 5))) false
      -- x = 3 ∧ 2x − 1 > 5 : UNSAT
      run "2x−1 bound (unsat)"
        (.and (eq x (r 3)) (.cmp .gt (.bin .sub (.bin .mul (r 2) x) (r 1)) (r 5))) true
      -- x = 1/3 ∧ 3x < 1 : UNSAT (rational printing exact, not decimal-rounded)
      run "exact rational (unsat)"
        (.and (eq x (r (1/3))) (.cmp .lt (.bin .mul (r 3) x) (r 1))) true
      -- x = −2 ∧ x·x ≠ 4 : UNSAT (negative literal + ne encoding)
      run "neg literal square (unsat)"
        (.and (eq x (r (-2))) (.cmp .ne (.bin .mul x x) (r 4))) true
      s.close

/-! ## IR drift check: every embedded literal must equal a fresh parse of its file

The 19 carried-over legacy literals (`Instances/BenchIR`) are tied to these by
`InstancesV2/SameIR.lean` (`rfl`), so this one check covers them too. -/

/-- The suite_v2 drift check: every `benchIRTableV2` literal equals a fresh parse of
`benchmarks/suite_v2/<name>/input.txt`, and the table covers all 45 files. -/
def testIRDriftV2 : IO Unit := do
  IO.println "[ir-drift-v2]"
  let mut bad := 0
  for (nm, p) in RelCertifier.Parse.benchIRTableV2 do
    let path := s!"benchmarks/suite_v2/{nm}/input.txt"
    let txt ← try IO.FS.readFile path catch _ => pure ""
    match RelCertifier.Parse.parseProblemE txt with
    | .error e => bad := bad + 1; check s!"{nm}: parse ({e})" false
    | .ok q =>
        if q == p then pure ()
        else bad := bad + 1; check s!"{nm}: literal == fresh parse (suite_v2)" false
  check s!"all {RelCertifier.Parse.benchIRTableV2.length} suite_v2 IR literals match their files"
    (bad == 0 && RelCertifier.Parse.benchIRTableV2.length == 45)

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
      match ← loadProblem "match_multi_rate" with
      | none => skip "match_multi_rate: 8× identical CERTIFIED" "BENCH_PATHS not set"
      | some p => do
          let mut outs : List Bool := []
          for _ in [0:8] do outs := outs ++ [isCert (← certify s p)]
          check "match_multi_rate: 8× identical CERTIFIED" (outs.all id)
      -- a DECLINED benchmark, 8× identical verdict (stability, not the value):
      -- `acc_spoof_lag` declines unless `RELCERT_IMPLIED_CUT=1` widens the cut channel
      match ← loadProblem "acc_spoof_lag" with
      | none => skip "acc_spoof_lag: 8× identical verdict" "BENCH_PATHS not set"
      | some p => do
          let mut tags : List String := []
          for _ in [0:8] do tags := tags ++ [(← certify s p).tag]
          check "acc_spoof_lag: 8× identical verdict" (tags.eraseDups.length == 1)
      s.close

def main : IO Unit := do
  IO.println "relcert-test — trusted-layer suite\n"
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"cannot discover z3: {e}"; IO.Process.exit 2
  | .ok cfg =>
      testZ3Layer cfg
      testParser
      testIRDriftV2
      testPrinter cfg
      testLowering
      testOutcomeIntegrity cfg
      testDeterminism cfg
      let fails ← failCount.get
      let skips ← skipCount.get
      let verdict :=
        if fails > 0 then s!"{fails} FAILED"
        else if skips > 0 then s!"ALL PASS ({skips} SKIPPED — set BENCH_PATHS to run them)"
        else "ALL PASS"
      IO.println s!"\n{verdict}"
      if fails > 0 then IO.Process.exit 1
