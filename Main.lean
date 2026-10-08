/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Runnable Stage-1 tool

Builds a relational flow obligation (the `rover_position` benchmark),
computes the verified `lieDeriv` (via the IR mirror, pinned to it by
`ilieDeriv_toHost`), emits SMT-LIB for the flow query `domain ∧ ġ > 0`, calls Z3, and
reports certified / not. `unsat` is the only trusted verdict:
`unsat ⟹ flow_certified ⟹ the invariant component is preserved along the flow`.
-/
import RelCertifier.Trusted.Smt
import RelCertifier.Trusted.EmitIR
import RelCertifier.Trusted.Oracle
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.Z3
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Trusted.ViabilityEmit
import RelCertifier.Trusted.KeyAudit
import RelCertifier.Verdicts.Run
import RelCertifier.Verdicts.RunModal
import RelCertifier.Verdicts.RunCut
import RelCertifier.Verdicts.RunHandoff

open RelCertifier DL

/-- Coordinate names for the 2-D rover state: `px` (position), `vx` (velocity). -/
def coord : Fin 2 → String := fun i => if i = 0 then "px" else "vx"

def iL (i : Fin 2) : ITerm 2 := .var (Lv i)
def iR (i : Fin 2) : ITerm 2 := .var (Rv i)

/-- `L_px − R_px − 2`  (the invariant component `g ≤ 0`, offset `d = 2`). -/
def gRover : ITerm 2 := .bin .sub (.bin .sub (iL 0) (iR 0)) (.rat 2)

/-- Left dynamics `Stop_L`: `px' = L_vx`,  `vx' = −½·L_vx`. -/
def fL_stop : Fin 2 → ITerm 2 :=
  fun i => if i = 0 then iL 1 else .bin .mul (.rat (-1/2)) (iL 1)

/-- Right dynamics `Safe_R`: `px' = R_vx`,  `vx' = 0`. -/
def fR_safe : Fin 2 → ITerm 2 :=
  fun i => if i = 0 then iR 1 else .rat 0

/-- `lo ≤ t ≤ hi`. -/
def between (t : ITerm 2) (lo hi : ℚ) : IForm 2 :=
  .and (.cmp .ge t (.rat lo)) (.cmp .le t (.rat hi))

/-- Domain box: `px ∈ [0,15]` (both sides), `vx ∈ [vlo,vhi]` (both sides). -/
def domainBox (vlo vhi : ℚ) : IForm 2 :=
  .and (between (iL 0) 0 15)
    (.and (between (iR 0) 0 15)
      (.and (between (iL 1) vlo vhi) (between (iR 1) vlo vhi)))

/-- Parse a verdict string from Z3 stdout. -/
def parseVerdict (s : String) : Verdict :=
  let s := s.trim
  if s.startsWith "unsat" then .unsat
  else if s.startsWith "sat" then .sat
  else .unknown

def runObligation (name : String) (g : ITerm 2) (fL fR : Fin 2 → ITerm 2)
    (lam : ITerm 2) (domain : IForm 2) (expect : Verdict) : IO Bool := do
  let q := iflowQuery g fL fR lam domain
  let script := q.toScript coord
  let tmp := s!"/tmp/relcert_flow_{name}.smt2"
  IO.FS.writeFile tmp script
  let out ← IO.Process.output { cmd := "z3", args := #[tmp] }
  let v := parseVerdict out.stdout
  let tag := match v with
    | .unsat => "CERTIFIED  (unsat ⇒ ġ ≤ 0 on domain ⇒ invariant preserved, via flow_certified)"
    | .sat => "not certified (sat: ġ > 0 somewhere on domain)"
    | .unknown => s!"unknown ({out.stdout.trim})"
  IO.println s!"  [{name}]  ġ-query → z3: {repr v}"
  IO.println s!"      {tag}"
  pure (v == expect)

def demoStage1 : IO Unit := do
  IO.println "relCertifier-lean — Stage 1: verified flow certificate"
  IO.println "  invariant component g = L_px − R_px − 2   (g ≤ 0)"
  IO.println "  soundness: flow_certified = z3_unsat_sound + flow_cert_sound (dL-lean DI_nonstrict_domain)"
  IO.println "  UNSAT of  domain ∧ ġ>0  is the only trusted verdict"
  IO.println ""
  IO.println "rover_position  Stop_L / Safe_R :"
  -- λ=4: ġ = L_vx − 4·R_vx, vx∈[0.3,1] ⇒ ġ ≤ −0.2 < 0 ⇒ unsat (PASS)
  let r1 ← runObligation "stop_safe_lam4" gRover fL_stop fR_safe (.rat 4)
              (domainBox (3/10) 1) Verdict.unsat
  -- λ=1: ġ = L_vx − R_vx, vx∈[0,1] ⇒ ġ can be +1 ⇒ sat (FAIL, rate gap)
  let r2 ← runObligation "stop_safe_lam1" gRover fL_stop fR_safe (.rat 1)
              (domainBox 0 1) Verdict.sat
  IO.println ""
  if r1 && r2 then
    IO.println "✓ both verdicts match the expected flow-certificate results"
  else do
    IO.println "✗ verdict mismatch"
    IO.Process.exit 1

open RelCertifier.Oracle in
/-- Run the oracle over `paths` on ONE warm Z3 session; print `path: TAG (Δms)` per file
and an ERROR count, returning the `(certified, declined, errors)` tally.

Split out from `runBatch` so `--check-quick` can consume the tally instead of
re-implementing the loop; a check that reasons about a copy of this code would not be
checking what the tool does. -/
def runBatchTally (paths : List String) : IO (Nat × Nat × Nat) := do
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
            | .ok p => certify s p
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

def runBatch (paths : List String) : IO Unit := do
  let (_, _, errs) ← runBatchTally paths
  if errs > 0 then IO.Process.exit 1

/-- Every verdict phase, with its declared coverage checked. Shared by `--run-verdicts`
and `--check-quick`. -/
def runAllVerdicts (cfg : RelCertifier.Z3Config) : IO Bool := do
  let exp := RelCertifier.Verdicts.expected
  let n0 ← RelCertifier.Verdicts.dischargedCount.get
  let ok1 ← RelCertifier.Verdicts.runVerdicts cfg
  let n1 ← RelCertifier.Verdicts.dischargedCount.get
  let ok2 ← RelCertifier.Verdicts.runCutProbes cfg
  let n2 ← RelCertifier.Verdicts.dischargedCount.get
  let ok3 ← RelCertifier.Verdicts.runModal cfg
  let n3 ← RelCertifier.Verdicts.dischargedCount.get
  let ok4 ← RelCertifier.Verdicts.runHandoffAll cfg
  let n4 ← RelCertifier.Verdicts.dischargedCount.get
  -- a phase that issued fewer queries than it owes is not a green run, however clean
  -- its own output looked (Verdicts/Coverage.lean)
  let c1 ← RelCertifier.Verdicts.checkPhase "watertank" (n1 - n0) exp.watertank
  let c2 ← RelCertifier.Verdicts.checkPhase "cut probes" (n2 - n1) exp.cut
  let c3 ← RelCertifier.Verdicts.checkPhase "modal" (n3 - n2) exp.modal
  -- the handoff phase counts its `unsat`s; the declared failures are not discharged, so
  -- the owed count is the total minus the declared failure list
  let c4 ← RelCertifier.Verdicts.checkPhase "handoff" (n4 - n3)
    (exp.handoff - RelCertifier.Verdicts.expectedHandoffFailures.length)
  pure (ok1 && ok2 && ok3 && ok4 && c1 && c2 && c3 && c4)

def usage : String :=
"relcert — the relCertifier certification tool

USAGE
  relcert <benchmark input.txt>...        certify benchmarks (CERTIFIED/DECLINED/ERROR)
  relcert --run-verdicts                  re-run every theorem's Z3 hypotheses
                                          (incl. the cross-mode handoff phase)
  relcert --handoff <input.txt>...        the handoff check alone, per benchmark, with
                                          per-transition verdicts and wall time
  relcert --check-quick <input.txt>...    the fast checks: certify, then --run-verdicts
  relcert --help                          this text

EMITTERS (regenerate committed Lean literals; each prints to stdout)
  relcert --emit-ir         <input.txt> <defname>
  relcert --emit-cover      <input.txt> <defname>
  relcert --emit-cuts       <input.txt> <defname>
  relcert --emit-viability  <input.txt> <defname>     (also --emit-viability2, -3)

NOT PART OF THIS BINARY
  The kernel check is the Lean toolchain, not a flag here:
    lake build                                      kernel-checks everything (~13 h)
    lake build RelCertifier.Instances.ModalBattery  the 47 theorems + axiom audit
  The trusted-layer tests are a separate executable:
    BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test
  `relcert-test` silently skips its two Z3-determinism checks unless BENCH_PATHS
  points at a TSV of `<benchmark name>\\t<absolute path to input.txt>`; a complete run
  prints a bare `ALL PASS`, a skipping one says so in the final line.

  The full four-check recipe is docs/CERTIFICATION-CHECK.md.

EXIT
  0 success · 1 a check failed · 2 environment problem (no z3, bad usage)"

open RelCertifier.Oracle in
/-- `--emit-cuts <file> <defname>`: run the checked-cut search (Z3) and print the kept
atoms with their routes as a `EvolStrengthening` Lean literal (the cut-lift's single door — the
search stays untrusted; its output is certified against the IR by `evolStrengtheningWF = true`,
`rfl`). -/
def emitCuts (path defname : String) : IO Unit := do
  match ← Z3Config.discover with
  | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 2
  | .ok cfg =>
    match ← Z3Session.start cfg with
    | .error e => IO.eprintln s!"ERROR: z3 session: {e}"; IO.Process.exit 2
    | .ok s =>
      match ← RelCertifier.Oracle.readProblemStrict path with
      | .error e => IO.eprintln s!"ERROR: parse: {e}"; s.close; IO.Process.exit 1
      | .ok p => do
        let vars := p.L.stateVars
        let n := vars.length
        let coord := fun (i : Fin n) => vars.getD i.val "v"
        let cnt ← IO.mkRef 0
        let deadline := (← IO.monoMsNow) + 120000
        let emitAtoms (atoms : List (RelCertifier.Parse.PForm × CutRoute)) : String :=
          "[" ++ String.intercalate ", " (atoms.map (fun ar =>
            "(" ++ RelCertifier.Parse.emitForm ar.1 ++ ", CutRoute." ++
              (match ar.2 with
                | .shape => "shape"
                | .frozen => "frozen"
                | .diStrict => "diStrict"
                | .diNonstrict => "diNonstrict") ++ ")")) ++ "]"
        let mut ls : List String := []
        for mM in p.L.modes do
          let (_, kept) ← checkedCut s cnt 5000 200000 deadline vars n coord
            RelCertifier.Side.L mM
          ls := ls ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtoms kept})"]
        let mut rs : List String := []
        for mM in p.R.modes do
          let (_, kept) ← checkedCut s cnt 5000 200000 deadline vars n coord
            RelCertifier.Side.R mM
          rs := rs ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtoms kept})"]
        s.close
        IO.println s!"def {defname} : EvolStrengthening :="
        IO.println "  { L := ["
        IO.println (String.intercalate ",
" ls)
        IO.println "    ]"
        IO.println "    R := ["
        IO.println (String.intercalate ",
" rs)
        IO.println "    ] }"

/-- `--emit-ir <file> <defname>`: print the parsed `PProblem` as a Lean literal (the
single-door bridge for the `Faithful` kernel certificates — see EmitIR.lean). -/
def emitIR (path defname : String) : IO Unit := do
  match ← RelCertifier.Oracle.readProblemStrict path with
  | .error e => IO.eprintln s!"ERROR: parse: {e}"; IO.Process.exit 1
  | .ok p => IO.println (RelCertifier.Parse.emitProblem defname p)

def main (args : List String) : IO Unit := do
  match args with
  | ["--emit-ir", path, defname] => emitIR path defname
  | ["--help"] => IO.println usage
  | ["-h"] => IO.println usage
  | ["--run-verdicts"] => do
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 1
      | .ok cfg =>
          if ← runAllVerdicts cfg then
            IO.println "ALL HYPOTHESES DISCHARGED"
          else
            IO.eprintln "SOME HYPOTHESIS NOT DISCHARGED"; IO.Process.exit 1
  | ["--emit-viability3", path, defname] => do
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 1
      | .ok cfg => RelCertifier.Oracle.emitViabilityFileStrat cfg path defname
  | ["--emit-viability2", path, defname] => do
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 1
      | .ok cfg => RelCertifier.Oracle.emitViabilityFileB cfg path defname
  | ["--emit-viability", path, defname] => do
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 1
      | .ok cfg => RelCertifier.Oracle.emitViabilityFile cfg path defname
  | ["--emit-cover", path, defname] => do
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 1
      | .ok cfg => RelCertifier.Oracle.emitCoverFile cfg path defname
  | ["--emit-cuts", path, defname] => emitCuts path defname
  | [] => demoStage1
  | "--handoff" :: paths => do
      if paths.isEmpty then
        IO.eprintln "ERROR: --handoff needs benchmark paths (see --help)"
        IO.Process.exit 2
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 2
      | .ok cfg =>
        match ← RelCertifier.Z3Session.start cfg with
        | .error e => IO.eprintln s!"ERROR: z3 session: {e}"; IO.Process.exit 2
        | .ok s =>
          let mut anyFail := false
          let mut total := 0
          for path in paths do
            match ← RelCertifier.Oracle.readProblemStrict path with
            | .error e => IO.println s!"{path}: ERROR [parse: {e}]"; anyFail := true
            | .ok p =>
              let name := (path.splitOn "/").reverse.getD 1 path
              let r ← RelCertifier.Verdicts.runHandoffBench s cfg name p
              IO.println r.line
              total := total + r.checked
              if !r.failing.isEmpty || r.checked != r.declared then anyFail := true
          s.close
          IO.println s!"handoff: {total} transition(s) checked over {paths.length} benchmark(s)"
          if anyFail then IO.Process.exit 1
  | "--check-quick" :: paths => do
      if paths.isEmpty then
        IO.eprintln "ERROR: --check-quick needs benchmark paths (see --help)"
        IO.Process.exit 2
      IO.println "== check 1/2 : certify the benchmarks =="
      let (cert, decl, errs) ← runBatchTally paths
      let okSuite ← RelCertifier.Verdicts.checkSuite paths.length cert decl errs
      IO.println "\n== check 2/2 : discharge the verdict hypotheses =="
      let okVerd ← match ← RelCertifier.Z3Config.discover with
        | .error e => IO.eprintln s!"ERROR: {e}"; pure false
        | .ok cfg => runAllVerdicts cfg
      IO.println ""
      IO.println s!"  suite:    {if okSuite then "PASS" else "FAIL"}"
      IO.println s!"  verdicts: {if okVerd then "PASS" else "FAIL"}"
      if okSuite && okVerd then
        IO.println "QUICK CHECKS PASSED  (the kernel check is `lake build` — see --help)"
      else
        IO.eprintln "QUICK CHECKS FAILED"; IO.Process.exit 1
  -- Reject unknown flags rather than treating them as benchmark paths: a mistyped
  -- `--run-verdict` used to be reported as a missing *file*, which reads like a bad
  -- path rather than a bad command.
  | _ =>
      match args.find? (fun a => a.startsWith "-") with
      | some bad =>
          IO.eprintln s!"ERROR: unknown option '{bad}'\n"
          IO.eprintln usage
          IO.Process.exit 2
      | none => runBatch args
