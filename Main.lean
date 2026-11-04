/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `relcert`: the certification tool and its verdict runner

* `relcert <input.txt>…` runs the certifier (`Trusted/OracleAPI.certify`) on each benchmark
  on one warm Z3 session, then the handoff check (`Verdicts/RunHandoff`) on every covered
  benchmark, and prints CERTIFIED / DECLINED / ERROR per file; CERTIFIED requires both.
* `relcert --run-verdicts-v2` re-sends every Z3 hypothesis of the suite_v2 verdict phases
  (`VerdictsV2`) with declared per-phase counts (`runAllVerdictsV2`);
  `--check-quick-v2` certifies the suite_v2 files first (in the strict well-formedness
  mode) and checks the tally, then runs the verdicts, then the strict Assumption 1 gate
  (declared right-mode count `expectedSuiteV2.wfModes`, 0 UNKNOWN, 0 BLOCKING; both clauses
  per mode).
* `relcert --handoff <input.txt>…` runs the cross-mode handoff check per benchmark.
* `relcert --wellformed <input.txt>…` runs the Assumption 1 check (Well-Formedness) of the
  right models, both clauses, nonblocking and complete (`Trusted/WellFormedCheck.lean`,
  informational; `RELCERT_WELLFORMED_STRICT=1` makes an `UNKNOWN` or `BLOCKING` mode
  decline a certified benchmark).
* `--emit-*` print the Lean literals the kernel-checked data layer is generated from.

`unsat` is the only verdict the proofs consume (`z3_unsat_sound`). The kernel check is
`lake build`, not a flag of this binary.
-/
import RelCertifier.Trusted.EmitIR
import RelCertifier.Trusted.Run
import RelCertifier.Trusted.Z3
import RelCertifier.Trusted.OracleAPI
import RelCertifier.Trusted.WellFormedCheck
import RelCertifier.Trusted.ViabilityEmit
import RelCertifier.Trusted.KeyAudit
import RelCertifier.Verdicts.RunHandoff
import RelCertifier.VerdictsV2.RunV2

open RelCertifier DL

open RelCertifier.Oracle in
/-- Run the oracle over `paths` on ONE warm Z3 session; print `path: TAG (Δms)` per file
and an ERROR count, returning the `(certified, declined, errors)` tally.

`runBatch` and `--check-quick-v2` both call this function, so the quick check tallies the
loop the tool runs rather than a copy of it. -/
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
        let name := (path.splitOn "/").reverse.getD 1 path
        -- CERTIFIED is the verdict of Theorem 3 (Soundness of Synthesis): a cover with its
        -- certificates for every left mode AND the handoff condition Eq. (13) at every
        -- declared left mode change. A cover without a passing handoff is DECLINED, with
        -- the failing transitions named.
        let (oc, why) ← try
            match ← RelCertifier.Oracle.readProblemStrict path with
            | .error e => pure (Outcome.error s!"parse: {e}", "")
            | .ok p =>
                let o ← match strict with
                  | some b => RelCertifier.WellFormed.certifyWFWith b s p
                  | none => RelCertifier.WellFormed.certifyWF s p
                match o with
                | .certified =>
                    let h ← RelCertifier.Verdicts.runHandoffBench s cfg name p (verbose := false)
                    if h.failing.isEmpty && h.checked == h.declared then
                      pure (Outcome.certified, "")
                    else
                      let fs := String.intercalate ", "
                        (h.failing.map (fun f => s!"{f.1.1}->{f.1.2}"))
                      pure (Outcome.declined,
                        s!" [handoff: {h.passed}/{h.declared} transitions pass; failing: {fs}]")
                | o => pure (o, "")
          catch e => pure (Outcome.error s!"io: {e}", "")
        let dt := (← IO.monoMsNow) - t0
        match oc with
        | .certified => cert := cert + 1; IO.println s!"{name}: CERTIFIED ({dt}ms)"
        | .declined  => decl := decl + 1; IO.println s!"{name}: DECLINED{why} ({dt}ms)"
        | .error m   => errs := errs + 1; IO.println s!"{name}: ERROR [{m}] ({dt}ms)"
      s.close
      IO.println s!"errors={errs}"
      pure (cert, decl, errs)

def runBatch (paths : List String) : IO Unit := do
  let (_, _, errs) ← runBatchTally paths
  if errs > 0 then IO.Process.exit 1

/-- Every suite_v2 verdict phase, with its declared coverage checked (`--run-verdicts-v2`,
`--check-quick-v2`). -/
def runAllVerdictsV2 (cfg : RelCertifier.Z3Config) : IO Bool := do
  let n0 ← RelCertifier.Verdicts.dischargedCount.get
  let ok1 ← RelCertifier.VerdictsV2.runModalV2 cfg
  let n1 ← RelCertifier.Verdicts.dischargedCount.get
  let c1 ← RelCertifier.Verdicts.checkPhase "suite_v2 modal" (n1 - n0)
    RelCertifier.VerdictsV2.expectedModalV2
  let ok2 ← RelCertifier.VerdictsV2.runHandoffAllV2 cfg
  let n2 ← RelCertifier.Verdicts.dischargedCount.get
  let c2 ← RelCertifier.Verdicts.checkPhase "suite_v2 handoff" (n2 - n1)
    (RelCertifier.VerdictsV2.expectedHandoffV2
      - RelCertifier.VerdictsV2.expectedHandoffFailuresV2.length)
  let ok3 ← RelCertifier.VerdictsV2.runNonConnAllV2 cfg
  let n3 ← RelCertifier.Verdicts.dischargedCount.get
  let c3 ← RelCertifier.Verdicts.checkPhase "suite_v2 non-connection" (n3 - n2)
    RelCertifier.VerdictsV2.expectedNonConnV2
  let c3' ← RelCertifier.Verdicts.checkPhase "suite_v2 pruned edges"
    RelCertifier.VerdictsV2.prunedEdgesV2.length RelCertifier.VerdictsV2.expectedPrunedEdgesV2
  let ok4 ← RelCertifier.VerdictsV2.runDynV2 cfg
  let n4 ← RelCertifier.Verdicts.dischargedCount.get
  let c4 ← RelCertifier.Verdicts.checkPhase "suite_v2 reposition (dyn)" (n4 - n3)
    RelCertifier.VerdictsV2.expectedDynV2
  pure (ok1 && c1 && ok2 && c2 && ok3 && c3 && c3' && ok4 && c4)

def usage : String :=
"relcert — the relCertifier certification tool

USAGE
  relcert <benchmark input.txt>...        certify benchmarks (CERTIFIED/DECLINED/ERROR)
  relcert --run-verdicts-v2               re-send every Z3 hypothesis of the suite_v2
                                          battery, with declared per-phase counts:
                                          modal packs, handoff, non-connection (both
                                          pruning queries of every pruned edge) and
                                          reposition packs
  RELCERT_IMPLIED_CUT=1 relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
                                          certify the suite_v2 files in the strict
                                          well-formedness mode (declared: every file
                                          certified, 0 declined), then --run-verdicts-v2,
                                          then the strict --wellformed gate (declared
                                          right-mode count, 0 UNKNOWN, 0 BLOCKING; any
                                          mode not ok fails the run)
  relcert --handoff <input.txt>...        the handoff check alone, per benchmark, with
                                          per-transition verdicts and wall time
  relcert --wellformed <input.txt>...     the Assumption 1 (Well-Formedness) check of the
                                          right model, per right mode, both clauses
                                          (informational, never a verdict). Complete
                                          (clause ii):
                                          `ok (invariant)` when the mode's guard atoms are
                                          kept by its own flow (stratified DI routes B/A
                                          over its evolve domain) and it has a self-loop;
                                          `ok (exit→S)` when every run of at most one
                                          control interval ε_r ends in the guard of a
                                          declared successor in S (rate bounds on the
                                          atoms that are not kept, then one coverage
                                          query). Nonblocking (clause i), on top of
                                          either: every evolve-domain atom persists for
                                          ε_r from the guard (exact, boundary, monotone or
                                          interval-margin routes, a sign split on a
                                          contraction coordinate) and the solution cannot
                                          blow up; `BLOCKING (leaves d)` when a guard
                                          state leaves the domain at once (no
                                          full-interval run). `UNKNOWN` otherwise (the
                                          check is sufficient, not necessary;
                                          `UNKNOWN (nonblocking)`: clause ii shown, clause
                                          i not). The kernel's per-benchmark result is
                                          WellFormedR, one hand-written proof per
                                          benchmark (lake build
                                          RelCertifier.InstancesV2.WellFormedBattery)
  relcert --help                          this text

EMITTERS (regenerate committed Lean literals; each prints to stdout)
  relcert --emit-ir         <input.txt> <defname>
  relcert --emit-cover      <input.txt> <defname>
  relcert --emit-cuts       <input.txt> <defname>      (the mode facts)
  relcert --emit-viability  <input.txt> <defname>     (also --emit-viability2, -3)
  scripts/gen_v2_data.py drives the first three over benchmarks/suite_v2.

NOT PART OF THIS BINARY
  The kernel check is the Lean toolchain, not a flag here:
    lake build                                       kernel-checks everything
    lake build RelCertifier.InstancesV2.WellFormedBattery   the Assumption 1 battery + axiom audit
    lake build RelCertifier.InstancesV2.AxiomCheck   the axiom audit of the generic theorems
  The trusted-layer tests are a separate executable:
    BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test
  `relcert-test` skips its two Z3-determinism checks unless BENCH_PATHS points at a TSV
  of `<benchmark name>\\t<absolute path to input.txt>` covering benchmarks/suite_v2; a
  complete run prints a bare `ALL PASS`, a skipping one says so in the final line.

  The full recipe is docs/CERTIFICATION-CHECK.md.

SWITCHES (environment)
  RELCERT_IMPLIED_CUT=1
                       widen the mode-fact candidates (Definition 2; off by default; the
                       suite_v2 runs set it, and some suite_v2 benchmarks decline without
                       it). Each atom is a mode fact by two obligations: O1, the guard
                       implies it; O2, the mode's flow keeps it. The widened atoms are the
                       closure of a strict guard conjunct (O1 by weakening) and, for a
                       contraction field x' = k (c - x), the set-point half-lines
                       x <= c / x >= c (O1 by rational comparison with a threshold guard
                       conjunct, else one Z3 query UNSAT(guard and not atom)), and the
                       linear-form chain of a recognized second-order pair x' = y,
                       y' = -a (x - c) - b y with rational eigenvalues: y + r (x - c) <=
                       sup / >= inf over the guard box (O1 rational, O2 by the rational
                       linear shape), then the derived bound x <= c + K/r stratified on
                       it; --emit-cuts then also prints the extended certificate
                       `<defname>X` (atom, kind, O1, O2 route, conditioning atoms) that
                       Proofs/Soundness/CutLiftX lifts to the kernel
  RELCERT_NO_IMPLIED_CUT=1
                       force the widened candidates off (the counter-run of the suite_v2
                       matrix: guard-conjunct mode facts only)
  RELCERT_NO_LINEAR_CUT=1
                       keep the closures and implied-contraction atoms but switch the
                       linear-form chain off (the matrix's M6L counter-run)
  RELCERT_NO_PRUNE=1   disable pruning by non-connection certificates (Definition 6,
                       Section 4.2): every declared right mode change stays a retained
                       successor of the cover
  RELCERT_NO_CUT=1     disable the mode facts (queries on the bare evolve domains)
  RELCERT_DEBUG=1      per-mode diagnostics on stderr (mode facts as [cut] lines,
                       admissible starts, pruned edges, per-stretch segment status;
                       [cut-x] lines for the widened atoms)
  RELCERT_WELLFORMED_STRICT=1
                       run the --wellformed check on every CERTIFIED benchmark and turn it
                       into DECLINED when a right mode is UNKNOWN or BLOCKING (off by default; off, no
                       verdict and no emission changes)
  Solver and budget defaults (override per run):
  RELCERT_Z3=<path>               the Z3 binary (else the first of a fixed list of paths)
  RELCERT_Z3_TIMEOUT=<ms>         per-query wall-clock timeout, default 10000
  RELCERT_Z3_RLIMIT=<units>       per-query deterministic rlimit, default 64000000
                                  (0 disables it)
  RELCERT_MAX_QUERIES=<n>         per-benchmark query budget, default 20000
  RELCERT_NO_PROGRESS=1           do not require reposition certificates (Definition 7)
                                  at right-only nodes (ablation)
  RELCERT_NO_CHOICE=1             no committed successor subsets after the retained
                                  successors fail to close a cover (ablation)
  RELCERT_NO_STUTTER=1            no stretch 0 (the witness stands still) on joint
                                  segments (ablation; stretch 0 on by default)
  RELCERT_NO_PRELANDING=1         right-only nodes need the right-only flow certificate on
                                  the whole mode, not on the restricted mode m|¬target of
                                  Lemma 4 (ablation; the restricted mode on by default)
  RELCERT_TIME_BUDGET_MS=<ms>     per-benchmark wall-clock budget, default 300000

EXIT
  0 success · 1 a check failed · 2 environment problem (no z3, bad usage)"

open RelCertifier.Oracle in
/-- `--emit-cuts <file> <defname>`: run the mode-fact search (Definition 2, with Z3) and print
the kept atoms with their routes as an `EvolStrengthening` Lean literal, the only way mode
facts enter the kernel. The search stays untrusted: its output is checked against the IR by
`evolStrengtheningWF = true` (`rfl`), and `CutLiftX` lifts it. -/
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
        let vars := p.jointVars
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
        -- RELCERT_IMPLIED_CUT=1: the extended mode-fact search (`checkedCutX`) runs
        -- instead; its `guardConj` subset is the guard-conjunct certificate (printed first,
        -- same literal), and the full extended certificate is printed as a second
        -- `def <defname>X`.
        let implied ← impliedCutsOn
        let emitAtomsX (xs : List CutAtomX) : String :=
          "[" ++ String.intercalate ", " (xs.map (fun x =>
            "⟨" ++ RelCertifier.Parse.emitForm x.atom ++ ", CutKind." ++
              (match x.kind with
                | .guardConj => "guardConj"
                | .impliedContract => "impliedContract"
                | .closure => "closure"
                | .linearForm => "linearForm"
                | .derivedBound => "derivedBound") ++ ", CutEntry." ++
              (match x.entry with
                | .membership => "membership"
                | .rational => "rational"
                | .z3 => "z3"
                | .weakening => "weakening") ++ ", CutRouteX." ++
              (match x.route with
                | .shape => "shape"
                | .frozen => "frozen"
                | .diStrict => "diStrict"
                | .diNonstrict => "diNonstrict"
                | .linearShape => "linearShape"
                | .derivedShape => "derivedShape"
                | .diSuperlevel => "diSuperlevel") ++ ", [" ++
              String.intercalate ", " (x.given.map RelCertifier.Parse.emitForm) ++ "]⟩")) ++ "]"
        let legacyOf (xs : List CutAtomX) : List (RelCertifier.Parse.PForm × CutRoute) :=
          (xs.filter (fun x => x.kind == CutKind.guardConj)).filterMap (fun x =>
            match x.route with
            | .shape => some (x.atom, CutRoute.shape)
            | .frozen => some (x.atom, CutRoute.frozen)
            | .diStrict => some (x.atom, CutRoute.diStrict)
            | .diNonstrict => some (x.atom, CutRoute.diNonstrict)
            | _ => none)
        let mut ls : List String := []
        let mut lxs : List String := []
        for mM in p.L.modes do
          if implied then
            let (_, xs) ← checkedCutX s cnt 5000 200000 deadline vars n coord
              RelCertifier.Side.L mM
            ls := ls ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtoms (legacyOf xs)})"]
            lxs := lxs ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtomsX xs})"]
          else
            let (_, kept) ← checkedCut s cnt 5000 200000 deadline vars n coord
              RelCertifier.Side.L mM
            ls := ls ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtoms kept})"]
        let mut rs : List String := []
        let mut rxs : List String := []
        for mM in p.R.modes do
          if implied then
            let (_, xs) ← checkedCutX s cnt 5000 200000 deadline vars n coord
              RelCertifier.Side.R mM
            rs := rs ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtoms (legacyOf xs)})"]
            rxs := rxs ++ [s!"      ({RelCertifier.Parse.qs mM.name}, {emitAtomsX xs})"]
          else
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
        if implied then
          IO.println ""
          IO.println s!"def {defname}X : EvolStrengtheningX :="
          IO.println "  { L := ["
          IO.println (String.intercalate ",
" lxs)
          IO.println "    ]"
          IO.println "    R := ["
          IO.println (String.intercalate ",
" rxs)
          IO.println "    ] }"

/-- `--emit-ir <file> <defname>`: print the parsed `PProblem` as a Lean literal (the only way
the parsed model enters the `Faithful` kernel certificates, see EmitIR.lean), with the run's
feature flags (`Oracle.withRunFeatures`: stretch 0 and the restricted mode of Lemma 4, each
on unless `RELCERT_NO_STUTTER` / `RELCERT_NO_PRELANDING`). -/
def emitIR (path defname : String) : IO Unit := do
  match ← RelCertifier.Oracle.readProblemStrict path with
  | .error e => IO.eprintln s!"ERROR: parse: {e}"; IO.Process.exit 1
  | .ok p => IO.println (RelCertifier.Parse.emitProblem defname (← RelCertifier.Oracle.withRunFeatures p))

def main (args : List String) : IO Unit := do
  match args with
  | ["--emit-ir", path, defname] => emitIR path defname
  | ["--help"] => IO.println usage
  | ["-h"] => IO.println usage
  | ["--run-verdicts-v2"] => do
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 1
      | .ok cfg =>
          if ← runAllVerdictsV2 cfg then
            IO.println "ALL suite_v2 HYPOTHESES DISCHARGED"
          else
            IO.eprintln "SOME suite_v2 HYPOTHESIS NOT DISCHARGED"; IO.Process.exit 1
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
  | [] => IO.println usage
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
  | "--wellformed" :: paths => do
      if paths.isEmpty then
        IO.eprintln "ERROR: --wellformed needs benchmark paths (see --help)"
        IO.Process.exit 2
      match ← RelCertifier.Z3Config.discover with
      | .error e => IO.eprintln s!"ERROR: {e}"; IO.Process.exit 2
      | .ok cfg =>
        let (_, okParse) ← RelCertifier.WellFormed.runWellformed cfg paths
        if !okParse then IO.Process.exit 1
  | "--check-quick-v2" :: paths => do
      if paths.isEmpty then
        IO.eprintln "ERROR: --check-quick-v2 needs the suite_v2 paths (see --help)"
        IO.Process.exit 2
      if (← IO.getEnv "RELCERT_IMPLIED_CUT").isNone ||
          (← IO.getEnv "RELCERT_NO_IMPLIED_CUT").isSome then
        IO.eprintln "ERROR: --check-quick-v2 certifies suite_v2 with the widened cut channel; \
run it as RELCERT_IMPLIED_CUT=1 relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt"
        IO.Process.exit 2
      IO.println "== check 1/3 : certify the suite_v2 benchmarks (widened cut channel, strict \
well-formedness: a CERTIFIED file with an UNKNOWN or BLOCKING right mode is DECLINED) =="
      let (cert, decl, errs) ← runBatchTally paths (strict := some true)
      let okSuite ← RelCertifier.VerdictsV2.checkSuiteV2 paths.length cert decl errs
      IO.println "\n== check 2/3 : discharge the suite_v2 verdict hypotheses =="
      let okVerd ← match ← RelCertifier.Z3Config.discover with
        | .error e => IO.eprintln s!"ERROR: {e}"; pure false
        | .ok cfg => runAllVerdictsV2 cfg
      IO.println "\n== check 3/3 : the Assumption 1 check of the right models (--wellformed, strict) =="
      let e := RelCertifier.VerdictsV2.expectedSuiteV2
      let (okWF, wfLine) ← match ← RelCertifier.Z3Config.discover with
        | .error err => IO.eprintln s!"ERROR: {err}"; pure (false, s!"not run ({err})")
        | .ok cfg => do
            let (t, okParse) ← RelCertifier.WellFormed.runWellformed cfg paths
            let line := s!"{t.modes - t.failing}/{t.modes} right modes ok, both clauses \
({t.inv} invariant, {t.exit} exit), {t.unknown} UNKNOWN, {t.blocking} BLOCKING"
            if paths.length != e.paths then
              IO.println s!"  [wellformed] {line} over {paths.length} path(s) — tally not \
enforced (the declared suite is {e.paths} paths); a mode not ok still fails"
              pure (okParse && t.failing == 0, line)
            else if okParse && t.modes == e.wfModes && t.unknown == e.wfUnknown &&
                t.blocking == e.wfBlocking then
              IO.println s!"  [wellformed] STRICT: {line} — matches the declared suite \
({e.wfModes} modes, {e.wfUnknown} UNKNOWN, {e.wfBlocking} BLOCKING)"
              pure (true, line)
            else
              IO.eprintln s!"  [wellformed] STRICT: {line}, but the declared suite is \
{e.wfModes} modes, {e.wfUnknown} UNKNOWN, {e.wfBlocking} BLOCKING"
              pure (false, line)
      IO.println ""
      IO.println s!"  suite_v2: {if okSuite then "PASS" else "FAIL"}"
      IO.println s!"  verdicts: {if okVerd then "PASS" else "FAIL"}"
      IO.println s!"  wellformed (strict): {if okWF then "PASS" else "FAIL"} ({wfLine})"
      if okSuite && okVerd && okWF then
        IO.println "SUITE_V2 QUICK CHECKS PASSED  (the kernel check is `lake build`)"
      else
        IO.eprintln "SUITE_V2 QUICK CHECKS FAILED"; IO.Process.exit 1
  -- Reject unknown flags rather than treating them as benchmark paths, so that a mistyped
  -- option is reported as a bad command, not as a missing file.
  | _ =>
      match args.find? (fun a => a.startsWith "-") with
      | some bad =>
          IO.eprintln s!"ERROR: unknown option '{bad}'\n"
          IO.eprintln usage
          IO.Process.exit 2
      | none => runBatch args
