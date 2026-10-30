# Checking the artifact end to end

This is the reproduction recipe: starting from the benchmark files, what to run, and what
you should see, to confirm that every suite_v2 benchmark carries a machine-checked
Theorem 3 (the paper's Soundness of Synthesis) whose hypotheses all hold. Read `README.md` first for what the theorems say.

> **Last run:** 2026-10-29, branch `benchmark-fixes` after the merge of branch `stutter` (opt-in stretch 0, `docs/STUTTER.md`) and `lit_nahs25_salt_tank` set to the source's Def. 8 distance 0 with `stutter = true` (`docs/OVERNIGHT-2026-10-29.md` "Stutter merge (2026-10-29)"). All green: `lake build` exit 0 (library and the five executables, no `sorry`); `--check-quick-v2` 50 certified, modal 1162/1162, handoff 2827/2827, non-connection 44/44, pruned 22/22, reposition 74/74, strict gate 181/181 (80 invariant, 101 exit); one domain PASS (48 + 2 kind (iii)); `relcert-test` ALL PASS; bridge 7437/7437; progress 194/194; refute 206/206 (75 instances); WellFormedBattery 66 lines at the three standard axioms (plus the 11 `CutLiftX` replay lines), AxiomCheck 9; the three negatives DECLINED; `lit_hypercert_vehicle_s8` BLOCKING / DECLINED under strict; `scripts/stutter_tests.py` 91/91; stutter demo 54/54 groups.

---

## 0. The chain being checked

```
benchmarks/suite_v2/<b>/input.txt                the benchmark, as text
   │ strict parser (Trusted/Parse.lean, IN the trust base)
   ▼
InstancesV2/BenchIR/<b>.lean  `<b>_IRv2`         the emitted IR literal
   │ ▲ relcert-test [ir-drift-v2]: re-parse and compare              ← check 4
   │   (+ BenchCovers, BenchProgress, Cuts, BenchChoice: the emitted records)
   ▼
InstancesV2/Bridge/<B>.lean  `<b>_bridge`        the generic-bridge instance (generated):
   │ Lean kernel; structural facts by decide +kernel                 ← check 1
   │ Assumption 1 from InstancesV2/WellFormed/<B>.lean (transported, lifted)   ← check 5
   ▼
windowClaim / keyedClaim (rvalid (theorem3Form …) over rightAutomatonBodyC)
   │ #print axioms (InstancesV2/WellFormedBattery.lean, InstancesV2/AxiomCheck.lean)  ← check 2
   ▼
[propext, Classical.choice, Quot.sound] (+ z3_unsat_sound through the `Verdicts` hypothesis)
   │ relcert-bridge-verdicts: `Verdicts` IS the group list it issues    ← check 6
   ▼
every verdict group: Z3 says unsat
```

Until 2026-10-22 the chain ran through the standalone instances (`InstancesV2/Modal/<B>.lean`,
`Instances/<B>Guarded.lean`, audited by `InstancesV2/BatteryV2.lean`, their packs discharged by
`relcert --run-verdicts-v2`); that route is archived on branch `archive/legacy-2026-10`
(`docs/CLEANUP-SCOPE.md`, planning record, last present at commit 29663d8).

Trusted and not discharged by any check below: the parser, the lowering, the SMT printer
and Z3's `unsat` (axiom `z3_unsat_sound`), the Lean kernel, and the model assumptions of
the transition semantics (README, "Trust base").

## What you need

The Lean toolchain of `lean-toolchain` (elan fetches it; `lake` fetches the pinned dL-rel
dependency and its Mathlib), and Z3 (looked up at `/opt/homebrew/bin/z3`,
`/usr/local/bin/z3`, `/usr/bin/z3`, or `RELCERT_Z3`). Nothing else: the emitted data the
theorems consume is in the repository.

## The checks at a glance

| # | what it establishes | command |
|---|---|---|
| 1 | every proof kernel-checks (the root imports the proof chain, the Assumption 1 battery, the bridge and the refutation instances) | `lake build` (see *Cost*), then `lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts` |
| 2 | the axiom audit of the Assumption 1 battery and of the generic theorems | `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 \| grep -A3 "depends on axioms"`; the same for `RelCertifier.InstancesV2.AxiomCheck` |
| 3 | the 50 files certify in the strict well-formedness mode (declared 50 / 0 / 0), the tool's own queries hold (modal, handoff, non-connection, pruned edges, reposition, against declared counts), and the tool's Assumption 1 check (both clauses, nonblocking and complete, since 2026-10-26) finds every right mode `ok` (declared 181 modes, 0 `UNKNOWN`, 0 `BLOCKING`) | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt` |
| 3a | one physical evolve domain per benchmark: every suite_v2 file has the same `evolve` text on every mode of both sides (owner's rule of 2026-10-29: physical constraints only, never set points, asymptotes or reachable-set bands), except the files whitelisted in the script for kind (iii) (one trip setting in two reading scales, `train_ato_odometry`, `turbine_startup_gearratio`), each with a header line `# Domain conversion (kind iii):` stating the conversion; expected `ONE DOMAIN: PASS (50 benchmarks: 48 with one evolve domain, 2 kind (iii) with a stated conversion)` | `python3 scripts/check_one_domain.py` |
| 3' | the expected DECLINEs (the leaky FREEDM controller, the leaky CSF 2021 car, the CSF 2021 bus with reversed arbitration: all three `DECLINED`) | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt` |
| 3'' | the expected Assumption 1 failure (`lit_hypercert_vehicle_s8`, a self-contained right model that blocks at `s = 8`; its suite benchmark is in `benchmarks/skipped/` since 2026-10-28): all five right modes `BLOCKING`, DECLINED under the strict switch | `./.lake/build/bin/relcert --wellformed benchmarks/negative_wellformed/*/input.txt`; `RELCERT_IMPLIED_CUT=1 RELCERT_WELLFORMED_STRICT=1 ./.lake/build/bin/relcert benchmarks/negative_wellformed/*/input.txt` |
| 4 | each file parses to the literal the theorems quote; parser, printer, Z3-layer and determinism tests | `BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test` |
| 5 | Assumption 1 of every right model (`WellFormedR`): proved for all 50, none refuted; axiom audit; the tool's check, strict in check 3 | `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 \| grep -A3 "depends on axioms"`; `./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt` |
| 6 | every Z3 hypothesis of the generic bridge instances (`InstancesV2/Bridge/`, 52 `*_bridge` theorems: stays, non-connection pairs, flow and reposition packs, admissibility, handoffs, progress, coverage) holds, against the declared total 7433 over the 50 suite benchmarks and the 2 choice exhibits; every query is sent at the instance's dimension `bridgeDimV2 b` (`VerdictsV2/RunBridge.lean:74`: the Assumption 1 lemma's dimension plus one, the right clock of the clocked right automaton `rightAutomatonBodyC`), which is the dimension the instance's `Verdicts` hypothesis names | `./.lake/build/bin/relcert-bridge-verdicts` |
| 7 | the progress certificates (the paper's reposition certificates, Definition 7) of every reposition node (194 queries) hold, against the declared count | `./.lake/build/bin/relcert-progress-verdicts` |
| 8 | the 75 kernel refutations (`InstancesV2/Refute/`, `docs/REFUTATION-RESULTS.md`): every Z3 group of `RefVerdicts` holds against the declared total 206, each instance at its benchmark's bridge dimension (`RefRec.dim + 1`, `InstancesV2/Refute/Table.lean`), and each instance concludes `¬ keyedClaim … 0 1 2 3 dt` / `¬ windowClaim … 0 1 2 dt`, the negation of the clocked bridge claim at that dimension (`refute_keyed_C/A/B_clocked`, `refute_window_B_clocked`) | `./.lake/build/bin/relcert-refute-verdicts`; `lake build RelCertifier.InstancesV2.Refute` |

The totals 4457 and 188 are unchanged by the dimension change of 2026-10-21 (branch
`clocked-right`): the padded coordinate is unbound in every lowered formula, so no query reads
it and every group is the same script as before. The trust base is unchanged: parser, lowering,
printer, Z3 `unsat`, kernel (`README.md`, "Trust base"); the axiom set stays `propext`,
`Classical.choice`, `Quot.sound`, `z3_unsat_sound`.

## Check 1: the kernel checks every proof

```bash
lake build          # the library root imports InstancesV2.{WellFormedBattery,Bridge,Refute,AxiomCheck}
lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts
```

Expected: `Build completed successfully` for both, and no `declaration uses 'sorry'` in the
log (`grep -c "declaration uses 'sorry'"` prints 0).

### Cost

Since the standalone instances were archived (2026-10-22) no module of the tree takes more
than about a minute: on the 2026-10-22 run (Apple M2 Max, incremental after the archive) the
heaviest modules were the 12-dimensional Assumption 1 proofs
`InstancesV2/WellFormed/{RoverRollover6to7,RoverAttitude8to12,RoverRollover6to12,
RoverLateral8to12,RoverLateral6to8,RoverAttitude6to8,RoverTerrain6to12,RoverTerrain6to8}`
at 30 to 35 s each (the terrain chain's proofs were rewritten on 2026-10-26, `RoverTerrain6to8` is
now `RoverTerrain4to6`; they take about 20 s; the rollover, attitude and lateral files left the suite on 2026-10-27, batch I3, and the reinstalled `RoverLadder8to12` is the heaviest ladder proof); a plain `lake build` is enough. The last full measurement of the
pre-cleanup tree (2026-10-10, every module invalidated: 64 min 45 s wall, the archived
standalone instances between 154 s and 651 s each at up to 15.6 GB) is in this file's history
on branch `archive/legacy-2026-10`. A build from a cold tree also compiles dL-rel and the
Mathlib subset it imports first; that part was not re-measured.

Practical notes:

* `lake build <Module>` builds one module and what it imports; `lake build` the rest.
* Run long builds detached and log to a file (`tee`, not `tail`).
* Killing `lake build` can orphan Lean workers; follow up with
  `pkill -f "lake build"; pkill -9 -f "leanprover--lean4"`.
* To check one file against already-built dependencies: `lake env lean <file>`.
* An edit to anything under `Proofs/`, `Checker/` or `Trusted/` (comments included)
  invalidates every instance downstream.

## Check 2: the axiom audit

```bash
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
lake build RelCertifier.InstancesV2.AxiomCheck 2>&1 | grep -A3 "depends on axioms"
```

Use `-A3`: a four-axiom list prints over four lines. Expected from `WellFormedBattery.lean`:
66 lines (check 5 lists them), each exactly `[propext, Classical.choice, Quot.sound]` (`lake`
also replays the 11 lines of `Proofs/Soundness/CutLiftX.lean`'s own audit, which carry
`z3_unsat_sound`). Expected from `AxiomCheck.lean`: 9 lines, the generic theorems
`cover_sound`, `check_sound`, `theorem3_faithful`, `rvalid_from_cert`,
`decideCovered_implies_theorem3_faithful`, `stratified_barrier_sound` at the three standard
axioms and `flow_certified`, `segPres_from_flowCert`, `cut_hcert` at the three plus
`z3_unsat_sound`. No `sorryAx`, no other axiom. The bridge instances print no audit of their
own: their only Z3 leaf is the `Verdicts` hypothesis (check 6). The pre-cleanup audit of the
standalone battery (`BatteryV2`, 72 lines) is on branch `archive/legacy-2026-10`.

## Check 3: certify the suite and discharge the verdict hypotheses

```bash
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
```

`--check-quick-v2` refuses to run without `RELCERT_IMPLIED_CUT=1` (6 suite_v2 benchmarks
DECLINE without the widened cut channel, measured 2026-10-29). Check 1/3 certifies in the STRICT well-formedness
mode (`RELCERT_WELLFORMED_STRICT` forced on: a CERTIFIED file with an `UNKNOWN` or `BLOCKING`
right mode is DECLINED, a `[wellformed]` line per file on stderr); check 3/3 is the
`--wellformed` report, gated. Expected tail:

```
  [suite_v2] 50 certified, 0 declined, 0 error(s) — matches the declared suite
  [coverage] suite_v2 modal: 1162/1162 hypotheses discharged
  [coverage] suite_v2 handoff: 2827/2827 hypotheses discharged
  [coverage] suite_v2 non-connection: 44/44 hypotheses discharged
  [coverage] suite_v2 pruned edges: 22/22 hypotheses discharged
  [coverage] suite_v2 reposition (dyn): 74/74 hypotheses discharged
[wellformed] summary: 50 benchmark(s), 181 right mode(s): 80 ok (invariant), 101 ok (exit), 0 UNKNOWN (0 of them nonblocking), 0 BLOCKING (0 benchmark(s) with a mode not ok); both clauses checked; 12326 queries
  [wellformed] STRICT: 181/181 right modes ok, both clauses (80 invariant, 101 exit), 0 UNKNOWN, 0 BLOCKING — matches the declared suite (181 modes, 0 UNKNOWN, 0 BLOCKING)

  suite_v2: PASS
  verdicts: PASS
  wellformed (strict): PASS (181/181 right modes ok, both clauses (80 invariant, 101 exit), 0 UNKNOWN, 0 BLOCKING)
SUITE_V2 QUICK CHECKS PASSED  (the kernel check is `lake build`)
```

The well-formedness gate (check 5's tool part, strict since 2026-10-10; it was informational
while 9 models blocked): the declared mode count `ExpectedSuiteV2.wfModes = 181`
(`VerdictsV2/RunV2.lean`; its kernel pin against the IR table, `CoveragePinsV2`, was archived
with the standalone route), `wfUnknown = 0` and `wfBlocking = 0`; any `UNKNOWN` or `BLOCKING`
mode, a mode count off the declared one, or a file that does not parse fails the run. The
gate checks both clauses of Assumption 1 per right mode (since 2026-10-26; before, only the
successor clause, so a right model that blocks at a domain bound passed): from every guard
state the flow stays in the evolve domain for one control interval and cannot blow up
(nonblocking), and every evolution of at most one interval ends in a declared successor's
guard (complete). It is sufficient, not necessary, and outside the guarantee, whose
Assumption 1 is the kernel's `WellFormedR` (check 5).

The coverage phases re-send the tool's own queries (`VerdictsV2/{ModalX,ModalDynX}`,
`Trusted/NonConnQuery`, `Verdicts/RunHandoff`) against the declared counts of
`VerdictsV2/RunV2.lean`; the theorems' own Z3 leaves are the bridge groups of check 6. A phase
that discharged fewer (or more) queries than declared fails the run; anything the runner
cannot rebuild is a `SKIP`/`FAIL`, never a pass. The expected DECLINE: `RELCERT_IMPLIED_CUT=1
./.lake/build/bin/relcert benchmarks/negative/*/input.txt` prints `lit_csf21_vehicle_bus_thermoprio:
DECLINED`, `lit_csf21_vehicle_thermo_leaky: DECLINED` and `lit_freedm_meter_leaky: DECLINED`, `errors=0`.

## Check 4: the files match the IR the theorems quote

```bash
for d in benchmarks/suite_v2/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"
done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test
```

Expected: `ok   all 50 suite_v2 IR literals match their files (50 files)` and a bare `ALL PASS`
(the table must name exactly the benchmark directories of `benchmarks/suite_v2`).
Without `BENCH_PATHS` the two determinism checks (`gantry_speed_zones` 8× CERTIFIED;
`engine_start_highidle`, which declines without the widened channel, 8× the same verdict) are
skipped and the last line says `ALL PASS (2 SKIPPED …)`.

## Check 5: Assumption 1, verified per benchmark

```bash
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt
```

Expected: 66 axiom lines from `WellFormedBattery.lean`, each exactly `[propext,
Classical.choice, Quot.sound]` (no `z3_unsat_sound`: every proof is Z3-free): 50 right
models (43 `<b>_wellFormedR`, 3 `<b>_wellFormedR_direct` for the two dRL benchmarks and
`lit_freedm_meter` (`lit_hypercert_vehicle`'s line went with the benchmark, 2026-10-28), and the 3 satellites' `<b>_wellFormedR`,
unconditional since 2026-10-15), the three satellites' `<b>_band_invariant`, and
13 generic lemmas (`wellFormedR_terrain`, `wellFormedR_switchLegal`, `not_wellFormedR_of_run`,
`not_wellFormedR_of_noRun`, `exists_contract_run`, `exists_rate_run`,
`exists_of_HExistSegB_zero`, `coord_le_barrier`, `affine_const`, the platoon follower's
`PlatoonCaccAeb.cacc_w_band`, `PlatoonCaccAeb.aeb_w_const`, `PlatoonCaccAeb.cacc_box`,
`WellFormedBattery.wf_coverage`; the declared counts `(47, 0, 3)`, `(30, 9, 6)` before the repairs, and the three name lists a
permutation of the suite's IR table). Each proof lives in its own self-contained
`InstancesV2/WellFormed/<B>.lean` (right model and proof; since 2026-10-22 the 19 carried-over
ones too). The tool line: `[wellformed] summary: 50 benchmark(s), 172 right mode(s): 87 ok
(invariant), 85 ok (exit), 0 UNKNOWN (0 of them nonblocking), 0 BLOCKING (0 benchmark(s) with
a mode not ok); both clauses checked`; check 3 gates it. What this establishes and what it does
not (the tool's check is sufficient, of both clauses since 2026-10-26, of the successor clause
only before; the predicate's domain conjunct; the satellites' band): `docs/WELLFORMED.md`. The repairs:
`docs/SUITE-REDESIGN.md` §21.

**Nonblocking negative check** (2026-10-26; the suite benchmark named here is in `benchmarks/skipped/` since 2026-10-28, the exhibit is self-contained): `--check-quick-v2` over the suite with
`benchmarks/negative_wellformed/lit_hypercert_vehicle_s8` (a right model that blocks at `s = 8`) in
place of `lit_hypercert_vehicle`: check 1 `49 certified, 1 declined, 0 error(s) but the declared
suite is 50/0/0` (`[wellformed] STRICT: lit_hypercert_vehicle_s8 DECLINED (a BLOCKING right
mode)`), check 3 `169/174 right modes ok, both clauses (90 invariant, 79 exit), 0 UNKNOWN, 5
BLOCKING`, `SUITE_V2 QUICK CHECKS FAILED`, exit 1. With the successor clause alone the same
file passed the gate (all five modes `ok`).

**Stutter (opt-in stretch 0)** (2026-10-29, branch `stutter`, `docs/STUTTER.md`): the
`[problem] stutter = true` key lets a joint segment run at stretch 0 (the right waits). No
suite_v2 file sets it, and with every input unchanged the covers, verdicts (control and six
switch runs, the exhibits) and `--check-quick-v2` output are byte-identical to `de241c5`. Without
the key the CLI never certifies with a stretch-0 pairing (`λ_min = 0` alone now declines where it
used to certify unbacked). Tests: `python3 scripts/stutter_tests.py` (91/91, incl. the 78
negatives with the key, all DECLINED); end to end: `python3 scripts/gen_stutter_demo.py`,
`lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter`, `lake env lean
scripts/stutter_demo_verdicts.lean` (54/54 groups): the salt tank at band 0.

**Strict-gate negative check** (2026-10-10): `--check-quick-v2` over the suite with the
pre-repair `platoon_delay_linkloss` in its place: check 1 `44 certified, 1 declined, 0
error(s) but the declared suite is 45/0/0` (`[wellformed] STRICT: platoon_delay_linkloss
DECLINED`), check 3 `145/146 right modes ok … 1 UNKNOWN`, `SUITE_V2 QUICK CHECKS FAILED`,
exit 1.

**Regression of the repair pass** (2026-10-10): `--emit-ir`, `--emit-cover`, `--emit-cuts`
(the last two with `RELCERT_IMPLIED_CUT=1`) of the 36 untouched files byte-identical, stdout
and stderr, against the binary of `5dd8798` (108 outputs); regenerating every data leaf
(`scripts/gen_v2_data.py` over all 50) leaves the committed leaves unchanged; the
non-connection pruning extension (a compound successor guard pruned on its strict leading
conjunct) touches no other file (none has such a guard); the full matrix re-run changes no
cell of the 36.

## Per-benchmark inventory

"std 3" = `[propext, Classical.choice, Quot.sound]`. Every instance is generated by
`scripts/gen_bridge.py` (the strict exhibit `WatertankStrict` by `scripts/gen_strict_demo.py`)
and states `<b>_bridge : Verdicts p n cX cov prog → dt ≤ εL → windowClaim … 0 1 2 dt` (or
`keyedClaim … 0 1 2 3 dt`): Theorem 3 with the paper's left program (`leftAutomatonBody`) over
the clocked guarded right automaton (`rightAutomatonBodyC`) at dimension `bridgeDimV2 b`, the
loop invariant carrying `guard ∧ cuts` of the right's current mode (`regionG`: the paper's
operating region `op_R` with the mode facts of Definition 2, the tool's checked cuts), every
switch kernel-checked legal. The one Z3 hypothesis `Verdicts` is the group list
`relcert-bridge-verdicts` issues for the benchmark (check 6); Assumption 1 comes from the
benchmark's `WellFormedR` lemma (check 5), transported and lifted. The pre-cleanup inventory of
the standalone instances (their files, theorem names and pack counts) is in this file's history
on branch `archive/legacy-2026-10`.

| benchmark | file | theorem | form | Assumption 1 from | hypothesis | axioms |
|---|---|---|---|---|---|---|
| `acc_spoof_lag` | `InstancesV2/Bridge/AccSpoofLag.lean` | `acc_spoof_lag_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/AccSpoofLag.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `acc_spoof_limp` | `InstancesV2/Bridge/AccSpoofLimp.lean` | `acc_spoof_limp_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/AccSpoofLimp.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `acc_tune_lag` | `InstancesV2/Bridge/AccTuneLag.lean` | `acc_tune_lag_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/AccTuneLag.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `acc_tune_limp` | `InstancesV2/Bridge/AccTuneLimp.lean` | `acc_tune_limp_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/AccTuneLimp.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `bottling_fill_strainer` | `InstancesV2/Bridge/BottlingFillStrainer.lean` | `bottling_fill_strainer_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/BottlingFillStrainer.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `charger_fast_tapers` | `InstancesV2/Bridge/ChargerFastTapers.lean` | `charger_fast_tapers_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/ChargerFastTapers.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_csf21_vehicle_bus` | `InstancesV2/Bridge/LitCsf21VehicleBus.lean` | `lit_csf21_vehicle_bus_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitCsf21VehicleBus.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_csf21_vehicle_thermo` | `InstancesV2/Bridge/LitCsf21VehicleThermo.lean` | `lit_csf21_vehicle_thermo_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitCsf21VehicleThermo.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_csf25_salt_tank_hold` | `InstancesV2/Bridge/LitCsf25SaltTankHold.lean` | `lit_csf25_salt_tank_hold_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/LitCsf25SaltTankHold.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_drl_lane_control` | `InstancesV2/Bridge/LitDrlLaneControl.lean` | `lit_drl_lane_control_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitDrlLaneControl.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `elevator_start_discbrake` | `InstancesV2/Bridge/ElevatorStartDiscbrake.lean` | `elevator_start_discbrake_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/ElevatorStartDiscbrake.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `engine_start_highidle` | `InstancesV2/Bridge/EngineStartHighidle.lean` | `engine_start_highidle_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/EngineStartHighidle.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `flaps_slow_approach` | `InstancesV2/Bridge/FlapsSlowApproach.lean` | `flaps_slow_approach_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FlapsSlowApproach.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_freedm_meter` | `InstancesV2/Bridge/LitFreedmMeter.lean` | `lit_freedm_meter_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitFreedmMeter.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `fuelcell_chp_dos` | `InstancesV2/Bridge/FuelcellChpDos.lean` | `fuelcell_chp_dos_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FuelcellChpDos.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `furnace_program_timebase` | `InstancesV2/Bridge/FurnaceProgramTimebase.lean` | `furnace_program_timebase_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FurnaceProgramTimebase.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `gantry_speed_zones` | `InstancesV2/Bridge/GantrySpeedZones.lean` | `gantry_speed_zones_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/GantrySpeedZones.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_girard08_robot` | `InstancesV2/Bridge/LitGirard08Robot.lean` | `lit_girard08_robot_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitGirard08Robot.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_gpt10_boost_converter` | `InstancesV2/Bridge/LitGpt10BoostConverter.lean` | `lit_gpt10_boost_converter_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitGpt10BoostConverter.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `canal_gate_notches` | `InstancesV2/Bridge/CanalGateNotches.lean` | `canal_gate_notches_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/CanalGateNotches.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `h2_refuel_ambientbias` | `InstancesV2/Bridge/H2RefuelAmbientbias.lean` | `h2_refuel_ambientbias_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/H2RefuelAmbientbias.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `hydro_rejection_gatecal` | `InstancesV2/Bridge/HydroRejectionGatecal.lean` | `hydro_rejection_gatecal_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/HydroRejectionGatecal.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_lz21_vehicle_position` | `InstancesV2/Bridge/LitLz21VehiclePosition.lean` | `lit_lz21_vehicle_position_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitLz21VehiclePosition.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `platoon_latency` | `InstancesV2/Bridge/PlatoonLatency.lean` | `platoon_latency_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/PlatoonLatency.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `platoon_linkloss` | `InstancesV2/Bridge/PlatoonLinkloss.lean` | `platoon_linkloss_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/PlatoonLinkloss.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `platoon_profiles` | `InstancesV2/Bridge/PlatoonProfiles.lean` | `platoon_profiles_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/PlatoonProfiles.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `quad_light_lag` | `InstancesV2/Bridge/QuadLightLag.lean` | `quad_light_lag_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/QuadLightLag.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `quad_light_profiles` | `InstancesV2/Bridge/QuadLightProfiles.lean` | `quad_light_profiles_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/QuadLightProfiles.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rampmeter_poll_2to1` | `InstancesV2/Bridge/RampmeterPoll2to1.lean` | `rampmeter_poll_2to1_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RampmeterPoll2to1.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `reactor_feed_wireless` | `InstancesV2/Bridge/ReactorFeedWireless.lean` | `reactor_feed_wireless_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/ReactorFeedWireless.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_2to3` | `InstancesV2/Bridge/RoverLadder2to3.lean` | `rover_ladder_2to3_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder2to3.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_3to6` | `InstancesV2/Bridge/RoverLadder3to6.lean` | `rover_ladder_3to6_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder3to6.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_6to8` | `InstancesV2/Bridge/RoverLadder6to8.lean` | `rover_ladder_6to8_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder6to8.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_8to12` | `InstancesV2/Bridge/RoverLadder8to12.lean` | `rover_ladder_8to12_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder8to12.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_patrol_lag` | `InstancesV2/Bridge/RoverPatrolLag.lean` | `rover_patrol_lag_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverPatrolLag.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_terrain_2to4` | `InstancesV2/Bridge/RoverTerrain2to4.lean` | `rover_terrain_2to4_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverTerrain2to4.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_terrain_4to6` | `InstancesV2/Bridge/RoverTerrain4to6.lean` | `rover_terrain_4to6_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverTerrain4to6.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_terrain_6to12` | `InstancesV2/Bridge/RoverTerrain6to12.lean` | `rover_terrain_6to12_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverTerrain6to12.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `lit_nahs25_salt_tank` | `InstancesV2/Bridge/LitNahs25SaltTank.lean` | `lit_nahs25_salt_tank_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/LitNahs25SaltTank.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `sat3w_detumble_phases` | `InstancesV2/Bridge/Sat3wDetumblePhases.lean` | `sat3w_detumble_phases_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/Sat3wDetumblePhases.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `sat_detumble_phases` | `InstancesV2/Bridge/SatDetumblePhases.lean` | `sat_detumble_phases_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/SatDetumblePhases.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `sat_detumble_weak` | `InstancesV2/Bridge/SatDetumbleWeak.lean` | `sat_detumble_weak_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/SatDetumbleWeak.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `syringe_relay_prearm` | `InstancesV2/Bridge/SyringeRelayPrearm.lean` | `syringe_relay_prearm_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/SyringeRelayPrearm.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `tank_dos_3to1` | `InstancesV2/Bridge/TankDos3to1.lean` | `tank_dos_3to1_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/TankDos3to1.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `train_ato_odometry` | `InstancesV2/Bridge/TrainAtoOdometry.lean` | `train_ato_odometry_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/TrainAtoOdometry.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `antenna_track_kvretune` | `InstancesV2/Bridge/AntennaTrackKvretune.lean` | `antenna_track_kvretune_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/AntennaTrackKvretune.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `turbine_startup_gearratio` | `InstancesV2/Bridge/TurbineStartupGearratio.lean` | `turbine_startup_gearratio_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/TurbineStartupGearratio.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `vehicle_accel_copy` | `InstancesV2/Bridge/VehicleAccelCopy.lean` | `vehicle_accel_copy_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/Choice/General/VehicleAccelCopy.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `ventilator_vc_cuffleak` | `InstancesV2/Bridge/VentilatorVcCuffleak.lean` | `ventilator_vc_cuffleak_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/VentilatorVcCuffleak.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `watertank_choice` | `InstancesV2/Bridge/WatertankChoice.lean` | `watertank_choice_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/Choice/General/WatertankChoice.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `watertank_strict` | `InstancesV2/Bridge/WatertankStrict.lean` | `watertank_strict_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/Watertank.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `watertank_twospeed` | `InstancesV2/Bridge/WatertankTwospeed.lean` | `watertank_twospeed_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/WatertankTwospeed.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `watertank` | `InstancesV2/Bridge/Watertank.lean` | `watertank_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/Watertank.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |

## One-shot (after creating the manifest of check 4)

```bash
lake build && lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts \
  && lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms" \
  && lake build RelCertifier.InstancesV2.AxiomCheck 2>&1 | grep -A3 "depends on axioms" \
  && RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt \
  && python3 scripts/check_one_domain.py \
  && RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt \
  && BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test \
  && ./.lake/build/bin/relcert-bridge-verdicts \
  && ./.lake/build/bin/relcert-refute-verdicts \
  && ./.lake/build/bin/relcert-progress-verdicts
```

A green build, an axiom listing with nothing beyond the four axioms, `SUITE_V2 QUICK CHECKS
PASSED`, `ONE DOMAIN: PASS`, `ALL PASS`, `7437/7437`, `194/194` and `206/206` = every suite_v2 benchmark is
certified end to end, modulo the trust base.

## Earlier recipes

Until 2026-10-10 this document described the legacy suite (`suite_uniform`) and its
checks (`--check-quick`, `--run-verdicts`, `Instances/ModalBattery.lean`), with dated
records of full runs (the last cold-tree build of that development: 2026-08-02, 12h59m,
8988 jobs). That suite and those entry points were removed; the records are in the git
history of this file. Until 2026-10-22 it described the standalone route (`BatteryV2`,
`relcert --run-verdicts-v2`, `relcert-choice-verdicts`, the per-benchmark inventory of the
hand-written instances); that route is archived on branch `archive/legacy-2026-10`.
