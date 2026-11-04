# Checking the artifact end to end

This is the reproduction recipe of the paper's Appendix B.7: starting from the benchmark files,
what to run and what you should see, to confirm that every benchmark of `benchmarks/suite_v2`
carries a machine-checked instance of Theorem 3 (Soundness of Synthesis) whose hypotheses all
hold. Read `README.md` first for what the theorems say; `docs/PAPER-MAPPING.md` maps the paper
to the Lean names.

> **Last full run** (the state of the paper's frozen numbers, `docs/paper-numbers/MANIFEST.txt`).
> All green: `lake build`, no `sorry`; `--check-quick-v2` 50 certified, modal 1421/1421, handoff
> 2846/2846, non-connection 32/32, pruned 16/16, reposition 950/950, strict gate 181/181 (75
> invariant, 106 exit), PASSED; `relcert-test` ALL PASS (50 IR literals); bridge 13677/13677;
> progress 1009/1009; refute 416/416 (140 instances); WellFormedBattery 78 axiom lines (2 with
> `z3_unsat_sound`), AxiomCheck 16 (7 with `z3_unsat_sound`), no `sorryAx`; negatives DECLINED;
> `lit_hypercert_vehicle_s8` BLOCKING, DECLINED under strict; ONE DOMAIN PASS; stutter tests
> 172/172, prelanding tests 179/179; demo verdicts 54/54, 18/18, 15/15, 90, progress demo 92/92
> with 24/24 adversarial certificates DECLINED.

---

## 0. The chain being checked

```
benchmarks/suite_v2/<b>/input.txt                the benchmark, as text
   │ strict parser (Trusted/Parse.lean, IN the trust base)
   ▼
InstancesV2/BenchIR/<b>.lean  `<b>_IRv2`         the emitted IR literal
   │ ▲ relcert-test [ir-drift-v2]: re-parse and compare              ← check 4
   │   (+ BenchCovers, BenchProgress, BenchPrelanding, Cuts, BenchChoice: the emitted records)
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

Trusted and not discharged by any check below: the parser, the lowering, the SMT printer
and Z3's `unsat` (axiom `z3_unsat_sound`), the Lean kernel, and the statement of Theorem 3
(README, "Trust base"). The earlier route through hand-written standalone instances is
archived on branch `archive/legacy-2026-10`.

## What you need

The Lean toolchain of `lean-toolchain` (elan fetches it; `lake` fetches the pinned dL-rel
dependency and its Mathlib), and Z3 4.15.1 (looked up at `/opt/homebrew/bin/z3`,
`/usr/local/bin/z3`, `/usr/bin/z3`, or `RELCERT_Z3`). Nothing else: the emitted data the
theorems consume is in the repository.

## The checks at a glance

| # | what it establishes | command |
|---|---|---|
| 1 | every proof kernel-checks (the root imports the proof chain, the Assumption 1 battery, the 52 bridge instances, the 5 demo and strict bridge files, and the 140 refutation instances) | `lake build`, then `lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts` |
| 2 | the axiom audit of the Assumption 1 battery and of the generic theorems | `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 \| grep -A3 "depends on axioms"`; the same for `RelCertifier.InstancesV2.AxiomCheck` |
| 3 | the 50 files certify in the strict well-formedness mode (declared 50 / 0 / 0), the tool's own queries hold (modal, handoff, non-connection, pruned edges, reposition, against declared counts), and the tool's Assumption 1 check (both clauses, nonblocking and complete) finds every right mode `ok` (declared 181 modes, 0 `UNKNOWN`, 0 `BLOCKING`) | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt` |
| 3a | one physical evolve domain per benchmark: every suite_v2 file has the same `evolve` text on every mode of both sides (physical constraints only, never set points, asymptotes or reachable-set bands), except the two files whitelisted in the script (`train_ato_odometry`, `turbine_startup_gearratio`: one trip setting in two reading scales), each with a header line `# Domain conversion (kind iii):` stating the conversion; expected `ONE DOMAIN: PASS (50 benchmarks: 48 with one evolve domain, 2 kind (iii) with a stated conversion)` | `python3 scripts/check_one_domain.py` |
| 3' | the expected DECLINEs (the leaky FREEDM controller, the leaky CSF 2021 car, the CSF 2021 bus with reversed arbitration: all three `DECLINED`) | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt` |
| 3'' | the expected Assumption 1 failure (`lit_hypercert_vehicle_s8`, a self-contained right model that blocks at `s = 8`): all five right modes `BLOCKING`, DECLINED under the strict switch | `./.lake/build/bin/relcert --wellformed benchmarks/negative_wellformed/*/input.txt`; `RELCERT_IMPLIED_CUT=1 RELCERT_WELLFORMED_STRICT=1 ./.lake/build/bin/relcert benchmarks/negative_wellformed/*/input.txt` |
| 4 | each file parses to the literal the theorems quote; parser, printer, Z3-layer and determinism tests | `BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test` |
| 5 | Assumption 1 of every right model (`WellFormedR`): proved for all 50, none refuted; axiom audit; the tool's check, strict in check 3 | `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 \| grep -A3 "depends on axioms"`; `./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt` |
| 6 | every Z3 hypothesis of the generic bridge instances (`InstancesV2/Bridge/`, 52 `*_bridge` theorems: stays, non-connection pairs, flow and reposition packs, admissibility, handoffs, progress, coverage) holds, against the declared total 13677 over the 50 suite benchmarks and the 2 committed-subset exhibits; every query is sent at the instance's dimension `bridgeDimV2 b` (`VerdictsV2/RunBridge.lean`: the Assumption 1 lemma's dimension plus one, the right clock of the clocked right automaton `rightAutomatonBodyC`), which is the dimension the instance's `Verdicts` hypothesis names | `./.lake/build/bin/relcert-bridge-verdicts` |
| 7 | the reposition certificates (the tool's progress certificates, Definition 7) of every reposition node (1009 groups) hold, against the declared count | `./.lake/build/bin/relcert-progress-verdicts` |
| 8 | the 140 kernel refutations (`InstancesV2/Refute/`, `docs/REFUTATION-RESULTS.md`): every Z3 group of `RefVerdicts` holds against the declared total 416, each instance at its benchmark's bridge dimension (`RefRec.dim + 1`, `InstancesV2/Refute/Table.lean`), and each instance concludes `¬ keyedClaim … 0 1 2 3 dt` / `¬ windowClaim … 0 1 2 dt`, the negation of the clocked bridge claim at that dimension (`refute_keyed_C/A/B_clocked`, `refute_window_B_clocked`) | `./.lake/build/bin/relcert-refute-verdicts`; `lake build RelCertifier.InstancesV2.Refute` |

The trust base is the same for every check: parser, lowering, printer, Z3 `unsat`, kernel
(`README.md`, "Trust base"); the axiom set is `propext`, `Classical.choice`, `Quot.sound`,
`z3_unsat_sound`.

## Check 1: the kernel checks every proof

```bash
lake build          # the library root imports the proof chain and InstancesV2.{WellFormedBattery,Bridge,Refute,AxiomCheck} and the demo bridges
lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts
```

Expected: `Build completed successfully` for both, and no `declaration uses 'sorry'` in the
log (`grep -c "declaration uses 'sorry'"` prints 0).

### Cost

On an Apple M2 Max a from-scratch build takes about 15 min (the paper's Appendix B.7); an
incremental build after an edit to an instance takes a few minutes. A build from a cold tree also compiles dL-rel and the Mathlib subset it imports.

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

Use `-A3`: a four-axiom list prints over four lines. Expected from the battery: 78 lines,
67 from `WellFormedBattery.lean` itself (check 5 lists them), each exactly `[propext,
Classical.choice, Quot.sound]`, and the 11 lines of `Proofs/Soundness/CutLiftX.lean`'s own
audit, which `lake` replays, two of which (`entry_z3`, `entryZ3Fact_of_unsat`) carry
`z3_unsat_sound`: 76 lines at the three standard axioms, 2 with `z3_unsat_sound`. Expected
from `AxiomCheck.lean`: 16 lines, the generic theorems `cover_sound`, `check_sound`,
`theorem3_faithful`, `rvalid_from_cert`, `decideCovered_implies_theorem3_faithful`,
`stratified_barrier_sound`, Lemma 1's `odeSol_stretch_iff`, `odeSol_rightBlock_stretch_iff` and
Theorem 3's generic `theorem3_of_coverX` at the three standard axioms, and `flow_certified`,
`segPres_from_flowCert`, `cut_hcert` (the flow-certificate, segment-preservation and mode-fact
lemmas) and the four record-level theorems `Emitted.theorem3_window_of_records(_pl)`,
`Emitted.theorem3_keyed_of_records(_pl)` at the three plus `z3_unsat_sound`. No `sorryAx`, no
other axiom. The bridge instances apply the record-level theorems and inherit exactly their
axioms; their only Z3 leaf is the `Verdicts` hypothesis (check 6).

## Check 3: certify the suite and discharge the verdict hypotheses

```bash
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
```

`--check-quick-v2` refuses to run without `RELCERT_IMPLIED_CUT=1` (the implied mode-fact
candidates; 5 suite benchmarks decline without them, the `NO_IMPLIED_CUT` column of
`docs/paper-numbers/matrix.log`). Check 1/3 certifies in the STRICT well-formedness mode
(`RELCERT_WELLFORMED_STRICT` forced on: a CERTIFIED file with an `UNKNOWN` or `BLOCKING` right
mode is DECLINED, a `[wellformed]` line per file on stderr); check 3/3 is the `--wellformed`
report, gated. Expected tail:

```
  [suite_v2] 50 certified, 0 declined, 0 error(s) — matches the declared suite
  [coverage] suite_v2 modal: 1421/1421 hypotheses discharged
  [coverage] suite_v2 handoff: 2846/2846 hypotheses discharged
  [coverage] suite_v2 non-connection: 32/32 hypotheses discharged
  [coverage] suite_v2 pruned edges: 16/16 hypotheses discharged
  [coverage] suite_v2 reposition (dyn): 950/950 hypotheses discharged
[wellformed] summary: 50 benchmark(s), 181 right mode(s): 75 ok (invariant), 106 ok (exit), 0 UNKNOWN (0 of them nonblocking), 0 BLOCKING (0 benchmark(s) with a mode not ok); both clauses checked; … queries
  [wellformed] STRICT: 181/181 right modes ok, both clauses (75 invariant, 106 exit), 0 UNKNOWN, 0 BLOCKING — matches the declared suite (181 modes, 0 UNKNOWN, 0 BLOCKING)

  suite_v2: PASS
  verdicts: PASS
  wellformed (strict): PASS (181/181 right modes ok, both clauses (75 invariant, 106 exit), 0 UNKNOWN, 0 BLOCKING)
SUITE_V2 QUICK CHECKS PASSED  (the kernel check is `lake build`)
```

The well-formedness gate (check 5's tool part): the declared mode count
`ExpectedSuiteV2.wfModes = 181` (`VerdictsV2/RunV2.lean`), `wfUnknown = 0` and
`wfBlocking = 0`; any `UNKNOWN` or `BLOCKING` mode, a mode count off the declared one, or a file
that does not parse fails the run. The gate checks both clauses of Assumption 1 per right
mode: from every guard state the flow stays in the evolve domain for one control interval and
cannot blow up (nonblocking), and every evolution of at most one interval ends in a declared
successor's guard (complete). It is sufficient, not necessary, and outside the guarantee,
whose Assumption 1 is the kernel's `WellFormedR` (check 5).

The coverage phases re-send the tool's own queries (`VerdictsV2/{ModalX,ModalDynX}`,
`Trusted/NonConnQuery`, `Verdicts/RunHandoff`) against the declared counts of
`VerdictsV2/RunV2.lean` (`expectedModalV2`, `expectedHandoffV2`, `expectedNonConnV2`,
`expectedPrunedEdgesV2`, `expectedDynV2`); the theorems' own Z3 leaves are the bridge groups of
check 6. A phase that discharged fewer (or more) queries than declared fails the run; anything
the runner cannot rebuild is a `SKIP`/`FAIL`, never a pass. The expected DECLINE:
`RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt` prints
`lit_csf21_vehicle_bus_thermoprio: DECLINED`, `lit_csf21_vehicle_thermo_leaky: DECLINED` and
`lit_freedm_meter_leaky: DECLINED`, `errors=0`.

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
`engine_start_highidle`, which declines without the implied mode-fact candidates, 8× the same
verdict) are skipped and the last line says `ALL PASS (2 SKIPPED …)`.

## Check 5: Assumption 1, verified per benchmark

```bash
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt
```

Expected: the 67 axiom lines of `WellFormedBattery.lean` (plus the 11 replayed from
`CutLiftX`, check 2), each exactly `[propext, Classical.choice, Quot.sound]` (no
`z3_unsat_sound`: every proof is Z3-free): the 50 right models (40 `<b>_wellFormedR`, and 10
`<b>_wellFormedR_direct` for the ten literature benchmarks, stated over the bridge's graph
directly), the three satellites' `<b>_band_invariant`, and 14 generic lemmas
(`wellFormedR_terrain`, `wellFormedR_stopline`, `wellFormedR_switchLegal`,
`not_wellFormedR_of_run`, `not_wellFormedR_of_noRun`, `exists_contract_run`,
`exists_rate_run`, `exists_of_HExistSegB_zero`, `coord_le_barrier`, `affine_const`, the platoon
follower's `PlatoonCaccAeb.cacc_w_band`, `PlatoonCaccAeb.aeb_w_const`,
`PlatoonCaccAeb.cacc_box`, and `WellFormedBattery.wf_coverage`, whose name lists are a
permutation of the suite's IR table). Each proof lives in its own self-contained
`InstancesV2/WellFormed/<B>.lean` (right model and proof). The tool line: `[wellformed]
summary: 50 benchmark(s), 181 right mode(s): 75 ok (invariant), 106 ok (exit), 0 UNKNOWN (0 of
them nonblocking), 0 BLOCKING (0 benchmark(s) with a mode not ok); both clauses checked`; check
3 gates it. What this establishes and what it does not (the tool's check is sufficient; the
predicate's domain conjunct; the satellites' momentum band): `docs/WELLFORMED.md`.

**Nonblocking negative check.** `benchmarks/negative_wellformed/lit_hypercert_vehicle_s8` is a
right model that blocks at `s = 8`. `relcert --wellformed` reports its five right modes
`BLOCKING`, and under `RELCERT_WELLFORMED_STRICT=1` the file is DECLINED (`[wellformed] STRICT:
lit_hypercert_vehicle_s8 DECLINED (a BLOCKING right mode)`). With the successor clause alone the
same file would pass the gate (all five modes `ok`).

**Stretch 0 and the pre-landing certificate.** Both are run features, on for every benchmark;
`RELCERT_NO_STUTTER=1` / `RELCERT_NO_PRELANDING=1` switch them off for an ablation
(`docs/STUTTER.md`, `docs/PRELANDING.md`; the former opt-in keys `stutter = true` /
`prelanding = true` are refused by the unknown-key gate). Stretch 0 (the witness stands still)
is a candidate only for a file whose declared stretch range includes 0 (`lambda_min = 0`,
`Run.stutterAllowed`; only `lit_nahs25_salt_tank` and the stutter demo). The emitted IR records
the run's values, which the kernel gates read (`Emitted.timeOK` admits a stretch-0 pairing only
when also `lambdaMin = 0`; `Emitted.plOK` / `Emitted.nodeStage` a pre-landing record and region,
exactly when the IR records the feature as on); the CLI guards refuse a stretch-0 pairing or a
pre-landing node with the feature off. Every right-only node is a pre-landing node (the paper's
right-only certificate on the restricted mode, `BenchPrelanding/<b>.lean` for every benchmark);
every bridge instance with right-only nodes is over the cover merged with its record
(`theorem3_window_of_records_pl`, `theorem3_keyed_of_records_pl`).

Tests: `python3 scripts/stutter_tests.py` (172/172: the salt tank demo's tight band 0 by default
and 3 under `RELCERT_NO_STUTTER=1`, the adversarial claims of `docs/STUTTER-SOUNDNESS.md`, the
retired key refused, the 140 refutation mutants and 3 negatives DECLINED by default) and
`python3 scripts/prelanding_tests.py` (179/179: the engine cooling demo's tight band 0.3, the
cause test, the strict-row demo, the adversarial synthetic files with stretch 0 off (their left
holds, so with stretch 0 on the right may wait and every one of their claims is true and
certifies; listed as such), the retired key refused, the same 143 negatives DECLINED by default).

The five demo and strict bridge files (the paper's further bridge files) are built by
`lake build`; their generators and verdict runs:

```bash
python3 scripts/gen_stutter_demo.py; python3 scripts/gen_prelanding_demo.py
python3 scripts/gen_strict_demo.py;  python3 scripts/gen_progress_demo.py
lake build RelCertifier.InstancesV2.Bridge.SaltTankStutter RelCertifier.InstancesV2.Bridge.EngineCoolingPrelanding \
  RelCertifier.InstancesV2.Bridge.HoldRepositionStrict RelCertifier.InstancesV2.Bridge.WatertankStrict \
  RelCertifier.InstancesV2.Bridge.StoplineFrictionMixed
lake env lean scripts/stutter_demo_verdicts.lean      # 54/54 groups
lake env lean scripts/prelanding_demo_verdicts.lean   # 18/18 and 15/15
lake env lean scripts/strict_demo_verdicts.lean       # 90 groups
lake env lean scripts/progress_demo_verdicts.lean     # 92/92 groups, 24/24 adversarial certificates DECLINED, 8 axiom lines
lake env lean scripts/stutter_kernel_checks.lean      # 6 axiom lines, the kernel negatives
lake env lean scripts/prelanding_kernel_checks.lean   # 8 axiom lines, the kernel negatives
```

The prelanding kernel negatives: a record with the flag off fails `plOK`, a cover without its
pre-landing nodes fails `coversOK`. The progress demo (`docs/PRELANDING.md`, "Two-stage
certificates in every direction") also checks that a three-stage certificate fails `certOK`.

## Per-benchmark inventory

Every instance is generated by `scripts/gen_bridge.py` and states `<b>_bridge : Verdicts p n cX
cov prog → dt ≤ εL → windowClaim … 0 1 2 dt` (or `keyedClaim … 0 1 2 3 dt`): Theorem 3 with the
paper's left program (`leftAutomatonBody`) over the clocked guarded right automaton
(`rightAutomatonBodyC`) at dimension `bridgeDimV2 b`, the loop invariant carrying `guard ∧ cuts`
of the right's current mode (`regionG`: the paper's operating region `op_R` with the mode facts
of Definition 2), every switch kernel-checked legal. The one Z3 hypothesis `Verdicts` is the
group list `relcert-bridge-verdicts` issues for the benchmark (check 6); Assumption 1 comes from
the benchmark's `WellFormedR` lemma (check 5), transported and lifted. Every instance rests on
the three standard axioms plus `z3_unsat_sound`. The record theorem is the window form
(`windowClaim … 0 1 2 dt`, a mode-independent invariant: 32 suite benchmarks) or the mode-keyed
form (`keyedClaim … 0 1 2 3 dt`, a mode-dependent invariant: 18), with the suffix `_pl` when
the cover has right-only nodes checked on the restricted mode (41 suite benchmarks and both
exhibits; the groups are then on the cover merged with its pre-landing record, `withPL cov pl`).

| benchmark | file | form | record theorem | Assumption 1 from |
|---|---|---|---|---|
| `acc_spoof_lag` | `InstancesV2/Bridge/AccSpoofLag.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/AccSpoofLag.lean` |
| `acc_spoof_limp` | `InstancesV2/Bridge/AccSpoofLimp.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/AccSpoofLimp.lean` |
| `acc_tune_limp` | `InstancesV2/Bridge/AccTuneLimp.lean` | mode-keyed | `theorem3_keyed_of_records` | `InstancesV2/WellFormed/AccTuneLimp.lean` |
| `antenna_track_kvretune` | `InstancesV2/Bridge/AntennaTrackKvretune.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/AntennaTrackKvretune.lean` |
| `autoclave_liquid_steambank` | `InstancesV2/Bridge/AutoclaveLiquidSteambank.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/AutoclaveLiquidSteambank.lean` |
| `boiler_purge_vfd` | `InstancesV2/Bridge/BoilerPurgeVfd.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/BoilerPurgeVfd.lean` |
| `bottling_fill_strainer` | `InstancesV2/Bridge/BottlingFillStrainer.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/BottlingFillStrainer.lean` |
| `canal_gate_notches` | `InstancesV2/Bridge/CanalGateNotches.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/CanalGateNotches.lean` |
| `elevator_start_discbrake` | `InstancesV2/Bridge/ElevatorStartDiscbrake.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/ElevatorStartDiscbrake.lean` |
| `engine_start_highidle` | `InstancesV2/Bridge/EngineStartHighidle.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/EngineStartHighidle.lean` |
| `extruder_pe100_manualstart` | `InstancesV2/Bridge/ExtruderPe100Manualstart.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/ExtruderPe100Manualstart.lean` |
| `flaps_slow_approach` | `InstancesV2/Bridge/FlapsSlowApproach.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/FlapsSlowApproach.lean` |
| `furnace_program_timebase` | `InstancesV2/Bridge/FurnaceProgramTimebase.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/FurnaceProgramTimebase.lean` |
| `gantry_speed_zones` | `InstancesV2/Bridge/GantrySpeedZones.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/GantrySpeedZones.lean` |
| `h2_refuel_ambientbias` | `InstancesV2/Bridge/H2RefuelAmbientbias.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/H2RefuelAmbientbias.lean` |
| `hydro_rejection_gatecal` | `InstancesV2/Bridge/HydroRejectionGatecal.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/HydroRejectionGatecal.lean` |
| `lit_csf21_vehicle_bus` | `InstancesV2/Bridge/LitCsf21VehicleBus.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitCsf21VehicleBus.lean` |
| `lit_csf21_vehicle_thermo` | `InstancesV2/Bridge/LitCsf21VehicleThermo.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitCsf21VehicleThermo.lean` |
| `lit_csf25_salt_tank_hold` | `InstancesV2/Bridge/LitCsf25SaltTankHold.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/LitCsf25SaltTankHold.lean` |
| `lit_drl_lane_control` | `InstancesV2/Bridge/LitDrlLaneControl.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitDrlLaneControl.lean` |
| `lit_freedm_meter` | `InstancesV2/Bridge/LitFreedmMeter.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitFreedmMeter.lean` |
| `lit_girard08_robot` | `InstancesV2/Bridge/LitGirard08Robot.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitGirard08Robot.lean` |
| `lit_gpt10_boost_converter` | `InstancesV2/Bridge/LitGpt10BoostConverter.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/LitGpt10BoostConverter.lean` |
| `lit_lz21_vehicle_position` | `InstancesV2/Bridge/LitLz21VehiclePosition.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitLz21VehiclePosition.lean` |
| `lit_nahs25_engine_cooling` | `InstancesV2/Bridge/LitNahs25EngineCooling.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitNahs25EngineCooling.lean` |
| `lit_nahs25_salt_tank` | `InstancesV2/Bridge/LitNahs25SaltTank.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/LitNahs25SaltTank.lean` |
| `molding_pack_checkring` | `InstancesV2/Bridge/MoldingPackCheckring.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/MoldingPackCheckring.lean` |
| `platoon_profiles` | `InstancesV2/Bridge/PlatoonProfiles.lean` | mode-keyed | `theorem3_keyed_of_records` | `InstancesV2/WellFormed/PlatoonProfiles.lean` |
| `quad_light_lag` | `InstancesV2/Bridge/QuadLightLag.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/QuadLightLag.lean` |
| `quad_light_profiles` | `InstancesV2/Bridge/QuadLightProfiles.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/QuadLightProfiles.lean` |
| `rampmeter_poll_2to1` | `InstancesV2/Bridge/RampmeterPoll2to1.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/RampmeterPoll2to1.lean` |
| `reactor_feed_wireless` | `InstancesV2/Bridge/ReactorFeedWireless.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/ReactorFeedWireless.lean` |
| `rover_ladder_2to3` | `InstancesV2/Bridge/RoverLadder2to3.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/RoverLadder2to3.lean` |
| `rover_ladder_3to6` | `InstancesV2/Bridge/RoverLadder3to6.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/RoverLadder3to6.lean` |
| `rover_ladder_6to8` | `InstancesV2/Bridge/RoverLadder6to8.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/RoverLadder6to8.lean` |
| `rover_ladder_8to12` | `InstancesV2/Bridge/RoverLadder8to12.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/RoverLadder8to12.lean` |
| `sat_detumble_phases` | `InstancesV2/Bridge/SatDetumblePhases.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/SatDetumblePhases.lean` |
| `sat_detumble_weak` | `InstancesV2/Bridge/SatDetumbleWeak.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/SatDetumbleWeak.lean` |
| `sat3w_detumble_phases` | `InstancesV2/Bridge/Sat3wDetumblePhases.lean` | window | `theorem3_window_of_records` | `InstancesV2/WellFormed/Sat3wDetumblePhases.lean` |
| `stopline_drag` | `InstancesV2/Bridge/StoplineDrag.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/StoplineDrag.lean` |
| `stopline_friction` | `InstancesV2/Bridge/StoplineFriction.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/StoplineFriction.lean` |
| `stopline_lag` | `InstancesV2/Bridge/StoplineLag.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/StoplineLag.lean` |
| `stopline_tyre` | `InstancesV2/Bridge/StoplineTyre.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/StoplineTyre.lean` |
| `syringe_relay_prearm` | `InstancesV2/Bridge/SyringeRelayPrearm.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/SyringeRelayPrearm.lean` |
| `tank_dos_3to1` | `InstancesV2/Bridge/TankDos3to1.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/TankDos3to1.lean` |
| `train_ato_odometry` | `InstancesV2/Bridge/TrainAtoOdometry.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/TrainAtoOdometry.lean` |
| `turbine_startup_gearratio` | `InstancesV2/Bridge/TurbineStartupGearratio.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/TurbineStartupGearratio.lean` |
| `vehicle_accel_copy` | `InstancesV2/Bridge/VehicleAccelCopy.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/Choice/General/VehicleAccelCopy.lean` |
| `ventilator_vc_cuffleak` | `InstancesV2/Bridge/VentilatorVcCuffleak.lean` | mode-keyed | `theorem3_keyed_of_records_pl` | `InstancesV2/WellFormed/VentilatorVcCuffleak.lean` |
| `watertank_choice` | `InstancesV2/Bridge/WatertankChoice.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/Choice/General/WatertankChoice.lean` |
| `watertank_twospeed` | `InstancesV2/Bridge/WatertankTwospeed.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/WatertankTwospeed.lean` |
| `watertank` | `InstancesV2/Bridge/Watertank.lean` | window | `theorem3_window_of_records_pl` | `InstancesV2/WellFormed/Watertank.lean` |

The strict exhibit `watertank_strict` (`InstancesV2/Bridge/WatertankStrict.lean`, generated by
`scripts/gen_strict_demo.py`, Assumption 1 from `InstancesV2/WellFormed/Watertank.lean`) and
the pre-landing strict demo `HoldRepositionStrict` go through
`theorem3_window_strict_of_records_pl`; the other demo files are listed under check 5.

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
PASSED`, `ONE DOMAIN: PASS`, `ALL PASS`, `13677/13677`, `416/416` and `1009/1009` = every
suite_v2 benchmark is certified end to end, modulo the trust base.

The numbers of the paper's Section 6 (Table 1, the baseline, the ablations, Table 3) come from
one frozen run, `scripts/paper_numbers.sh OUTDIR`, whose output is committed in
`docs/paper-numbers/` (`numbers.tex`, `table1.tex`, `table_per_benchmark.tex`, `letters.md`,
`MANIFEST.txt`).
