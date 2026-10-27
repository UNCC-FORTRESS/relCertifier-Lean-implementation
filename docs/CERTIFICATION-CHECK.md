# Checking the artifact end to end

This is the reproduction recipe: starting from the benchmark files, what to run, and what
you should see, to confirm that every suite_v2 benchmark carries a machine-checked
Theorem 3 (the paper's Soundness of Synthesis) whose hypotheses all hold. Read `README.md` first for what the theorems say.

> **Last run:** 2026-10-27, branch `benchmark-fixes` (batch I6, second group: five new benchmarks, `flaps_slow_approach`, `tunnel_jetfan_pairout`, `rampmeter_poll_2to1`, `bottling_fill_strainer`, `antenna_track_kvretune`: 50 suite benchmarks), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9283 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 50 certified / 0 declined / 0 errors, modal 1349/1349, handoff 517/517, non-connection 46/46, pruned edges 23/23, reposition (dyn) 69/69, `[wellformed] STRICT: 170/170 right modes ok, both clauses (84 invariant, 86 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4864/4864; `relcert-progress-verdicts` 107/107; `relcert-refute-verdicts` 235/235 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 66 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I6, first group: the round C fixes, `rover_terrain_2to4`'s plan at 8 /s and lambda 1, six stretch ranges pinned, two tier-2 header notes: 45 suite benchmarks), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9222 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 45 certified / 0 declined / 0 errors, modal 1098/1098, handoff 466/466, non-connection 44/44, pruned edges 22/22, reposition (dyn) 69/69, `[wellformed] STRICT: 155/155 right modes ok, both clauses (80 invariant, 75 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4392/4392; `relcert-progress-verdicts` 107/107; `relcert-refute-verdicts` 196/196 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 61 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I5, second group: `rover_rollover_payload`, and four designs to `benchmarks/reserve/`: 45 suite benchmarks), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9222 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 45 certified / 0 declined / 0 errors, modal 1098/1098, handoff 466/466, non-connection 44/44, pruned edges 22/22, reposition (dyn) 69/69, `[wellformed] STRICT: 155/155 right modes ok, both clauses (80 invariant, 75 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4392/4392; `relcert-progress-verdicts` 107/107; `relcert-refute-verdicts` 196/196 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 61 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I5, first group: nine new benchmarks, `molding_pack_checkring`, `fuelcell_chp_dos`, `elevator_start_discbrake`, `furnace_program_timebase`, `compressor_station_recycle`, `syringe_relay_prearm`, `hydro_rejection_gatecal`, `ventilator_vc_cuffleak`, `insulin_basal_cgmloss`: 44 suite benchmarks), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9205 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 44 certified / 0 declined / 0 errors, modal 1098/1098, handoff 461/461, non-connection 44/44, pruned edges 22/22, reposition (dyn) 69/69, `[wellformed] STRICT: 152/152 right modes ok, both clauses (79 invariant, 73 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4228/4228; `relcert-progress-verdicts` 107/107; `relcert-refute-verdicts` 181/181 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 60 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I4, third group: `sat_detumble_phases` and `sat3w_detumble_phases` with three-mode design models and exact energy rows in both phases, `sat_detumble_weak` with both sides at the design-model level, all at equal 1 s periods: 35 suite benchmarks), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9136 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 35 certified / 0 declined / 0 errors, modal 717/717, handoff 370/370, non-connection 40/40, pruned edges 20/20, reposition (dyn) 11/11, `[wellformed] STRICT: 120/120 right modes ok, both clauses (71 invariant, 49 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 3025/3025; `relcert-progress-verdicts` 86/86; `relcert-refute-verdicts` 175/175 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 51 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I4, second group: `acc_spoof_lag`, `acc_tune_lag` and `acc_tune_limp` at equal 0.1 s periods, the two lagged files with their left loop's engaged envelope as the left guard: 35 suite benchmarks), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9180 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 35 certified / 0 declined / 0 errors, modal 731/731, handoff 368/368, non-connection 40/40, pruned edges 20/20, reposition (dyn) 11/11, `[wellformed] STRICT: 118/118 right modes ok, both clauses (69 invariant, 49 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 3018/3018; `relcert-progress-verdicts` 86/86; `relcert-refute-verdicts` 217/217 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 51 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I4, first group: seven benchmarks moved to `benchmarks/reserve/`: 35 suite benchmarks, seventeen in the reserve), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9180 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 35 certified / 0 declined / 0 errors, modal 729/729, handoff 368/368, non-connection 40/40, pruned edges 20/20, reposition (dyn) 11/11, `[wellformed] STRICT: 118/118 right modes ok, both clauses (69 invariant, 49 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 3016/3016; `relcert-progress-verdicts` 86/86; `relcert-refute-verdicts` 217/217 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 51 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I3: the rover hierarchy, the four ladder rungs and `rover_patrol_lag` reinstalled on new models, ten rover files out of the suite, four rover designs added to `benchmarks/reserve/`: 42 suite benchmarks, ten in the reserve), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9269 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 42 certified / 0 declined / 0 errors, modal 782/782, handoff 399/399, non-connection 58/58, pruned edges 29/29, reposition (dyn) 24/24, `[wellformed] STRICT: 145/145 right modes ok, both clauses (83 invariant, 62 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 3595/3595; `relcert-progress-verdicts` 180/180; `relcert-refute-verdicts` 280/280 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 61 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I2: the renames `gantry_speed_zones` and `platoon_profiles`, the redesigned `quad_light_{airframe_20,profiles}` and `watertank_twospeed`, the new `bms_chiller_undercharge`, `canal_gate_notches` and `turbine_startup_gearratio`: 52 suite benchmarks, six in `benchmarks/reserve/`), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9361 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 52 certified / 0 declined / 0 errors, modal 807/807, handoff 454/454, non-connection 66/66, pruned edges 33/33, reposition (dyn) 24/24, `[wellformed] STRICT: 177/177 right modes ok, both clauses (94 invariant, 83 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4350/4350; `relcert-progress-verdicts` 252/252; `relcert-refute-verdicts` 313/313 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 71 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-27, branch `benchmark-fixes` (batch I1, commit `6590a08`, 49 suite benchmarks, four in `benchmarks/reserve/`): `lake build` exit 0 (9336 jobs); `--check-quick-v2`: 49 certified, modal 771/771, handoff 434/434, non-connection 70/70, pruned edges 35/35, reposition (dyn) 23/23, `[wellformed] STRICT: 167/167 right modes ok, both clauses (87 invariant, 80 exit)`, PASSED; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4094/4094; `relcert-progress-verdicts` 227/227; `relcert-refute-verdicts` 309/309; `WellFormedBattery` 71 axiom lines. Previous: 2026-10-26, branch `benchmark-fixes` (commit `a902fe5`, the Assumption 1 check of both clauses), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9339 jobs), no `sorry`; the five exes build; `--check-quick-v2`: 50 certified / 0 declined / 0 errors, modal 784/784, handoff 417/417, non-connection 92/92, pruned edges 46/46, reposition (dyn) 21/21, `[wellformed] STRICT: 174/174 right modes ok, both clauses (91 invariant, 83 exit), 0 UNKNOWN, 0 BLOCKING`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS`; `relcert-bridge-verdicts` 4350/4350; `relcert-progress-verdicts` 213/213; `relcert-refute-verdicts` 315/315 and every `InstancesV2/Refute/*` instance builds; `WellFormedBattery` 75 axiom lines at the three standard axioms; `AxiomCheck` 9 lines; `freedm_meter_leaky` DECLINED; `vehicle_hypercert_s8` five modes `BLOCKING`, DECLINED under the strict switch. Previous: 2026-10-22, branch `cleanup-2026-10` (commit `093b2d1`, the standalone route archived on branch `archive/legacy-2026-10`), Apple M2 Max, Z3 4.15.1: `lake build` exit 0 (9252 jobs, the root now imports `InstancesV2.Bridge`), no `sorry`; the five exes build; `--check-quick-v2`: 50 certified / 0 declined / 0 errors, modal 625/625, handoff 401/401, non-connection 88/88, pruned edges 44/44, reposition (dyn) 81/81, `[wellformed] STRICT: 174/174 right modes ok (94 invariant, 80 exit), 0 UNKNOWN`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test` `ALL PASS` (50 literals); `relcert-bridge-verdicts` 4457/4457; `relcert-refute-verdicts` 188/188 and every `InstancesV2/Refute/*` instance builds; `relcert-progress-verdicts` 261/261; `WellFormedBattery` 75 axiom lines, all at the three standard axioms; `AxiomCheck` 9 lines; `benchmarks/negative/freedm_meter_leaky` DECLINED. Previous: 2026-10-15, branch `theorem3-general` (commit `12a0c6b`): full `lake build` exit 0, no `sorry`; `relcert-test` `ALL PASS`; `--run-verdicts-v2` all phases discharged; `relcert-progress-verdicts` 261/261; `relcert-choice-verdicts` 32/32; `relcert-bridge-verdicts` 3512/3512 (`STATUS.md`; 4457/4457 since the literature benchmarks and the choice exhibits). 2026-10-21, branch `clocked-right`: the 52 bridge instances regenerated at dimension `bridgeDimV2` (+1), `relcert-bridge-verdicts` 4457/4457 (commit `61d7389`); the 67 refute instances regenerated at the same rule, `relcert-refute-verdicts` 188/188 (commit `b14f129`). Previous run: 2026-10-11, branch `per-pairing-stretch`, Apple M2 Max (12 cores, 64 GB), Z3 4.15.1. `lake build RelCertifier relcert relcert-test`: `Build completed successfully (17885 jobs)`, no `sorry`. Axiom audit: BatteryV2 72 lines, 48 with `z3_unsat_sound` (the 46 Theorem 3s, `match_multi_rate_nonconn`, `couple_cutX`), 24 at the three standard axioms; WellFormedBattery 77 lines, all at the three standard axioms; nothing else. `--check-quick-v2`: 46 certified / 0 declined / 0 errors (strict well-formedness mode), modal 625/625, handoff 187/187, non-connection 88/88, pruned edges 44/44, copied benchmarks 385/385, reposition (dyn) 81/81, `[wellformed] STRICT: 148/148 right modes ok (84 invariant, 64 exit), 0 UNKNOWN — matches the declared suite`, `SUITE_V2 QUICK CHECKS PASSED`. `relcert-test` with the suite_v2 manifest: 46 IR literals match, bare `ALL PASS`. The stretch pin `VerdictsV2/LamPinV2.lean` (every pack row's stretch is the emitted cover's stretch of that pairing) decides for all 236 rows.

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
| 3 | the 50 files certify in the strict well-formedness mode (declared 50 / 0 / 0), the tool's own queries hold (modal, handoff, non-connection, pruned edges, reposition, against declared counts), and the tool's Assumption 1 check (both clauses, nonblocking and complete, since 2026-10-26) finds every right mode `ok` (declared 170 modes, 0 `UNKNOWN`, 0 `BLOCKING`) | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt` |
| 3' | the expected DECLINE (the leaky FREEDM controller) | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt` |
| 3'' | the expected Assumption 1 failure (`vehicle_hypercert_s8`, a right model that blocks at `s = 8`): all five right modes `BLOCKING`, DECLINED under the strict switch | `./.lake/build/bin/relcert --wellformed benchmarks/negative_wellformed/*/input.txt`; `RELCERT_IMPLIED_CUT=1 RELCERT_WELLFORMED_STRICT=1 ./.lake/build/bin/relcert benchmarks/negative_wellformed/*/input.txt` |
| 4 | each file parses to the literal the theorems quote; parser, printer, Z3-layer and determinism tests | `BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test` |
| 5 | Assumption 1 of every right model (`WellFormedR`): proved for all 50, none refuted; axiom audit; the tool's check, strict in check 3 | `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 \| grep -A3 "depends on axioms"`; `./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt` |
| 6 | every Z3 hypothesis of the generic bridge instances (`InstancesV2/Bridge/`, 52 `*_bridge` theorems: stays, non-connection pairs, flow and reposition packs, admissibility, handoffs, progress, coverage) holds, against the declared total 4864 over the 50 suite benchmarks and the 2 choice exhibits; every query is sent at the instance's dimension `bridgeDimV2 b` (`VerdictsV2/RunBridge.lean:74`: the Assumption 1 lemma's dimension plus one, the right clock of the clocked right automaton `rightAutomatonBodyC`), which is the dimension the instance's `Verdicts` hypothesis names | `./.lake/build/bin/relcert-bridge-verdicts` |
| 7 | the progress certificates (the paper's reposition certificates, Definition 7) of every reposition node (107 queries) hold, against the declared count | `./.lake/build/bin/relcert-progress-verdicts` |
| 8 | the 82 kernel refutations (`InstancesV2/Refute/`, `docs/REFUTATION-RESULTS.md`): every Z3 group of `RefVerdicts` holds against the declared total 235, each instance at its benchmark's bridge dimension (`RefRec.dim + 1`, `InstancesV2/Refute/Table.lean`), and each instance concludes `¬ keyedClaim … 0 1 2 3 dt` / `¬ windowClaim … 0 1 2 dt`, the negation of the clocked bridge claim at that dimension (`refute_keyed_C/A/B_clocked`, `refute_window_B_clocked`) | `./.lake/build/bin/relcert-refute-verdicts`; `lake build RelCertifier.InstancesV2.Refute` |

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

`--check-quick-v2` refuses to run without `RELCERT_IMPLIED_CUT=1` (3 suite_v2 benchmarks
DECLINE without the widened cut channel). Check 1/3 certifies in the STRICT well-formedness
mode (`RELCERT_WELLFORMED_STRICT` forced on: a CERTIFIED file with an `UNKNOWN` or `BLOCKING`
right mode is DECLINED, a `[wellformed]` line per file on stderr); check 3/3 is the
`--wellformed` report, gated. Expected tail:

```
  [suite_v2] 50 certified, 0 declined, 0 error(s) — matches the declared suite
  [coverage] suite_v2 modal: 1349/1349 hypotheses discharged
  [coverage] suite_v2 handoff: 517/517 hypotheses discharged
  [coverage] suite_v2 non-connection: 46/46 hypotheses discharged
  [coverage] suite_v2 pruned edges: 23/23 hypotheses discharged
  [coverage] suite_v2 reposition (dyn): 69/69 hypotheses discharged
[wellformed] summary: 50 benchmark(s), 170 right mode(s): 84 ok (invariant), 86 ok (exit), 0 UNKNOWN (0 of them nonblocking), 0 BLOCKING (0 benchmark(s) with a mode not ok); both clauses checked; 12676 queries
  [wellformed] STRICT: 170/170 right modes ok, both clauses (84 invariant, 86 exit), 0 UNKNOWN, 0 BLOCKING — matches the declared suite (170 modes, 0 UNKNOWN, 0 BLOCKING)

  suite_v2: PASS
  verdicts: PASS
  wellformed (strict): PASS (170/170 right modes ok, both clauses (84 invariant, 86 exit), 0 UNKNOWN, 0 BLOCKING)
SUITE_V2 QUICK CHECKS PASSED  (the kernel check is `lake build`)
```

The well-formedness gate (check 5's tool part, strict since 2026-10-10; it was informational
while 9 models blocked): the declared mode count `ExpectedSuiteV2.wfModes = 170`
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
./.lake/build/bin/relcert benchmarks/negative/*/input.txt` prints `freedm_meter_leaky:
DECLINED`, `errors=0`.

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
`freedm_meter`, `V2VehicleHypercert.vehicle_hypercert_wellFormedR`, and the 3 satellites' `<b>_wellFormedR`,
unconditional since 2026-10-15), the three satellites' `<b>_band_invariant`, and
13 generic lemmas (`wellFormedR_terrain`, `wellFormedR_switchLegal`, `not_wellFormedR_of_run`,
`not_wellFormedR_of_noRun`, `exists_contract_run`, `exists_rate_run`,
`exists_of_HExistSegB_zero`, `coord_le_barrier`, `affine_const`, the platoon follower's
`PlatoonCaccAeb.cacc_w_band`, `PlatoonCaccAeb.aeb_w_const`, `PlatoonCaccAeb.cacc_box`,
`WellFormedBattery.wf_coverage`; the declared counts `(47, 0, 3)`, `(30, 9, 6)` before the repairs, and the three name lists a
permutation of the suite's IR table). Each proof lives in its own self-contained
`InstancesV2/WellFormed/<B>.lean` (right model and proof; since 2026-10-22 the 19 carried-over
ones too). The tool line: `[wellformed] summary: 50 benchmark(s), 170 right mode(s): 84 ok
(invariant), 86 ok (exit), 0 UNKNOWN (0 of them nonblocking), 0 BLOCKING (0 benchmark(s) with
a mode not ok); both clauses checked`; check 3 gates it. What this establishes and what it does
not (the tool's check is sufficient, of both clauses since 2026-10-26, of the successor clause
only before; the predicate's domain conjunct; the satellites' band): `docs/WELLFORMED.md`. The repairs:
`docs/SUITE-REDESIGN.md` §21.

**Nonblocking negative check** (2026-10-26): `--check-quick-v2` over the suite with
`benchmarks/negative_wellformed/vehicle_hypercert_s8` (a right model that blocks at `s = 8`) in
place of `vehicle_hypercert`: check 1 `49 certified, 1 declined, 0 error(s) but the declared
suite is 50/0/0` (`[wellformed] STRICT: vehicle_hypercert_s8 DECLINED (a BLOCKING right
mode)`), check 3 `169/174 right modes ok, both clauses (90 invariant, 79 exit), 0 UNKNOWN, 5
BLOCKING`, `SUITE_V2 QUICK CHECKS FAILED`, exit 1. With the successor clause alone the same
file passed the gate (all five modes `ok`).

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
| `antenna_track_kvretune` | `InstancesV2/Bridge/AntennaTrackKvretune.lean` | `antenna_track_kvretune_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/AntennaTrackKvretune.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `bms_chiller_undercharge` | `InstancesV2/Bridge/BmsChillerUndercharge.lean` | `bms_chiller_undercharge_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/BmsChillerUndercharge.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `bottling_fill_strainer` | `InstancesV2/Bridge/BottlingFillStrainer.lean` | `bottling_fill_strainer_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/BottlingFillStrainer.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `canal_gate_notches` | `InstancesV2/Bridge/CanalGateNotches.lean` | `canal_gate_notches_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/CanalGateNotches.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `compressor_station_recycle` | `InstancesV2/Bridge/CompressorStationRecycle.lean` | `compressor_station_recycle_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/CompressorStationRecycle.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `drl_car_stop` | `InstancesV2/Bridge/DrlCarStop.lean` | `drl_car_stop_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/DrlCarStop.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `drl_lane_control` | `InstancesV2/Bridge/DrlLaneControl.lean` | `drl_lane_control_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/DrlLaneControl.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `elevator_start_discbrake` | `InstancesV2/Bridge/ElevatorStartDiscbrake.lean` | `elevator_start_discbrake_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/ElevatorStartDiscbrake.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `engine_start_highidle` | `InstancesV2/Bridge/EngineStartHighidle.lean` | `engine_start_highidle_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/EngineStartHighidle.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `flaps_slow_approach` | `InstancesV2/Bridge/FlapsSlowApproach.lean` | `flaps_slow_approach_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FlapsSlowApproach.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `freedm_meter` | `InstancesV2/Bridge/FreedmMeter.lean` | `freedm_meter_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FreedmMeter.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `fuelcell_chp_dos` | `InstancesV2/Bridge/FuelcellChpDos.lean` | `fuelcell_chp_dos_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FuelcellChpDos.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `furnace_program_timebase` | `InstancesV2/Bridge/FurnaceProgramTimebase.lean` | `furnace_program_timebase_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/FurnaceProgramTimebase.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `gantry_speed_zones` | `InstancesV2/Bridge/GantrySpeedZones.lean` | `gantry_speed_zones_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/GantrySpeedZones.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `hvac_fan_staging` | `InstancesV2/Bridge/HvacFanStaging.lean` | `hvac_fan_staging_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/HvacFanStaging.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `hydro_rejection_gatecal` | `InstancesV2/Bridge/HydroRejectionGatecal.lean` | `hydro_rejection_gatecal_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/HydroRejectionGatecal.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `insulin_basal_cgmloss` | `InstancesV2/Bridge/InsulinBasalCgmloss.lean` | `insulin_basal_cgmloss_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/InsulinBasalCgmloss.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `molding_pack_checkring` | `InstancesV2/Bridge/MoldingPackCheckring.lean` | `molding_pack_checkring_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/MoldingPackCheckring.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `platoon_latency` | `InstancesV2/Bridge/PlatoonLatency.lean` | `platoon_latency_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/PlatoonLatency.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `platoon_linkloss` | `InstancesV2/Bridge/PlatoonLinkloss.lean` | `platoon_linkloss_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/PlatoonLinkloss.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `platoon_profiles` | `InstancesV2/Bridge/PlatoonProfiles.lean` | `platoon_profiles_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/PlatoonProfiles.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `quad_light_airframe_20` | `InstancesV2/Bridge/QuadLightAirframe20.lean` | `quad_light_airframe_20_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/QuadLightAirframe20.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `quad_light_lag` | `InstancesV2/Bridge/QuadLightLag.lean` | `quad_light_lag_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/QuadLightLag.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `quad_light_profiles` | `InstancesV2/Bridge/QuadLightProfiles.lean` | `quad_light_profiles_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/QuadLightProfiles.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rampmeter_poll_2to1` | `InstancesV2/Bridge/RampmeterPoll2to1.lean` | `rampmeter_poll_2to1_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RampmeterPoll2to1.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_2to3` | `InstancesV2/Bridge/RoverLadder2to3.lean` | `rover_ladder_2to3_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder2to3.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_3to6` | `InstancesV2/Bridge/RoverLadder3to6.lean` | `rover_ladder_3to6_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder3to6.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_6to8` | `InstancesV2/Bridge/RoverLadder6to8.lean` | `rover_ladder_6to8_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder6to8.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_ladder_8to12` | `InstancesV2/Bridge/RoverLadder8to12.lean` | `rover_ladder_8to12_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverLadder8to12.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_patrol_lag` | `InstancesV2/Bridge/RoverPatrolLag.lean` | `rover_patrol_lag_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverPatrolLag.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_rollover_payload` | `InstancesV2/Bridge/RoverRolloverPayload.lean` | `rover_rollover_payload_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverRolloverPayload.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_terrain_2to4` | `InstancesV2/Bridge/RoverTerrain2to4.lean` | `rover_terrain_2to4_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverTerrain2to4.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_terrain_4to6` | `InstancesV2/Bridge/RoverTerrain4to6.lean` | `rover_terrain_4to6_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverTerrain4to6.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `rover_terrain_6to12` | `InstancesV2/Bridge/RoverTerrain6to12.lean` | `rover_terrain_6to12_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/RoverTerrain6to12.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `sat3w_detumble_phases` | `InstancesV2/Bridge/Sat3wDetumblePhases.lean` | `sat3w_detumble_phases_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/Sat3wDetumblePhases.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `sat_detumble_phases` | `InstancesV2/Bridge/SatDetumblePhases.lean` | `sat_detumble_phases_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/SatDetumblePhases.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `sat_detumble_weak` | `InstancesV2/Bridge/SatDetumbleWeak.lean` | `sat_detumble_weak_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/SatDetumbleWeak.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `syringe_relay_prearm` | `InstancesV2/Bridge/SyringeRelayPrearm.lean` | `syringe_relay_prearm_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/SyringeRelayPrearm.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `tank_dos_3to1` | `InstancesV2/Bridge/TankDos3to1.lean` | `tank_dos_3to1_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/TankDos3to1.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `train_ato_odometry` | `InstancesV2/Bridge/TrainAtoOdometry.lean` | `train_ato_odometry_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/TrainAtoOdometry.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `tunnel_jetfan_pairout` | `InstancesV2/Bridge/TunnelJetfanPairout.lean` | `tunnel_jetfan_pairout_bridge` | mode-keyed (`keyedClaim … 0 1 2 3 dt`) | `InstancesV2/WellFormed/TunnelJetfanPairout.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `turbine_startup_gearratio` | `InstancesV2/Bridge/TurbineStartupGearratio.lean` | `turbine_startup_gearratio_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/TurbineStartupGearratio.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `vehicle_accel_copy` | `InstancesV2/Bridge/VehicleAccelCopy.lean` | `vehicle_accel_copy_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/Choice/General/VehicleAccelCopy.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
| `vehicle_hypercert` | `InstancesV2/Bridge/VehicleHypercert.lean` | `vehicle_hypercert_bridge` | window (`windowClaim … 0 1 2 dt`) | `InstancesV2/WellFormed/VehicleHypercert.lean` | `Verdicts` (the runner's groups) | std 3 + `z3_unsat_sound` |
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
  && RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt \
  && BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test \
  && ./.lake/build/bin/relcert-bridge-verdicts \
  && ./.lake/build/bin/relcert-refute-verdicts \
  && ./.lake/build/bin/relcert-progress-verdicts
```

A green build, an axiom listing with nothing beyond the four axioms, `SUITE_V2 QUICK CHECKS
PASSED`, `ALL PASS`, `4864/4864`, `235/235` and `107/107` = every suite_v2 benchmark is
certified end to end, modulo the trust base.

## Earlier recipes

Until 2026-10-10 this document described the legacy suite (`suite_uniform`) and its
checks (`--check-quick`, `--run-verdicts`, `Instances/ModalBattery.lean`), with dated
records of full runs (the last cold-tree build of that development: 2026-08-02, 12h59m,
8988 jobs). That suite and those entry points were removed; the records are in the git
history of this file. Until 2026-10-22 it described the standalone route (`BatteryV2`,
`relcert --run-verdicts-v2`, `relcert-choice-verdicts`, the per-benchmark inventory of the
hand-written instances); that route is archived on branch `archive/legacy-2026-10`.
