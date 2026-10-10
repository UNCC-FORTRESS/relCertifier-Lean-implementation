# Checking the artifact end to end

This is the reproduction recipe: starting from the benchmark files, what to run, and what
you should see, to confirm that every suite_v2 benchmark carries a machine-checked
Theorem 3 whose hypotheses all hold. Read `README.md` first for what the theorems say.

> **Last run:** 2026-10-10, branch `wellformed-models`, Apple M2 Max (12 cores, 64 GB), Z3 4.15.1. `lake build`: `Build completed successfully (9005 jobs)`, no `sorry`; `lake build relcert relcert-test`: 17725 jobs. Axiom audit: 71 lines, 31 with `z3_unsat_sound`, 40 at the three standard axioms, nothing else; Assumption 1 battery: 76 lines, all at the three standard axioms. `--check-quick-v2`: 45 certified / 0 declined / 0 errors (strict well-formedness mode), modal 262/262, handoff 186/186, non-connection 88/88, pruned edges 44/44, copied benchmarks 385/385, `[wellformed] STRICT: 146/146 right modes ok (83 invariant, 63 exit), 0 UNKNOWN`, `SUITE_V2 QUICK CHECKS PASSED`. `--run-verdicts-v2`: the same counts, `ALL suite_v2 HYPOTHESES DISCHARGED`. `relcert-test` with the suite_v2 manifest: 45 IR literals match, bare `ALL PASS`.

---

## 0. The chain being checked

```
benchmarks/suite_v2/<b>/input.txt                the benchmark, as text
   │ strict parser (Trusted/Parse.lean, IN the trust base)
   ▼
InstancesV2/BenchIR/<b>.lean  `<b>_IRv2`         the emitted IR literal
   │ ▲ relcert-test [ir-drift-v2]: re-parse and compare              ← check 4
   │ ▲ InstancesV2/SameIR.lean: for the 19 carried-over benchmarks, the literal
   │   IS the one the legacy theorems quote (rfl)
   ▼
InstancesV2/Modal/<B>.lean, or Instances/<B>…    the Theorem 3 instance
   │ Lean kernel                                                     ← check 1
   ▼
rvalid (theorem3Form …)                          the ∀∃ refinement statement
   │ #print axioms (InstancesV2/BatteryV2.lean)                      ← check 2
   ▼
[propext, Classical.choice, Quot.sound] (+ z3_unsat_sound at the verdict leaves)
   │ relcert --run-verdicts-v2, each query pinned to its hypothesis  ← check 3
   ▼
every verdict leaf: Z3 says unsat
```

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
| 1 | every proof kernel-checks | `lake build` (see *Cost*), then `lake build relcert relcert-test` |
| 2 | the axiom audit of every battery theorem | `lake build RelCertifier.InstancesV2.BatteryV2 2>&1 \| grep -A3 "depends on axioms"` |
| 3 | the 45 files certify in the strict well-formedness mode (declared 45 / 0 / 0), every Z3 hypothesis of the battery holds, and the tool's Assumption 1 check finds no `UNKNOWN` right mode (declared 146 modes, 0 `UNKNOWN`), all against declared counts | `RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt` |
| 3' | the hypotheses alone | `./.lake/build/bin/relcert --run-verdicts-v2` |
| 4 | each file parses to the literal the theorems quote; parser, printer, Z3-layer and determinism tests | `BENCH_PATHS=<manifest> ./.lake/build/bin/relcert-test` |
| 5 | Assumption 1 of every right model (`WellFormedR`): 39 proved, 6 proved on the momentum band, none refuted; axiom audit; the tool's check, strict in check 3 | `lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 \| grep -A3 "depends on axioms"`; `./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt` |

## Check 1: the kernel checks every proof

```bash
lake build
lake build relcert relcert-test
```

Expected: `Build completed successfully` for both, and no `declaration uses 'sorry'` in the
log (`grep -c "declaration uses 'sorry'"` prints 0).

### Cost

Measured 2026-10-10 on an Apple M2 Max (12 cores, 64 GB), with the Lean dependencies
(dL-rel, Mathlib) already built and every `RelCertifier` module invalidated by comment edits
under `Proofs/`, `Checker/` and `Trusted/`: **64 min 45 s** wall with the serial recipe below.
The `Core`/`Checker`/`Proofs`/`Trusted` layer took 175 s (built in parallel); the 24 legacy
instance modules and the 26 suite_v2 instance modules, built one at a time, took between
11 s and 651 s each: the heaviest were `Instances/Story1AttdistRungBHandoff` 651 s (peak
resident memory about 15.6 GB, sampled every 10 s), `RoverLadderRung4Modal` 530 s (13.5 GB),
`Story1AttdistRungBModal` 523 s (13.4 GB), `Story2LateralBModal`, `Story3RolloverBaseModal`,
`Story3RolloverRungAModal`, `Story3RolloverRungBModal` about 225 s each (about 9 GB), and
`RoverDofTerrainRung3Modal` 154 s; every suite_v2 instance took under 35 s. The remaining
modules (data leaves, runner, pins, battery) took 112 s. A build from a cold tree also
compiles dL-rel and the Mathlib subset it imports first; that part was not re-measured.

Practical notes:

* Build the heavy instance files one at a time before the rest: building several of them in
  parallel can exhaust memory. `lake build <Module>` builds one module and what it imports;
  for example, in dependency order, every module under `RelCertifier/Instances/` and
  `RelCertifier/InstancesV2/Modal/`, then a final `lake build`.
* Run long builds detached and log to a file (`tee`, not `tail`).
* Killing `lake build` can orphan Lean workers; follow up with
  `pkill -f "lake build"; pkill -9 -f "leanprover--lean4"`.
* To check one file against already-built dependencies: `lake env lean <file>`.
* An edit to anything under `Proofs/`, `Checker/` or `Trusted/` (comments included)
  invalidates every instance downstream.

## Check 2: the axiom audit

```bash
lake build RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"
```

Use `-A3`: a four-axiom list prints over four lines. Expected: 71 lines, in the groups of
`BatteryV2`: (1) the 45 Theorem 3s with the paper's left program over the guarded automata at
the mode-consistent region (`rung2c` for `dt ≤ ε_L = 1`, the `platoon3` pair on the repaired
model); `match_multi_rate_nonconn`; and 25 generic lemmas. Every list is a subset of
`[propext, Classical.choice, Quot.sound, z3_unsat_sound]`; 31 carry `z3_unsat_sound` (29 of
the 45, `couple_cutX`, `match_multi_rate_nonconn`); 40 are at the three standard axioms alone:
the 16 Z3-free theorems (`arm_plateau_{crit,profiles,slow}_leftAut`,
`rover3tier_rung12_modeKeyed_guarded`, `match_multi_rate_leftAut`,
`rover_patrol_{zones,refine}_guarded`, `rover_ladder_rung1_leftAut`,
`rover_ladder_rung3_6to8_leftAut`, `rover_ladder_rung4_8to12_leftAut`,
`rover_dof_terrain_rung{1,2,3,3_8d}_leftAut`, `rung2{,b}_6dof_leftAut`) and 24 generic lemmas
(all but `couple_cutX`).
No `sorryAx`, no other axiom.
The generic theorems' audit is `Instances/AxiomCheck.lean`, re-emitted by `lake build`.

## Check 3: certify the suite and discharge the verdict hypotheses

```bash
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
```

`--check-quick-v2` refuses to run without `RELCERT_IMPLIED_CUT=1` (10 suite_v2 benchmarks
DECLINE without the widened cut channel). Check 1/3 certifies in the STRICT well-formedness
mode (`RELCERT_WELLFORMED_STRICT` forced on: a CERTIFIED file with an `UNKNOWN` right mode is
DECLINED, a `[wellformed]` line per file on stderr); check 3/3 is the `--wellformed` report,
gated. Expected tail:

```
  [suite_v2] 45 certified, 0 declined, 0 error(s) — matches the declared suite
  [coverage] suite_v2 modal: 262/262 hypotheses discharged
  [coverage] suite_v2 handoff: 186/186 hypotheses discharged
  [coverage] suite_v2 non-connection: 88/88 hypotheses discharged
  [coverage] suite_v2 pruned edges: 44/44 hypotheses discharged
  [coverage] suite_v2 copied benchmarks (legacy packs): 385/385 hypotheses discharged
  [wellformed] summary: 45 benchmark(s), 146 right mode(s): 83 ok (invariant), 63 ok (exit), 0 UNKNOWN (0 benchmark(s) with an UNKNOWN mode); 2279 queries
  [wellformed] STRICT: 146/146 right modes ok (83 invariant, 63 exit), 0 UNKNOWN — matches the declared suite (146 modes, 0 UNKNOWN)

  suite_v2: PASS
  verdicts: PASS
  wellformed (strict): PASS (146/146 right modes ok (83 invariant, 63 exit), 0 UNKNOWN)
SUITE_V2 QUICK CHECKS PASSED  (the kernel check is `lake build`)
```

The well-formedness gate (check 5's tool part, strict since 2026-10-10; it was informational
while 9 models blocked): the declared mode count `ExpectedSuiteV2.wfModes = 146` is
kernel-checked to be the right-mode count of the 45 IR literals
(`VerdictsV2/CoveragePinsV2.suiteV2_wfModes`), and `wfUnknown = 0`; any `UNKNOWN` mode, a
mode count off the declared one, or a file that does not parse fails the run.

What each phase is and what pins it to the theorems: `docs/VERDICTS.md`. A phase that
discharged fewer (or more) queries than declared fails the run; anything the runner cannot
rebuild is a `SKIP`/`FAIL`, never a pass.

## Check 4: the files match the IR the theorems quote

```bash
for d in benchmarks/suite_v2/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"
done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test
```

Expected: `ok   all 45 suite_v2 IR literals match their files` and a bare `ALL PASS`.
Without `BENCH_PATHS` the two determinism checks (`match_multi_rate` 8× CERTIFIED;
`acc_spoof_lag`, which declines without the widened channel, 8× the same verdict) are
skipped and the last line says `ALL PASS (2 SKIPPED …)`. The 19 carried-over legacy
literals are covered by the same check through `SameIR`.

## Check 5: Assumption 1, verified per benchmark

```bash
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
./.lake/build/bin/relcert --wellformed benchmarks/suite_v2/*/input.txt
```

Expected: 76 axiom lines, each exactly `[propext, Classical.choice, Quot.sound]` (no
`z3_unsat_sound`: every proof is Z3-free): 39 `<b>_wellFormedR` (proved; the nine repaired
on 2026-10-10 with their repaired modes' per-mode theorems `…_brake` / `…_limit`), for the 6
satellites `<b>_wellFormedR_onBand`, `<b>_band_invariant` and `<b>_wellFormedR_false` (the
literal predicate), and 13 generic lemmas including `Platoon3Link.brake_guard_Ronly`,
`Platoon3Link.solB_sol` and `WellFormedBattery.wf_coverage` (the declared counts `(39, 0, 6)`,
`(30, 9, 6)` before the repairs, and the three name lists a permutation of the suite's IR
table). The tool line: `[wellformed] summary: 45 benchmark(s), 146 right mode(s): 83 ok
(invariant), 63 ok (exit), 0 UNKNOWN (0 benchmark(s) with an UNKNOWN mode)`; check 3 gates it.
What this establishes and what it does not (the tool checks only the successor half; the
predicate's domain conjunct; the satellites' band): `docs/WELLFORMED.md`. The repairs:
`docs/SUITE-REDESIGN.md` §21.

**Strict-gate negative check** (2026-10-10): `--check-quick-v2` over the suite with the
pre-repair `platoon_delay_linkloss` in its place: check 1 `44 certified, 1 declined, 0
error(s) but the declared suite is 45/0/0` (`[wellformed] STRICT: platoon_delay_linkloss
DECLINED`), check 3 `145/146 right modes ok … 1 UNKNOWN`, `SUITE_V2 QUICK CHECKS FAILED`,
exit 1.

**Regression of the repair pass** (2026-10-10): `--emit-ir`, `--emit-cover`, `--emit-cuts`
(the last two with `RELCERT_IMPLIED_CUT=1`) of the 36 untouched files byte-identical, stdout
and stderr, against the binary of `5dd8798` (108 outputs); regenerating every data leaf
(`scripts/gen_v2_data.py` over all 45) leaves the committed leaves unchanged; the
non-connection pruning extension (a compound successor guard pruned on its strict leading
conjunct) touches no other file (none has such a guard); the full matrix re-run changes no
cell of the 36.

## Per-benchmark inventory

"std 3" = `[propext, Classical.choice, Quot.sound]`. The hypotheses are the theorem's
binders besides the window duration `dt` (and `0 ≤ dt` for some carried-over theorems,
`0 ≤ dt ≤ 1` for `rung2c`): named Z3 verdict packs. Every statement: Theorem 3 with the
paper's left program (`leftAutomatonBody`) over the guarded right automaton, the loop
invariant carrying `guard ∧ cuts` of the right's current mode (`regionG`), every switch
kernel-checked legal (`docs/GUARDED-SWITCHING.md` §3.1, §3.3, §6). Mode-independent
benchmarks are carried from their window-choice theorem by `theorem3_leftAut_of_choiceR`.
Each `InstancesV2/Modal/` pack `Verd l q` is one row of `VerdictsV2/RunV2.packsV2`; each
carried-over pack is pinned to a row of `Verdicts/RunModal.modalTable`.

| benchmark | file | theorem | verdict packs | axioms |
|---|---|---|---|---|
| `acc_spoof_lag` | `InstancesV2/LeftAutV2.lean` | `V2AccSpoofLag.acc_spoof_lag_leftAut` | 1×`Verd` | std 3 + `z3_unsat_sound` |
| `acc_spoof_limp` | `InstancesV2/Modal/AccSpoofLimp.lean` | `V2AccSpoofLimp.acc_spoof_limp_modeKeyed` | 6×`Verd` | std 3 + `z3_unsat_sound` |
| `acc_tune_lag` | `InstancesV2/LeftAutV2.lean` | `V2AccTuneLag.acc_tune_lag_leftAut` | 1×`Verd` | std 3 + `z3_unsat_sound` |
| `acc_tune_limp` | `InstancesV2/Modal/AccTuneLimp.lean` | `V2AccTuneLimp.acc_tune_limp_modeKeyed` | 6×`Verd` | std 3 + `z3_unsat_sound` |
| `arm_plateau_crit` | `InstancesV2/LeftAutV2.lean` | `V2ArmPlateauCrit.arm_plateau_crit_leftAut` | none | std 3 |
| `arm_plateau_profiles` | `InstancesV2/LeftAutV2.lean` | `V2ArmPlateauProfiles.arm_plateau_profiles_leftAut` | none | std 3 |
| `arm_plateau_slow` | `InstancesV2/LeftAutV2.lean` | `V2ArmPlateauSlow.arm_plateau_slow_leftAut` | none | std 3 |
| `charger_fast_setpoints` | `InstancesV2/LeftAutV2.lean` | `V2ChargerFastSetpoints.charger_fast_setpoints_leftAut` | 7×`Verd` | std 3 + `z3_unsat_sound` |
| `charger_fast_tapers` | `InstancesV2/LeftAutV2.lean` | `V2ChargerFastTapers.charger_fast_tapers_leftAut` | 9×`Verd` | std 3 + `z3_unsat_sound` |
| `match_multi_rate` | `Instances/LeftAutLegacy.lean` | `MatchMultiRateGuarded.match_multi_rate_leftAut` | none | std 3 |
| `platoon3_linkloss` | `InstancesV2/Modal/Platoon3Linkloss.lean` | `V2Platoon3Linkloss.platoon3_linkloss_modeKeyed` | 2×`Verd` | std 3 + `z3_unsat_sound` |
| `platoon3_profiles` | `InstancesV2/Modal/Platoon3Profiles.lean` | `V2Platoon3Profiles.platoon3_profiles_leftAut` | 3×`Verd` | std 3 + `z3_unsat_sound` |
| `platoon_delay_linkloss` | `InstancesV2/Modal/PlatoonDelayLinkloss.lean` | `V2PlatoonDelayLinkloss.platoon_delay_linkloss_modeKeyed` | 6×`Verd` | std 3 + `z3_unsat_sound` |
| `platoon_delay_profiles` | `InstancesV2/LeftAutV2.lean` | `V2PlatoonDelayProfiles.platoon_delay_profiles_leftAut` | 6×`Verd` | std 3 + `z3_unsat_sound` |
| `quad_light_airframe_20` | `InstancesV2/LeftAutV2.lean` | `V2QuadLightAirframe20.quad_light_airframe_20_leftAut` | 1×`Verd` | std 3 + `z3_unsat_sound` |
| `quad_light_lag` | `InstancesV2/LeftAutV2.lean` | `V2QuadLightLag.quad_light_lag_leftAut` | 1×`Verd` | std 3 + `z3_unsat_sound` |
| `quad_light_profiles` | `InstancesV2/LeftAutV2.lean` | `V2QuadLightProfiles.quad_light_profiles_leftAut` | 3×`Verd` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung1_2to3` | `Instances/LeftAutLegacy.lean` | `RoverLadderRung1Guarded.rover_ladder_rung1_leftAut` | none | std 3 |
| `refinement_ladder_rover_rung2_3to6` | `Instances/RoverLadderRung2Guarded.lean` | `RoverLadderRung2Guarded.rover_ladder_rung2_3to6_leftAut` | 6×`Verd36` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung2_6dof` | `Instances/LeftAutLegacy.lean` | `RoverRung26dofGuarded.rung2_6dof_leftAut` | none | std 3 |
| `refinement_ladder_rover_rung2b_6dof` | `Instances/LeftAutLegacy.lean` | `RoverRung2b6dofGuarded.rung2b_6dof_leftAut` | none | std 3 |
| `refinement_ladder_rover_rung2c_6dof` | `Instances/LeftAutLegacy.lean` | `RoverRung2cGuarded.rover_rung2c_leftAut` (`0 ≤ dt ≤ 1`) | 3×`VerdR6` | std 3 + `z3_unsat_sound` |
| `refinement_ladder_rover_rung3_6to8` | `Instances/LeftAutLegacy.lean` | `RoverLadderRung3Guarded.rover_ladder_rung3_6to8_leftAut` | none | std 3 |
| `refinement_ladder_rover_rung4_8to12` | `Instances/LeftAutLegacy.lean` | `RoverLadderRung4Guarded.rover_ladder_rung4_8to12_leftAut` | none | std 3 |
| `rover3tier_rung12` | `Instances/Rover3tierRung12Guarded.lean` | `Rover3tierRung12Guarded.rover3tier_rung12_modeKeyed_guarded` | none | std 3 |
| `rover_dof_terrain_rung1` | `Instances/LeftAutLegacy.lean` | `RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_leftAut` | none | std 3 |
| `rover_dof_terrain_rung2` | `Instances/LeftAutLegacy.lean` | `RoverDofTerrainRung2Guarded.rover_dof_terrain_rung2_leftAut` | none | std 3 |
| `rover_dof_terrain_rung3` | `Instances/LeftAutLegacy.lean` | `RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_leftAut` | none | std 3 |
| `rover_dof_terrain_rung3_8d` | `Instances/LeftAutLegacy.lean` | `RoverDofTerrainRung38dGuarded.rover_dof_terrain_rung3_8d_leftAut` | none | std 3 |
| `rover_patrol_refine` | `InstancesV2/Modal/RoverPatrolRefineGuarded.lean` | `V2RoverPatrolRefineGuarded.rover_patrol_refine_guarded` | none | std 3 |
| `rover_patrol_zones` | `InstancesV2/Modal/RoverPatrolZonesGuarded.lean` | `V2RoverPatrolZonesGuarded.rover_patrol_zones_guarded` | none | std 3 |
| `sat3w_detumble_nominal` | `InstancesV2/LeftAutV2.lean` | `V2Sat3wDetumbleNominal.sat3w_detumble_nominal_leftAut` | 1×`Verd` | std 3 + `z3_unsat_sound` |
| `sat3w_detumble_phases` | `InstancesV2/Modal/Sat3wDetumblePhases.lean` | `V2Sat3wDetumblePhases.sat3w_detumble_phases_modeKeyed` | 2×`Verd` | std 3 + `z3_unsat_sound` |
| `sat3w_detumble_weak` | `InstancesV2/LeftAutV2.lean` | `V2Sat3wDetumbleWeak.sat3w_detumble_weak_leftAut` | 3×`Verd` | std 3 + `z3_unsat_sound` |
| `sat_detumble_nominal` | `InstancesV2/LeftAutV2.lean` | `V2SatDetumbleNominal.sat_detumble_nominal_leftAut` | 1×`Verd` | std 3 + `z3_unsat_sound` |
| `sat_detumble_phases` | `InstancesV2/Modal/SatDetumblePhases.lean` | `V2SatDetumblePhases.sat_detumble_phases_modeKeyed` | 2×`Verd` | std 3 + `z3_unsat_sound` |
| `sat_detumble_weak` | `InstancesV2/LeftAutV2.lean` | `V2SatDetumbleWeak.sat_detumble_weak_leftAut` | 3×`Verd` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_a_6to8` | `Instances/Story1AttdistRungAGuarded.lean` | `Story1AttdistRungAGuarded.story1_attdist_rung_a_guarded` | 3×`VerdS`, 6×`VerdD` | std 3 + `z3_unsat_sound` |
| `story1_attdist_rung_b_12dof` | `Instances/Story1AttdistRungBGuarded.lean` | `Story1AttdistRungBGuarded.story1_attdist_rung_b_guarded` | 6×`VerdR` | std 3 + `z3_unsat_sound` |
| `story2_lateral_rung_a_8dof` | `Instances/Story2LateralAGuarded.lean` | `Story2LateralAGuarded.story2_lateral_rung_a_leftAut` | 6×`VerdY` | std 3 + `z3_unsat_sound` |
| `story2_lateral_rung_b_12dof` | `Instances/Story2LateralBGuarded.lean` | `Story2LateralBGuarded.story2_lateral_rung_b_leftAut` | 6×`VerdZ` | std 3 + `z3_unsat_sound` |
| `story3_rollover_base_12dof` | `Instances/LeftAutLegacy.lean` | `Story3RolloverBaseGuarded.story3_rollover_base_leftAut` | 6×`VerdB` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_a` | `Instances/LeftAutLegacy.lean` | `Story3RolloverRungAGuarded.story3_rollover_rung_a_leftAut` | 6×`VerdA` | std 3 + `z3_unsat_sound` |
| `story3_rollover_ladder_rung_b` | `InstancesV2/Modal/Story3RolloverRungBGuarded.lean` | `V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_guarded` | 9×`Verd` | std 3 + `z3_unsat_sound` |
| `watertank` | `InstancesV2/LeftAutV2.lean` | `V2Watertank.watertank_leftAut` | 11×`Verd` | std 3 + `z3_unsat_sound` |

## One-shot (after creating the manifest of check 4)

```bash
lake build && lake build relcert relcert-test \
  && lake build RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms" \
  && RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt \
  && BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test \
  && lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
```

A green build, an axiom listing with nothing beyond the four axioms, `SUITE_V2 QUICK CHECKS
PASSED` and `ALL PASS` = every suite_v2 benchmark is certified end to end, modulo the
trust base.

## Earlier recipes

Until 2026-10-10 this document described the legacy suite (`suite_uniform`) and its
checks (`--check-quick`, `--run-verdicts`, `Instances/ModalBattery.lean`), with dated
records of full runs (the last cold-tree build of that development: 2026-08-02, 12h59m,
8988 jobs). That suite and those entry points were removed; the records are in the git
history of this file.
