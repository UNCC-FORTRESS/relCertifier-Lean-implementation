# Suite deduplication — 46 → 40 certified benchmarks (2026-10-08, branch `dedupe-suite`)

Status: landed 2026-10-08. Six benchmark directories removed with everything that
referenced them; no proof added, no surviving benchmark file touched. Every check
re-run green on the 40-benchmark suite (§5).

## 1. The finding, re-verified

Normalize every `benchmarks/suite_uniform/<name>/input.txt` by removing comments, blank
lines and the `name =` line, then group the results by content hash:

```bash
for b in benchmarks/suite_uniform/*/; do n=$(basename $b)
  sed -E 's/#.*$//; s/[[:space:]]+$//; /^[[:space:]]*$/d; /^name[[:space:]]*=/d' \
    $b/input.txt > norm/$n.txt
done
md5 -q norm/*.txt | sort | uniq -c | awk '$1>1'      # three hashes occur more than once
```

Three normalized files are byte-identical across several names (md5 of the normalized
text in parentheses), and one pair differs in a single constant:

| group | members (normalized text identical) | raw `diff` between members |
|---|---|---|
| arm high (`a857461a…`) | `arm_chain_rung3` = `arm_fidelity_high` = `plant_fan_high` | the leading `# <name> (REDESIGNED) …` comment and the `name =` line only (2 lines) |
| arm low (`d9dab6de…`) | `arm_fidelity_low` = `arm_refinement` = `plant_fan_low` | comment blocks and the `name =` line only |
| rover speed (`31a7341f…`) | `match_multi_eps` = `rover3tier_M1` | comment blocks, blank lines and the `name =` line (`rover3tier_M1`'s file still carries `name = rover_patrol_simple`; the parser takes the name from the directory, as `relcert-test`'s `[ir-drift]` check confirms) |
| arm mid | `arm_fidelity_mid` vs `plant_fan_mid` | comments, the `name =` line, and the tolerance constant in both invariant rows: `theta[l] <= theta[r] + 0.25` vs `+ 0.3` — same plant, same reference automaton, same guards and evolve domains |

The normalized diff of each identical group is empty; the mid pair's normalized diff is
exactly the two invariant rows:

```
38,39c38,39
< Accelerate = theta[l] <= theta[r] + 0.25
< Brake      = theta[l] <= theta[r] + 0.25
---
> Accelerate = theta[l] <= theta[r] + 0.3
> Brake      = theta[l] <= theta[r] + 0.3
```

This matches what the Lean side already recorded: the emitted IR, covers and cut
certificates of each group were identical up to the benchmark name, and
`docs/CUT-COMPOSITION.md` §2a/§2b describe the high trio and the mid pair as one system
each.

## 2. The decision and the removals

Removed (one representative kept per group): **`arm_fidelity_high`, `plant_fan_high`**
(keep `arm_chain_rung3`); **`arm_refinement`, `plant_fan_low`** (keep
`arm_fidelity_low`); **`match_multi_eps`** (keep `rover3tier_M1`); **`plant_fan_mid`**
(keep `arm_fidelity_mid`; the looser tolerance 0.3 adds nothing the 0.25 instance does
not certify). The certified suite is **40 benchmarks**; **41 inputs** with
`shield_unreachable`, which stays as the held-out discriminator.

Files deleted (`git rm`), 44 in all:

* `benchmarks/suite_uniform/<name>/` for the six;
* instance leaves: `Instances/ArmFidelityHighModal.lean`, `ArmFidelityHighDeclared.lean`,
  `PlantFanHighModal.lean`, `PlantFanHighDeclared.lean`, `ArmRefinementModal.lean`,
  `PlantFanLowModal.lean`, `MatchMultiEpsModal.lean`, `PlantFanMidModal.lean`,
  `PlantFanMidDeclared.lean` (9);
* emitted-data leaves: `Instances/BenchIR/<name>.lean` (6), `BenchCovers/<name>.lean`
  (6), `BenchCoversNC/` (`arm_refinement`, `match_multi_eps`, `plant_fan_low`,
  `plant_fan_mid`), `EvolStrengthenings/<name>.lean` (6), `Throughout/`
  (`arm_refinement`, `match_multi_eps`, `plant_fan_low`, `plant_fan_mid`),
  `CutThroughout/` (`arm_fidelity_high`, `plant_fan_high`) — 28;
* `Archive/Mega.lean` — the archived (vacuous-route) `arm_refinement` mega-theorem,
  which consumed `arm_refinementM`/`arm_refinement_IR`; its import in `RelCertifier.lean`
  went with it.

Files edited (removal only — lines or blocks naming the six; `row N` indices renumbered):
the aggregators `Instances/BenchIR.lean` (imports and `benchIRTable`), `BenchCovers.lean`,
`BenchCoversNC.lean`, `EvolStrengthenings.lean`, `ThroughoutBattery.lean`,
`CutThroughoutBattery.lean`; `BenchCoverReplay.lean`, `BenchViability2.lean` (1121 →
1085 faces), `FaithfulCerts.lean`, `SettlingInstances.lean` (25 → 19 settling models),
`RealInstances.lean` (46 → 40 `*_real`), `ModalSpecs.lean` (namespaces and `specs`),
`ModalBattery.lean` (imports and `#print axioms`; 59 → 50 theorems);
`Verdicts/RunModal.lean` (`modalTable` 47 → 41 rows), `Verdicts/RunCut.lean`
(`cutBenchmarks` 13 → 11), `Verdicts/ModalPinTable.lean` (58 → 49 theorems),
`ModalTablePins.lean` (47 → 41), `ModalCodePins.lean` (86 → 80) — all `row N`
references renumbered to the new table positions (old rows 3, 6, 11, 13, 14, 15
removed); `Verdicts/Coverage.lean` (`expected` 6/105/522/215 → **6/97/504/191**,
`expectedSuite` 47/46 → **41/40**), and `CoveragePins` re-proves the new constants by
`decide` against the tables; `Main.lean` help text; `scripts/gen_cut_throughout.py`,
`gen_real_instances.py` (`PADDED`), `h_audit.py`, `cover_drift.sh`, `gen_covers.sh`;
docstrings naming the six in `Proofs/Encoding/SplitCoupling.lean` and
`CutComposition.lean`, and the `match_multi_eps` face-shape analogy in
`RoverLadderRung1Modal.lean` / `RoverDofTerrainRung1Modal.lean` now names its surviving
twin `rover3tier_M1`.

### Counts, before → after

| quantity | before | after |
|---|---|---|
| benchmark inputs / certified | 47 / 46 | 41 / 40 |
| base modal theorems (`*_modal`; `rover3tier_rung12` has two) | 47 | 41 |
| mode-keyed theorems (`*_modeKeyed`) | 7 | 7 |
| cut-composed theorems (`*_declared`) | 5 | 2 |
| theorems in `ModalBattery` | 59 | 50 |
| … with `z3_unsat_sound` / standard three only | 46 / 13 | 40 / 10 |
| verdict packs in `RunModal.modalTable` | 47 (42 base + 5 mode-keyed) | 41 (36 + 5) |
| declared coverage: watertank / cut / modal / handoff | 6 / 105 / 522 / 215 | 6 / 97 / 504 / 191 |
| total Z3 queries in `--run-verdicts` | 848 | 798 |
| `--handoff` over all inputs | 216 (215 unsat + `shield_unreachable`) | 192 (191 + 1) |
| `Throughout` / `CutThroughout` instances | 33 / 13 | 29 / 11 |
| settling models / `*_real` theorems | 25 (+19 terrain, +2 affine) / 46 | 19 (+19, +2) / 40 |
| evolve-box faces in `BenchViability2` | 1121 | 1085 |
| benchmarks with a cover window at λ ≠ 1 | 23 | 21 |
| intra-window switch instances (`SplitCoupling`) | 5 | 3 |
| region-carrying base instances (`Hold` cut as invariant conjunct) | 5 | 2 |
| Lean files tracked in git (`git ls-tree`) | 416 | 378 |

## 3. The 40 benchmarks and their declared-invariant theorems

Columns: Table-1 group (the paper's Table 1 — groups as given in the task; see the note
on (†)); the Lean theorem that states the benchmark's DECLARED invariant — the base
modal theorem for mode-independent invariants, `*_modeKeyed`
(`Instances/*Handoff.lean`) for the seven mode-dependent ones, `*_declared`
(`Instances/*Declared.lean`) for the two checked-cut benchmarks whose base theorem
conditions on the `Hold` region; Z3-free = the theorem audits to the three standard
axioms alone (from the `ModalBattery` audit of §5); mode-dependent = the
`[relational_invariant]` block has more than one distinct row; max dim = the larger of
the two sides' `state_vars` counts; moving L / R = the number of state variables on
each side whose ODE right-hand side is not syntactically zero in at least one mode of
that side (`0`, `0.0`, `smt2:0`, `smt2:(- 0 0)` count as zero).

| # | benchmark | Table-1 group | declared-invariant theorem | Z3-free | mode-dependent | max dim | moving L / R |
|---|---|---|---|---|---|---|---|
| 1 | `watertank` | Water tank | `WatertankViability.watertank_modal_certified` | no | no | 1 | 1 / 1 |
| 2 | `arm_chain_rung1` | Arm fidelity tower | `ArmChainRung1Modal.arm_chain_rung1_modal` | no | no | 1 | 1 / 1 |
| 3 | `arm_chain_rung2` | Arm fidelity tower | `ArmChainRung2Modal.arm_chain_rung2_modal` | no | no | 1 | 1 / 1 |
| 4 | `arm_chain_rung3` | Arm fidelity tower | `ArmChainRung3Declared.arm_chain_rung3_declared` | **yes** | no | 2 | 2 / 1 |
| 5 | `arm_fidelity_low` | Arm fidelity tower | `ArmFidelityLowModal.arm_fidelity_low_modal` | no | no | 2 | 2 / 1 |
| 6 | `arm_fidelity_mid` | Arm fidelity tower | `ArmFidelityMidDeclared.arm_fidelity_mid_declared` | **yes** | no | 2 | 2 / 1 |
| 7 | `robot_braking` | Robot braking | `RobotBrakingModal.robot_braking_modal` | no | no | 1 | 1 / 1 |
| 8 | `endurance_gain_M1` | Endurance speed-match | `EnduranceGainM1Modal.endurance_gain_M1_modal` | no | no | 2 | 2 / 2 |
| 9 | `endurance_orderlift_1to2` | Endurance speed-match | `EnduranceOrderlift1to2Modal.endurance_orderlift_1to2_modal` | no | no | 3 | 3 / 2 |
| 10 | `endurance_orderlift_2to3` | Endurance speed-match | `EnduranceOrderlift2to3Modal.endurance_orderlift_2to3_modal` | no | no | 4 | 4 / 3 |
| 11 | `match_multi_rate` | Multi-cycle matching | `MatchMultiRateModal.match_multi_rate_modal` | no | no | 2 | 2 / 2 |
| 12 | `attitude_rate` | Attitude rate | `AttitudeRateModal.attitude_rate_modal` | no | no | 6 | 6 / 6 |
| 13 | `rover3_M1` | Rover box/tier | `Rover3M1Handoff.rover3_M1_modeKeyed` | **yes** | **yes** | 2 | 2 / 2 |
| 14 | `rover3tier_M1` | Rover box/tier | `Rover3tierM1Modal.rover3tier_M1_modal` | no | no | 2 | 2 / 2 |
| 15 | `rover3tier_rung12` | Rover box/tier | `Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed` | no | **yes** | 3 | 3 / 2 |
| 16 | `rover_4d_box` | Rover box/tier | `Rover4dBoxModal.rover_4d_box_modal` | no | no | 4 | 0 / 4 |
| 17 | `rover_coupled` | Rover box/tier | `RoverCoupledHandoff.rover_coupled_modeKeyed` | **yes** | **yes** | 4 | 4 / 3 |
| 18 | `rover_position` | Rover box/tier | `RoverPositionHandoff.rover_position_modeKeyed` | **yes** | **yes** | 4 | 4 / 3 |
| 19 | `rover_terrain_M1` (†) | Rover box/tier | `RoverTerrainM1Modal.rover_terrain_M1_modal` | no | no | 2 | 2 / 2 |
| 20 | `rover_tier_r1` | Rover box/tier | `RoverTierR1Modal.rover_tier_r1_modal` | no | no | 3 | 3 / 2 |
| 21 | `rover_drag` | Rover drag | `RoverDragModal.rover_drag_modal` | no | no | 1 | 1 / 1 |
| 22 | `refinement_ladder_rover_rung1_2to3` | Terrain/pos. ladder | `RoverLadderRung1Modal.rover_ladder_rung1_modal` | no | no | 3 | 3 / 2 |
| 23 | `refinement_ladder_rover_rung2_3to6` | Terrain/pos. ladder | `RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal` | no | no | 6 | 6 / 4 |
| 24 | `refinement_ladder_rover_rung2_6dof` | Terrain/pos. ladder | `RoverRung26dofModal.rung2_6dof_modal` | **yes** | no | 4 | 4 / 2 |
| 25 | `refinement_ladder_rover_rung2b_6dof` | Terrain/pos. ladder | `RoverRung2b6dofModal.rung2b_6dof_modal` | **yes** | no | 6 | 6 / 2 |
| 26 | `refinement_ladder_rover_rung2c_6dof` | Terrain/pos. ladder | `RoverRung2cModal.rover_rung2c_modal` | no | no | 6 | 6 / 4 |
| 27 | `refinement_ladder_rover_rung3_6to8` | Terrain/pos. ladder | `RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal` | no | no | 8 | 8 / 6 |
| 28 | `refinement_ladder_rover_rung4_8to12` | Terrain/pos. ladder | `RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal` | no | no | 12 | 12 / 9 |
| 29 | `rover_dof_terrain_rung1` | Terrain/pos. ladder | `RoverDofTerrainRung1Modal.rover_dof_terrain_rung1_modal` | no | no | 3 | 3 / 2 |
| 30 | `rover_dof_terrain_rung2` | Terrain/pos. ladder | `RoverDofTerrainRung2Modal.rover_dof_terrain_rung2_modal` | no | no | 6 | 6 / 3 |
| 31 | `rover_dof_terrain_rung3` | Terrain/pos. ladder | `RoverDofTerrainRung3Modal.rover_dof_terrain_rung3_modal` | no | no | 12 | 10 / 6 |
| 32 | `rover_dof_terrain_rung3_8d` | Terrain/pos. ladder | `RoverDofTerrainRung38dModal.rover_dof_terrain_rung3_8d_modal` | no | no | 8 | 8 / 6 |
| 33 | `story1_attdist_rung_a_6to8` | Attitude distance | `Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed` | no | **yes** | 8 | 8 / 6 |
| 34 | `story1_attdist_rung_b_12dof` | Attitude distance | `Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed` | no | **yes** | 12 | 12 / 9 |
| 35 | `story2_lateral_rung_a_8dof` | Lateral keeping | `Story2LateralAModal.story2_lateral_rung_a_modal` | no | no | 8 | 7 / 7 |
| 36 | `story2_lateral_rung_b_12dof` | Lateral keeping | `Story2LateralBModal.story2_lateral_rung_b_modal` | no | no | 12 | 12 / 8 |
| 37 | `story3_rollover_base_12dof` | Rollover energy | `Story3RolloverBaseModal.story3_rollover_base_modal` | no | no | 12 | 12 / 6 |
| 38 | `story3_rollover_ladder_rung_a` | Rollover energy | `Story3RolloverRungAModal.story3_rollover_rung_a_modal` | no | no | 12 | 7 / 6 |
| 39 | `story3_rollover_ladder_rung_b` | Rollover energy | `Story3RolloverRungBHandoff.story3_rollover_rung_b_modeKeyed` | no | **yes** | 12 | 12 / 7 |
| 40 | `rover_attitude_cone_12dof` | Attitude cone | `RoverAttitudeConeModal.rover_attitude_cone_modal` | no | no | 12 | 12 / 8 |

(†) `rover_terrain_M1` is not named by the task's group list. The paper's Table 1 gives
Rover box/tier 8 members (1–4D) and Terrain/pos. ladder 11 (2–12D); the seven
`refinement_ladder_rover_*` and four `rover_dof_terrain_*` benchmarks fill the ladder
group exactly, so `rover_terrain_M1` (2D, the M1 rover speed envelope lifted to a terrain
profile) is placed in Rover box/tier as its eighth member. Flagged here because it is an
inference from the counts, not a statement in the docs.

Several base theorems in this table state the declared row **plus** bookkeeping that is
not part of the declared invariant: the ceiling heads `v_R ≤ c_m` of the terrain
composites (`rover_attitude_cone_12dof`, `refinement_ladder_rover_rung3_6to8`,
`rung4_8to12`, `rover_tier_r1`, `story3_rollover_base_12dof`,
`story3_rollover_ladder_rung_a`, and `story1_attdist_rung_b_12dof`'s mode-keyed form)
and `rung2c`'s tail region — the tool's checked cuts, carried as mode regions
(`docs/PAPER-MAPPING.md` §2c, `docs/VERDICTS.md` *The composite tier*). They are listed
as the declared-invariant theorems because the region is a mode-region conjunct of the
loop invariant (`mvRegionR`), not a strengthening of the row.

### Totals

| group | count |
|---|---|
| Water tank | 1 |
| Arm fidelity tower | 5 |
| Robot braking | 1 |
| Endurance speed-match | 3 |
| Multi-cycle matching | 1 |
| Attitude rate | 1 |
| Rover box/tier | 8 |
| Rover drag | 1 |
| Terrain/pos. ladder | 11 |
| Attitude distance | 2 |
| Lateral keeping | 2 |
| Rollover energy | 3 |
| Attitude cone | 1 |
| **total** | **40** |

* **Mode-dependent invariants: 7** (`rover3_M1`, `rover_coupled`, `rover_position`,
  `rover3tier_rung12`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof`,
  `story3_rollover_ladder_rung_b`) — as expected.
* **Z3-free declared-invariant theorems: 7** (`rover3_M1`, `rover_coupled`,
  `rover_position`, `refinement_ladder_rover_rung2_6dof`,
  `refinement_ladder_rover_rung2b_6dof`, `arm_chain_rung3`, `arm_fidelity_mid`) —
  confirmed from the axiom audit of §5, which prints exactly these seven theorems
  (the three `*_modeKeyed`, the two catch-up `*_modal`, the two `*_declared`) plus the
  three Z3-free *base* theorems of the rover trio at `[propext, Classical.choice,
  Quot.sound]`; every other theorem adds `z3_unsat_sound`.
* **Right side has fewer moving variables than the left: 27** with the criterion above
  (expected 26). The three borderline rows are `rover3tier_rung12` and `rover_tier_r1`,
  whose right side writes `a' = smt2:(- 0 0)` (counted as zero here; counting it as
  nonzero gives 25), and `story3_rollover_ladder_rung_a` (7 vs 6: both sides freeze five
  coordinates, the right also freezes `r`). The full per-benchmark moving-variable
  counts are in the table, so any other criterion can be re-totalled from it.
* **Max state dimension: 12** (`refinement_ladder_rover_rung4_8to12`,
  `rover_attitude_cone_12dof`, `rover_dof_terrain_rung3`, `story1_attdist_rung_b_12dof`,
  `story2_lateral_rung_b_12dof`, the three `story3_rollover_*`).

## 4. Rebuild cost

The removal touched only whole-suite aggregators, the runner/pin layer, and two
`Proofs/` docstrings (`SplitCoupling`, `CutComposition`) whose importers are the ≤ 6-dof
catch-up, switch and declared leaves. Warm `lake build`: 8969 jobs, 1m27s wall, exit 0;
no 8–12-dof instance re-elaborated.

## 5. Verification on the 40-benchmark suite (2026-10-08, Z3 4.15.1)

`lake build` (warm): `Build completed successfully (8969 jobs)`, exit 0; `lake build
relcert relcert-test`: exit 0.

`./.lake/build/bin/relcert --check-quick benchmarks/suite_uniform/*/input.txt` (tail):

```
errors=1
  [suite] 40 certified, 0 declined, 1 error(s) — matches the declared suite
HANDOFF PHASE COMPLETE (0 declared failure(s), as expected)
  [coverage] watertank: 6/6 hypotheses discharged
  [coverage] cut probes: 97/97 hypotheses discharged
  [coverage] modal: 504/504 hypotheses discharged
  [coverage] handoff: 191/191 hypotheses discharged
  suite:    PASS
  verdicts: PASS
QUICK CHECKS PASSED  (the kernel check is `lake build` — see --help)
```

`BENCH_PATHS=<manifest of the 41 inputs> ./.lake/build/bin/relcert-test`:

```
relcert-test — trusted-layer suite

[z3-layer]
  ok   known-UNSAT → unsat
  ok   known-SAT → sat
  ok   malformed SMT → error (not a verdict)
  ok   check on closed session → error
  ok   missing z3 binary → error
[parser]
  ok   malformed input → none
  ok   offset atom parses
  ok   quadratic atom parses
  ok   product atom parses
  ok   smt2 atom parses
  ok   empty-arg sexpr rejected
  ok   op-dropping (op x) rejected
  ok   unknown expr op rejected
  ok   unknown cmp op rejected
  ok   (and) not top
  ok   minimal skeleton parses
  ok   unparsable invariant line → error (was: dropped)
  ok   pair-keyed invariant row → error (dead syntax)
  ok   invariant key not a mode → error
  ok   unprojected var in invariant → error
  ok   undeclared var in evolve → error
  ok   missing ode for state var → error
  ok   unresolved next → error
  ok   duplicate key → error
  ok   junk line → error
  ok   missing guard → error
  ok   malformed numeral → error
  ok   ode LHS without prime → error
[ir-drift]
  ok   all 40 IR literals match their files
[smt-printer]
  ok   golden var
  ok   golden neg-rat
  ok   golden frac
  ok   golden nested sub
  ok   golden ne
  ok   2x−1 arithmetic (sat)
  ok   2x−1 bound (unsat)
  ok   exact rational (unsat)
  ok   neg literal square (unsat)
[lowering]
  ok   offset → 1 component
  ok   multi-conjunct → n components
  ok   quadratic → 1 component
  ok   product/bilinear → 1 component
  ok   unlowerable (division of vars) → none
[outcome-integrity]
  ok   missing z3 → ERROR
  ok   unparsed input → ERROR
  ok   unreadable file → ERROR
[determinism / oracle-consistency]
  ok   watertank: 8× identical CERTIFIED
  ok   declined benchmark: 8× identical verdict

ALL PASS
```

`./.lake/build/bin/relcert --run-verdicts` (tail):

```
HANDOFF PHASE COMPLETE (0 declared failure(s), as expected)
  [coverage] watertank: 6/6 hypotheses discharged
  [coverage] cut probes: 97/97 hypotheses discharged
  [coverage] modal: 504/504 hypotheses discharged
  [coverage] handoff: 191/191 hypotheses discharged
ALL HYPOTHESES DISCHARGED
```

`./.lake/build/bin/relcert --handoff benchmarks/suite_uniform/*/input.txt` (the one FAIL
is the documented `shield_unreachable` self-loop, exit 1 by design):

```
  FAIL  shield_unreachable Cruise -> Cruise  (handoff query did not lower)
  [handoff] shield_unreachable: 1/1 transitions checked, 0 passed, failing: 0->0 (vacuous: mode-independent invariant) (0ms)
handoff: 192 transition(s) checked over 41 benchmark(s)
```

`lake build RelCertifier.Instances.ModalBattery 2>&1 | grep -A3 "depends on axioms"` —
50 theorems, 40 with `z3_unsat_sound`, 10 standard-three, no `sorryAx`, no
`native_decide`, no other axiom:

| theorem | axioms |
|---|---|
| `RelCertifier.ArmChainRung1Modal.arm_chain_rung1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.ArmChainRung2Modal.arm_chain_rung2_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.ArmChainRung3Modal.arm_chain_rung3_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.ArmFidelityLowModal.arm_fidelity_low_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.ArmFidelityMidModal.arm_fidelity_mid_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.AttitudeRateModal.attitude_rate_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.EnduranceGainM1Modal.endurance_gain_M1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.EnduranceOrderlift1to2Modal.endurance_orderlift_1to2_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.EnduranceOrderlift2to3Modal.endurance_orderlift_2to3_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.MatchMultiRateModal.match_multi_rate_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverLadderRung1Modal.rover_ladder_rung1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverRung26dofModal.rung2_6dof_modal` | **std 3 only** |
| `RelCertifier.RoverRung2b6dofModal.rung2b_6dof_modal` | **std 3 only** |
| `RelCertifier.RoverRung2cModal.rover_rung2c_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverLadderRung3Modal.rover_ladder_rung3_6to8_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverLadderRung4Modal.rover_ladder_rung4_8to12_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RobotBrakingModal.robot_braking_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Rover3M1Modal.rover3_M1_modal` | **std 3 only** |
| `RelCertifier.Rover3tierM1Modal.rover3tier_M1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Rover3tierRung12Modal.rover3tier_rung12_modal_ACCEL` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Rover3tierRung12Modal.rover3tier_rung12_modal_COAST` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Rover4dBoxModal.rover_4d_box_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverAttitudeConeModal.rover_attitude_cone_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverCoupledModal.rover_coupled_modal` | **std 3 only** |
| `RelCertifier.RoverDofTerrainRung1Modal.rover_dof_terrain_rung1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverDofTerrainRung2Modal.rover_dof_terrain_rung2_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverDofTerrainRung3Modal.rover_dof_terrain_rung3_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverDofTerrainRung38dModal.rover_dof_terrain_rung3_8d_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverDragModal.rover_drag_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverPositionModal.rover_position_modal` | **std 3 only** |
| `RelCertifier.RoverTerrainM1Modal.rover_terrain_M1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.RoverTierR1Modal.rover_tier_r1_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story1AttdistRungAModal.story1_attdist_rung_a_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story1AttdistRungBModal.story1_attdist_rung_b_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story2LateralAModal.story2_lateral_rung_a_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story2LateralBModal.story2_lateral_rung_b_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story3RolloverBaseModal.story3_rollover_base_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story3RolloverRungAModal.story3_rollover_rung_a_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story3RolloverRungBModal.story3_rollover_rung_b_modal` | std 3 + `z3_unsat_sound` |
| `RelCertifier.WatertankModal.watertank_modal_certified` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Rover3M1Handoff.rover3_M1_modeKeyed` | **std 3 only** |
| `RelCertifier.RoverCoupledHandoff.rover_coupled_modeKeyed` | **std 3 only** |
| `RelCertifier.RoverPositionHandoff.rover_position_modeKeyed` | **std 3 only** |
| `RelCertifier.Story1AttdistRungAHandoff.story1_attdist_rung_a_modeKeyed` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story1AttdistRungBHandoff.story1_attdist_rung_b_modeKeyed` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Story3RolloverRungBHandoff.story3_rollover_rung_b_modeKeyed` | std 3 + `z3_unsat_sound` |
| `RelCertifier.Rover3tierRung12Handoff.rover3tier_rung12_modeKeyed` | std 3 + `z3_unsat_sound` |
| `RelCertifier.ArmChainRung3Declared.arm_chain_rung3_declared` | **std 3 only** |
| `RelCertifier.ArmFidelityMidDeclared.arm_fidelity_mid_declared` | **std 3 only** |

## 6. Not changed, deliberately

* `docs/history/*`, `docs/archive/*`, `docs/VERDICT-EVIDENCE-AUDIT.md`,
  `docs/VIABILITY-FACE-CENSUS.md` and the dated run records in `docs/VERDICTS.md` and
  `docs/HANDOFF.md` are records of the suite as it was measured; they keep their counts
  and the removed names, under a note at the top where one was needed.
* `Archive/DecayDischarge.lean` (built) mentions `match_multi_eps` in a docstring as a
  shape analogy and depends on nothing removed; `Archive/BenchViability.lean` (not
  built — not imported from `RelCertifier.lean`) carries the retired per-mode viability
  lists of the six. Both left as archived records.
* The paper-side benchmark list is a separate repository and is not touched here.
