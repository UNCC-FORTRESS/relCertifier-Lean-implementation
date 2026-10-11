# Replaying the emitted cover (branch `replay`)

The paper's §6 says of every benchmark's Theorem 3 that "its proof follows the witness strategy
the tool emits". This document records, per benchmark, whether the kernel proof does that, and
the conversion of every proof that did not.

## 0. What "replays the emitted cover" means

The tool's witness strategy for a left window `l` is its emitted cover
(`relcert --emit-cover`, frozen in `InstancesV2/BenchCovers/<b>.lean` and re-decided in the
kernel by `InstancesV2/CoverReplay.lean`): the stretch `λ_l`, the budget `B_l`, per right mode
the certificates it established (`jointOK`: the joint segment of the pair `(l, q)` at `λ_l`;
`dynPre`/`dynPost`: the right-only reposition of `q` with the left held), the admissible starts,
the pruned edges, and the strata orders of every pack. Its derivation (`decideCovered`) answers
an admissible start `q` with a joint segment at a `jointOK` node followed by a switch into a
retained (declared, non-pruned) successor, all of which are covered, until the budget closes;
a start that is only a reposition node first moves alone along its exits.

A Theorem 3 proof **REPLAYS** the cover when, for every left window `l` and every start `q`:

* **R1** every joint segment of the response is at a `jointOK` node of `l`, at the cover's
  `λ_l`, and its flow fact (preservation of the rows and both sides' kept cut atoms) is the
  tool's verdict pack of that pair (`modalVerdX`, pinned to a row of
  `VerdictsV2/RunV2.packsV2`);
* **R2** every right-only reposition is at a node the cover flags `dynPre` (before the first
  joint segment) or `dynPost`, and its flow fact is the tool's reposition pack (`modalVerdDynX`,
  pinned to a row of `RunV2.dynPacksV2`);
* **R3** every switch follows a declared, non-pruned edge into a successor whose guard holds at
  the switch state (legality against the guards, as before); where the cover's step is a
  demonic successor set, the proof picks an enabled successor among the retained ones;
* **R4** a start the cover drops as inadmissible gets no response: the proof derives the
  contradiction of the left guard, the right mode's guard and the rows (the content of the
  tool's admissibility query).

Explicit solutions may supply the EXISTENCE of the right's runs and the instants of the
switches (they are not flow facts). They may not replace a pack as the preservation fact.

On the budget. The mechanized right automaton has no control-interval clock on its flows (a
joint segment at a node is a time-unbounded run, the `evolve` step of `RightReach`), and
Theorem 3 is stated for every window length `dt`, also beyond `ε_L`, the left residence the
cover's budget `B_l = ⌈ε_L λ_l / ε_R⌉` measures. A replay therefore uses one joint segment per
stretch the guards allow, and switches (R3) where the right would otherwise leave every
successor's guard; on windows within the cover's horizon this is the derivation's own
segment/switch structure, on longer windows the same structure iterated (every node it visits
is a node of the cover for `l`, every pack a pack of the cover).

## 1. Inventory before the conversion (`replay` at `4b6a6b0`, = `main`)

Columns: the headline theorem's response; the flow facts it uses (V2 = the tool's own
`modalVerdX` packs, pinned in `VerdictsV2/PinsV2`; legacy = the carried-over packs of
`Verdicts/RunModal.modalTable`, built on the bare evolve domains with legacy devices (ceiling
heads, tail faces, legacy λ and orders), not the emitted cover's queries; none = Z3-free); the
classification against R1 to R4.

| # | benchmark | response (before) | flow facts | class | why |
|---|---|---|---|---|---|
| 1 | `acc_spoof_lag` | joint segment at the start node, enabled switch, or no step | V2 (1) | REPLAY | |
| 2 | `acc_spoof_limp` | same, per left mode | V2 (6) | REPLAY | |
| 3 | `acc_tune_lag` | same | V2 (1) | REPLAY | |
| 4 | `acc_tune_limp` | same | V2 (6) | REPLAY | |
| 5 | `arm_plateau_crit` | explicit band climb after the window | none | EXPLICIT | own run, own preservation arithmetic; no pack; the `Brake` window's `ApproachA` start is a `dynPre` node in the cover |
| 6 | `arm_plateau_profiles` | explicit band climb | none | EXPLICIT | as above |
| 7 | `arm_plateau_slow` | explicit three-band climb | none | EXPLICIT | as above (`ApproachB` is only `dynPre`/`dynPost` for `Accelerate`) |
| 8 | `charger_fast_setpoints` | `BULK` right-only run to `max(x₀, 80)`, `BULK → ABSORB`, then joint segment | V2 (7) | EXPLICIT | the reposition's preservation is the proof's own arithmetic (no reposition pack; `BULK` is only `dynPre` for the `BULK`/`ABSORB` windows) |
| 9 | `charger_fast_tapers` | paths `BULK → ABSORB_* → FULL` (right-only), no step when `x_R ≥ 96`, cut runs | V2 (9) | EXPLICIT | repositions without packs; the idle response at `x_R ≥ 96` from an `ABSORB_*` start of the `BULK` window is not a cover step (those starts are `dynPre` nodes) |
| 10 | `match_multi_rate` | one explicit `DRIVE` run to the target after the window | none | EXPLICIT | own run and preservation; no pack |
| 11 | `platoon3_linkloss` | joint segment at the start node, legal self-loop | V2 (2) | REPLAY | |
| 12 | `platoon3_profiles` | same | V2 (3) | REPLAY | |
| 13 | `platoon_delay_linkloss` | joint segment, enabled switch | V2 (6) | REPLAY | |
| 14 | `platoon_delay_profiles` | same | V2 (6) | REPLAY | |
| 15 | `quad_light_airframe_20` | same | V2 (1) | REPLAY | |
| 16 | `quad_light_lag` | same | V2 (1) | REPLAY | |
| 17 | `quad_light_profiles` | same | V2 (3) | REPLAY | |
| 18 | `refinement_ladder_rover_rung1_2to3` | explicit ladder climb after the window | none | EXPLICIT | own runs and arithmetic; the cover repositions `STEEP`/`MODER` starts below the window's band |
| 19 | `refinement_ladder_rover_rung2_3to6` | synchronized climb, ordered bands | legacy (6) | EXPLICIT | legacy packs, not the emitted cover's queries |
| 20 | `refinement_ladder_rover_rung2_6dof` | explicit combined-coordinate climb | none | EXPLICIT | own arithmetic; cover has `dynPre` repositions |
| 21 | `refinement_ladder_rover_rung2b_6dof` | same | none | EXPLICIT | as above |
| 22 | `refinement_ladder_rover_rung2c_6dof` | mirror in the window's band | legacy (3) | EXPLICIT | legacy packs (with the tail-face device) |
| 23 | `refinement_ladder_rover_rung3_6to8` | explicit climb with a decay budget | none | EXPLICIT | own arithmetic (attitude form `Q`) |
| 24 | `refinement_ladder_rover_rung4_8to12` | explicit climb, weighted odometer | none | EXPLICIT | own arithmetic |
| 25 | `rover3tier_rung12` | one explicit run to the target, per left mode | none | EXPLICIT | own run and arithmetic |
| 26 | `rover_dof_terrain_rung1` | explicit ladder climb | none | EXPLICIT | as #18 |
| 27 | `rover_dof_terrain_rung2` | explicit ladder climb | none | EXPLICIT | as #18 |
| 28 | `rover_dof_terrain_rung3` | explicit ladder climb | none | EXPLICIT | as #18 |
| 29 | `rover_dof_terrain_rung3_8d` | explicit ladder climb | none | EXPLICIT | as #18 |
| 30 | `rover_patrol_refine` | explicit climb to `FAST`, linear-form cap | none | EXPLICIT | own arithmetic; cover repositions the lower zones |
| 31 | `rover_patrol_zones` | explicit climb to `FAST` | none | EXPLICIT | as above |
| 32 | `sat3w_detumble_nominal` | joint segment, enabled switch | V2 (1) | REPLAY | |
| 33 | `sat3w_detumble_phases` | same | V2 (2) | REPLAY | |
| 34 | `sat3w_detumble_weak` | same | V2 (3) | REPLAY | |
| 35 | `sat_detumble_nominal` | same | V2 (1) | REPLAY | |
| 36 | `sat_detumble_phases` | same | V2 (2) | REPLAY | |
| 37 | `sat_detumble_weak` | same | V2 (3) | REPLAY | |
| 38 | `story1_attdist_rung_a_6to8` | synchronized climb | legacy (9) | EXPLICIT | legacy packs |
| 39 | `story1_attdist_rung_b_12dof` | synchronized climb, two-piece windows, virtual-band stretch | legacy (6) | EXPLICIT | legacy packs; the three pairs below the window's band (all `jointOK` in the cover) are answered by a "virtual band" stretch with the proof's own arithmetic instead of their packs |
| 40 | `story2_lateral_rung_a_8dof` | synchronized climb, ordered bands | legacy (6) | EXPLICIT | legacy packs |
| 41 | `story2_lateral_rung_b_12dof` | same | legacy (6) | EXPLICIT | legacy packs |
| 42 | `story3_rollover_base_12dof` | explicit ladder climb; deployed-only conjuncts from packs | legacy (6) | EXPLICIT | own climb; legacy packs |
| 43 | `story3_rollover_ladder_rung_a` | same | legacy (6) | EXPLICIT | as above |
| 44 | `story3_rollover_ladder_rung_b` | synchronized climb at the cover's nodes | V2 (9) | REPLAY | every stretch at a `jointOK` node with its V2 pack, switches along retained edges |
| 45 | `watertank` | joint segment, enabled switch; a zero-duration hop `Low → MidBoost` for a `Low` start of the `Mid` window | V2 (11) | EXPLICIT | the hop is not a cover step: the cover drops `Low` as inadmissible for `Mid` (R4); with the mode-consistent region that start is contradictory, but the proof answers it with its own move |

Totals before: REPLAY 18, EXPLICIT 27: the 16 Z3-free theorems (#5, 6, 7, 10, 18, 20, 21,
23, 24, 25, 26, 27, 28, 29, 30, 31), the 8 carried-over theorems on legacy packs (#19, 22,
38, 39, 40, 41, 42, 43), `charger_fast_setpoints`, `charger_fast_tapers` (repositions without
their packs) and `watertank` (the hop). All 19 carried-over benchmarks are EXPLICIT (none of
their proofs uses the emitted cover's packs). The REPLAY ones answer every window with one
joint segment at the start node (or a synchronized chain of them, #44) and an enabled switch.

## 2. The replay layer (new leaves, no upstream edits)

| file | what it provides |
|---|---|
| `Proofs/Encoding/ReplayDyn.lean` | the reposition pack: `VerdDynCore`, `modalVerdDynX` (the tool's `OracleAPI.checkDynRepo` route A: `domain ∧ ġ > 0` UNSAT with the left field 0 at stretch 1, the domain the strata of both evolve domains, both sides' kept cut atoms and, for `dynPre`, the left guard); `couple_box_dyn` (the anchor of a pair is preserved along a right-only flow with the left held); `anchor_hand` (an anchor survives a switch into a mode whose guard implies its kept atoms) |
| `VerdictsV2/ModalDynX.lean` | `modalVerdDynXQueries`, the IR rebuild of a reposition pack, and its pin `modalVerdDynX_of_queries` |
| `Proofs/Encoding/ReplayEngine.lean` | the generic replay of one gated window: `replay_repo` (pre-joint repositions, each preserved by its reposition pack, until a joint node), `replay_piece` / `replay_pieces` (the joint segments of each clocked left piece at the cover's stretch `λ`, `joint_of_sols_lam`, each preserved by its joint pack, switching where the instance's choreography `HMove` says), `replay_gresp` |
| `Proofs/Encoding/ReplayOne.lean` | `replay_gresp_k`: the same, with the middle-of-window obligation needed only when the window has a piece boundary (one-piece windows whose right may end in a reposition-only mode) |
| `Proofs/Encoding/LadderReplay.lean` | the three-band odometer ladder's choreography (`ladder_hmove`, `ladder_hexit`) over its explicit band runs |
| `Proofs/Encoding/ContractRun.lean` | explicit contraction runs `x' = k (c − x)` as `ODESol`s and their crossing instants (`contract_hit_up/_down`, `contract_hit_le_up/_down`) |
| `Proofs/Encoding/ReplayBridge.lean` | `ofP_hsim_gated` / `ofGI_hsim_gated`: a guarded left edge of the carried-over left automata is a run of the gated window |
| `Proofs/Encoding/ReplayModeKeyed.lean` | `hstep_modeKeyed_g` (the mode-keyed step given the entered mode's guard, which the left edge tests) and `faModal_ungate` |
| `Proofs/Encoding/ReplayComps.lean` | `hostComps_atoms`: the tool's invariant components are the rows' atoms |
| `VerdictsV2/RunV2.lean`, `Main.lean` | the reposition table `dynPacksV2` and a fifth runner phase "suite_v2 reposition (dyn)" with its declared count `expectedDynV2` (`derivedDynV2_eq` in `CoveragePinsV2`) |
| `VerdictsV2/CoveragePinsV2.lean` | `packsV2_rowOfWindow`, `dynPacksV2_rowOfWindow`: every joint and reposition pack quotes the row the tool reads for the window's left mode (`Handoff.invRowOf`, by name), kernel-decided |

What an instance supplies is what the cover does not: the existence of the right's runs (explicit
solutions: the ladders' band runs, constant rates, contractions, the patrol zones' solutions with
their odometer crossings by the intermediate value theorem), the switch instants, the legality
of every switch against the entered mode's guard (`HMove`, `HExit`), and, for a start the cover
drops as inadmissible, the contradiction. Every preservation fact is a pack's.

## 3. After the conversion: all 45 replay the emitted cover

Columns: the replay (stretch `λ`; the joint nodes the response visits and its switches;
repositions; the starts the cover drops as inadmissible, answered by a contradiction); the
number of joint packs (`modalVerdX`, rows of `RunV2.packsV2`) and reposition packs
(`modalVerdDynX`, rows of `RunV2.dynPacksV2`) the headline theorem takes; whether it replays the
cover (R1 to R4). No benchmark is Z3-free any more: every flow fact is a pack.

| # | benchmark | replay | joint | repo | replays cover |
|---|---|---|---|---|---|
| 1 | `acc_spoof_lag` | unchanged: joint segment at `CRUISE` (λ 5/2), enabled switch | 1 | 0 | yes |
| 2 | `acc_spoof_limp` | unchanged | 6 | 0 | yes |
| 3 | `acc_tune_lag` | unchanged | 1 | 0 | yes |
| 4 | `acc_tune_limp` | unchanged | 6 | 0 | yes |
| 5 | `arm_plateau_crit` | λ 1; ramp `ApproachA → B → C → Hold` at the band ceilings; `Brake` from `ApproachA` repositions alone to 0.35 | 7 | 1 | yes |
| 6 | `arm_plateau_profiles` | λ 1; ramp `A → B → Cfast → Hold`, `Cslow → Hold` | 10 | 0 | yes |
| 7 | `arm_plateau_slow` | λ 1; `Accelerate`: `ApproachA` flows to 0.5 and switches into `ApproachC` (`ApproachB` is a reposition node of that window and repositions alone to 0.5); `Brake`: `B → C → Hold`, its `ApproachA` start inadmissible | 6 | 1 | yes |
| 8 | `charger_fast_setpoints` | λ 1; joint `ABSORB`, `FULL`, `ABSORB → FULL` at 99; `BULK` start of the `BULK`/`ABSORB` window repositions alone to 80, `BULK → ABSORB`; the `FULL` window's `BULK` start inadmissible | 6 | 2 | yes |
| 9 | `charger_fast_tapers` | λ 1; `BULK → ABSORB_FAST` at 80, tapers `→ FULL` at 99; the `BULK` window's `BULK`/taper starts reposition along `BULK → ABSORB_FAST → FULL`; the `FULL` window's `BULK` start inadmissible | 8 | 3 | yes |
| 10 | `match_multi_rate` | λ 3, 2, 1, 1; joint `DRIVE`, closing stay `DRIVE → DRIVE`; `STALL` (pruned sink) excluded by the region | 4 | 0 | yes |
| 11 | `platoon3_linkloss` | unchanged | 2 | 0 | yes |
| 12 | `platoon3_profiles` | unchanged | 3 | 0 | yes |
| 13 | `platoon_delay_linkloss` | unchanged | 6 | 0 | yes |
| 14 | `platoon_delay_profiles` | unchanged | 6 | 0 | yes |
| 15 | `quad_light_airframe_20` | unchanged | 1 | 0 | yes |
| 16 | `quad_light_lag` | unchanged | 1 | 0 | yes |
| 17 | `quad_light_profiles` | unchanged | 3 | 0 | yes |
| 18 | `refinement_ladder_rover_rung1_2to3` | λ 1; synchronized ladder climb in the joint bands; lower bands reposition up the ladder; `FLAT` window from `STEEP` inadmissible | 6 | 2 | yes |
| 19 | `refinement_ladder_rover_rung2_3to6` | λ 1; synchronized climb, ordered bands (`l ≤ q` forced) | 6 | 0 | yes |
| 20 | `refinement_ladder_rover_rung2_6dof` | λ 1001/1000, two-piece windows; `STEEP`/`MODER` starts of the `FLAT` window reposition up the chain | 6 | 3 | yes |
| 21 | `refinement_ladder_rover_rung2b_6dof` | as #20 | 6 | 3 | yes |
| 22 | `refinement_ladder_rover_rung2c_6dof` | `dt ≤ ε_L = 1`; λ 1; one joint segment at `(l, l)`, legal switch at its end; `q ≠ l` inadmissible | 3 | 0 | yes |
| 23 | `refinement_ladder_rover_rung3_6to8` | λ 9/4, three-piece windows; ladder climb; lower bands reposition; `FLAT` window from `STEEP` inadmissible | 6 | 2 | yes |
| 24 | `refinement_ladder_rover_rung4_8to12` | λ 17/10, two-piece windows; ladder climb; lower bands reposition; `FLAT` window from `STEEP` inadmissible | 6 | 2 | yes |
| 25 | `rover3tier_rung12` | `ACCEL` window λ 7/4, `COAST` window λ 1; both modes joint, `ACCEL → COAST` at `v_R = 0.6` | 4 | 0 | yes |
| 26–29 | `rover_dof_terrain_rung1`, `_rung2`, `_rung3`, `_rung3_8d` | λ 1; ladder climb; lower bands reposition; `FLAT` window from `STEEP` inadmissible | 6 each | 2 each | yes |
| 30 | `rover_patrol_refine` | λ 9/4; the route `SLOW → MEDIUM_ECO → FAST`, `MEDIUM_BRISK → FAST` at the odometer floors; zones below the window's reposition alone; the `FAST` window's `SLOW` start inadmissible | 10 | 5 | yes |
| 31 | `rover_patrol_zones` | as #30 at λ 1 | 10 | 5 | yes |
| 32–37 | `sat3w_detumble_*`, `sat_detumble_*` | unchanged | 1, 2, 3 | 0 | yes |
| 38 | `story1_attdist_rung_a_6to8` | λ 1; all nine pairs joint; synchronized climb at the declared row of each left mode | 9 | 0 | yes |
| 39 | `story1_attdist_rung_b_12dof` | λ 1, two-piece windows; all nine pairs joint (the virtual-band stretch is gone); the band ceiling carried as the ladder's cap | 9 | 0 | yes |
| 40 | `story2_lateral_rung_a_8dof` | λ 1; synchronized climb, ordered bands | 6 | 0 | yes |
| 41 | `story2_lateral_rung_b_12dof` | as #40 | 6 | 0 | yes |
| 42 | `story3_rollover_base_12dof` | λ 5/4; ladder climb; lower bands reposition; `FLAT` window from `STEEP` inadmissible | 6 | 2 | yes |
| 43 | `story3_rollover_ladder_rung_a` | λ 27/20; as #42 | 6 | 2 | yes |
| 44 | `story3_rollover_ladder_rung_b` | unchanged | 9 | 0 | yes |
| 45 | `watertank` | λ 2, 2, 1; joint segment at the start node, enabled switch; the inadmissible starts (`Low` window from `High`, `Mid` window from `Low`, `High` window from any mode but `High`) contradictory: the zero-duration hop is gone | 7 | 0 | yes |

Totals: **45 of 45 replay the emitted cover**; 0 Z3-free (was 16). The 45 headline theorems take
**234 joint packs** (every row of `RunV2.packsV2`, each consumed by exactly one headline) and
**41 reposition packs** (every row of `RunV2.dynPacksV2`): 275 pack hypotheses, against 132
before. Runner phases: suite_v2 modal **621** component queries (was 262), reposition **81**
(new phase; was 0); handoff 186, non-connection 88, pruned edges 44 and the copied benchmarks'
legacy packs 385 unchanged (the legacy phase now discharges only the packs of the carried-over
choice-form and relaxation theorems that remain in the tree; no headline theorem takes a legacy
pack).

Six rows of `RunV2.packsV2` that existed at `4b6a6b0` were dropped because the replay no
longer consumes them: their pairs are starts the cover drops as inadmissible
(`charger_fast_setpoints` and `charger_fast_tapers` `(FULL, BULK)`; `watertank` `(Low, High)`,
`(High, Low)`, `(High, MidEco)`, `(High, MidBoost)`); the later pins were renumbered.

## 4. Per-file changes

* Carried-over instances (`Instances/*Guarded.lean`): `RoverDofTerrainRung1/2/3/38dGuarded`,
  `RoverLadderRung1/2/3/4Guarded`, `RoverRung26dofGuarded`, `RoverRung2b6dofGuarded`,
  `RoverRung2cGuarded`, `Story1AttdistRungA/BGuarded`, `Story2LateralA/BGuarded`,
  `Story3RolloverBase/RungAGuarded`, `MatchMultiRateGuarded`, `Rover3tierRung12Guarded`: the
  response section is replaced by a replay (`replay_gresp` or `replay_gresp_k`); the instance
  adds its packs `Verd l q` / `VerdD l q` (the emitted cover's queries, `modalVerdX` /
  `modalVerdDynX` over `InstancesV2/BenchIR` and `InstancesV2/Cuts`), the cut atoms' entry
  (`hO1L`, `hO1R`) and staying (`stayL`, `stayR_gen`) lemmas, the anchors, and the choreography
  (`HMove`, `HExit`). Theorem names, automata, regions and rows are unchanged; the hypotheses
  are the new packs. `LeftAutLegacy.lean`: the `_leftAut` theorems take the packs and carry the
  gated choice to the left automaton with `ofP_hsim_gated` / `ofGI_hsim_gated`.
  `WellFormed/MatchMultiRate.lean`, `WellFormed/Rover3tierRung12.lean`: the explicit-run lemma
  moved into the instance.
* suite_v2 instances (`InstancesV2/Modal/`): `ArmPlateauCrit/Profiles/Slow`,
  `ChargerFastSetpoints/Tapers`, `RoverPatrolZonesGuarded`, `RoverPatrolRefineGuarded`,
  `Watertank`: the catch-up / climb / hop responses are replaced by replays (`Watertank`: the
  inadmissible starts become contradictions); `LeftAutV2.lean`: the `_leftAut` theorems take
  the packs.
* Tables and pins: `VerdictsV2/RunV2.lean` (`packsV2` 104 → 234 rows, `expectedModalV2`
  262 → 621; `dynPacksV2` 0 → 41 rows, `expectedDynV2` 0 → 81), `VerdictsV2/PinsV2.lean` (one pin
  per new row, `pin_<tag>_j<k>` / `pin_<tag>_d<k>`), `VerdictsV2/CoveragePinsV2.lean`
  (`derivedDynV2_eq`, the row-of-window pins), `Main.lean` (the fifth phase).

## 5. Unreplayable covers

None. Every cover was replayed legally: every joint segment at a `jointOK` node with its pack,
every reposition at a `dynPre` node with its pack, every switch along a declared, non-pruned
edge into a successor whose guard holds, every inadmissible start contradictory.
