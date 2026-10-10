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
