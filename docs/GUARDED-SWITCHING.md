# Guard-gated switching on the right (branch `guarded-right`)

**Status (2026-10-10, branch `guarded-right`): done.** 22 of the 45 benchmarks carry Theorem 3
over the guarded right automaton; for 21 the guarded statement is false as stated (two
refutations are machine-checked); for 2 it is open. Summary table: section 6.

## 1. The problem

The paper's nominal model `R` switches only into a declared successor whose guard holds at
the switch state (`cpsProg`: `?(m ∈ next(mv)) ; ?guard_m(x) ; mv := m ; flow`); staying in
a mode is the same move with `m = mv`, so a stay also tests the mode's own guard. The
mechanized right automaton already has this shape (`modeStep` in
`Proofs/Encoding/JointBridge.lean`: `?(mv = q) ; flow_q ; ⋃_e (?e.guard ; mv := e.tgt)`, a
rotation of the paper's loop body), but every graph the instances built set
`e.guard := ⊤`, and the bridge lemmas took the premise `htt : ∀ q e, e.guard = ⊤`. The
existential witnesses could therefore switch anywhere: zero-duration hops, self-loop
"stays" after a segment, switches after a dynamic reposition. The theorems were about the
declared-successor relaxation of `R`.

## 2. Inventory of the generic layer (where `⊤` guards are set or assumed)

Edge construction with `guard := ⊤`:

* `Checker/CoverEmit.lean:82` (`coverGraph` of an emitted cover) and
  `Proofs/Encoding/CoverInstance.lean:124` (`realGraphOf`): the cover-based family; no
  battery theorem is stated over these graphs.
* `Checker/WellFormedChecker.lean:439, 575, 588, 668`: the retired settling checker's
  graph.
* Every instance: `edgeW`/`edgeX`/`edgeM`/`edgeV`/… in the 26 `InstancesV2/Modal/*.lean`
  and the 24 legacy modules `Instances/*.lean`.

Lemmas whose premise is `htt` (or a per-edge `e.guard = ⊤`):

| file | lemmas | on the battery's path before this branch |
|---|---|---|
| `JointBridge.lean` | `SelfEdges` (definition), `rightReach_is_R_real_run` | no |
| `BridgeReposition.lean` | `single_seg_R_real`, `faithful_rights_bridge`, `hstep_single_multi`, `hstep_assembled_multi` | yes (`faithful_rights_bridge` via the F chain) |
| `EnvelopeChain.lean` | `hstep_single_multiE`, `hstep_assembled_multiE`, the E-shape `hddF` | via `hddF_multiE` (legacy) |
| `EnvelopeChainM.lean` | `hstep_single_multiF`, `hstep_assembled_multiF` | yes (legacy F instances) |
| `EnvelopeChainR.lean` | `faithful_rights_bridge_pinned`, `hstep_single_multiR`, `hstep_assembled_multiR`, `hddF_multiR` | yes (all R instances) |
| `ModeHandoff.lean` | `hstepMode_multiF`, `hstepMode_multiR`, `hd_modeKeyed`, `hddF_modeKeyed`, `notMem_bv_rightAutomatonBody` | yes (all mode-keyed instances) |
| `UniformFvDischarge.lean` | `vars_modeStepU_sub`, `vars_bodyU_sub`, three `hddF`/`hd` dischargers | yes (`vars_bodyU_sub` everywhere) |
| `CutComposition.lean` | `hddF_multiR_plain` | yes (`match_multi_rate_pruned`) |
| `SinkExtension.lean` | `extend_htt` and the sink-extension step | yes (`match_multi_rate_pruned`) |
| `UniformMultiflow.lean`, `CoverExtract.lean`, `RepositionFinish.lean`, `RepositionEndToEnd.lean`, `RepositionDischarge.lean`, `BridgeDischarge.lean`, `BridgeUnit1/2.lean`, `ClockedTop.lean`, `Soundness/GuardThreaded.lean`, `FvDischarge.lean:418` | the Emit-carrying, cover-based and retired settling/clocked families | no |

Zero-duration hops (a flow of duration 0 followed by a switch):
`RepoPrefixR.static_hop_existsR`, `faModalB_repoPrefixR`/`faModalB_repoPathR`,
`WindowRF.Hmulti_windowRF_prefixed` (its `hops` list), `EnvelopeChainM.Hmulti_window1_prefixedF`
(its `hops` list), `CutComposition.sem_bigSeq_identity`, and the local `static_hop*`
lemmas of the legacy modules.

## 3. The guarded generic layer (`Proofs/Encoding/GuardedSwitch.lean`, new leaf)

* **Right program.** Unchanged: `rightAutomatonBody G mv` (its `modeStep` already tests
  `e.guard`). What changes is the graph: every edge carries the lowered guard of the mode it
  ENTERS, `e.guard = hostGuard vars n Side.R (mR e.tgt)`, built exactly as the left windows'
  guards (`hostGuard … Side.L (mL l)`). Each migrated instance proves this as `Gr_guards`.
* **`SwitchLegal e ω := Formula.sat e.guard ω`**, the per-switch obligation.
* **`gseg s := flow_{s.mode} ; ?s.edge.guard`**: a segment with its switch test. A run of
  `bigSeq (segs.map gseg)` is a sequence of flows, each followed by a legal switch.
* **`guarded_rights_bridge`**: such a run is a run of `star (rightAutomatonBody G mv)`, the
  mode variable threaded `q0 ↦ qfOf segs q0`. No premise on the guards (it needs only that
  `mv` is fresh for them, `GuardsFresh`).
* **`GResp G q P post σ`**, the guarded step obligation: for every run of the left program
  `P` from `σ` there are declared, chained segments from `q`, every switch legal, ending where
  `post` of the final mode holds. The segments are chosen after the left run, so the final
  switch can depend on the end state (the demonic successor choice is resolved by choosing an
  enabled successor).
* **Loop steps:** `hstep_single_GR`/`hstep_assembled_GR` (region chain `phiInvR`),
  `hstep_single_GF`/`hstep_assembled_GF` (`mvValid` chain), `hstepMode_GR`/`hstepMode_GF`
  (per left mode, for `theorem3_modeKeyed`). The top-level assemblies
  (`theorem3_faithful_multiR_LR`, `theorem3_modeKeyed`, …) take any `hstep` over
  `star (rightAutomatonBody G mv)` and are reused unchanged.
* **Building blocks:** `gresp_gate` (the left window's own guard test), `gresp_hop` (a
  zero-duration flow followed by a legal switch, legality required at the left run's end
  state), `gresp_final` (the certified response flow, then a switch into an enabled
  successor), `gresp_final_idle` (the same, or no step at all when the flow had zero
  duration), `gresp_idle` (no step at all), `gresp_mono`, `sat_framed`/`notMem_bv_of_vars`
  (right-only facts survive the left window), `ode_coord_end_lt_or_eq` (a flow cannot end on
  an upper face it pushes away from, unless it has zero duration).
* **More building blocks** (added during the migration): `gresp_final_choose` (the general
  one-flow response: no step, or the same mode's run from the left run's end to a chosen
  point, then an enabled switch), `gresp_final_pre` (a legal prefix of guarded segments before
  the final flow), `faModalB_repoPrefixG` / `hopAG` (the dynamic right-only reposition with its
  switch test, the guarded counterparts of `faModalB_repoPrefix` and the instances' `hopA`),
  `ode_run_hits` (cut a run where a coordinate reaches a level), `ode_linear_coord` (a linear
  coordinate along a run is `c + (x₀ − c) e^{−k r}`), `ode_coord_mono`, `windowSeg_preserve`,
  `hdis_multi_G`, `hddF_multiR_plain_G`, `rsplit_eval`/`sat_canonInv_bi` (relational
  semantics at a bi-state, used by the refutations).
* **`NonblockingAt G qs Post' post`**: from every state `Post'` describes, some declared
  successor of `qs` is enabled and the loop postcondition holds for it. This is Assumption 1
  (successor-completeness / nonblocking) restricted to the end states of the response; every
  instance that uses `gresp_final` discharges it from the explicit end state.
* **Footprints without `htt`:** `vars_bodyG_sub`, `hddF_multiR_G`, `hd_modeKeyed_G`,
  `hddF_modeKeyed_G`, `notMem_bv_rightAutomatonBody_G`, `hostGuard_fv_R`; the only new
  premise is `GuardsRight G` (the guards read right coordinates).

The `htt` lemmas of section 2 are left in place for the retired families; no migrated
instance uses them (a guarded graph cannot satisfy `htt`).

## 4. Classification of the switches in the witnesses (Phase 0)

Kinds: **(a)** zero-duration hop into `q'` at the window start; **(b)** self-loop stay
`q → q` after a segment; **(c)** switch after a dynamic right-only reposition; **(d)** the
post-joint continuation (the proof fixes a successor although the real right may need
another). In the old witnesses every (b) is also a (d): the stay was fixed in advance.

### 4.1 The 26 suite_v2 instances

All 26 call `Hmulti_windowRF_prefixed` with an EMPTY hop list (the `static_hop_existsR`
inside their `respond` lemmas is vacuous). Their live switches:

| benchmark | switches in the old witness | legality as constructed | plan |
|---|---|---|---|
| `watertank` | (b) stays in every certified pair; (a) `Low → MidBoost` for a `Low` start of the `Mid` window | (a) legal: `10 ≤ x_R ≤ 12.5 ⊆ [10,17)` from the `Mid` guard, the row and `Low`'s region. (b) illegal as constructed: `MidEco`/`MidBoost` end in `[10,17]`, guard `[10,17)` | rebuilt as (d): switch into the enabled successor (`High` at `x_R = 17`) |
| `acc_tune_limp` | (b) | legal: guards `[20,36]` closed, regions `[20,36]` | (d) over the same graph |
| `acc_spoof_limp`, `acc_spoof_lag`, `acc_tune_lag` | (b) | illegal only at `v_R = 40` (region `[20,40]`, guard `[20,40)`, `DISENGAGE` a pruned sink) | positive-duration flows end below 40 (`ode_coord_end_lt_or_eq`, field `k(c − v) < 0` at 40); a zero-duration response makes no step (`gresp_final_idle`) |
| `platoon_delay_profiles` | (b) | legal (closed `FOLLOW` guard; `GENTLE`/`ASSERTIVE` region = guard) | (d) |
| `platoon_delay_linkloss` | (b) | `FOLLOW` at `g_R = 40` illegal as a stay, `CATCH` (`g ≥ 30`) enabled | (d) |
| `quad_light_airframe_20`, `quad_light_lag`, `quad_light_profiles` | (b) | legal (region = guard `[0, 2.6]`) | (d) |
| `charger_fast_setpoints` | (b); (c) `BULK` run to `x_R = max(x0, 80)` then `BULK → ABSORB` | (c) legal (lands in `[80,90] ⊆ [80,99)`); (b) `BULK` at `[80,90]` and `ABSORB` at `[99,100]` illegal as stays, successors enabled | (d) |
| `charger_fast_tapers` | (b); (c) paths `BULK → ABSORB_FAST → FULL`, `ABSORB_* → FULL` | (c) `BULK → ABSORB_FAST` illegal when `x0 ≥ 99` (lands at `x0`); (b) `BULK` stays end anywhere in `[15,100]`, no successor enabled at `x_R ≥ 99` | rebuilt: no step when `x_R ≥ 96` (the row holds since `x_L ≤ 100`); otherwise the paths with their switch tests (`hopAG`), and a `BULK` stay that ends at `x_R ≥ 99` is cut at `x_R = 96` (`ode_run_hits`) and switches into `ABSORB_SLOW` |
| `arm_plateau_crit`, `arm_plateau_profiles` | (b) after an explicit catch-up run in the start mode | illegal: the catch-up crosses the band boundaries inside one mode; `ApproachA` above `0.5` has no enabled successor | rebuilt: a climb `ApproachA` → (switch at 0.35) → `ApproachB` → (switch at the target) or no step; a sharp end-of-window bound (`Accelerate` ends below `0.755`, `Brake` below its start: two more DI links of the chain) shows the target is at most `0.5` whenever the right lags |
| `arm_plateau_slow` | as above | illegal | the guarded statement is false: §4.3 |
| `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}` | (b) | legal: the region contains `E_R ≤ 1`, the guard | (d) |
| `platoon3_profiles`, `platoon3_linkloss` | (b) | illegal as constructed: the region (linear-form atoms, `g ∈ [24,36]`, `|r|` up to 2) is not covered by the successors' guards (`|r_i| ≤ 1` in every non-sink mode) | open: see 4.4 |
| `rover_patrol_zones`, `rover_patrol_refine` | (b); (c) zone runs to `s_R = max(s0, lo_{q'})` then `q → q'` | (c) illegal when `s0 ≥ hi_{q'}`; (b) illegal: zone regions bound `s_R` only from below | see 4.2 (counterexample) |
| `story3_rollover_ladder_rung_b` | (b) | illegal: regions `s_R ≥ sK q` only | see 4.2 (counterexample) |

### 4.2 The legacy modules (19 benchmarks)

`match_multi_rate` (in place `DRIVE`, 3/2/1/1 pieces with self-loops between pieces),
`rover3tier_rung12` (in place, 7/4 pieces), and the seventeen rover/story ladder benchmarks
(the one-way chain `STEEP → MODER → FLAT`, `CLIMB-k` dispatch: (a) zero-duration hops up the
chain to `max(l, q)` then `k` pieces with (b) self-loops; `INPLACE-9` for story1A/story3B;
explicit catch-up to `FLAT` for `rung2_6dof`/`rung2b_6dof`).

* (a) hops up the chain are illegal in general: `STEEP → MODER` at the window start needs
  `0.6 ≤ s_R < 1.4` (and `v_R ≤ 0.5` where the guard caps `v`), which neither the row nor the
  bookkeeping implies.
* (b) self-loops between pieces and after the last piece are illegal in general: the bands
  `s < 0.6`, `s < 1.4` are left by the flow.
* `rover3tier_rung12` and `match_multi_rate`: restated over the guarded automaton in new files
  (`Instances/Rover3tierRung12Guarded.lean`, `Instances/MatchMultiRateGuarded.lean`) with an
  explicit catch-up response (both right modes accelerate monotonically and both rows bound
  the left from above by an increasing function of the right): flow to the least value that
  restores the row (and lies in a guard), then switch there; no step when the right is
  already ahead. Both are Z3-free; the statements are those of the `⊤` theorems
  (`rover3tier_rung12_modeKeyed`, `match_multi_rate_pruned`) with the graph guarded.

### 4.3 Benchmarks whose guarded Theorem 3 is false as stated

For a benchmark below, the stated loop invariant `Φ` admits a state from which the guarded
right automaton has no step at all (every outgoing guard is false along the whole flow of the
current mode), while some left window run breaks `Φ` if the right does not move. Then
`Φ → [|(L*, R*)⟩⟩ Φ` fails at that state over the guarded automaton (the right's only run is
the empty one). Under the `⊤`-guarded relaxation the right could flow and "stay", which is
why the old theorems hold.

Machine-checked (`¬ RFormula.rvalid (theorem3Form …)` over the guarded graph, for every
`dt > 0`, at the three standard axioms):

* `rover_patrol_zones` — `InstancesV2/RoverPatrolZonesCounterexample.lean`,
  `rover_patrol_zones_guarded_false`. `u_L = SLOW`, `s_L = 10`, `v_L = 0.35`; `mv = SLOW`,
  `s_R = 60`, `v_R = 0.35`. `Φ` holds (row `v_L ≤ v_R ∧ s_L ≤ s_R + 0.5`, envelopes, `SLOW`'s
  region `s_R ≥ 0 ∧ 0.3 ≤ v_R ≤ 0.6`). Along `SLOW`'s flow `s_R ≥ 60` and `v_R ≥ 0.35`, so
  the guards of `MEDIUM_*`/`SLOW` (`s < 50`, `s < 20`) and `STALL` (`v < 0.2`) never hold. The
  left iteration `SLOW → SLOW` (window `v' = 1.25 (0.48 − v)`) ends at
  `v_L = 0.48 − 0.13 e^{−1.25 dt} > 0.35`.
* `refinement_ladder_rover_rung1_2to3` — `Instances/RoverLadderRung1Counterexample.lean`,
  `rover_ladder_rung1_guarded_false`. `mv = STEEP`, `s_R = 5`, `v_R = 0.1`; `v_L = 0.1`,
  `s_L = 0.3`, `ψ_L = 0`. `STEEP`'s flow keeps `s_R ≥ 5`; `STEEP` (`s < 0.6`) and `MODER`
  (`s < 1.4`) are never enabled. The left `STEEP` window ends at
  `v_L = 0.3 − 0.2 e^{−3 dt} > 0.1`.

By the same argument (stated here, not machine-checked):

* `rover_patrol_refine`: the same state shape (`SLOW` has no `STALL` edge); the left window
  raises `a_L + 5 v_L` (row `a_L + 5 v_L ≤ 5 v_R + 0.35`, start at equality with `a_L = 0.35`,
  `v_L = 0.35`: `(a + 5v)' = 6.25 (0.48 − v) > 0`).
* `story3_rollover_ladder_rung_b`: `mv = STEEP`, `s_R = 5`, `v_R = v_L = 0.1`, `u_L = STEEP`,
  `s_L = 0.3`; `STEEP`'s region is `s_R ≥ 0`; along `STEEP`'s flow
  `s' = v (1 − 0.5ψ² − 0.3θ²) ≥ 0` (the domain bounds `|ψ|, |θ| ≤ 0.6`), so `STEEP` and
  `MODER` are never enabled; the left `STEEP` window (`v' = 3 (0.3 − v)`) raises `v_L` above
  `v_R`.
* `arm_plateau_slow`: `mv = ApproachA`, `θ_R = 0.51` (`ApproachA`'s region is `θ_R ≥ 0`; its
  successors' guards end at `0.35` and `0.5`, and its flow increases `θ_R`: no step);
  `Accelerate` at `θ_L = 0.49`, `v_L = 0.354` (row `θ_L ≤ θ_R + 0.0775` holds). The left flow
  `e'' + 2.5 e' + e = 0` (`e = θ − 0.5`) is `e(t) = 0.2227 e^{−t/2} − 0.2327 e^{−2t}`, so
  `θ_L(1) ≈ 0.6036 > 0.5875 = θ_R + 0.0775` (numerically, maximum `0.6037` at `t ≈ 0.95`): for
  `dt ≥ 1` the row breaks. (For `arm_plateau_crit` and `_profiles` the analogous maximum is
  `≈ 0.623` resp. `≈ 0.67`, below `0.755`, and the guarded theorems are proved.)
* The sixteen other carried-over ladder benchmarks (`refinement_ladder_rover_rung2_3to6`,
  `rung2_6dof`, `rung2b_6dof`, `rung2c_6dof`, `rung3_6to8`, `rung4_8to12`,
  `rover_dof_terrain_rung1/2/3/3_8d`, `story1_attdist_rung_a/b`, `story2_lateral_rung_a/b`,
  `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a`): `mv = STEEP` at `s_R ≥ 1.4`
  is in `Φ` (bookkeeping `mvValid`, or the `CEIL` region `v_R ≤ c_STEEP`, or `rung2c`'s
  `s_R ≥ 0`); `STEEP` has no step; a left window breaks a row that the frozen right cannot
  follow: `v_L ≤ v_R` with `v_L = v_R < 0.3` in a `STEEP` window (all rows with the velocity
  conjunct); for `rung2_6dof`/`2b` (`s_L − s_R − 0.2 + (v_L − v_R)/3 ≤ 0`) start at equality
  with `s_R = 1.4`, `s_L = 1.6`, `v_L = v_R = 0.5` in a `FLAT` window; for `rung2c` (equality
  rows) `s_L = s_R = 5`, `v_L = v_R = 0.3` in a `FLAT` window.

These are not proof-engineering gaps: the invariant's right bookkeeping (kept cut atoms, or
none) does not exclude right states that the guarded model can never leave. A guarded
Theorem 3 for these benchmarks needs a different statement: a right region that carries the
entered mode's guard (the bookkeeping the guarded automaton maintains by construction: every
round ends with a legal switch), and, for the ladders, responses that switch inside a window
when the right crosses a band (the cover's per-segment demonic successor choice) with a
window bound tied to `ε`. That is a redesign of the statement and of the witnesses, not a
migration; it is not attempted on this branch.

### 4.4 The open benchmarks: `platoon3_profiles`, `platoon3_linkloss`

The right never gets stuck (every non-sink mode's flow is a damped oscillator converging into
its own guard), so the refutation above does not apply. But the certified response ends where
the region (linear-form atoms) allows `|r_R|` up to 2 while every non-sink successor's guard
needs `|r_i| ≤ 1`, so `NonblockingAt` fails at those end states (e.g. `g = 30`, `r = 1.5` on
every link, consistent with the row, both envelopes and the left atoms); a legal response
would have to run the right past the coupled duration until it re-enters a guard while keeping
the two-sided relational row against the fixed left state, which the certificate does not
provide. Whether the guarded statement holds is not settled here; these two theorems stay
over the `⊤` relaxation.

## 5. Cost

* Pilot (`watertank`): about 15 minutes of editing; the file compiles in 12 s
  (`lake env lean`). Legality proofs: `sat_guardR` (the right guards evaluated by `simp` on the
  IR literal), `nonblock` (per non-sink mode, a case split on the end state, `linarith`), the
  hop's guard at the start state transported to the window's end by `right_framed`.
* The mechanical part of every suite_v2 instance (guarded edges, `Gr_guards`, footprints,
  `GResp` signatures, the step and assembly lemmas) is uniform; the per-instance content is the
  guard evaluation and `nonblock`/`nonblockI`/`pickStay` (5–60 lines). Each file still compiles
  in seconds to a minute with `lake env lean`; the whole battery rebuilds in about a minute
  (`lake build RelCertifier.InstancesV2.BatteryV2`, 75 s wall).
* Rebuilt witnesses: `charger_fast_tapers` (≈ 200 lines), `arm_plateau_crit/profiles`
  (≈ 330 lines each: two DI links and the band climb), `rover3tier_rung12` and
  `match_multi_rate` (new files, ≈ 300 lines each, explicit solutions). Refutations: ≈ 400
  lines each.

## 6. Final table

Kinds as in section 4. "guarded" = Theorem 3 stated over the guarded right automaton, every
switch kernel-checked legal; "refuted" = the guarded statement is false as stated
(machine-checked where marked ✓); "open" = no legal witness from the certificate, truth not
settled. Z3 = the theorem's verdict hypotheses (unchanged from the `⊤` theorem unless noted).

| benchmark | switches in the new witness | legality proof | rebuilt? | status |
|---|---|---|---|---|
| `watertank` | (d) after every joint segment; (a) `Low → MidBoost` | `nonblock` by cases on `x_R`; hop guard from the row, `Mid` guard, `Low` region | no | guarded |
| `acc_tune_limp` | (d) stays | region = closed guard | no | guarded |
| `acc_spoof_limp`, `acc_spoof_lag`, `acc_tune_lag` | (d) stays, or no step | `ode_coord_end_lt_or_eq` at `v_R = 40`; zero-duration → `gresp_final_idle` | no | guarded |
| `platoon_delay_profiles` | (d) stays | region = closed guard | no | guarded |
| `platoon_delay_linkloss` | (d) stay or `FOLLOW → CATCH` | cases on `g_R < 40` | no | guarded |
| `quad_light_airframe_20`, `quad_light_lag`, `quad_light_profiles` | (d) stays | region = guard | no | guarded |
| `charger_fast_setpoints` | (c) `BULK → ABSORB` after the `BULK` run; (d) | landing `[80, 90]`; `nonblock` by cases | hop carries its test (`faModalB_repoPrefixG`) | guarded |
| `charger_fast_tapers` | (c) `BULK → ABSORB_FAST → FULL`, `ABSORB_* → FULL`; (d); cut runs; no step | explicit landings; `pickStay` (cut at 96) | yes | guarded |
| `arm_plateau_crit`, `arm_plateau_profiles` | band climb `A → B`, final switch at the target; no step | explicit runs; sharp end bound | yes (Z3-free, unchanged) | guarded |
| `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}` | (d) stays | the kept atom is the guard | no | guarded |
| `rover3tier_rung12` | one run to the target, switch into `ACCEL`/`COAST` | explicit end state | yes, new file; now Z3-free (was 4 packs) | guarded |
| `match_multi_rate` | one `DRIVE` run to the target, stay; no step | explicit end state; left bounds from `ode_linear_coord` | yes, new file; now Z3-free (was 4 packs) | guarded |
| `rover_patrol_zones` | — | — | — | refuted ✓ |
| `refinement_ladder_rover_rung1_2to3` | — | — | — | refuted ✓ |
| `rover_patrol_refine`, `story3_rollover_ladder_rung_b`, `arm_plateau_slow` | — | — | — | refuted |
| 16 other carried-over ladder benchmarks (§4.3) | — | — | — | refuted |
| `platoon3_profiles`, `platoon3_linkloss` | — | — | — | open |

Totals: 22 guarded (20 suite_v2 instances, 2 carried over), 21 refuted (2 machine-checked), 2
open. No theorem carries an Assumption-1 (nonblocking) hypothesis: every `NonblockingAt`
obligation is discharged from the explicit end state. No new axiom; the guarded theorems are
at the three standard axioms plus `z3_unsat_sound` exactly where their `⊤` versions were
(`arm_plateau_crit/profiles`, `rover3tier_rung12`, `match_multi_rate` at the standard three).
