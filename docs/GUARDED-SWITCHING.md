# Guard-gated switching on the right (branch `guarded-right`)

**Status (2026-10-10, branch `guarded-right`): done.** The statement is strengthened to one
uniform shape for all 45 benchmarks: Theorem 3 over the guarded right automaton with the loop
invariant carrying the MODE-CONSISTENT region `regionG guard cuts q = guard q ∧ cuts q` of the
right's current mode (section 3.1). 39 benchmarks carry it for every window length,
`refinement_ladder_rover_rung2c` for windows `dt < 1` (false for `dt > 2.12` by argument); it is
false for `platoon3_linkloss` (every `dt > 0`, kernel-checked), `platoon3_profiles` (every
`dt ≥ 1` kernel-checked, every `dt > 0.575` by argument, `dt ≤ 0.575` open), and `refinement_ladder_rover_rung2_3to6`, `story2_lateral_rung_a_8dof`,
`story2_lateral_rung_b_12dof` (every `dt > 0`, by the argument of section 4.5, not
kernel-checked). Summary table: section 6.

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

### 3.1 The strengthened statement: the mode-consistent region

The first pass kept each benchmark's loop invariant unchanged (rows, envelopes, the right
mode's kept cut atoms or the bare bookkeeping `mvValid`). Over the guarded automaton that
invariant admits right states the guarded model never reaches and from which it has no step
(section 4.3). The flow-then-jump rotation (`modeStep`: flow, then a guarded jump) guarantees
more: at every loop boundary the right has just taken a guarded jump into its current mode, so
it satisfies that mode's guard. The strengthened statement carries exactly this:

```lean
-- Proofs/Encoding/GuardedSwitch.lean
def regionG (guard cuts : ℕ → Formula (Var n)) (q : ℕ) : Formula (Var n) :=
  Formula.and (guard q) (cuts q)

-- per instance (cuts = the old region: kept cut atoms, the CEIL face, or ⊤)
noncomputable def gregion (q : ℕ) : Formula (Var k) :=
  regionG (fun q => hostGuard vs k Side.R (mR q)) region q

theorem <benchmark>_guarded (dt : ℝ) … :
    RFormula.rvalid (theorem3Form L (rightAutomatonBody G mv)
      (RFormula.and (RFormula.and (canonInvM g gs) (envLR domL domR))
        (mvRegionR mv gregion G.modes.length)))
```

with every edge of `G` testing the lowered guard of the mode it enters
(`G_guards : ∀ q, ∀ e ∈ G.edgesFrom q, e.guard = hostGuard … Side.R (mR e.tgt)`). Mode-keyed
instances use the same `mvRegionR mv gregion …` inside `psiK`. The declared rows (`canonInvM`)
and the envelopes are unchanged; there is no Assumption-1 (nonblocking) hypothesis and no new
axiom. Generic support: `sat_regionG`, `regionG_fv_sub`, `notMem_regionG_fv`, `gresp_guard`
(a response may end with no step when the right is still in its current mode's guard),
`Hmulti_regionG` / `HMode_regionG` / `HMode_regionG_ofF` (the step obligations at
`regionG`), `frames_right` (a left window does not move the right's guard),
`hostGuard_fv_R_getD`.

### 3.2 Response layers for the switching responses (new leaves)

* `Proofs/Encoding/GuardedClimb.lean`: `RResp`/`RRespP` (a guarded response written as a
  chain of `flow ; legal switch` steps, `rresp_step`/`rresp_stop`, composition `rrespP_bind`),
  `gresp_of_rresp`; explicit right trajectories (`trajR`, `explicit_run`, `explicit_sol`) and
  the derivative helpers they need; left-window bounds on linear coordinates
  (`windowSeg_coord_le_max/ge_min/le_or_lt`); `clockedSeg_sol` (a clocked piece is an
  `ODESol` of duration at most `dt`).
* `Proofs/Encoding/LadderClimb.lean`: `LadderRun` (what a `STEEP → MODER → FLAT` ladder
  supplies) and the climb `LadderRun.climb` (run each band to the next band's floor, switch
  there, hold `FLAT` until the rows hold, self-loop); `LadderRun.ofLinear` /
  `LadderRun.ofKappa` (the explicit runs, the attitude-weighted odometer
  `s' = v · κ(t)` by FTC); `LadderRun.climbD` (the climb with a decay budget: `FLAT` held
  for at least `Dmin` more, so every coordinate with `x' = −x` ends at most `e^{−Dmin}` times
  its start value).
* `Proofs/Encoding/SyncSwitch.lean`: joint solutions from a left and a right solution
  (`joint_of_sols`, and `joint_of_sols_lam` at a right-clock rate `λ`), `couple_box_cutX`
  (a certified pair's anchor box along a joint flow), `mergeLR`.
* `Proofs/Encoding/LadderSync.lean`: the synchronized climb (`syncClimbP`, `syncClimb`,
  `syncWindow`): when a row ties the reference to the deployed's clock, the right runs in
  lockstep with the window and switches at each band floor INSIDE the window, the certified
  pair's anchor preserved across the switch; `sync_stretch` (virtual-band stretch for the
  pairs the certificate does not cover).

## 4. Classification of the switches in the witnesses (Phase 0)

Sections 4.1 and 4.2 record the first pass (the old invariants); the plans marked "refuted"
or "open" there are superseded by sections 4.3 to 4.5 and the final table.

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

### 4.3 History: the cut-only statement and its refutations

The first pass stated the guarded theorems at the OLD invariant (rows, envelopes, and the
right's kept cut atoms or the bare bookkeeping `mvValid`, without the right mode's guard). For
23 benchmarks that cut-only statement is false: the invariant admits a right state from which
the guarded automaton has no step (every outgoing guard false along the whole flow of the
current mode), while a left window breaks a row if the right does not move. Two of these were
refuted in the kernel (commit `3a2762e` and `5c0a6a9`; the files
`InstancesV2/RoverPatrolZonesCounterexample.lean` and
`Instances/RoverLadderRung1Counterexample.lean` were retired in `8ec3e5c` because they are
about the cut-only statement, not the final one; their last version is at `a96a3bf`):

* `rover_patrol_zones`: `u_L = SLOW`, `s_L = 10`, `v_L = 0.35`; `mv = SLOW`, `s_R = 60`,
  `v_R = 0.35`. Along `SLOW`'s flow no outgoing guard (`s < 50`, `s < 20`, `v < 0.2`) holds;
  the left `SLOW` window raises `v_L` to `0.48 − 0.13 e^{−1.25 dt} > 0.35`.
* `refinement_ladder_rover_rung1_2to3`: `mv = STEEP`, `s_R = 5`, `v_R = 0.1`; `v_L = 0.1`,
  `s_L = 0.3`, `ψ_L = 0`. `STEEP` (`s < 0.6`) and `MODER` (`s < 1.4`) are never enabled; the
  left `STEEP` window ends at `v_L = 0.3 − 0.2 e^{−3 dt} > 0.1`.

Every such witness has the right OUTSIDE its current mode's guard (`s_R = 60` in `SLOW`,
`s_R = 5` in `STEEP`). The mode-consistent region (section 3.1) excludes them, and with it 39
of the 45 statements are provable for every window length (section 4.4).

### 4.4 The new responses (17 benchmarks)

All responses below are explicit: the right's runs are closed-form solutions (`trajR`,
`explicit_run`), every switch is at a state where the entered guard holds by the explicit end
state, and the response ends in the final mode's guard.

| benchmark | response | Z3 |
|---|---|---|
| `refinement_ladder_rover_rung1_2to3`, `rover_dof_terrain_rung1/2/3/3_8d` | ladder climb (`LadderRun.climb`): band to the next floor, switch, hold `FLAT` until `v_L ≤ v_R` and `s_L ≤ s_R + d` | none (was 6 packs each) |
| `refinement_ladder_rover_rung4_8to12` | ladder climb with the attitude-weighted odometer (`ofKappa`, `κ ≥ 0.7`) | none (was 6) |
| `refinement_ladder_rover_rung3_6to8` | ladder climb with a decay budget (`climbD`, `Dmin = max(0, 27 dt / 4)`): the reference's `ψ_R`, `θ_R` decay as `e^{−t}`; the deployed's attitude form `Q = ψ² + 3 (ω − ψ)²` obeys `Q' + (9/2) Q ≥ 0` (positive definite `(9/2) a² − 4 a b + (3/2) b²`), so each clocked piece keeps `e^{−(9/2) dt}` of it (`QL_piece`, `QL_window`) and the attitude rows `ψ_R² ≤ Q_L` hold at the end | none (was 6) |
| `refinement_ladder_rover_rung2_6dof`, `rung2b_6dof` | climb on the combined coordinate `w = s + v/3` (row `s_L − s_R − 0.2 + (v_L − v_R)/3 ≤ 0`) | none (unchanged) |
| `story3_rollover_base_12dof`, `story3_rollover_ladder_rung_a` | ladder climb; the deployed-only conjuncts of the rows from the unchanged packs (`bigSeq_odes_left`) | 6 packs each (unchanged); `0 ≤ dt` |
| `story3_rollover_ladder_rung_b`, `story1_attdist_rung_a_6to8` | synchronized climb (`syncClimb`): the rows tie the reference to the deployed's clock, so the right runs in lockstep and switches at each band floor inside the window, the certified pair's anchor preserved | 9 packs each (unchanged) |
| `story1_attdist_rung_b_12dof` | synchronized climb across two-piece windows (`syncWindow`), virtual-band stretch for the lower pairs the cover does not certify | 6 packs (unchanged) |
| `arm_plateau_slow` | three-band climb (merged with `arm_plateau_crit`'s two-band climb), in place | none (unchanged) |
| `rover_patrol_zones` | climb to `FAST` (zone runs to each zone's floor, switch, hold) | none (was 10) |
| `rover_patrol_refine` | the same climb; the deployed's `a + 5 v` capped by a linear-form chain (`w_L ≤ max(start, 29/4)`) | none (was 10) |
| `refinement_ladder_rover_rung2c_6dof` | mirror: the lockstep (equality) rows forbid a mid-window switch, so the right mirrors the window in the window's band; switches only at window ends | 3 packs (unchanged); `0 ≤ dt < 1` |

### 4.5 Benchmarks without a guarded theorem for every window length

Each item gives the exact state; in each the start satisfies the full loop invariant
(rows, envelopes, the right in its current mode's guard and cuts, the left in its window's
guard where the window has one).

* **`platoon3_linkloss`: false for every `dt > 0` (kernel-checked,
  `InstancesV2/Platoon3LinklossGuardedRefuted.lean`, `platoon3_linkloss_guarded_false`).**
  Deployed links `(33, 1)`, `(25, −1)`, `(29, 0)` in `FOLLOW` (`u_L = 0`), reference links
  `(34, 1)`, `(26, −1)`, `(30, 0)` in `FOLLOW` (`mv = 0`). The `FOLLOW` row is the exact
  refinement up to the 1 m offset, so after any `FOLLOW` window the reference's end state is
  determined (`g_i^R = g_i^L + 1`, `r_i^R = r_i^L`) whatever the reference did. The left edge
  tests its guard before the window, so the deployed may leave its box: a window of length
  `T = min(dt, 1)` carries `g₁^L = 29 + 12 u − 8 u²` (`u = e^{−T/4} ∈ (3/4, 1)`) above 33,
  hence `g₁^R > 34`, outside `FOLLOW`'s guard; the AEB sinks have the empty region.
* **`platoon3_profiles`: false for every `dt ≥ 1` (kernel-checked,
  `InstancesV2/Platoon3ProfilesGuardedRefuted.lean`, `platoon3_profiles_guarded_false`);
  `dt < 1` open.** Deployed links `(33, 1)`, `(25, −1)`, `(29, 0)`; reference `(34, 1)`,
  `(26, −1)`, `(30, 0)` in `NORMAL`. The profiles share one loop per link, so the reference's
  link difference `x = g₁ − g₂`, `y = r₁ − r₂` has profile-independent dynamics; its forms
  `P = y + x/2`, `W = y + x/4` decay as `e^{−t/4}`, `e^{−t/2}` in every profile, so
  `9 W = P²` with `0 < P ≤ 6` holds along every run of the guarded automaton (`star_J`).
  Every profile guard bounds `x ≤ 8`, leaving `W = 4` (`P = 6`) or `W ≤ 1` (`P ≤ 3`). A
  `FOLLOW` window of length 1 ends with `W_L = 4 e^{−1/2} ∈ (2, 3)`; the `ρ = 1/4` rows of
  links 1 and 2 give `|W_R − W_L| ≤ 1`. With a window of length `T` instead of 1,
  `W_L = 4 e^{−T/2}` and the same two conditions refute every `T ∈ (2 ln(4/3), 2 ln 2) ≈
  (0.575, 1.386)`, so the statement is false for every `dt > 0.575` (kernel-checked for
  `dt ≥ 1`); for `dt ≤ 0.575` it is open (with this witness the empty response keeps the two
  rows used). The `⊤`-relaxation theorem is kept.
* **`refinement_ladder_rover_rung2c_6dof`: guarded for `dt < 1`; false for `dt > 2.12`
  (argument, not kernel-checked); `1 ≤ dt ≤ 2.12` open.** The rows are equalities on
  `v, s, ψ, θ`, so the response must end exactly at the deployed's end state. A `STEEP`
  window (the left guard tests `s < 0.6` at its start) from `s = 0.6 − ε`, `v = 0.8`,
  `ψ = θ = 0` grows the odometer by `0.3 t + (1 − e^{−3t})/6`, past `1.4` once `t > 2.12`.
  If the reference never leaves `STEEP` its last switch is out of `STEEP` (guards `s < 0.6`,
  `s < 1.4`), impossible at `s_R = s_L ≥ 1.4`; if it leaves `STEEP` (at `s_R = 0.6`, after
  flowing for the time `t₁ < t` it needs to grow its odometer by `ε`), its `v` stays at least
  `min(0.3 + 0.5 e^{−3 t₁}, 0.5)` (`MODER`/`FLAT` pull `v` toward `0.5`/`0.65`), above the
  deployed's `0.3 + 0.5 e^{−3t}`; the empty response leaves `s_R < 0.6`.
  For `dt < 1` the odometer grows by at most `0.8 dt < 0.8`, the width of `MODER`'s band, and
  the mirror response is proved (`rover_rung2c_guarded`).
* **`refinement_ladder_rover_rung2_3to6`, `story2_lateral_rung_a_8dof`,
  `story2_lateral_rung_b_12dof`: false for every `dt > 0` (argument, not kernel-checked).**
  The left windows are plain (no left guard test); the rows contain heading equality
  `ψ_L = ψ_R` (and pitch equality where present) and `v_L ≤ v_R`. State: right in `STEEP`,
  `s_L = s_R = 0.1`, `v_L = v_R = 0.3`, `ψ_L = ψ_R = 0.1`, every other attitude coordinate
  0. Left `FLAT` window of length `δ = min(dt, 0.1)`: `v_L = 0.65 − 0.35 e^{−3δ} > 0.3` and
  `ψ_L = 0.1 e^{−δ}`. Every reference mode has `ψ' = −ψ`, so the row `ψ_R = ψ_L` forces the
  reference's total flow time to be exactly `δ`; within `δ ≤ 0.1` the reference's odometer
  stays below `0.1 + 0.3 δ < 0.6`, so `MODER`'s guard is never enabled and the reference stays
  in `STEEP` at `v_R = 0.3 < v_L`. The `⊤`-relaxation theorems are kept.

## 5. Cost

* First pass (22 benchmarks at the old invariants, the guarded generic layer): see the
  commits up to `fcd0949`. The mechanical part of every instance (guarded edges,
  `Gr_guards`, footprints, `GResp` signatures) is uniform; each file compiles in seconds to a
  minute with `lake env lean`.
* Strengthened statement (`c736f54`): the 22 instances moved to `gregion` with a few lines
  each (`Hmulti_regionG` / `HMode_regionG`).
* The 17 new responses: the ladder climbs share `LadderClimb.lean` (≈ 1100 lines), a ladder
  instance is ≈ 450 to 600 lines (generated for the four `rover_dof_terrain` rungs); the
  synchronized climbs share `SyncSwitch.lean` / `LadderSync.lean` (≈ 700 lines), an
  instance ≈ 500 to 650 lines. Refutations: ≈ 450 lines each.
* Whole battery: `lake build RelCertifier.InstancesV2.BatteryV2` rebuilds the new leaves in a
  few minutes; the full `lake build` is incremental.

## 6. Final table

"guarded" = Theorem 3 at the mode-consistent region over the guarded right automaton (section
3.1), every switch kernel-checked legal, for every window length unless noted; "refuted ✓" =
`¬ rvalid` of that statement kernel-checked; "refuted (arg.)" = false by the argument of
section 4.5, not kernel-checked; those benchmarks keep their `⊤`-relaxation theorem. Packs =
verdict-pack hypotheses of the final theorem (Z3-free when 0).

| # | benchmark | status | response | packs | theorem |
|---|---|---|---|---|---|
| 1 | `acc_spoof_lag` | guarded | (d) stays, or no step | 1 | `V2AccSpoofLag.acc_spoof_lag_modal` |
| 2 | `acc_spoof_limp` | guarded | (d) stays, or no step | 6 | `V2AccSpoofLimp.acc_spoof_limp_modeKeyed` |
| 3 | `acc_tune_lag` | guarded | (d) stays, or no step | 1 | `V2AccTuneLag.acc_tune_lag_modal` |
| 4 | `acc_tune_limp` | guarded | (d) stays | 6 | `V2AccTuneLimp.acc_tune_limp_modeKeyed` |
| 5 | `arm_plateau_crit` | guarded | band climb `A → B` | 0 | `V2ArmPlateauCrit.arm_plateau_crit_modal` |
| 6 | `arm_plateau_profiles` | guarded | band climb | 0 | `V2ArmPlateauProfiles.arm_plateau_profiles_modal` |
| 7 | `arm_plateau_slow` | guarded | three-band climb | 0 | `V2ArmPlateauSlow.arm_plateau_slow_modal` |
| 8 | `charger_fast_setpoints` | guarded | (c) `BULK → ABSORB`; (d) | 7 | `V2ChargerFastSetpoints.charger_fast_setpoints_modal` |
| 9 | `charger_fast_tapers` | guarded | (c) paths; cut runs; no step | 9 | `V2ChargerFastTapers.charger_fast_tapers_modal` |
| 10 | `match_multi_rate` | guarded | one `DRIVE` run to the target | 0 | `MatchMultiRateGuarded.match_multi_rate_guarded` |
| 11 | `platoon3_linkloss` | refuted ✓ (every `dt > 0`) | — | — | `V2Platoon3LinklossRefuted.platoon3_linkloss_guarded_false` |
| 12 | `platoon3_profiles` | refuted ✓ (`dt ≥ 1`), by arg. for `dt > 0.575`; `dt ≤ 0.575` open | — | — | `V2Platoon3ProfilesRefuted.platoon3_profiles_guarded_false` |
| 13 | `platoon_delay_linkloss` | guarded | (d) stay or `FOLLOW → CATCH` | 6 | `V2PlatoonDelayLinkloss.platoon_delay_linkloss_modeKeyed` |
| 14 | `platoon_delay_profiles` | guarded | (d) stays | 6 | `V2PlatoonDelayProfiles.platoon_delay_profiles_modal` |
| 15 | `quad_light_airframe_20` | guarded | (d) stays | 1 | `V2QuadLightAirframe20.quad_light_airframe_20_modal` |
| 16 | `quad_light_lag` | guarded | (d) stays | 1 | `V2QuadLightLag.quad_light_lag_modal` |
| 17 | `quad_light_profiles` | guarded | (d) stays | 3 | `V2QuadLightProfiles.quad_light_profiles_modal` |
| 18 | `refinement_ladder_rover_rung1_2to3` | guarded | ladder climb | 0 | `RoverLadderRung1Guarded.rover_ladder_rung1_guarded` |
| 19 | `refinement_ladder_rover_rung2_3to6` | refuted (arg.) | — | — | (`⊤`: `RoverLadderRung2Modal.rover_ladder_rung2_3to6_modal`) |
| 20 | `refinement_ladder_rover_rung2_6dof` | guarded | combined-coordinate climb | 0 | `RoverRung26dofGuarded.rung2_6dof_guarded` |
| 21 | `refinement_ladder_rover_rung2b_6dof` | guarded | combined-coordinate climb | 0 | `RoverRung2b6dofGuarded.rung2b_6dof_guarded` |
| 22 | `refinement_ladder_rover_rung2c_6dof` | guarded for `dt < 1`; refuted (arg.) for `dt > 2.12`; open between | mirror | 3 | `RoverRung2cGuarded.rover_rung2c_guarded` |
| 23 | `refinement_ladder_rover_rung3_6to8` | guarded | ladder climb, decay budget | 0 | `RoverLadderRung3Guarded.rover_ladder_rung3_6to8_guarded` |
| 24 | `refinement_ladder_rover_rung4_8to12` | guarded | ladder climb, weighted odometer | 0 | `RoverLadderRung4Guarded.rover_ladder_rung4_8to12_guarded` |
| 25 | `rover3tier_rung12` | guarded | one run to the target | 0 | `Rover3tierRung12Guarded.rover3tier_rung12_modeKeyed_guarded` |
| 26 | `rover_dof_terrain_rung1` | guarded | ladder climb | 0 | `RoverDofTerrainRung1Guarded.rover_dof_terrain_rung1_guarded` |
| 27 | `rover_dof_terrain_rung2` | guarded | ladder climb | 0 | `RoverDofTerrainRung2Guarded.rover_dof_terrain_rung2_guarded` |
| 28 | `rover_dof_terrain_rung3` | guarded | ladder climb | 0 | `RoverDofTerrainRung3Guarded.rover_dof_terrain_rung3_guarded` |
| 29 | `rover_dof_terrain_rung3_8d` | guarded | ladder climb | 0 | `RoverDofTerrainRung38dGuarded.rover_dof_terrain_rung3_8d_guarded` |
| 30 | `rover_patrol_refine` | guarded | climb to `FAST`, linear-form cap | 0 | `V2RoverPatrolRefineGuarded.rover_patrol_refine_guarded` |
| 31 | `rover_patrol_zones` | guarded | climb to `FAST` | 0 | `V2RoverPatrolZonesGuarded.rover_patrol_zones_guarded` |
| 32 | `sat3w_detumble_nominal` | guarded | (d) stays | 1 | `V2Sat3wDetumbleNominal.sat3w_detumble_nominal_modal` |
| 33 | `sat3w_detumble_phases` | guarded | (d) stays | 2 | `V2Sat3wDetumblePhases.sat3w_detumble_phases_modeKeyed` |
| 34 | `sat3w_detumble_weak` | guarded | (d) stays | 3 | `V2Sat3wDetumbleWeak.sat3w_detumble_weak_modal` |
| 35 | `sat_detumble_nominal` | guarded | (d) stays | 1 | `V2SatDetumbleNominal.sat_detumble_nominal_modal` |
| 36 | `sat_detumble_phases` | guarded | (d) stays | 2 | `V2SatDetumblePhases.sat_detumble_phases_modeKeyed` |
| 37 | `sat_detumble_weak` | guarded | (d) stays | 3 | `V2SatDetumbleWeak.sat_detumble_weak_modal` |
| 38 | `story1_attdist_rung_a_6to8` | guarded | synchronized climb | 9 | `Story1AttdistRungAGuarded.story1_attdist_rung_a_guarded` |
| 39 | `story1_attdist_rung_b_12dof` | guarded | synchronized climb, two-piece windows | 6 | `Story1AttdistRungBGuarded.story1_attdist_rung_b_guarded` |
| 40 | `story2_lateral_rung_a_8dof` | refuted (arg.) | — | — | (`⊤`: `Story2LateralAModal.story2_lateral_rung_a_modal`) |
| 41 | `story2_lateral_rung_b_12dof` | refuted (arg.) | — | — | (`⊤`: `Story2LateralBModal.story2_lateral_rung_b_modal`) |
| 42 | `story3_rollover_base_12dof` | guarded (`0 ≤ dt`) | ladder climb | 6 | `Story3RolloverBaseGuarded.story3_rollover_base_guarded` |
| 43 | `story3_rollover_ladder_rung_a` | guarded (`0 ≤ dt`) | ladder climb | 6 | `Story3RolloverRungAGuarded.story3_rollover_rung_a_guarded` |
| 44 | `story3_rollover_ladder_rung_b` | guarded | synchronized climb | 9 | `V2Story3RolloverRungBGuarded.story3_rollover_ladder_rung_b_guarded` |
| 45 | `watertank` | guarded | (d); (a) `Low → MidBoost` | 11 | `V2Watertank.watertank_modal` |

Totals: 39 guarded for every window length (`0 ≤ dt` for the two story3 ladders, which is no
restriction: a negative `dt` admits no window), `rung2c` guarded for `dt < 1`, 2 refuted ✓
(`platoon3_profiles` only for `dt ≥ 1`), 3 refuted by argument for every `dt > 0`. No theorem carries an
Assumption-1 hypothesis; no new axiom. Z3-free final theorems: 16 guarded ones (rows with
packs 0) and both refutations. Pack hypotheses of the 40 guarded statements: 109, against 171
for the same 40 benchmarks' theorems before this branch (−62: `rung1`, `rung3_6to8`,
`rung4_8to12`, the four `rover_dof_terrain` rungs at 6 each, `rover_patrol_zones` and
`rover_patrol_refine` at 10 each). The verdict runner's tables are unchanged (the relaxation
theorems, still built and imported by the guarded files for their shared definitions, take
those packs).
