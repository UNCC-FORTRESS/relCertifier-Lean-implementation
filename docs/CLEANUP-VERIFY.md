# Independent verification of `docs/CLEANUP-SCOPE.md`

> **Executed 2026-10-22** (commit 093b2d1 on `cleanup-2026-10`): the endorsed archive list was applied as corrected here (137 minus `AxiomCheck` relocated and `Choice/Verdicts` + `ChoiceVerdictsMain` removed earlier = 134 modules); open questions 2 to 7 resolved as recommended (X-modules kept, `AxiomCheck` kept, `GUARDED-SWITCHING.md` and `SUITE-DEDUPE.md` kept, `Instances/WellFormed/` renamed, `benchmarks/negative` kept with a recipe line).

Re-derived 2026-10-21 against `main` = `3d64743`, read-only, with an own closure script over
the `import RelCertifier.*` lines of all 813 Lean files (803 under `RelCertifier/`, root, 7 exe
roots, 2 `scripts/*.lean`).

## Verdict: CONSISTENT, with corrections

The closure, the KEEP/ARCHIVE split and the wires P1 to P4 reproduce. The corrections below
do not change the split; 1, 2, 4, 5 change the work of P1 and the answer to open question 2.

| closure | mine | scope |
|---|---|---|
| all modules | 813 / 181,715 lines | 811 / 182,426 (no `scripts/*.lean`; line convention) |
| roots `Main`, `{Bridge,Refute,Progress}VerdictsMain`, `Bridge`, `Refute`, `WellFormedBattery`, `WatertankStrict`+`strict_demo_verdicts` | 787 / 174,663 | 787 / 175,776 |
| + `Test`, `ChoiceVerdictsMain`, `refute_dump` (the scope's roots) | 791 / 175,166 | |
| `RelCertifier.lean` lib root (`lake build`) | 672 / 171,711 | 672 |
| KEEP after P1 to P4, choice exe dropped | 675 / 87,990 | ~675 / ~88,800 |
| ARCHIVE (§2.2 to §2.4 + `ChoiceVerdictsMain`) | 136 / 93,502 (+`SlimMain` 49) | ~136 / ~93,600 |

Wires (archive modules in today's closure, with keep-set importers): 28 `InstancesV2/Modal/*`
<- `InstancesV2/WellFormed/*` (P1); 19 `Instances/*Guarded` + `GuardedPins` <-
`Instances/WellFormed/*`, `WellFormed/Story3RolloverRungB` (P1); `Verdicts/RunModal` <-
`VerdictsV2/RunV2` (P2); `ChoiceVerdictsMain` as root (P3); 3 `Choice/Modal/*` <-
`Choice/General/*` (P4). Nothing else: all 116 archive modules in the closure enter through
these wires; after cutting them no archive module remains and everything outside the cut
closure is the scope's list plus `SlimMain`. The root's archived direct imports match §3c.
The lib root does not reach `Bridge/*`, `BenchProgress/*`, `RunBridge`, `RunProgress`,
`Emitted/{Lift,Transport}` (58 keep modules): add `InstancesV2.Bridge` to the root (§3c).

## Corrections to the scope

1. P1 is 47 files, not 50: `WellFormed/{DrlCarStop,DrlLaneControl,FreedmMeter}` already
   import only `BenchIR.<b>`, `Emitted.Data`, `WellFormedR`. `WellFormed/Platoon3Link.lean` is a
   shared helper over `Modal/Platoon3Link` (556 lines, also imported by `Modal/Platoon3{Linkloss,
   Profiles}`); `WellFormedBattery` prints `Platoon3Link.{link_guard_Ronly,brake_guard_Ronly,solB_sol}`.
2. The 20 legacy WellFormed files (19 in `Instances/WellFormed/` + `Story3RolloverRungB`)
   quote the legacy literal `<b>_IR` of `Instances/BenchIR/<b>.lean` (archive; 20 files, not 19),
   while the bridge quotes `<b>_IRv2` (`SameIR`: `rfl`-equal). P1 must re-point them to
   `InstancesV2/BenchIR/<b>` or keep the 20 literal files (2.2k lines). Missed by the scope.
3. Name counts are 14 to 39 per file over the transitive chain (the scope's "7 to 45"
   counts the directly imported module only; the legacy files take `vsN/mRN/fRN/cstN_eq/
   sat_domRN` and the `hq*/hf*/hv*` pins from `<B>Modal` through `open`, not from `<B>Guarded`).
4. §2.3 "no `decide`/`rfl` in the keep set reads an archived module" is false today: 22
   bridge instances (20 legacy, `MatchMultiRate` (`GrPG`), `RoverPatrol{Refine,Zones}`) run
   `decide +kernel` on `<B>Guarded.GrG` (`nR_eq`, `edges_ok`, `src_ok`), the other 28 on
   `V2<B>.Gr`, and `wellFormedR_transport` names `<ns>.<b>_wellFormedR`. True after P1 only
   if `Gr/GrG/GrPG`, `Gr_modeAt`, `edgeG/edgeW`, `edgeList` keep names and namespaces (also
   read by `gen_bridge.py:60-67,78-86`). The 129 eval-line hits in the 47 wire files are all
   right-model data (`edgeW edgeG GrG edgeList modeW <b>_IR vsM mRM fRM cstM GrPG`): the P1
   payload. No non-wire keep module evaluates an archive definition.
5. Open question 2: `RunBridge` does NOT rebuild through `ModalX` (it sends
   `Emitted.bridgeGroupsS`), but the bridge proof chain imports the X-modules: `Emitted/Run`
   uses `modalVerdXQueries`, `modalVerdX_of_queries` (`ModalX` via `ModalDynX`);
   `Emitted/StrictRun` uses `modalVerdXQueriesS`, `modalVerdXS_of_queries` (`ModalXStrict`);
   `Emitted/Progress` uses `progressVerd_{one,one_down,two}`, `RegionSat` (`ProgressPin` ->
   `ProgressX`). So the five X-modules and `Verdicts/{GenericPins,ModalPins,Combinators,
   Mirrors}` are load-bearing for every bridge and refute theorem. `RunBridge:75` also reads
   `RunV2.packsV2` for `bridgeDimV2`: that table stays in `RunV2` even if its Z3 phase goes.
6. P3 / open question 4: `paper_numbers.sh:101` reads `choice_verdicts.txt` into
   `\numchoiceunsat`; the paper (`mymacros.sty:2079ff`, hand-copied; `numbers.tex` not `\input`)
   uses neither `\numchoiceunsat` nor `\numexhibits`. Archive is safe; delete lines 10 (exe
   build), 55-57, 101. `suite_v2_matrix.py` has no `choice` reference.
7. P2: the legacy phase is `RunV2:629-666` (`sameModalTable`, `expectedSameModalV2 = 385`) +
   `Main:114` (`c4`). Only `copied benchmarks (legacy packs) 385/385` disappears from
   `--check-quick-v2` / `--run-verdicts-v2`; 625, 88, 44, 81 and handoff 401 are `RunV2`
   phases over `ModalX`/`ModalDynX`/`NonConnQuery` and stay. `paper_numbers.sh` never runs
   `--check-quick-v2`, so `numbers.tex` is unchanged. README:239-240 needs the edit.
8. `Instances/AxiomCheck.lean` (open question 3) names only kept theorems (`cover_sound`,
   `check_sound`, `theorem3_faithful`, `rvalid_from_cert`, `decideCovered_implies_theorem3_faithful`,
   `segPres_from_flowCert`, `flow_certified`, `stratified_barrier_sound`, `cut_hcert`; imports
   `BridgeDischarge`, `StratifiedBarrier`, `CutLift`). KEEP, relocated (`Proofs/AxiomCheck.lean`).
9. `docs/history` links from current docs: 6 links to 5 files (`PAPER-MAPPING.md:20,365,366`,
   `CLOCKED-RIGHT-SCOPE.md:6`, `VERDICTS.md:100`, `README.md:515`), directory mentions
   `README.md:364`, `PAPER-MAPPING.md:105`, `SUITE-REDESIGN.md:15`, and, missed by the scope,
   `scripts/suite_v2_matrix.py:66,165,181` citing `docs/history/SUITE-DEDUPE.md`.
10. `scripts/black_mutation.py`: absent on `main`, present on branch `mutation`; referenced by
    `refute_finder.py:5,34`, `REFUTATION-SCOPE.md:19` and (missed) `REFUTATION-RESULTS.md:73`.
11. `benchmarks/negative/freedm_meter_leaky`: cited README:360, STATUS:81-82,
    benchmarks/README:182; no script or recipe step runs it. Counts: `WellFormedBattery` has
    75 `#print axioms` lines (README 76, CERTIFICATION-CHECK 77), `BatteryV2` 72.

## P1 name inventory (names used from the archived chain; drag-in = closure inside that chain)

d = right-model data (`vs mR modeW fR domR Gr/GrG edgeW/edgeG edgeList nbF linkFields kR cRc`), l =
solution/evaluation lemmas (`fR*_eval sat_guardR* sat_domR edge_mem Gr_modeAt_inv flowR_exists solΦ* ex solR* cst*_eq`), p = pins (`hp* hq* gp_1_0`).

| WellFormed file(s) | from | #names (d/l/p) | drag-in decls / lines | difficulty |
|---|---|---|---|---|
| AccSpoofLag/Limp, AccTuneLag/Limp | `Modal/<B>` (860-964 l.) | 15-16 (7-8/6-8/0-3) | 23-26 / 102-125 | E |
| ArmPlateauCrit/Profiles/Slow | `Modal/<B>` (1283-1382) | 16 (9/6/1) | 25-26 / 122-129 | E |
| ChargerFastSetpoints/Tapers | `Modal/<B>` (1065-1207) | 14-16 (8-9/6-7/0) | 25-27 / 119-130 | E |
| PlatoonDelayLinkloss/Profiles | `Modal/<B>` (799-1003) | 19 (9-10/5-7/3-4) | 27-28 / 114-126 | E |
| Watertank, WatertankTwospeed | `Modal/<B>` (789-966) | 15-18 (9-10/6-7/0-1) | 27-29 / 143-160 | E |
| QuadLightAirframe20/Lag/Profiles | `Modal/<B>` (947-1028) | 26-28 (8-10/13-18/2-3) | 34-40 / 305-347 | M: `ex`, `odeField_R`, `cRc_*` |
| SatDetumbleNominal/Phases/Weak | `Modal/<B>` (+Nominal for Weak) | 19-21 (7-8/8-9/4) | 44-50 / 265-299 | M: `ex`, `solR*`, `eval_hw` |
| Sat3wDetumbleNominal/Phases/Weak | `Modal/<B>` (1199-1402) | 21-24 (7-8/10-13/4) | 58-68 / 376-434 | M: `ex`, `solR_0..4`, `c1T..c3T` |
| RoverPatrolRefine, RoverPatrolZones | `Modal/<B>Guarded` + `Modal/<B>` | 20-24 (6-8/13/1-3) | 47-68 / 283-366 | M: two modules, `flowR_run`, 30 pins |
| Platoon3Link (helper) | `Modal/Platoon3Link` (556) | 15 (0/15/0) | 29 / 294 | M: `solΦ`, `E1/E2`, `gS/rS` hasDeriv chain |
| Platoon3Linkloss, Platoon3Profiles | `Modal/<B>` + `Modal/Platoon3Link` | 39 (10-11/14-15/13-15) | 66-67 / 502-505 | H: two modules + helper, `solΦ_box/deriv/frozen`, `QBounds`, `LinkStart` |
| MatchMultiRate | `<B>Guarded`+`<B>Pruned`+`<B>Modal`+`BenchIR/<b>` | 15 (6/8/1) | 30 / 247 | M: `GrPG`, `drive_sol`, `driveEnd*` |
| Rover3tierRung12, RoverDofTerrainRung1/2/3/38d, RoverLadderRung1 | `<B>Guarded`+`<B>Modal` (+`Handoff`, `BenchIR/<b>`, `GuardedPins`) | 15-23 (3-5/11-19/1) | 30-63 / 241-604 | M: legacy `<b>_IR` (corr. 2), `gp_1_0` -> local pin |
| RoverLadderRung2/3/4, RoverRung26dof/2b6dof/2c, Story1AttdistRungA/B, Story2LateralA/B, Story3RolloverBase/RungA/RungB | same shape | 18-19 (4/13-14/1) | 41-63 / 321-604 (my tool over-reports 189-205 / 1.3k through short-name false positives `LR dR φo`) | M: verify `φo/kapT/dR` (handoff curve, 12-20 decls) at move time |
| DrlCarStop, DrlLaneControl, FreedmMeter | none | 0 | 0 | done |

Totals (47 files): 918 names; drag-in roughly 12k to 14k lines of a 93k-line chain. No dragged
body names a declaration of any §2.4 module although the `*Guarded`/`*Modal` files import
them, and every generic module the dragged bodies use (`CutRespond`, `GuardedSwitch`,
`FaceBridge`, `WindowGrowth`, `LeftAutUniform`, `LadderClimb`, `SyncSwitch`) is in the keep
set. So P1 is a cut-and-paste of a dependency-closed block per file plus `open ...
RelCertifier.Oracle`, `set_option`s and, for the legacy files, re-namespacing `<B>Modal.vsN`
into `<B>Guarded` (only `GrG`, `GrG_modeAt`, `<b>_wellFormedR` are named from outside).
Examples: `AccSpoofLag` 15 names + 8 dragged (`dm edgeList`, 6 pins) = 23 decls / 102 lines
of 975; `Sat3wDetumbleWeak` 23 names, `flowR_exists` pulls `ex ex_hasDeriv solR solR_0..4`
(25 decls / 149 lines) = 68 / 434; `Platoon3Profiles` 37 names (`solΦ*`, 13 pins, `QBounds
LinkStart linkFields fR_field`) + 2 from `Modal/Platoon3Link`, whose shared `solΦ` chain
(29 decls / 294 lines) belongs in `WellFormed/Platoon3Link`.

P4: `Bridge/<X>` uses only `<ns>.{Gr|GrP, Gr_modeAt|GrP_modeAt, wellFormedR}`; `wellFormedR`
needs 2 (8 for the tank) General decls + 24-28 decls / 105-150 lines of `Choice/Modal/<X>`.
The other 22-39 General decls (`AG_*`, `hop_cover`, `Gr_sys/dom/weight`, `cov_*`, `certified`,
`Packs`) have no kept user. `WellFormedBattery` imports `General.VehicleHypercert`.

## Open questions 2 to 7

2. Correction 5: keep the X-modules and `packsV2`; the 625/88/44/81 Z3 phases of `RunV2` are
   a tool self-check with no kept theorem behind them once `BatteryV2` and the four pins go.
3. `AxiomCheck`: keep, relocate (correction 8). 4. `\numchoiceunsat` unused by the paper (6).
5. `GUARDED-SWITCHING.md`: keep (README:410,498, STATUS:14,36, PAPER-MAPPING:131 point at its
   per-benchmark table). Archive `VERDICTS.md` (README:113,502: rewrite to the three runners)
   and `REPLAY.md` (README:21,503, STATUS:19,91: the replay claim is a `BatteryV2` property).
6. Rename `Instances/WellFormed/` into `InstancesV2/WellFormed/`: yes; after correction 2
   nothing of `Instances/` remains (`gen_bridge.py:24`, 19 bridge imports, `WellFormedBattery`).
7. `benchmarks/negative`: keep; add one DECLINED run line to `paper_numbers.sh`.

## Endorsed ARCHIVE list (Lean, 137 files)

Exactly the scope's §2.2 to §2.4 groups (136) plus `SlimMain.lean` + `relcert-slim`, with two
conditions: `Instances/AxiomCheck` only after relocation (correction 8); `Instances/BenchIR/*`
(20, not 19) + `Instances/EvolStrengthenings/match_multi_rate` only after the 20 legacy
WellFormed files point at `_IRv2` (correction 2). Non-Lean as §2.5 plus `docs/VERDICTS.md`
and `docs/REPLAY.md`.

## KEEP additions the scope missed or left open

`VerdictsV2/{ModalX,ModalDynX,ModalXStrict,ProgressX,ProgressPin}` and
`Verdicts/{GenericPins,ModalPins,Combinators,Mirrors}` (bridge proof dependencies, not
optional); `RunV2.packsV2` (read by `RunBridge.bridgeDimV2`); `Instances/AxiomCheck`
(relocated); `WellFormed/Platoon3Link` under namespace `Platoon3Link`; `docs/GUARDED-SWITCHING.md`;
`docs/history/SUITE-DEDUPE.md` or an edit of `suite_v2_matrix.py:66,165,181`.
