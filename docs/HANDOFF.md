# Cross-mode handoff: the implication at every declared left mode change

The handoff condition is the paper's Eq. 13, used by Theorem 2 (Composition) and checked by the
tool for every declared left mode change (Section 6.1, "Handoff."). The tool issues one query
per declared left transition, self-loops included, and the bridge instances take the same
queries as their `handoff` verdicts (`docs/BRIDGE.md`), so the queries the tool sends and the
hypotheses the theorems assume are one formula.

## What is checked, and why

Seventeen suite benchmarks declare a MODE-DEPENDENT relational invariant: a
`[relational_invariant]` block with a different formula per LEFT mode. The tool certifies
each left mode's cycle against that mode's own row. A run of the full left program also
switches mode, and at a declared transition `m' → m` (`m ∈ next(m')`) the state is unchanged
while the left mode variable changes. The mode-keyed global invariant (Eq. 9)

    Φ ≡ ⋀_m (u_L = m → φ_inv(m))

therefore survives the switch exactly when the row implication holds at every state a
switch can occur in. At such a state the left is at the end of an `m'` cycle, so it
satisfies `m'`'s evolve domain, and it satisfies `m`'s guard (the switch condition); the
right state satisfies its evolve domain. The DOMAIN-CONDITIONED implication is therefore the
sound form:

    φ_inv(m') ∧ evolve_{m'}(x_L) ∧ guard_m(x_L) ∧ evolve_R(x_R) → φ_inv(m)

`Trusted/Handoff.lean` defines the query once, at the SMT-IR level, as

    UNSAT( φ_inv(m') ∧ evolve_{m'}(x_L) ∧ guard_m(x_L) ∧ evolve_R(x_R) ∧ ¬φ_inv(m) )

over the joint left and right variables (the rows lower through `invComponents`, the
certifier's own invariant lowering; the guard and the domains through `lowerF` on their
side, as in the admissibility and flow queries). `evolve_R` is the right system's one
evolution domain (every suite benchmark declares one domain per system); the runner checks
that uniformity per benchmark and reports a violation as a failure rather than picking a
mode. The same IR term is what `Verdicts/RunHandoff.lean` (`runHandoffBench`) prints to Z3
and what the composition's handoff hypothesis denotes: `ModeHandoff.handoff_of_unsat`
consumes `z3solve (ihandoffQuery …).toHost = unsat` and yields the conditioned implication
that `theorem3_modeKeyed_gen` takes (the loop invariant carries `env = domL ∧ domR` and the
edge's test supplies the guard); in the bridge, `handoff_sound` (`Emitted/Barrier.lean`)
reads the `handoff` verdicts.

Self-loops are checked too (trivially unsat) and counted. A mode-INDEPENDENT invariant (every
row syntactically identical) makes every query vacuous; such benchmarks are still run and
reported as `vacuous`, never skipped.

**Coverage is declared.** `VerdictsV2/RunV2.expectedHandoffV2 = 2846` is the suite total (one
query per declared left transition over the 50 suite files, self-loops included), and
`expectedHandoffFailuresV2` (the transitions known to fail) is empty. The handoff phase of
`--check-quick-v2` is green iff all 2846 queries come back `unsat` and every per-benchmark
count matches its declaration. The 48 abstraction modes of `lit_gpt10_boost_converter`, each
a successor of every mode, alone declare 2304 of them, all vacuous.

`relcert <input.txt>` includes the check in its verdict (CERTIFIED requires every handoff
query `unsat`); `relcert --handoff <input.txt>...` runs it alone, with per-transition verdicts,
wall time, and a Z3 countermodel for a failing transition.

## Results: suite_v2 (50 files, 2846 transitions, all `unsat`)

Declared transitions per benchmark, read from the files' `next` lists; the Theorem 3 form of
the bridge instance (`docs/CERTIFICATION-CHECK.md`, per-benchmark inventory). 17 benchmarks
are mode-dependent, 33 vacuous; `platoon_profiles` is stated in the mode-keyed form with
identical rows.

| benchmark | left modes | transitions | invariant | Theorem 3 form |
|---|---|---|---|---|
| `acc_spoof_lag` | 1 | 1 | vacuous (rows identical) | window |
| `acc_spoof_limp` | 2 | 3 | vacuous (rows identical) | window |
| `acc_tune_limp` | 2 | 3 | mode-dependent | mode-keyed |
| `antenna_track_kvretune` | 3 | 6 | mode-dependent | mode-keyed |
| `autoclave_liquid_steambank` | 4 | 8 | mode-dependent | mode-keyed |
| `boiler_purge_vfd` | 2 | 3 | mode-dependent | mode-keyed |
| `bottling_fill_strainer` | 2 | 3 | vacuous (rows identical) | window |
| `canal_gate_notches` | 3 | 7 | vacuous (rows identical) | window |
| `elevator_start_discbrake` | 4 | 7 | mode-dependent | mode-keyed |
| `engine_start_highidle` | 6 | 12 | mode-dependent | mode-keyed |
| `extruder_pe100_manualstart` | 4 | 16 | vacuous (rows identical) | window |
| `flaps_slow_approach` | 2 | 3 | vacuous (rows identical) | window |
| `furnace_program_timebase` | 3 | 5 | vacuous (rows identical) | window |
| `gantry_speed_zones` | 3 | 5 | vacuous (rows identical) | window |
| `h2_refuel_ambientbias` | 7 | 14 | mode-dependent | mode-keyed |
| `hydro_rejection_gatecal` | 2 | 3 | mode-dependent | mode-keyed |
| `lit_csf21_vehicle_bus` | 6 | 24 | vacuous (rows identical) | window |
| `lit_csf21_vehicle_thermo` | 6 | 36 | vacuous (rows identical) | window |
| `lit_csf25_salt_tank_hold` | 2 | 2 | mode-dependent | mode-keyed |
| `lit_drl_lane_control` | 6 | 36 | vacuous (rows identical) | window |
| `lit_freedm_meter` | 12 | 144 | vacuous (rows identical) | window |
| `lit_girard08_robot` | 6 | 12 | vacuous (rows identical) | window |
| `lit_gpt10_boost_converter` | 48 | 2304 | vacuous (rows identical) | window |
| `lit_lz21_vehicle_position` | 3 | 9 | vacuous (rows identical) | window |
| `lit_nahs25_engine_cooling` | 2 | 4 | vacuous (rows identical) | window |
| `lit_nahs25_salt_tank` | 2 | 4 | vacuous (rows identical) | window |
| `molding_pack_checkring` | 2 | 3 | mode-dependent | mode-keyed |
| `platoon_profiles` | 1 | 1 | vacuous (rows identical) | mode-keyed |
| `quad_light_lag` | 1 | 1 | vacuous (rows identical) | window |
| `quad_light_profiles` | 3 | 9 | vacuous (rows identical) | window |
| `rampmeter_poll_2to1` | 6 | 36 | vacuous (rows identical) | window |
| `reactor_feed_wireless` | 4 | 16 | vacuous (rows identical) | window |
| `rover_ladder_2to3` | 3 | 5 | vacuous (rows identical) | window |
| `rover_ladder_3to6` | 3 | 5 | vacuous (rows identical) | window |
| `rover_ladder_6to8` | 3 | 5 | vacuous (rows identical) | window |
| `rover_ladder_8to12` | 3 | 5 | vacuous (rows identical) | window |
| `sat3w_detumble_phases` | 2 | 4 | vacuous (rows identical) | window |
| `sat_detumble_phases` | 2 | 4 | vacuous (rows identical) | window |
| `sat_detumble_weak` | 1 | 1 | vacuous (rows identical) | window |
| `stopline_drag` | 3 | 5 | mode-dependent | mode-keyed |
| `stopline_friction` | 3 | 5 | mode-dependent | mode-keyed |
| `stopline_lag` | 3 | 5 | mode-dependent | mode-keyed |
| `stopline_tyre` | 3 | 5 | mode-dependent | mode-keyed |
| `syringe_relay_prearm` | 6 | 13 | mode-dependent | mode-keyed |
| `tank_dos_3to1` | 4 | 10 | vacuous (rows identical) | window |
| `train_ato_odometry` | 3 | 9 | vacuous (rows identical) | window |
| `turbine_startup_gearratio` | 5 | 10 | mode-dependent | mode-keyed |
| `ventilator_vc_cuffleak` | 2 | 3 | mode-dependent | mode-keyed |
| `watertank` | 3 | 6 | vacuous (rows identical) | window |
| `watertank_twospeed` | 3 | 6 | vacuous (rows identical) | window |

## Re-running

    RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt   # the handoff phase: 2846/2846
    ./.lake/build/bin/relcert --handoff benchmarks/suite_v2/*/input.txt                                # per benchmark, exit 1 on any failure
