# Kernel-checked refutations: results (branch `refutation`)

> Benchmark names here predate the 2026-10-25 rename; old -> new: `benchmarks/README.md`, "Renamed 2026-10-25".

> 2026-10-26 (branch `benchmark-fixes`): the tables below are the 2026-10-21 run and predate two
> suite changes. The `rover_lateral` model changes added refutations (79 instances, 224 groups),
> and `rover_tier_1to2` (`rover3tier_rung12`) was retired with its two refutations (m000 kind C,
> m004 kind B; 9 mutants) and replaced by `tank_dos_3to1` (3 mutants, no witness: m000 open,
> m001/m002 tautologies, certified). The rollover files were aligned (rows of `rover_rollover_6to12`
> on all three, s offset 0, audited left domain): the finder over their 72 mutants keeps
> `rover_rollover_6to12_m010` (kind B, re-derived) and adds six of `rover_rollover_6to7` (m011, m016,
> m018 to m021, kind B; each DECLINED by relcert), none for `rover_rollover_7to12`. The rover
> batch of 2026-10-26 (ladder, terrain, attitude, lateral_8to12, patrol_zones) re-ran the finder on
> its 15 files: `rover_patrol_zones` m008, m012 and `rover_ladder_6to8` m009, m010 are gone with the
> rows they refuted (graded zone margins; quadratic attitude rows), `rover_lateral_8to12` has 7
> (m015, m019 to m024, kind B; each DECLINED by relcert; was 6), no other file of the batch has a
> witness. The nine redesigned files of 2026-10-26 (`acc_tune_lag`, `acc_spoof_lag`,
> `quad_light_lag`, `rover_patrol_lag`, `charger_fast_setpoints`, `charger_fast_tapers`,
> `acc_tune_limp`, `platoon_delay_profiles`, `quad_light_profiles`; 84 mutants) re-ran the finder:
> `rover_patrol_lag` m003, m004, m009, m013 and `acc_tune_limp` m008 are gone with the rows they
> refuted, `charger_fast_setpoints` m003 and `charger_fast_tapers` m003 are new (the charging row
> `x_L <= x_R + 2` flipped, kind C; each DECLINED by relcert), no other file of the batch has a
> witness. The terrain chain redesign of 2026-10-26 (`rover_terrain_3to6` renamed
> `rover_terrain_2to4`, `rover_terrain_6to8` renamed `rover_terrain_4to6`, all three right models
> new; the old files had no witness among their 24 mutants) re-ran the finder over its 95 mutants:
> 33 new refutations, all kind B, each DECLINED by relcert (`rover_terrain_2to4` m008, m011, m012,
> m015; `rover_terrain_4to6` m016, m017, m019 to m022, m024, m028; `rover_terrain_6to12` m020,
> m021, m023 to m026, m028 to m030, m032, m035, m037, m039 to m047: flipped, deleted or
> cross-side rows of the slip, lag, heave, pitch, acceleration and squat bounds).
> On 2026-10-27 four benchmarks moved to `benchmarks/reserve/` (no Lean integration) with their
> refutations and witness lines: `arm_plateau_profiles` (m000, kind B; 3 mutants),
> `platoon3_linkloss` (m072, m084, m096, kind C; 104 mutants), `platoon3_profiles` (96 mutants, no
> witness), `airheader_dos_3to1` (16 mutants, no witness).
> Also 2026-10-27: the finder's `bench_dims` read the bridge instance's dimension, which since the
> clocked change of 2026-10-21 already counts the right clock, and `gen_refute.py` adds the clock
> again, so the 55 refutations found after 2026-10-21 (`charger_fast_setpoints` m003,
> `charger_fast_tapers` m003, `rover_lateral_6to8` 6, `rover_lateral_8to12` 7,
> `rover_rollover_6to12` 1, `rover_rollover_6to7` 6, `rover_terrain_*` 33) were stated one
> dimension above their benchmark's bridge claim. Fixed (`bench_dims` is the Assumption 1
> dimension); the 55 instances are regenerated at the bridge dimension (the witnesses do not read
> the padded coordinate), each builds and its groups are `unsat`. The four redesigned files of
> 2026-10-27 re-ran the finder: `acc_spoof_limp` (8 mutants; m008 is gone with the row it
> refuted), `quad_light_lag` (24 mutants; m021 and m023 new, kind B, each DECLINED by relcert),
> `tank_dos_3to1` (16) and `vehicle_hypercert` (16), no witness.
> The platoon pair of 2026-10-27 (`platoon_delay_linkloss`, 12 mutants without a witness, replaced
> by `platoon_linkloss`; `platoon_latency` new): `platoon_linkloss` 63 mutants, m036 and m039 new;
> `platoon_latency` 67 mutants, m040 and m043 new (kind B, the floor rows `L_g >= 5`,
> `L_g + 2 L_r >= 5` flipped; each DECLINED by relcert).
> The two new files of 2026-10-27: `engine_start_highidle` (6 mutants; m003 new, kind C, the
> `n_L <= n_R + 4` rows flipped, DECLINED by relcert) and `train_ato_odometry` (8 mutants, no
> witness).
> Batch I2 renames (2026-10-27): `match_multi_rate` (3 mutants, no witness) replaced by
> `gantry_speed_zones` (16 mutants, no witness); `platoon_delay_profiles` (8 mutants, no witness)
> replaced by `platoon_profiles` (51 mutants; m008 and m011 new, kind B, the floor rows
> `L_g >= 5`, `L_g + 2 L_r >= 5` flipped, as on `platoon_linkloss`; each DECLINED by relcert).
> Batch I2 redesigns: `quad_light_airframe_20` (18 mutants), `quad_light_profiles` (18) and
> `watertank_twospeed` (8), no witness (8 each before, none). Batch I2 new files:
> `bms_chiller_undercharge` (8 mutants), `canal_gate_notches` (8) and `turbine_startup_gearratio`
> (3), no witness.
> Batch I3 (2026-10-27, the rover hierarchy): the ten rover files that left the suite took their 20
> refutations and 190 witness lines with them (`rover_lateral_6to8` 6, `rover_lateral_8to12` 7,
> `rover_rollover_6to12` 1, `rover_rollover_6to7` 6; the other six had no witness). The five
> reinstalled files re-ran the finder (`--only`, their records replaced in place):
> `rover_ladder_2to3` (7 mutants), `rover_ladder_3to6` (10) and `rover_patrol_lag` (10), no
> witness; `rover_ladder_6to8` (22 mutants; m006 and m009 new) and `rover_ladder_8to12` (27; m005,
> m006, m008, m009, m010, m019 and m026 new), all kind B: a coordinate of a requirement row moved
> to the other side (`L_omega_psi -> R_omega_psi` and the like; in m026 the plan row's `R_theta_p
> -> L_theta_p`) or a rate row deleted; each DECLINED by relcert (`rover_ladder_8to12_m005` exceeds
> the default 40 s budget, ERROR, and DECLINES in 45 s with `RELCERT_TIME_BUDGET_MS=280000`). The
> two 6to8 mutant inputs carry the suite file's header as of the finder run (minutes before the
> header's scratch path was removed); their non-comment lines equal the current file's mutants
> (`gen_refute.py` checks this).
> On 2026-10-27 (batch I4) seven more benchmarks moved to `benchmarks/reserve/` with their
> refutations and witness lines: `charger_fast_setpoints` (m003; 6 mutants), `charger_fast_tapers`
> (m003; 6), `sat_detumble_nominal` (m002, m003, m005, m006; 16), `sat3w_detumble_nominal` (m002 to
> m007; 16), `sat3w_detumble_weak` (m002 to m007; 16), `arm_plateau_crit` (m000; 3),
> `arm_plateau_slow` (m000; 3): 20 refutations and 66 witness lines out.
> Batch I4 also re-ran the finder on its six installed files: `acc_spoof_lag` 20 mutants,
> `acc_tune_lag` 12, `acc_tune_limp` 8, `sat_detumble_weak` 16, no witness (the four
> `sat_detumble_weak` refutations m002, m003, m005, m006 are gone: both sides are now design
> models); `sat_detumble_phases` 16 mutants (m002, m003, m005, m006) and `sat3w_detumble_phases` 16
> (m002 to m007), all kind B (a left energy coordinate moved to the right side of a row), each
> DECLINED by relcert (mutant inputs rewritten to the new files); the other 18 of their 28
> refutations of the round-2 files (m000, m001, m004, m007, m018 to m023, resp. m000, m001, m018 to
> m023) are gone with the rows and the 24-mutant claims they refuted.
> Batch I5 (2026-10-27, first group: nine new benchmarks) ran the finder on each (`--only`, records
> appended): `molding_pack_checkring` 24 mutants, `fuelcell_chp_dos` 16, `elevator_start_discbrake`
> 20, `furnace_program_timebase` 24, `compressor_station_recycle` 16, `syringe_relay_prearm` 28,
> `insulin_basal_cgmloss` 24, no witness; `hydro_rejection_gatecal` 32 mutants, m024 and m028 new,
> and `ventilator_vc_cuffleak` 24, m020 new, all kind C (a row of the band after the breaker opens,
> resp. of the expiratory band, flipped from `<=` to `>=`); each DECLINED by relcert. 3
> refutations, 6 groups and 208 witness lines in.
> Batch I5, second group: `rover_rollover_payload` (78 mutants; m023, m027, m028, m031 and m032
> new, all kind B: the heading-rate, roll-rate and slip-rate envelope rows of the payload rover
> deleted (m023, m027, m031) or moved to the right side (m028 `L_omega_phi -> R_omega_phi`, m032
> `L_omega_y -> R_omega_y`); each DECLINED by relcert, in 8 to 13 s). 5 refutations, 15 groups and
> 78 witness lines in.
> Current instance set: **69 refutations, 196 groups**
> (`InstancesV2/Refute/Table.lean`, `relcert-refute-verdicts`), witnesses over 947 mutants in
> `docs/refute/witnesses.jsonl`. The operator table has not been recomputed.

Design: `docs/REFUTATION-SCOPE.md` (planning record, last present at commit 29663d8). This file reports what was built and the experiment.

## The claim

> Of the 776 Black-Okun-Yesha mutants of the 50 suite benchmarks, **67 are proved false in the
> Lean kernel** (a refutation of Theorem 3's claim for the mutated invariant), 303 are certified
> by relcert, and 406 are open. **relcert certifies none of the 67.**

The trust base of a refutation is the trust base of a certificate: the parser and lowering
(the instance quotes the parser-emitted IR of the mutant file), the query printer and Z3's
`unsat` answers (`z3_unsat_sound`, discharged by `relcert-refute-verdicts` with a declared
count), and the kernel. The witness finder is untrusted: it only proposes rational witnesses,
which the kernel re-checks.

## What is refuted

For a mutant with per-mode rows, `¬ keyedClaim IR n cX cov ⊤ 0 1 2 3 dt`; with one declared row,
`¬ windowClaim IR n cX cov ⊤ 0 1 2 dt` (the forms of the bridge instances, at the bridge dimension
`n` of the suite benchmark, `reg = ⊤`; since 2026-10-21 the claims are the clocked ones, the
right automaton `rightAutomatonBodyC` with the right clock `(Aux, 3)` resp. `(Aux, 2)`, and
`n` is the Assumption 1 lemma's dimension plus one, `RefRec.dim + 1` in
`InstancesV2/Refute/Table.lean`, the rule of `bridgeDimV2`). Each instance proves the refutation

* **for every cover record `cov`**, hence for every pruning: the proofs never use the right
  automaton's edges (kind C does not use the right run at all; kinds A and B bound the right
  run by a monotonicity argument over every mode's flow, and jumps change no coordinate the
  component reads);
* **at the model's cut certificate `cX`** (`Oracle.<bench>_cutsV2X`): the tool computes the
  kept cut atoms from the model alone (`checkedCutX` runs per mode with the mode's guard,
  evolve and field, no invariant input), and every instance proves `same_model`
  (`IR.L = <bench>_IRv2.L ∧ IR.R = <bench>_IRv2.R`, `rfl`). The witness satisfies the stored
  right mode's guard and its kept atoms;
* for every window length `dt ≥ 0` (kinds C, A) or `dt > 0` (kind B).

## Generic theorems (`RelCertifier/Proofs/Encoding/Emitted/`)

| Theorem | Statement (one line) |
|---|---|
| `refute_keyed_C` (`Refute.lean:596`) | `preOK` (kernel) ∧ no-partner `unsat` per right mode ⟹ `∀ cov, ¬ keyedClaimU … ⊤ … dt`, `dt ≥ 0` (the unclocked claim, right automaton `rightAutomatonBody`) |
| `refute_keyed_A` (`Refute.lean:617`) | `preOK` ∧ component `k` of the entered row `> 0` (kernel) ∧ rigidity `unsat` per right mode ⟹ same |
| `refute_keyed_B` (`RefuteFlow.lean:418`) | `preOK` ∧ `bQ` (interior of the left envelope, component `≥ 0`, left Lie derivative `> 0`) ∧ `namesOK` ∧ `cutsOK` ∧ rigidity ⟹ same, `dt > 0` |
| `refute_window_B` (`RefuteFlow.lean:494`) | `preOKW` ∧ `bQW` ∧ `rowsSame` ∧ `namesOK` ∧ `cutsOK` ∧ rigidity ⟹ `∀ cov, ¬ windowClaimU … ⊤ … dt`, `dt > 0` |
| `keyedClaim_to_unclocked` (`Refute.lean:561`), `windowClaim_to_unclocked` (`RefuteFlow.lean:331`) | `namesOK` ∧ `cutsOK` ∧ `reg.fv ⊆ range Rv` ∧ `d ≠ a` ⟹ the clocked claim implies the unclocked one (`t3_right_mono`, `Refute.lean:491`: Theorem 3's form is monotone in the right program up to a post-condition transport; `erase_right_clock`, `Refute.lean:544`, by `star_bodyC_to_body`) |
| `refute_keyed_C_clocked`, `refute_keyed_A_clocked` (`Refute.lean:653`, `:662`), `refute_keyed_B_clocked` (`RefuteFlow.lean:478`), `refute_window_B_clocked` (`RefuteFlow.lean:578`) | the same hypotheses plus `namesOK`, `cutsOK`, `d : Fin n`, `d ≠ a` ⟹ `∀ cov, ¬ keyedClaim … ⊤ a b c d dt` resp. `¬ windowClaim … ⊤ a b d dt`, the clocked claims the bridge instances prove; these are what the generated instances conclude (`gen_refute.py`, `d = 3` keyed, `2` window) |
| `exit_run` (`RefuteExit.lean`) | short-time existence of the polynomial flow inside an open domain, with `G > 0` at the end when `G ≥ 0` and `Lie G > 0` at the start |
| `rigid_star` (`Refute.lean`) | a component no right field decreases on the right envelope never decreases along any run of the right automaton (any pruning) |

`#print axioms` of all four refutation theorems: `propext, Classical.choice, Quot.sound,
RelCertifier.z3_unsat_sound`. No `sorry`, no new axiom, no `native_decide`; witness facts are
`decide +kernel` on exact rationals (`ITerm.evalQ`, `IForm.evalQ_iff`).

Mechanism. The claim is eliminated once at a bi-state (`t3_elim`, `t3_elim'`). The left run is
one step of the left automaton (keyed: `?(u_L = u) ; ?guard_m ; u_L := m ; ?guard_m ; clock := 0 ;
flow_m`; window: the window of `m`), with a zero-duration flow (C, A, `sem_ode_zero`) or a flow
of positive duration `≤ dt` (B, `clocked_exit`). Right runs keep every left coordinate
(`rightStar_keepsL`), so the post-condition's entered row is read at the right end state itself.
Kind B uses the bi-state `(σ, σ')`, `σ'` the right copy carrying the left end values (the
antecedent reads only right coordinates there: `namesOK`, `cutsOK`).

The kinds: **C** no right state pairs with the witness's left values under the entered row
(one closed query per right mode, the left values fixed by equalities); **A** a component of the
entered row is already `> 0` and right-rigid; **B** a component is `≥ 0` on the boundary, the left
flow pushes it out to first order, right-rigid. **D** (projection exit, needs quantifier
elimination) is out of scope.

## Pipeline

1. `scripts/refute_dump.lean`: prints the claim's lowered pieces (guards, envelopes, kept cut
   atoms, row components, left Lie derivatives, the pinned rigidity queries) through the tool's
   own parser and lowering, as SMT-LIB.
2. `scripts/refute_finder.py` (untrusted): the mutants of `black_mutation.py` (same enumeration,
   labels identical), rational witnesses over exactly the dumped formulas (Z3 models; grid
   models `ℤ/den` when Z3's model is algebraic; quadric repair). Output
   `docs/refute/witnesses.jsonl`.
3. `scripts/gen_refute.py`: per witness, `benchmarks/refute_mutants/<id>/input.txt`, the
   parser-emitted IR (`relcert --emit-ir`) and the witness (`InstancesV2/Refute/Data/<id>.lean`),
   the instance (`InstancesV2/Refute/<Camel>.lean`), the runner table with its declared count.
4. `relcert-refute-verdicts` (`VerdictsV2/RunRefute.lean`): every group `refGroups` builds, the
   exact queries `RefVerdicts` reads, each group at the instance's dimension `RefRec.dim + 1`.
   Run: **188/188 groups unsat** over the 67 instances (`docs/refute/runner.log`); rerun
   2026-10-21 at the +1 dimension, 67/67 instances, 188/188 groups (commit `b14f129`; the
   queries do not read the padded coordinate, so the count is unchanged).
5. `scripts/refute_experiment.py`: relcert on every mutant (this worktree's binary,
   `RELCERT_IMPLIED_CUT=1`; the default verdict includes the handoff check), the table below
   (`docs/refute/results.json`, `docs/refute/relcert.json`, archived on branch `archive/legacy-2026-10` on 2026-10-22; `docs/refute/witnesses.jsonl` stays).

A mutant counts as kernel-refuted only if its instance builds (`lake build
RelCertifier.InstancesV2.Refute`: all 67 build) and the runner discharges all its groups.

## Results

| Operator | Certified | Kernel-refuted | Open | Total |
|---|---|---|---|---|
| RRO/SNO | 21 | 18 | 125 | 164 |
| MCO | 85 | 2 | 66 | 153 |
| ORO | 197 | 47 | 215 | 459 |
| **all** | **303** | **67** | **406** | **776** |

Kernel-refuted by kind: C 6, A 28, B 33 (keyed 7, window 26). By operator: RRO/SNO C 6, A 6,
B 6; ORO A 20, B 27; MCO A 2.

**Kernel-refuted and certified: none.** relcert's verdicts on the 776 mutants are those of the
mutation run (443 DECLINED, 303 CERTIFIED, 30 ERROR; the ERRORs are time-budget exhaustion, all
counted open); every kernel-refuted mutant is DECLINED.

Against the mutation run's unverified refuter (72 REFUTED): 67 of its 72 are kernel-refuted
(its kind labels differ in places because the kernel form reads the exact claim: the cuts and
the stored right mode's guard enter the antecedent, the left envelope is mode 0's evolve); the
kernel set adds no mutant it did not flag. Its two D refutations are kernel-refuted as kind B.
The five not kernel-refuted, reported open:

* `sat3w_detumble_phases_m016` (its C): no kind-C witness at the exact antecedent (the quantified
  no-partner search with the cuts finds none);
* `story3_rollover_base_12dof_m016`, `_m019`, `story3_rollover_ladder_rung_a_m008`, `_m011` (its
  B): the boundary point is on a quadric with only algebraic solutions near Z3's models; no
  rational witness was found (the grid and quadric-repair fallbacks did not find one in time).

## Not done

* Kind D (2 in the mutation run; both are kernel-refuted here as kind B anyway).
* The optional `relcert --refute` mode (it would change `Main.lean`); the finder, the generator
  and the runner give the three outcomes outside the tool.

## Reproduce

```
lake build relcert relcert-refute-verdicts
python3 scripts/refute_finder.py --out docs/refute/witnesses.jsonl     # ~1.5 h, untrusted
python3 scripts/gen_refute.py
lake build RelCertifier.InstancesV2.Refute
.lake/build/bin/relcert-refute-verdicts > docs/refute/runner.log
python3 scripts/refute_experiment.py
```

One benchmark only: `python3 scripts/refute_finder.py --only <b>` replaces that benchmark's
records in `docs/refute/witnesses.jsonl` and keeps the others. `gen_refute.py` takes a mutant's
text only from the finder run that found its witness (the record's `sha256` against that run's
scratch file, or the committed `benchmarks/refute_mutants/<id>/input.txt`), checks that it is
mutant `idx` of the current suite file, and otherwise stops with an error before writing
anything (2026-10-27; before, it copied whatever the scratch folder held, which for benchmarks
the last run did not visit was another run's file). It lists every mutant input it writes and
every file no record produces.
