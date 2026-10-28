# relCertifier-lean

A mechanized relational certifier for hybrid-system refinement, in Lean 4, and the
artifact that accompanies the paper.

Given two hybrid automata, an ideal system `L` and an implementation `R`, written in a
small textual format, the tool `relcert` certifies that `R` refines `L` up to a relational
invariant (bounds such as `x_L ≤ x_R + 3`). For **all 50** benchmarks of the paper's suite
(41 designed for it and nine case studies reproduced from published work (`drl_car_stop`, `drl_lane_control`: the sampled form of the refinement examples of differential refinement logic; `vehicle_hypercert`: the continuous-time counterpart of the HyperCertificates opacity vehicle; `freedm_meter`: the FREEDM transformer's battery-level nondeducibility through the grid meter; `csf21_vehicle_thermo`, `csf21_vehicle_bus`: the car whose cabin-temperature sensor is attacked, alone and over the drive's internal bus, from the relational analysis of sensor attacks, CSF 2021; `lz_vehicle_position`: the vehicle of approximate-opacity verification by barrier certificates, Liu and Zamani; `girard_robot`: the planar robot of approximate simulation relations, Girard, Julius and Pappas; `salt_tank_sensor`: the brine tank under a bounded sensor attack of the robustness measure of NAHS 2025), all but `salt_tank_sensor` needing the existential mode choice)
the repository contains a **kernel-checked Theorem 3** (the paper's Theorem 3, Soundness of Synthesis: the relational ∀∃ statement)
with the paper's own automata on both sides, **guard-gated**: every left window is entered
only inside its mode's guard (the left automaton, jump then flow) and every right mode change
enters a declared successor whose guard holds at that instant (flow then jump), at the
**mode-consistent region** (the right in the guard of its current mode and its checked cuts, the paper's mode facts of
Definition 2; the paper's operating region `op_R`),
whose only assumptions are a small trust base and a finite list of named Z3 `unsat` verdicts,
each of which the tool re-sends on demand. In the generic-bridge instances (the paper's route)
the right automaton is clocked: each right cycle flows for at most the control interval `ε_R`
(`rightAutomatonBodyC`, the cap as a post-test; `docs/PAPER-MAPPING.md` §9). The 50 generic-bridge instances **replay the
cover the tool emits** by the verified checker, inside the kernel: every joint segment of the
response is at a node the cover certified, at the cover's stretch, preserved by that node's
verdict group; every right-only reposition is at a node the cover flags, preserved by its
reposition group; every switch is a declared, non-pruned edge into an enabled successor; every
start the cover drops as inadmissible is contradictory. Each holds for every window up to the
left control interval (`dt ≤ ε_L`). (The earlier route, one hand-written standalone proof per
benchmark, is archived on branch `archive/legacy-2026-10`; see "Archived routes" below.)
The mechanization also found a modelling defect: in the two `platoon3`
benchmarks (in `benchmarks/reserve/` since 2026-10-27) the nominal controller blocked after a full cycle (engagement-band guards, no
catch-all mode), a violation of the certificate's Assumption 1 that the certificate itself
cannot detect; the guards are now the operating range and both are proved
(`docs/SUITE-REDESIGN.md` §20). Assumption 1 itself is now a separately verified model fact
per benchmark (`WellFormedR`): **proved for all 50 right models** in its literal form (the three
satellites since 2026-10-15, when their conserved momentum band entered the right evolve
domain; `docs/WELLFORMED.md`). Nine models violated it until 2026-10-10
(refuted in the kernel with exhibited blocking states: fallback sinks whose own flow left
their guard, approach bands narrower than one control interval) and were repaired
(`docs/SUITE-REDESIGN.md` §21). The tool checks both clauses per right mode
(`relcert --wellformed`; until 2026-10-26 only the successor clause, so a right model that
blocks at a domain bound passed it), STRICT in the certification recipe: `--check-quick-v2`
fails on any right mode that is `UNKNOWN` or `BLOCKING`. See
[Assumption 1 is verified per benchmark](#assumption-1-is-verified-per-benchmark).

Everything except Z3 is Lean: the parser, the lowering, the SMT printer, the search, the
certificate checker, the proofs and the per-benchmark theorems. Z3 is consulted only
through printed SMT scripts, and only its `unsat` answers are trusted.

## Contents

* [What the artifact certifies](#what-the-artifact-certifies)
* [The headline claim](#the-headline-claim)
* [Trust base](#trust-base)
* [Theorem families](#theorem-families)
* [Build and check](#build-and-check)
* [How one benchmark becomes a theorem](#how-one-benchmark-becomes-a-theorem)
* [Repository layout](#repository-layout)
* [Switches](#switches)
* [Guard-gated switching](#guard-gated-switching)
* [Assumption 1 is verified per benchmark](#assumption-1-is-verified-per-benchmark)
* [The 17 carried-over Assumption 1 proofs](#the-17-carried-over-assumption-1-proofs)
* [Archived routes](#archived-routes)
* [Further reading](#further-reading)

## What the artifact certifies

`benchmarks/suite_v2/` holds the paper's suite: **50 benchmarks** (adaptive cruise control,
a car under a cabin-temperature sensor attack, vehicle position opacity, a planar robot against its
planner's model, a brine tank under a sensor attack, quadrotor climb, vehicle platoons, satellite
detumbling, rover patrol, a turbofan ground start, train speed control, a pick-and-place gantry, a building zone's
heating schedule in a lightweight construction, a wind turbine start-up, a fuel-cell CHP unit, an exothermic reactor's feed interlock, an elevator trip, a heat-treatment furnace program, a syringe-pump relay, a hydro unit's load rejection, volume-controlled ventilation, road-tunnel ventilation through a fire alarm, an island grid's fast frequency response under a denial-of-service attack, a bottle filler, a hydrogen refuelling under a sensor bias, a DC fast charger, an airliner's flap extension, the rover refinement ladder up to 12 degrees of freedom and the rover terrain chain; `benchmarks/README.md`). With the widened cut channel on
(`RELCERT_IMPLIED_CUT=1`) the tool CERTIFIES all 50; without it, 4 of them DECLINE; fifteen DECLINE without the existential mode choice (`RELCERT_NO_CHOICE=1`): eight of the nine literature benchmarks (all but `salt_tank_sensor`), `acc_tune_limp`, `quad_light_profiles`, `zone_lightmass_schedule`, `sat_detumble_phases`, `sat3w_detumble_phases`, `sat_detumble_weak` and `fuelcell_chp_dos`; the other 35 covers are byte-identical with it on or off. Near-duplicates and weak benchmarks are kept outside the suite in `benchmarks/reserve/` (inputs and verdicts only, `benchmarks/reserve/README.md`). One of them, `watertank_twospeed`, needs a different stretch per pairing (`RELCERT_NO_PAIR_STRETCH=1` DECLINES it; §22 of `docs/SUITE-REDESIGN.md`).

The parts of the artifact:

| part | where |
|---|---|
| the suite | `benchmarks/suite_v2/<name>/input.txt` |
| the tool (certifier, verdict runner, emitters) | `relcert` (`Main.lean`, `RelCertifier/Trusted/`) |
| the trusted-layer tests | `relcert-test` (`Test.lean`) |
| the generic soundness development | `RelCertifier/Core/`, `Checker/`, `Proofs/`, `Trusted/` |
| the runner tables and the pins tying every hypothesis to the query the runner sends | `RelCertifier/VerdictsV2/` (and `Verdicts/`: the shared verdict combinators, pins and the handoff runner) |
| Assumption 1 of every right model (`WellFormedR`), axiom-audited on every build | `RelCertifier/InstancesV2/WellFormedBattery.lean` (`docs/WELLFORMED.md`) |
| the generic bridge: Theorem 3 of every benchmark from its emitted records, the choice exhibits included | `RelCertifier/Proofs/Encoding/Emitted/`, `RelCertifier/InstancesV2/Bridge/`, `relcert-bridge-verdicts` (`docs/BRIDGE.md`) |
| the suite evaluation scripts | `scripts/suite_v2_matrix.py` (mechanism matrix), `scripts/domain_widening.py` (load-bearing domain bounds) |

## The headline claim

For each of the 50 suite_v2 benchmarks there is a Lean theorem

```lean
RFormula.rvalid (theorem3Form (leftAutomatonBody A uL)     -- the left automaton (jump, then flow)
                              (rightAutomatonBody Gr mv)   -- the right automaton (flow, then jump)
                              (psiK uL ϕ A.numModes domL domR (mvRegionR mv gregion Gr.modes.length)))
-- psiK = ⋀_m (u_L = m → ϕ m) ∧ domL ∧ domR ∧ mvRegionR mv gregion … ∧ u_L ∈ modes
-- gregion q = regionG guard cuts q = guard q ∧ cuts q   (the mode-consistent region)
```

with `theorem3Form L R Φ = Φ → [|(L*, R*)⟩⟩ Φ`: from every state satisfying `Φ`, whatever
the left system does, the right system can respond so that `Φ` holds again, through every
round. Both automata are the file's and both are **guard-gated**. The left automaton
`leftAutomatonBody A u_L` is the paper's `?(m ∈ next(u_L)) ; ?guard_m(x) ; u_L := m ; flow_m`:
each left step selects a declared successor of the current left mode `u_L`, tests its lowered
guard, and runs its clock-capped window (`A` is read from the IR: windows, guards, `next`
lists). The right automaton tests, on every declared edge, the lowered guard of the mode it
enters (`Gr_guards` in each instance), so every switch of the response is a legal move of the
paper's model `R`. `Φ` is the declared relational invariant keyed by `u_L` (one row for every
left mode in the 33 mode-independent benchmarks), the joint evolve domains, `u_L ∈ modes`, and
the mode-consistent region of the right's current mode `q`: `q`'s lowered guard and its checked
cuts (pruned sink modes have the empty region). What each rotation guarantees at a loop
boundary is what `Φ` carries: the right has just taken a guarded jump into `q`, so it is in
`q`'s guard; the left has just flowed, so the guard of its NEXT window is tested by the program,
not carried. The mode-independent benchmarks are proved over the choice of their windows and
carried to the left automaton by one generic bridge (`theorem3_leftAut_of_choice`,
`Proofs/Encoding/LeftAutUniform.lean`).
The theorem's one Z3 hypothesis, `Verdicts`, IS the list of groups the runner
`relcert-bridge-verdicts` issues (4874 over the 50 suite benchmarks and the 2 exhibits, against
the declared count), each coming back `unsat`; `relcert --check-quick-v2` re-sends the tool's
own queries as a self-check (modal 1004, handoff 528, non-connection 64, pruned edges 32,
reposition 75). The axiom audit of every theorem is a subset of
`{propext, Classical.choice, Quot.sound, z3_unsat_sound}`; none of the 50 is Z3-free (every
flow fact of every response is a group of the emitted cover). No
`sorry`, no `admit`, no `native_decide`.

The statement above is the unclocked form (`rightAutomatonBody Gr mv`, the form of the archived
standalone instances). The generic-bridge
instances (`InstancesV2/Bridge/`, all 50 suite benchmarks and the 2 choice exhibits; the
paper's route, `docs/BRIDGE.md`) state the same form over the **clocked** right automaton
`rightAutomatonBodyC Gr mv tr (epsR p)` (since 2026-10-21): per right mode `q`,
`?(mv = q); tr := 0; {x' = f_q, tr' = 1 & Q_q}; ?(tr ≤ ε_R); switch`, the paper's
`t := 0; {…, t' = 1 & t ≤ ε_R}` with the cap as a post-test (the same runs, the clock being
monotone from `0`). The right clock is a fourth auxiliary coordinate `(Aux, d)` next to the
right mode variable `(Aux, a)`, the left clock `(Aux, b)` and the stored left mode `(Aux, c)`,
so a bridge instance lives at the Assumption 1 lemma's dimension plus one (`bridgeDimV2`,
`VerdictsV2/RunBridge.lean:74`); the lemma is lifted by `Emitted.wellFormedR_lift` under the
kernel-decided `padOK` (`Proofs/Encoding/Emitted/Lift.lean`). The clocked claim implies the
unclocked one (`keyedClaim_to_unclocked`, `Proofs/Encoding/Emitted/Refute.lean:561`): the
bridge statement is the stronger of the two. The theorems are
`theorem3_keyed_of_records … (hwf : WellFormedRIn …) (a b c d : Fin n) … : keyedClaim p n cX cov reg a b c d dt`
(`Emitted/Keyed.lean:427`) and `theorem3_window_of_records … (a b d : Fin n) … : windowClaim p n cX cov reg a b d dt`
(`Emitted/Window.lean:83`); the generated instances take `0 1 2 3` resp. `0 1 2` and `reg = ⊤`.

## Trust base

| item | why it cannot be removed |
|---|---|
| the **parser** (`Trusted/Parse.lean`, strict; unknown keys refused by `Trusted/KeyAudit.lean`) reads the benchmark file correctly | the file is the specification |
| the **lowering** (`Trusted/Run.lean`) means what it says | it fixes how the parsed model becomes formulas |
| the **printer** (`toScript`) renders formulas to SMT-LIB faithfully | Z3 reads text |
| **Z3's `unsat`** answers are correct | the one oracle: axiom `z3_unsat_sound` (`Trusted/Oracle.lean`) |
| the **Lean kernel** | checks everything else |
| the **lowering of the right guards** onto the edges (`hostGuard … Side.R (mR t)`, the same lowering as the left guards) | part of the lowering item above; each instance proves its edges carry exactly these guards (`Gr_guards`) |
| (not an item) Assumption 1 of the right model | not assumed: stated as `WellFormedR` and proved for all 50 (the three satellites since their momentum band entered the right evolve domain, 2026-10-15), all Z3-free, kernel-only (no trust-base item beyond the parser and lowering that produce the automata); the generic-bridge instances take it as the hypothesis `hwf : WellFormedRIn …` of `theorem3_keyed_of_records` / `theorem3_window_of_records` and discharge it from the benchmark's proof, transported and lifted by one coordinate (`wellFormedR_lift`; `docs/WELLFORMED.md` §6) |
| (not an item) the right clock coordinate `(Aux, d)` of the bridge instances | a padded coordinate of the lowering, unbound in every lowered formula (`padOK`, decided in the kernel); the runners send every query at the instance's dimension and the declared counts (4457, 188) are unchanged |

The search (cover exploration, checked-cut search, route and λ selection) is untrusted: it
only proposes. Every accepted output is either re-decided in the kernel (the cover replay
`decideCovered`, the cut certificates' well-formedness) or becomes a named Z3 fact.

Guard-gated switching is no longer a trusted item: for all 50 theorems both automata test
each entered mode's guard in the program, and every switch of each response
is kernel-checked legal (`Proofs/Encoding/GuardedSwitch.lean`: `SwitchLegal`, `gseg`,
`guarded_rights_bridge`, `GResp`). The region of the loop invariant is `guard ∧ cuts` of the
right's current mode (`regionG`), the same shape for all 50 benchmarks; it is a property of
the statement, not an assumption: the theorem's premise and conclusion both carry it.
Nonblocking (the paper's Assumption 1) is taken by the generic-bridge theorems as `hwf` and
discharged from the per-benchmark proof. Assumption 1 itself is a separately verified model fact (`WellFormedR`, [below](#assumption-1-is-verified-per-benchmark));
the tool's `--wellformed` check of it is untrusted and only ever declines: strict in
`--check-quick-v2` (an `UNKNOWN` or `BLOCKING` right mode fails the recipe), informational as
`relcert --wellformed`, and per run under `RELCERT_WELLFORMED_STRICT=1`.

The search (cover exploration, checked-cut search, route and λ selection) is untrusted: it
only proposes. Every accepted output is either re-decided in the kernel (the cover replay
`decideCovered`, the cut certificates' well-formedness) or becomes a named Z3 fact.

## Theorem families

Counts read off `InstancesV2/Bridge.lean`, `InstancesV2/WellFormedBattery.lean`,
`InstancesV2/Refute.lean` and their build output.

| family | count | which |
|---|---|---|
| the generic bridge: Theorem 3 of the benchmark from its emitted records (IR, cut certificate, cover, progress and choice records), over the clocked right automaton `rightAutomatonBodyC` at dimension `bridgeDimV2 b` (the Assumption 1 lemma's dimension + 1, the right clock), Assumption 1 lifted by `wellFormedR_lift`, the structural facts decided in the kernel, every verdict from one Z3 run (`InstancesV2/Bridge/`, `relcert-bridge-verdicts`, 4874 groups over the 50 suite benchmarks and the 2 exhibits; `docs/BRIDGE.md`) | **52** | all 50 suite benchmarks (38 window form, 12 mode-keyed) and the choice exhibits `vehicle_accel_copy`, `watertank_choice` |
| of which mode-keyed (per-left-mode rows composed through handoffs, `keyedClaim`) | **12** | `acc_tune_limp`, `charger_fast_tapers`, `elevator_start_discbrake`, `engine_start_highidle`, `h2_refuel_ambientbias`, `hydro_rejection_gatecal`, `platoon_latency`, `platoon_linkloss`, `platoon_profiles`, `syringe_relay_prearm`, `tunnel_jetfan_pairout`, `ventilator_vc_cuffleak` (the satellite phase files' rows are identical since 2026-10-27: window form) |
| Assumption 1 (`WellFormedR`) of the right model, proved in the kernel, Z3-free (`InstancesV2/WellFormed/<B>.lean`, `InstancesV2/WellFormedBattery.lean`; 66 axiom lines, each the three standard axioms) | **50** | every suite benchmark (the three satellites with the conserved momentum band in the right evolve domain; `docs/WELLFORMED.md`) |
| model repaired by this mechanization (the nominal controller blocked after a full cycle; `docs/SUITE-REDESIGN.md` §20) | **0** | (the two, `platoon3_linkloss`, `platoon3_profiles`, are in `benchmarks/reserve/` since 2026-10-27) |
| model repaired for Assumption 1 (`WellFormedR` refuted in the kernel, then proved; `docs/SUITE-REDESIGN.md` §21) | **0** | (`arm_plateau_{crit,profiles,slow}` and `platoon3_{linkloss,profiles}` are in `benchmarks/reserve/`, `platoon_delay_{linkloss,profiles}` were replaced by `platoon_linkloss` and `platoon_profiles` (in `benchmarks/reserve/` since batch I8), and `quad_light_{airframe_20,profiles}` redesigned without the limiter mode, on 2026-10-27) |
| widened cut channel needed (`RELCERT_IMPLIED_CUT=1`; closures, implied contractions, linear-form chains; lifted to the kernel by `Proofs/Soundness/CutLiftX.lean`) | **4** | `engine_start_highidle`, `turbine_startup_gearratio`, `furnace_program_timebase`, `charger_fast_tapers` (each DECLINES without the channel; `charger_fast_tapers` was in `benchmarks/reserve/` from batch I4 to batch I7 on 2026-10-27; `arm_plateau_{crit,slow}` and `charger_fast_setpoints` needed it too until they moved to `benchmarks/reserve/` on 2026-10-27) |
| the non-connection certificate of a pruned edge (the paper's Definition 6, `Checker/NonConn.lean`): enters every bridge instance as the barrier of each pruned exit (`nonconn_entry`, `nonconn_keep`, `guard_pos_of_barrier`), the 50 queries of the 25 pruned edges re-sent by `--check-quick-v2` and as bridge groups | **25** edges | `docs/PAPER-MAPPING.md` §5 |
| kernel refutations of known-false invariant variants, each the negation of the clocked bridge claim at its benchmark's bridge dimension (`InstancesV2/Refute/`, `relcert-refute-verdicts`, 199 groups) | **67** | `docs/REFUTATION-RESULTS.md` |
| the strict-invariant exhibit (`benchmarks/strict_demo`, `InstancesV2/Bridge/WatertankStrict.lean`) | **1** | `watertank_strict` |

The generic theorems' audit (`InstancesV2/AxiomCheck.lean`, 9 lines) and the Assumption 1
battery's (51 lines) are re-emitted on every `lake build`; the bridge instances carry
`z3_unsat_sound` exactly through their `Verdicts` hypothesis.

## Build and check

Requirements: the Lean toolchain of `lean-toolchain` (elan fetches it; the one Lean
dependency, dL-rel, is pinned by tag in `lakefile.toml`) and Z3 (the tool looks for
`/opt/homebrew/bin/z3`, `/usr/local/bin/z3`, `/usr/bin/z3`, or `RELCERT_Z3`).

```bash
# 1. kernel-check everything (the library root imports the proof chain, the Assumption 1
#    battery, the bridge instances and the refutation instances; see the note on heavy files below)
lake build
lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts

# 2. the Assumption 1 battery (66 lines, the three standard axioms only) and the generic
#    theorems' audit (InstancesV2/AxiomCheck, 9 lines)
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
lake build RelCertifier.InstancesV2.AxiomCheck 2>&1 | grep -A3 "depends on axioms"

# 2b. the Z3 hypotheses of the 52 bridge instances (4874 groups) and the progress
#     certificates of every reposition node (199 queries), against declared counts
./.lake/build/bin/relcert-bridge-verdicts
./.lake/build/bin/relcert-progress-verdicts

# 3. certify the 50 files (strict well-formedness), re-send the tool's own queries, and run the
#    strict Assumption 1 gate, all with declared counts
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt

# 3b. the expected DECLINEs (the leaky FREEDM controller, the leaky CSF 2021 car)
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt

# 3c. the expected Assumption 1 failure (a right model that blocks at the bound s = 8; the
#     default run certifies it, the strict gate declines it)
./.lake/build/bin/relcert --wellformed benchmarks/negative_wellformed/*/input.txt
RELCERT_IMPLIED_CUT=1 RELCERT_WELLFORMED_STRICT=1 ./.lake/build/bin/relcert benchmarks/negative_wellformed/*/input.txt

# 4. the trusted-layer tests (IR drift of all 50 literals, parser, printer, Z3 layer,
#    determinism); the manifest lets the two determinism checks run
for d in benchmarks/suite_v2/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"
done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test

# 5. the kernel-checked refutations of the 67 invariant variants (docs/REFUTATION-RESULTS.md):
#    re-send their Z3 groups with the declared count (each at the variant's bridge dimension,
#    RefRec.dim + 1), then build their instances (each concludes the negation of the clocked
#    bridge claim, refute_*_clocked)
./.lake/build/bin/relcert-refute-verdicts
lake build $(ls RelCertifier/InstancesV2/Refute/*.lean | sed 's|/|.|g; s|\.lean$||')
```

Expected: `Build completed successfully`; 66 axiom lines (WellFormedBattery), each exactly
the three standard axioms (`lake` also replays the 11 lines of `CutLiftX.lean`'s own audit);
9 axiom lines (AxiomCheck), each a subset of the four axioms above; `relcert-bridge-verdicts`: `4874/4874` at the bridge dimensions;
`relcert-progress-verdicts`: `199/199`; `[suite_v2] 50 certified, 0 declined, 0 error(s)`,
coverage `modal 1004/1004`, `handoff 528/528`, `non-connection 64/64`, `pruned edges 32/32`,
`reposition (dyn) 76/76`, the strict Assumption 1 gate `[wellformed] STRICT: 184/184 right modes ok,
both clauses (88 invariant, 96 exit), 0 UNKNOWN, 0 BLOCKING — matches the declared suite`,
`wellformed (strict): PASS`, `SUITE_V2 QUICK CHECKS PASSED`;
`benchmarks/negative/freedm_meter_leaky` and `csf21_vehicle_thermo_leaky`: both `DECLINED`; `vehicle_hypercert_s8`: all five right
modes `BLOCKING (leaves s <= 8.0)`, and `DECLINED` under the strict switch;
`relcert-test`: a bare `ALL PASS`; `refute: 199/199 hypotheses discharged` (the bridge and
refute counts are unchanged by the right-clock coordinate of 2026-10-21: no query reads it).

The default `relcert <file>` verdict includes the handoff check (CERTIFIED requires the cover and
the handoff condition, the paper's Eq. 13, at every declared left mode change). Strict invariant atoms (`<`, `>`) are supported
faithfully: a strict component is certified only by the whole-domain or strict-boundary route,
and its Theorem 3 instance states the strict row (`theorem3_*_strict_of_records`,
`benchmarks/strict_demo/`); a strict atom in an evolve domain is refused by the Assumption 1
check.

**Heavy files.** Since the standalone instances were archived (2026-10-22) no module takes
more than about a minute: the heaviest are the 12-dimensional Assumption 1 proofs
(`InstancesV2/WellFormed/RoverLadder8to12`, `RoverTerrain6to12`, about 35 s each) and the refutation
instances; a plain `lake build` is enough. `lake build` is incremental, but an edit to
anything under `Proofs/`, `Checker/` or `Trusted/` rebuilds every instance downstream. The
full recipe, what each check establishes and what it does not, and the measured cost:
`docs/CERTIFICATION-CHECK.md`.

## How one benchmark becomes a theorem

```
benchmarks/suite_v2/<b>/input.txt                 the specification
  │ Trusted/Parse.lean + KeyAudit.lean             parse                      TRUSTED
  ▼
PProblem  ──(relcert --emit-ir)──▶ InstancesV2/BenchIR/<b>.lean   the frozen literal
  │                                 ▲ relcert-test [ir-drift-v2]: re-parse and compare
  │ Trusted/Run.lean                               lower to SMT-IR             TRUSTED
  │ Trusted/OracleAPI.lean                         search                      UNTRUSTED
  ▼
a cover (stretches, budgets, flags, admissible starts, strata orders, pruned edges),
a checked-cut certificate (the paper's mode facts, Definition 2), the progress certificates of
its reposition nodes (the paper's reposition certificates, Definition 7)
  ├─(--emit-cover)─▶ InstancesV2/BenchCovers/<b>.lean
  │                   ▲ the bridge instance: decideCovered / decideCoveredX accepts, by `decide +kernel`
  ├─(--emit-cuts)──▶ InstancesV2/Cuts/<b>.lean
  │                   ▲ evolStrengtheningWFX … = true, by `rfl`
  └─(RELCERT_PROGRESS_OUT)─▶ InstancesV2/BenchProgress/<b>.lean
  ▼
InstancesV2/Bridge/<B>.lean  (generated)           the generic-bridge instance at dimension
  │                                                 n = bridgeDimV2 b (the Assumption 1 lemma's
  │                                                 dimension n0 + 1, the right clock): the general
  │                                                 Theorem 3 (Proofs/Encoding/Theorem3General,
  │                                                 right automaton rightAutomatonBodyC)
  │                                                 applied to the records through
  │                                                 Proofs/Encoding/Emitted; structural facts
  │                                                 by `decide +kernel` (incl. pad_ok : padOK IR n0),
  │                                                 Assumption 1 from InstancesV2/WellFormed/<B>.lean
  │                                                 transported, then lifted (Emitted/Lift.lean)
  ▼
<b>_bridge : Verdicts p n cX cov prog → dt ≤ εL → windowClaim … 0 1 2 dt (or keyedClaim … 0 1 2 3 dt)
  │ Emitted/Run.lean: `Verdicts` IS the group list the runner issues (verdicts_of_groups)
  ▼
relcert-bridge-verdicts: rebuilds every group at n, prints it with toScript, Z3 says `unsat`
```

`scripts/gen_v2_data.py` regenerates the data leaves of every benchmark (IR literal, cover,
progress certificates, cut certificates, chosen sets) and the aggregators from the tool's
emitters; `scripts/gen_bridge.py` regenerates the bridge instances and `InstancesV2/Bridge.lean`.

## Repository layout

```
RelCertifier/
  Core/          3 files   flow certificates (DI routes A/B/C), rational reification
  Checker/      13 files   verified cover checkers (decideCovered, decideCoveredX with the
                           existential mode choice), emitted-cover types, checked-cut
                           certificates (EvolStrengthening, EvolStrengtheningX),
                           non-connection (Definition 6)
  Proofs/
    Encoding/   59 files   the ∀∃ chain: CSF/NFM'25 bridge, joint segments, repositions,
                           envelope and window chains, mode handoffs, guarded switching,
                           the non-connection bridge, Assumption 1 (WellFormedR; the shared
                           ladder and terrain-chain lemmas WellFormedLadder, WellFormedTerrain),
                           the general Theorem 3 (Theorem3General, CoverResp, Progress)
      Emitted/  19 files   the generic bridge: a benchmark's Theorem 3 from its emitted
                           records (Data, Stay, Barrier, Anchor, Progress, Keyed, Window,
                           Transport, Lift, Choice, Region, Run, the strict and refute layers)
    Flow/       15 files   DI routes, Picard existence, viability faces
    Soundness/   8 files   the cut lift (CutLift; CutLiftX for the widened channel)
    Transfer/    2 files   scaled-model transfer (FaithfulBridge, Rescale; imported by CutLiftX)
  Trusted/      20 files   parser, key audit, lowering, printer, Z3 session, the certifier
                           (OracleAPI), the query builders (handoff, non-connection,
                           bridge stays and admissibility, progress, choice), emitters,
                           the Assumption 1 check (WellFormedCheck); Trusted/README.md
  InstancesV2/  the suite_v2 battery
    BenchIR/ BenchCovers/ BenchProgress/ Cuts/ BenchChoice/   46 files each   emitted data,
                           one leaf per benchmark (IR literal, cover, progress certificates,
                           cuts, chosen sets) and the strict exhibit `watertank_strict`
    Bridge/     53 files   the generated generic-bridge instances (`<b>_bridge`): all 50
                           suite benchmarks, the two choice exhibits (docs/BRIDGE.md) and
                           the hand-written strict exhibit WatertankStrict
    WellFormed/ 51 files   Assumption 1 (`WellFormedR`) per suite benchmark, each file
                           self-contained (right model + proof; `platoon_linkloss`
                           and `platoon_profiles` share the follower lemmas
                           `PlatoonCaccAeb`); the
                           carried-over proofs included
    Refute/    68 files   the 67 kernel refutations and their Table; Refute/Data/ (67)
                           the mutant records (docs/REFUTATION-RESULTS.md)
    Choice/                the two choice exhibits' leaves (BenchIR, BenchCovers,
                           BenchProgress, BenchChoice, Cuts), ConstMirror, and General/
                           (the two exhibits' right models and Assumption 1 proofs)
    AxiomCheck.lean, WellFormedBattery.lean, Bridge.lean, Refute.lean, and the five
                           leaf aggregators (BenchIR, BenchCovers, BenchProgress, Cuts,
                           BenchChoice)
  VerdictsV2/    9 files   runners (RunV2, RunBridge, RunRefute, RunProgress), query
                           rebuild (ModalX, ModalDynX, ModalXStrict, ProgressX), the
                           progress pin (ProgressPin)
  Verdicts/      6 files   the shared verdict combinators and pins (Combinators, Mirrors,
                           Coverage, GenericPins, ModalPins) and the handoff runner (RunHandoff)
Main.lean                  relcert
Test.lean                  relcert-test
BridgeVerdictsMain.lean, ProgressVerdictsMain.lean, RefuteVerdictsMain.lean
                           relcert-bridge-verdicts, relcert-progress-verdicts,
                           relcert-refute-verdicts
benchmarks/suite_v2/       the 50 inputs; benchmarks/reserve/ the reserve inputs (no Lean); benchmarks/choice/ the 2 choice exhibits;
                           benchmarks/strict_demo/ the strict exhibit; benchmarks/refute_mutants/
                           the 77 mutants; benchmarks/negative/ two expected DECLINEs (the
                           leaky FREEDM controller, the leaky CSF 2021 car)
scripts/                   gen_v2_data.py, gen_bridge.py, gen_refute.py, gen_strict_demo.py,
                           paper_numbers.sh (the frozen paper numbers), suite_v2_matrix.py,
                           suite_v2_letters.py (Table 1 letters per benchmark),
                           domain_widening.py, z3_timing_proxy.py, trust_audit.py
docs/                      see Further reading; docs/paper-numbers/ the frozen run of
                           paper_numbers.sh (numbers.tex, matrix, letters, suite_results.json)
```

`RelCertifier.lean` imports the library (the proof chain, the Assumption 1 battery, the bridge
and refutation instances); `lake build` builds that closure. The runners and the tool are the
executables above.

## Switches

Environment variables of `relcert` (`relcert --help` prints the same list):

| variable | effect |
|---|---|
| `RELCERT_IMPLIED_CUT=1` | widen the checked-cut candidates (closures of strict guard conjuncts, implied-contraction atoms, linear-form chains of second-order pairs); every suite_v2 run sets it; `--emit-cuts` then also prints the extended certificate |
| `RELCERT_NO_IMPLIED_CUT=1` | force the widened candidates off (the matrix's M6+ counter-run) |
| `RELCERT_NO_LINEAR_CUT=1` | keep closures and implied atoms, switch the linear-form chain off (the M6L counter-run) |
| `RELCERT_NO_PRUNE=1` | disable non-connection pruning (the M4 counter-run) |
| `RELCERT_NO_CUT=1` | disable the checked-cut channel (the M6 counter-run) |
| `RELCERT_DEBUG=1` | per-mode diagnostics on stderr |
| `RELCERT_WELLFORMED_STRICT=1` | run the `--wellformed` check on every CERTIFIED benchmark and DECLINE it when a right mode is `UNKNOWN` or `BLOCKING` (off by default for a single run, no verdict and no emission changes; `--check-quick-v2` forces it on; on the repaired suite no benchmark declines, before the 2026-10-10 repairs 9 did) |
| `RELCERT_Z3=<path>` | the Z3 binary |
| `RELCERT_Z3_TIMEOUT=<ms>` | per-query timeout, default 10000 |
| `RELCERT_Z3_RLIMIT=<n>` | per-query deterministic resource limit, default 64000000 |
| `RELCERT_MAX_QUERIES=<n>` | per-benchmark query budget, default 20000 |
| `RELCERT_TIME_BUDGET_MS=<ms>` | per-benchmark wall-clock budget, default 300000 (5 min; 40000 before 2026-10-27) |

## Guard-gated switching

The paper's model switches only into a declared successor whose guard holds at the switch
state, on both sides. Until branch `guarded-right` every right graph the instances built
carried `⊤` edge guards (the theorems were about the declared-successor relaxation of `R`), and
the mode-independent instances flattened the left to the choice of its windows. The guarded
generic layer (`Proofs/Encoding/GuardedSwitch.lean`) states the step obligation `GResp` over
segments that each end with their switch test, and `guarded_rights_bridge` turns such a
response into a run of the guarded automaton. At the old invariants (rows, envelopes, kept
cuts, no guard) 23 statements were false: the invariant admitted right states the guarded
automaton never reaches and cannot leave. The final statement carries the mode-consistent
region `guard ∧ cuts` of the right's current mode (`regionG`), which the flow-then-jump
rotation maintains, and states the left as the paper's guard-gated automaton (one generic
bridge, `theorem3_leftAut_of_choice`). With them all 46 were proved on the standalone route,
mostly by explicit responses that switch at band floors (ladder climbs, synchronized climbs
inside the window, a decay budget for attitude rows: `GuardedClimb`, `LadderClimb`,
`SyncSwitch`, `LadderSync`; the route is archived, see "Archived routes").
Two findings: three ladders (`rover_ladder_3to6`, the `rover_lateral` pair) are false with a left window that
has no guard test but true with the paper's left program (the band order the left guard
gives makes every stretch a certified pair); and the two `platoon3` benchmarks (in `benchmarks/reserve/` since 2026-10-27) were refuted in
the kernel because their nominal controller BLOCKED after a full cycle (engagement-band stay
guards, no catch-all mode: Assumption 1 violated by the model, undetectable by the
certificate), and are repaired. Record, per-benchmark switch classification, the exact states
and the final table: `docs/GUARDED-SWITCHING.md`.

## Assumption 1 is verified per benchmark

The paper's Assumption 1 (Well-Formedness): *the right model is nonblocking and complete with
respect to its declared successor relation: from every state satisfying a source-mode guard,
an evolution spanning the control interval `ε_r` exists, and every evolution of duration at
most `ε_r`, including the empty one, ends in a state satisfying the guard of at least one
declared successor mode.* The generic-bridge theorems
take it as a hypothesis discharged from the per-benchmark proof (lifted by one coordinate,
`docs/WELLFORMED.md` §6); it is a separately audited model fact.

**The predicate** (`Proofs/Encoding/WellFormedR.lean`), over each benchmark's guarded right
automaton `G` (the graph of its Theorem 3), the lowered right guards and `ε = epsR p` (the
file's `epsilon`, read as the tool reads it):

```lean
def WellFormedRModeIn G guard reg ε q : Prop :=
  ∀ m, G.modeAt q = some m → ∀ x, sat (guard q) x → sat m.dom x → sat reg x →
    (∃ Φ, ODESol m.sys m.dom x ε Φ) ∧                                   -- (i) nonblocking
    ∀ t Φ, t ≤ ε → ODESol m.sys m.dom x t Φ →
      ∃ e ∈ G.edgesFrom q, sat (guard e.tgt) (Φ t)                       -- (ii) successors
def WellFormedR G guard ε := ∀ q < G.modes.length, WellFormedRModeIn G guard ⊤ ε q
```

(the evolve-domain conjunct `m.dom x`: a run, even the empty one, exists only from a domain
state; `docs/WELLFORMED.md` §1).

**Results** (`InstancesV2/WellFormedBattery.lean`, declared counts `(47, 0, 3)`: every mode
outside the detumble family, refuted, the detumble family, checked against the suite's IR
table, `(30, 9, 6)` until the 2026-10-10 repairs; 66 axiom lines, each
`[propext, Classical.choice, Quot.sound]`; no Z3):

| result | count | benchmarks |
|---|---|---|
| proved, every mode (`<b>_wellFormedR`; for the two dRL benchmarks, `freedm_meter` and the batch I8 case studies `_wellFormedR_direct`, over the bridge's automaton) | **47** | the acc, ladder, terrain, rover patrol files, `quad_light_{lag,profiles}`, `gantry_speed_zones`, `tank_dos_3to1`, `watertank`, `watertank_twospeed`, `engine_start_highidle`, `train_ato_odometry`, `zone_lightmass_schedule` (batch I10, in place of `bms_chiller_undercharge`), `h2_refuel_ambientbias` and `reactor_feed_wireless` (batch I11, in place of `molding_pack_checkring` and `compressor_station_recycle`), `turbine_startup_gearratio`, `platoon_linkloss`, `platoon_profiles`, `platoon_latency` (one shared follower lemma, `PlatoonCaccAeb`; `platoon_latency` back in batch I11 in place of `antenna_track_kvretune`), the six files of batch I5 still in the suite (`fuelcell_chp_dos`, `elevator_start_discbrake`, `furnace_program_timebase`, `syringe_relay_prearm`, `hydro_rejection_gatecal`, `ventilator_vc_cuffleak`; `insulin_basal_cgmloss` is in the reserve since batch I9, `molding_pack_checkring` and `compressor_station_recycle` since batch I11), the two files of batch I6 still in the suite (`tunnel_jetfan_pairout`: the first polynomial right field, `u^2` and `u c`, proved with an explicit Riccati run, `bottling_fill_strainer`; `antenna_track_kvretune` is in the reserve since batch I11), the two files of batch I7 (`charger_fast_tapers`: its round-2 proof at the minute time scale, `ε_r = 0.006`; `grid_ffr_dos`: an explicit run and a non-strict barrier for the FFR release line) and the nine literature benchmarks (the five of batch I8 are direct proofs: `csf21_vehicle_thermo`, `csf21_vehicle_bus` and `lz_vehicle_position` with explicit polynomial runs and an exit into a coast mode, `girard_robot` with constant headings over the whole plane, `salt_tank_sensor` with a contraction kept by every run) |
| of which repaired 2026-10-10 (refuted until then, with the exhibited state) | 0 | (the nine repaired models are all out of the suite: `arm_plateau_{crit,profiles,slow}` and `platoon3_{linkloss,profiles}` in `benchmarks/reserve/`, `platoon_delay_{linkloss,profiles}` replaced by `platoon_linkloss` and `platoon_profiles` (the latter in `benchmarks/reserve/` since batch I8), `quad_light_{airframe_20,profiles}` redesigned without the limiter on 2026-10-27) |
| false | **0** | — |
| proved, every mode, with the conserved momentum band `|h_i + J_i w_i| ≤ 2` in the right evolve domain since 2026-10-15 (`<b>_wellFormedR`; the band is kept by every mode's flow, `<b>_band_invariant`; without it `DETUMBLE` from `w3 = 0.4`, `h = 2` had no full-interval run) | **3** | `sat_detumble_{weak,phases}`, `sat3w_detumble_phases` |

Proof styles: (a) forward invariance of the guard, then the self-loop; (b) exit into a
successor's guard within one interval; the satellites are style (a) with the momentum band in
the domain (the explicit solution keeps the conserved sums). The 18 terrain ladders share
one theorem (`wellFormedR_ladder`). Per-benchmark table, the repaired defects and their
states: `docs/WELLFORMED.md`; the repairs and their tool evidence: `docs/SUITE-REDESIGN.md`
§21. The trust base is unchanged: these are kernel theorems about the automata the parser
and the lowering produce, with no Z3 leaf.

**The tool check** (`relcert --wellformed <inputs>`, `Trusted/WellFormedCheck.lean`): a cheap
sufficient check of BOTH clauses per right mode. Clause (ii): the guard atoms are kept by
the mode's own flow (stratified cut routes) and the mode has a self-loop (`ok (invariant)`),
or every run of at most `ε_r` ends in a declared successor's guard (rate bounds on the atoms
that are not kept, then one coverage query: `ok (exit→S)`). Clause (i), on top (since
2026-10-26; until then it was not checked, and `vehicle_hypercert` with `s ≤ 8` in the right
evolve domain passed although its right model blocks at `s = 8`): from every guard state the
solution stays in the evolve domain for `ε_r` (each domain atom persists by an exact,
boundary, monotone, remainder or interval-margin route, or the domain polyhedron is kept face
by face) and cannot blow up (an affine field, or a bounded one on the domain). A mode is `ok`
only when both are shown; `BLOCKING (leaves d)` when some guard state leaves the domain at
once (clause (i) refuted); else `UNKNOWN` (`UNKNOWN (nonblocking)`: clause (ii) shown, clause
(i) not). The label of an `ok` mode is the clause (ii) style, matching the Lean proofs'
styles (a) / (b). On the suite: 184 right modes, 88 ok (invariant), 96 ok (exit), **0
UNKNOWN, 0 BLOCKING** (clause (ii) before the repairs: 77 / 53 / 16 UNKNOWN, exactly the
blocking modes of the nine models; on the old `platoon3` model, commit `1a3507f`, every mode
is `UNKNOWN`). On the 37 round-2 designs: 122 right modes, all `ok`. **Strict in the
recipe:** `--check-quick-v2` certifies in the strict mode and gates the `--wellformed` report
against declared counts (180 modes, 0 `UNKNOWN`, 0 `BLOCKING`, the runner's declared
constants `ExpectedSuiteV2.wfModes` / `wfUnknown` / `wfBlocking`): any mode not `ok` fails the
run. `RELCERT_WELLFORMED_STRICT=1` does the same per `relcert` run. The check is not part of
the guarantee: the guarantee's Assumption 1 is the kernel's `WellFormedR`, above.

## The 17 carried-over Assumption 1 proofs

Since 2026-10-27 (batch I3) none of these files is in the suite in its carried-over form: the
ladder rungs were reinstalled on the canonical rover hierarchy with new proofs, the terrain rungs
had been redesigned as the terrain chain, and the attitude, lateral and rollover files left the
suite (`benchmarks/README.md`, "Retired 2026-10-27"). The rest of this section is history.

Seventeen suite_v2 benchmarks (the rover refinement ladder, the rover terrain rungs, and the attitude, lateral and rollover benchmarks except `rover_rollover_7to12`) are copies of files of the retired legacy
suite `suite_uniform` (removed from the tree on 2026-10-10; git history keeps it), byte-identical
up to the name lines of the 2026-10-25 rename and the first header line of `rover_ladder_2to6`
(`benchmarks/README.md`), except `rover_lateral_6to8`, whose right model freezes the lateral
pair (`y' = 0`, `w' = 0`) since 2026-10-26, with its Assumption 1 proof adapted. Their
Assumption 1 proofs were first written against the legacy literals; they now live with the
others in `InstancesV2/WellFormed/<B>.lean` (moved from `Instances/WellFormed/` on
2026-10-22), each self-contained and quoting the suite_v2 literal `<b>_IRv2` directly, so the
bridge instances transport them like any other (`wellFormedR_transport`). Their standalone
Theorem 3 instances and the legacy verdict packs are archived (below). The terrain rungs are
no longer copies: on 2026-10-26 they were redesigned as the terrain chain (`rover_terrain_2to4`,
`rover_terrain_4to6`, `rover_terrain_6to12`; `benchmarks/README.md`), with new Assumption 1
proofs over `Proofs/Encoding/WellFormedTerrain.lean`.

## Archived routes

The standalone route (one hand-written Theorem 3 proof per benchmark over the unclocked
right automaton, `InstancesV2/Modal/`, the carried-over `Instances/*Guarded`, the
`BatteryV2` audit, the legacy packs `Verdicts/RunModal` and their pins, the choice exhibits'
standalone instances and `relcert-choice-verdicts`, the replay and ladder lemmas of
`Proofs/Encoding`, `SlimMain`, the generator `scripts/gen_multif_*.py`, `docs/VERDICTS.md`,
`docs/REPLAY.md` and `docs/history/`) was removed from `main` on 2026-10-22 (134 Lean modules,
82,213 lines). The pre-cleanup tree is branch `archive/legacy-2026-10` (its `lake build` is the
full earlier artifact); what was kept and why: `docs/CLEANUP-SCOPE.md` and `docs/CLEANUP-VERIFY.md`
(planning record, last present at commit 29663d8).
The per-benchmark findings of that route stay in `docs/GUARDED-SWITCHING.md`.

## Further reading

* [`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md): the check recipe, what each
  check establishes, the cost, the last recorded run.
* [`docs/PAPER-MAPPING.md`](docs/PAPER-MAPPING.md): **start here with the paper open**: every
  definition, theorem and assumption of the paper, its Lean name, file, how its hypotheses are
  discharged, and the axioms; its vocabulary table maps the paper's terms (mode fact,
  reposition certificate, landing set, committed subset, operating region, witness strategy,
  stretch) to the tool's names (checked cut, progress certificate, retained successors or
  chosen set, choice, `regionG`, cover, `lam`).
* [`docs/GUARDED-SWITCHING.md`](docs/GUARDED-SWITCHING.md): the guarded automata (left and
  right), the mode-consistent region, the per-benchmark responses, the history.
* [`docs/WELLFORMED.md`](docs/WELLFORMED.md): Assumption 1 per benchmark (`WellFormedR`),
  the repaired defects, the tool check and its strict use in the recipe.
* [`docs/HANDOFF.md`](docs/HANDOFF.md): mode-dependent invariants and the handoff check.
* [`docs/REFUTATION-RESULTS.md`](docs/REFUTATION-RESULTS.md): the 67 kernel refutations of
  known-false invariant variants (its design was `docs/REFUTATION-SCOPE.md`, planning record, last present at commit 29663d8).
* [`docs/BRIDGE.md`](docs/BRIDGE.md): the generic bridge, Theorem 3 of every benchmark from
  its emitted records; [`docs/THEOREM3-GENERAL.md`](docs/THEOREM3-GENERAL.md): the general
  theorem with existential mode choice and reposition progress;
  [`docs/CHOICE-SOUNDNESS.md`](docs/CHOICE-SOUNDNESS.md): the choice argument.
* [`docs/SUITE-REDESIGN.md`](docs/SUITE-REDESIGN.md): the design record of suite_v2 and its
  mechanism matrix.
* [`benchmarks/README.md`](benchmarks/README.md): the input format and the suite.
* [`RelCertifier/Trusted/README.md`](RelCertifier/Trusted/README.md): the trusted surface,
  file by file.
* The 2026-10-22 cleanup archived the standalone route to branch `archive/legacy-2026-10`,
  where the superseded records live (see "Archived routes" above).
* `STATUS.md`: the current status in one page.
