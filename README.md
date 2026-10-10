# relCertifier-lean

A mechanized relational certifier for hybrid-system refinement, in Lean 4, and the
artifact that accompanies the paper.

Given two hybrid automata, an ideal system `L` and an implementation `R`, written in a
small textual format, the tool `relcert` certifies that `R` refines `L` up to a relational
invariant (bounds such as `x_L ≤ x_R + 3`). For **all 45** benchmarks of the paper's suite
the repository contains a **kernel-checked Theorem 3** (the paper's relational ∀∃ statement)
with the paper's own automata on both sides, **guard-gated**: every left window is entered
only inside its mode's guard (the left automaton, jump then flow) and every right mode change
enters a declared successor whose guard holds at that instant (flow then jump), at the
**mode-consistent region** (the right in the guard of its current mode and its checked cuts),
whose only assumptions are a small trust base and a finite list of named Z3 `unsat` verdicts,
each of which the tool re-sends on demand (16 of the 45 take none). 44 hold for every window
length; `refinement_ladder_rover_rung2c_6dof` for every window up to its control interval
(`dt ≤ ε_L = 1`). The mechanization also found a modelling defect: in the two `platoon3`
benchmarks the nominal controller blocked after a full cycle (engagement-band guards, no
catch-all mode), a violation of the certificate's Assumption 1 that the certificate itself
cannot detect; the guards are now the operating range and both are proved
(`docs/SUITE-REDESIGN.md` §20). Assumption 1 itself is now a separately verified model fact
per benchmark (`WellFormedR`): **proved for all 45 right models**, 39 in its literal form and
the 6 satellites on their conserved momentum band. Nine models violated it until 2026-10-10
(refuted in the kernel with exhibited blocking states: fallback sinks whose own flow left
their guard, approach bands narrower than one control interval) and were repaired
(`docs/SUITE-REDESIGN.md` §21). The tool checks its successor half (`relcert --wellformed`),
STRICT in the certification recipe: `--check-quick-v2` fails on any `UNKNOWN` right mode. See
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
* [The 19 carried-over theorems](#the-19-carried-over-theorems)
* [Further reading](#further-reading)

## What the artifact certifies

`benchmarks/suite_v2/` holds the paper's suite: **45 benchmarks** (adaptive cruise control,
quadrotor climb, battery charger, robot-arm plateau, vehicle platoons, satellite
detumbling, rover patrol, and the rover refinement ladders and story benchmarks up to 12
degrees of freedom; `benchmarks/README.md`). With the widened cut channel on
(`RELCERT_IMPLIED_CUT=1`) the tool CERTIFIES all 45; without it, 10 of them DECLINE.

The parts of the artifact:

| part | where |
|---|---|
| the suite | `benchmarks/suite_v2/<name>/input.txt` |
| the tool (certifier, verdict runner, emitters) | `relcert` (`Main.lean`, `RelCertifier/Trusted/`) |
| the trusted-layer tests | `relcert-test` (`Test.lean`) |
| the generic soundness development | `RelCertifier/Core/`, `Checker/`, `Proofs/`, `Trusted/` |
| the suite_v2 battery: Theorem 3 with the guard-gated left and right automata for all 45 benchmarks (`rung2c` for `dt ≤ 1`), axiom-audited on every build | `RelCertifier/InstancesV2/BatteryV2.lean` |
| the runner tables and the pins tying every hypothesis to the query the runner sends | `RelCertifier/VerdictsV2/` (and `Verdicts/` for the carried-over theorems) |
| Assumption 1 of every right model (`WellFormedR`), axiom-audited on every build | `RelCertifier/InstancesV2/WellFormedBattery.lean` (`docs/WELLFORMED.md`) |
| the suite evaluation scripts | `scripts/suite_v2_matrix.py` (mechanism matrix), `scripts/domain_widening.py` (load-bearing domain bounds) |

## The headline claim

For each of the 45 suite_v2 benchmarks there is a Lean theorem

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
The theorem's hypotheses are named Z3 verdict packs, and every one of them is re-sent by
`relcert --run-verdicts-v2` and comes back `unsat` (921 queries in four phases, against
declared counts; `docs/VERDICTS.md`). The axiom audit of every theorem is a subset of
`{propext, Classical.choice, Quot.sound, z3_unsat_sound}`; 16 of the 45 are Z3-free. No
`sorry`, no `admit`, no `native_decide`.

`refinement_ladder_rover_rung2c_6dof` carries the statement for windows `0 ≤ dt ≤ ε_L = 1`
(its control interval; false for `dt > 2.12` by a stated argument). See
[Guard-gated switching](#guard-gated-switching).

## Trust base

| item | why it cannot be removed |
|---|---|
| the **parser** (`Trusted/Parse.lean`, strict; unknown keys refused by `Trusted/KeyAudit.lean`) reads the benchmark file correctly | the file is the specification |
| the **lowering** (`Trusted/Run.lean`) means what it says | it fixes how the parsed model becomes formulas |
| the **printer** (`toScript`) renders formulas to SMT-LIB faithfully | Z3 reads text |
| **Z3's `unsat`** answers are correct | the one oracle: axiom `z3_unsat_sound` (`Trusted/Oracle.lean`) |
| the **Lean kernel** | checks everything else |
| the **lowering of the right guards** onto the edges (`hostGuard … Side.R (mR t)`, the same lowering as the left guards) | part of the lowering item above; each instance proves its edges carry exactly these guards (`Gr_guards`) |
| (not an item) Assumption 1 of the right model | not assumed: stated as `WellFormedR` and proved for all 45 (39 literally, the 6 satellites on their momentum band), all Z3-free, kernel-only (no trust-base item beyond the parser and lowering that produce the automata); no Theorem 3 uses it (`docs/WELLFORMED.md`) |

The search (cover exploration, checked-cut search, route and λ selection) is untrusted: it
only proposes. Every accepted output is either re-decided in the kernel (the cover replay
`decideCovered`, the cut certificates' well-formedness) or becomes a named Z3 fact.

Guard-gated switching is no longer a trusted item: for all 45 theorems both automata test
each entered mode's guard in the program, and every switch of each response
is kernel-checked legal (`Proofs/Encoding/GuardedSwitch.lean`: `SwitchLegal`, `gseg`,
`guarded_rights_bridge`, `GResp`). The region of the loop invariant is `guard ∧ cuts` of the
right's current mode (`regionG`), the same shape for all 45 benchmarks; it is a property of
the statement, not an assumption: the theorem's premise and conclusion both carry it.
Nonblocking (the paper's Assumption 1) enters no theorem as a hypothesis: every response
exhibits its switches and their enabled targets explicitly, or makes no step. Assumption 1
itself is a separately verified model fact (`WellFormedR`, [below](#assumption-1-is-verified-per-benchmark));
the tool's `--wellformed` check of it is untrusted and only ever declines: strict in
`--check-quick-v2` (an `UNKNOWN` right mode fails the recipe), informational as
`relcert --wellformed`, and per run under `RELCERT_WELLFORMED_STRICT=1`.

The search (cover exploration, checked-cut search, route and λ selection) is untrusted: it
only proposes. Every accepted output is either re-decided in the kernel (the cover replay
`decideCovered`, the cut certificates' well-formedness) or becomes a named Z3 fact.

## Theorem families

All counts read off `InstancesV2/BatteryV2.lean` and its build output.

| family | count | which |
|---|---|---|
| Theorem 3 with the guard-gated left and right automata at the mode-consistent region, every window length | **44** | all except `rung2c` |
| the same, windows up to the control interval `dt ≤ ε_L = 1` | **1** | `refinement_ladder_rover_rung2c_6dof` (`Instances/RoverRung2cGuarded`, `Instances/LeftAutLegacy`) |
| mode-independent rows, carried to the left automaton by the generic bridge `theorem3_leftAut_of_choice` | **33** | 16 suite_v2 (`InstancesV2/LeftAutV2.lean`), 13 carried-over (`Instances/LeftAutLegacy.lean`), `rung2_3to6` and the two story2 ladders (`Instances/*Guarded.lean`), `platoon3_profiles` |
| mode-keyed (per-left-mode rows composed through handoffs, `ModeHandoff.theorem3_modeKeyed`) | **12** | `acc_spoof_limp`, `acc_tune_limp`, `platoon_delay_linkloss`, `platoon3_linkloss`, `sat_detumble_phases`, `sat3w_detumble_phases`, `rover3tier_rung12`, `rover_patrol_zones`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof` |
| model repaired by this mechanization (the nominal controller blocked after a full cycle; `docs/SUITE-REDESIGN.md` §20) | **2** | `platoon3_linkloss`, `platoon3_profiles` |
| model repaired for Assumption 1 (`WellFormedR` refuted in the kernel, then proved; `docs/SUITE-REDESIGN.md` §21) | **9** | `arm_plateau_{crit,profiles,slow}`, `platoon_delay_{linkloss,profiles}`, `platoon3_{linkloss,profiles}`, `quad_light_{airframe_20,profiles}` |
| widened cut channel needed (`RELCERT_IMPLIED_CUT=1`; closures, implied contractions, linear-form chains; lifted to the kernel by `Proofs/Soundness/CutLiftX.lean`) | **10** | `acc_spoof_lag`, `arm_plateau_{crit,profiles,slow}`, `charger_fast_setpoints`, `platoon_delay_{linkloss,profiles}`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b`, `watertank` (each DECLINES without the channel) |
| Z3-free (the three standard axioms only, no verdict hypothesis) | **16** | `arm_plateau_{crit,profiles,slow}`, `rover3tier_rung12`, `match_multi_rate`, `rover_patrol_{zones,refine}`, `refinement_ladder_rover_rung{1_2to3,3_6to8,4_8to12,2_6dof,2b_6dof}`, `rover_dof_terrain_rung{1,2,3,3_8d}` (explicit responses: catch-ups and climbs) |
| stated on the nonblocking region (a conserved-momentum band of the model in the right region; it enters no verdict query) | **6** | `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}` (`docs/SUITE-REDESIGN.md` §19.2) |
| Theorem 2 (non-connection certificate of a pruned edge) | **1** | `match_multi_rate_nonconn`, the edge `DRIVE → STALL` |

The axiom audit has 71 lines: the 45 Theorem 3s, `match_multi_rate_nonconn`, and 25 generic
lemmas; 31 carry `z3_unsat_sound`, 40 are at the three standard axioms alone.

## Build and check

Requirements: the Lean toolchain of `lean-toolchain` (elan fetches it; the one Lean
dependency, dL-rel, is pinned by tag in `lakefile.toml`) and Z3 (the tool looks for
`/opt/homebrew/bin/z3`, `/usr/local/bin/z3`, `/usr/bin/z3`, or `RELCERT_Z3`).

```bash
# 1. kernel-check everything (see the note on heavy files below)
lake build
lake build relcert relcert-test

# 2. the axiom audit of the battery (71 lines)
lake build RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"

# 2b. the Assumption 1 battery (76 lines, the three standard axioms only)
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"

# 3. certify the 45 files (strict well-formedness), re-send every Z3 hypothesis, and run the
#    strict Assumption 1 gate, all with declared counts
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt

# 4. the trusted-layer tests (IR drift of all 45 literals, parser, printer, Z3 layer,
#    determinism); the manifest lets the two determinism checks run
for d in benchmarks/suite_v2/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"
done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test
```

Expected: `Build completed successfully`; 71 axiom lines (BatteryV2), each a subset of the
four axioms above; 76 axiom lines (WellFormedBattery), each exactly the three standard
axioms; `[suite_v2] 45 certified, 0 declined, 0 error(s)`, coverage `modal 262/262`,
`handoff 186/186`, `non-connection 88/88`, `pruned edges 44/44`, `copied benchmarks (legacy
packs) 385/385`, the strict Assumption 1 gate `[wellformed] STRICT: 146/146 right modes ok
(83 invariant, 63 exit), 0 UNKNOWN — matches the declared suite`, `wellformed (strict): PASS`,
`SUITE_V2 QUICK CHECKS PASSED`;
`relcert-test`: a bare `ALL PASS`.

**Heavy files.** A handful of instance files (the 12-dimensional rover and rollover
instances among the carried-over theorems, the larger suite_v2 instances) dominate the
build in time and memory. Building them in parallel can exhaust memory;
build them one at a time first (`lake build RelCertifier.Instances.<Name>`,
`lake build RelCertifier.InstancesV2.Modal.<Name>`), then run `lake build` for the rest.
`lake build` is incremental, but an edit to anything under `Proofs/`, `Checker/` or
`Trusted/` rebuilds every instance downstream. The full recipe, what each check
establishes and what it does not, and the measured cost: `docs/CERTIFICATION-CHECK.md`.

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
a cover (λ, budgets, flags, admissible starts, strata orders, pruned edges)
and a checked-cut certificate
  ├─(--emit-cover)─▶ InstancesV2/BenchCovers/<b>.lean
  │                   ▲ CoverReplay.lean: decideCovered accepts, by `decide`
  └─(--emit-cuts)──▶ InstancesV2/Cuts/<b>.lean
                      ▲ evolStrengtheningWFX … = true, by `rfl`
  ▼
InstancesV2/Modal/<B>.lean                         the Theorem 3 instance, composed from
  │                                                 Proofs/Encoding (the ∀∃ chain) and
  │                                                 Proofs/Soundness/CutLiftX (the cut lift)
  ▼
rvalid (theorem3Form …) under named `Verd l m` packs
  │ VerdictsV2/PinsV2.lean: each `Verd` IS a row of RunV2.packsV2  (kernel)
  │ VerdictsV2/ModalX.lean: the rebuilt queries denote the hypothesis (kernel)
  ▼
relcert --run-verdicts-v2: rebuilds each query, prints it with toScript, Z3 says `unsat`
```

`scripts/gen_v2_data.py` regenerates the three data leaves of every benchmark (IR literal,
cover, cut certificates) and the aggregators from the tool's emitters.

## Repository layout

```
RelCertifier/
  Core/          3 files   flow certificates (DI routes A/B/C), rational reification
  Checker/      12 files   verified cover checker (decideCovered, cover_sound, check_sound),
                           emitted-cover types, checked-cut certificates (EvolStrengthening,
                           EvolStrengtheningX), non-connection (Theorem 2); the settling
                           and Faithful checkers of a retired route
  Proofs/
    Encoding/   49 files   the ∀∃ chain: CSF/NFM'25 bridge, joint segments, dynamic
                           reposition prefixes, envelope and window chains, mode handoffs,
                           sink regions, the non-connection bridge, Assumption 1
                           (WellFormedR, WellFormedLadder)
    Flow/       14 files   DI routes, Picard existence, viability faces
    Soundness/   7 files   the cut lift (CutLift; CutLiftX for the widened channel)
    Transfer/    5 files   scaled-model transfer (retired Faithful route)
  Trusted/      14 files   parser, key audit, lowering, printer, Z3 session, the certifier
                           (OracleAPI), handoff and non-connection queries, emitters,
                           the Assumption 1 check (WellFormedCheck)
  InstancesV2/  the suite_v2 battery
    BenchIR/ BenchCovers/ Cuts/   45 files each   emitted data, one leaf per benchmark
    Modal/      26 files   the new Theorem 3 instances
    WellFormed/ 27 files   Assumption 1 (`WellFormedR`) per suite_v2 instance (26) and the
                           shared platoon link lemmas (operating range, latched AEB sink);
                           `Instances/WellFormed/` holds the 19
                           carried-over benchmarks
    SameIR.lean, CoverReplay.lean, BatteryV2.lean, WellFormedBattery.lean
  VerdictsV2/    5 files   runner (RunV2), pins (PinsV2, NonConnPinV2), query rebuild
                           (ModalX), declared counts derived from the tables (CoveragePinsV2)
  Instances/    27 files   the 19 carried-over theorems and their dependencies, their 20
                           IR leaves, ModalSpecs, AxiomCheck (generic axiom audit);
                           WellFormed/ (19 files): their Assumption 1
  Verdicts/     11 files   the carried-over packs: runner (RunModal), pins, shared pin lemmas
Main.lean                  relcert
Test.lean                  relcert-test
benchmarks/suite_v2/       the 45 inputs
scripts/                   gen_v2_data.py, suite_v2_matrix.py, domain_widening.py,
                           z3_timing_proxy.py, trust_audit.py, gen_multif_*.py
docs/                      see Further reading; docs/history/ holds superseded records
```

`RelCertifier.lean` imports everything; `lake build` builds that closure.

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
| `RELCERT_WELLFORMED_STRICT=1` | run the `--wellformed` check on every CERTIFIED benchmark and DECLINE it when a right mode is `UNKNOWN` (off by default for a single run, no verdict and no emission changes; `--check-quick-v2` forces it on; on the repaired suite no benchmark declines, before the 2026-10-10 repairs 9 did) |
| `RELCERT_Z3=<path>` | the Z3 binary |
| `RELCERT_Z3_TIMEOUT=<ms>` | per-query timeout, default 10000 |
| `RELCERT_Z3_RLIMIT=<n>` | per-query deterministic resource limit, default 64000000 |
| `RELCERT_MAX_QUERIES=<n>` | per-benchmark query budget, default 20000 |
| `RELCERT_TIME_BUDGET_MS=<ms>` | per-benchmark wall-clock budget, default 40000 |

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
bridge, `theorem3_leftAut_of_choice`). With them all 45 are proved, mostly by explicit
responses that switch at band floors (ladder climbs, synchronized climbs inside the window, a
decay budget for attitude rows: `GuardedClimb`, `LadderClimb`, `SyncSwitch`, `LadderSync`).
Two findings: three ladders (`rung2_3to6`, the story2 pair) are false with a left window that
has no guard test but true with the paper's left program (the band order the left guard
gives makes every stretch a certified pair); and the two `platoon3` benchmarks were refuted in
the kernel because their nominal controller BLOCKED after a full cycle (engagement-band stay
guards, no catch-all mode: Assumption 1 violated by the model, undetectable by the
certificate), and are repaired. Record, per-benchmark switch classification, the exact states
and the final table: `docs/GUARDED-SWITCHING.md`.

## Assumption 1 is verified per benchmark

The paper's Assumption 1 (Well-Formedness): *the right model is nonblocking and complete with
respect to its declared successor relation: from every state satisfying a source-mode guard,
an evolution spanning the control interval `ε_r` exists, and every evolution of duration at
most `ε_r`, including the empty one, ends in a state satisfying the guard of at least one
declared successor mode.* No Theorem 3 assumes it; it is now a separately audited model fact.

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

**Results** (`InstancesV2/WellFormedBattery.lean`, declared counts `(39, 0, 6)` checked
against the suite's IR table, `(30, 9, 6)` until the 2026-10-10 repairs; 76 axiom lines, each
`[propext, Classical.choice, Quot.sound]`; no Z3):

| result | count | benchmarks |
|---|---|---|
| proved, every mode (`<b>_wellFormedR`) | **39** | the acc, charger, ladder, terrain, story, rover patrol files, `quad_light_lag`, `match_multi_rate`, `rover3tier_rung12`, `watertank`, and the nine repaired models below |
| of which repaired 2026-10-10 (refuted until then, with the exhibited state) | 9 | `arm_plateau_{crit,profiles,slow}` (ApproachA from `θ = 0.35` reached `0.85` within one interval, past ApproachB's band: the sampled planner's successor sets now name every reachable band), `platoon_delay_{linkloss,profiles}` (sink BRAKE left `g < 20`: it now re-engages FOLLOW), `platoon3_{linkloss,profiles}` (sink BRAKE1 left `g₁ < 20`: the AEB sinks are now latched, speed matching with an invariant guard), `quad_light_{airframe_20,profiles}` (sink LIMIT decayed below its guard: it now hands back to the climb controller, whose operating range reaches the limiter threshold) |
| false | **0** | — |
| proved on the conserved momentum band, which every mode keeps (`<b>_wellFormedR_onBand`, `<b>_band_invariant`); the literal predicate refuted (`DETUMBLE` from `w3 = 0.4`, `h = 2` has no full-interval run) | **6** | `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}` |

Proof styles: (a) forward invariance of the guard, then the self-loop; (b) exit into a
successor's guard within one interval; (c) on the momentum band. The 18 terrain ladders share
one theorem (`wellFormedR_ladder`). Per-benchmark table, the repaired defects and their
states: `docs/WELLFORMED.md`; the repairs and their tool evidence: `docs/SUITE-REDESIGN.md`
§21. The trust base is unchanged: these are kernel theorems about the automata the parser
and the lowering produce, with no Z3 leaf.

**The tool check** (`relcert --wellformed <inputs>`, `Trusted/WellFormedCheck.lean`): a cheap
sufficient check of clause (ii) per right mode: the guard atoms are kept by the mode's own
flow (stratified cut routes) and the mode has a self-loop (`ok (invariant)`), or every run of
at most `ε_r` ends in a declared successor's guard (rate bounds on the atoms that are not
kept, then one coverage query: `ok (exit→S)`), else `UNKNOWN`. On the suite: 146 right
modes, 83 ok (invariant), 63 ok (exit), **0 UNKNOWN** (before the repairs: 77 / 53 / 16
UNKNOWN, exactly the blocking modes of the nine models; on the old `platoon3` model, commit
`1a3507f`, every mode is `UNKNOWN`). **Strict in the recipe:** `--check-quick-v2` certifies in
the strict mode and gates the `--wellformed` report against declared counts (146 modes, 0
`UNKNOWN`; the mode count is kernel-checked against the IR table): any `UNKNOWN` fails the
run. `RELCERT_WELLFORMED_STRICT=1` does the same per `relcert` run.

## The 19 carried-over theorems

Nineteen suite_v2 benchmarks (the rover refinement ladder, the rover terrain rungs,
`rover3tier_rung12`, `match_multi_rate`, and the story1, story2 and story3 benchmarks except `story3_rollover_ladder_rung_b`) are byte-identical copies of files of the retired legacy
suite `suite_uniform` (removed from the tree on 2026-10-10; git history keeps it). Their
Theorem 3 instances were proved against that suite (`RelCertifier/Instances/`), and
`InstancesV2/SameIR.lean` proves by `rfl` that each suite_v2 IR literal IS the literal those
theorems quote, so they are theorems about the suite_v2 files; `BatteryV2` re-exports them.
Their verdict packs are the 22 rows of `Verdicts/RunModal.modalTable` (pinned by
`Verdicts/ModalPinTable`, `ModalTablePins`, `ModalCodePins`), re-sent by the "copied
benchmarks" phase of `--run-verdicts-v2` (385 queries); the Theorem 2 hypothesis of
`match_multi_rate_nonconn` is pinned to the suite_v2 non-connection phase
(`VerdictsV2/NonConnPinV2.lean`). These proofs are over the `⊤`-guarded relaxation. All
nineteen are restated over the guarded automata at the mode-consistent region in new files
(`Instances/*Guarded.lean`, `Instances/LeftAutLegacy.lean`), `rung2c` for windows `dt ≤ 1`.

## Further reading

* [`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md): the check recipe, what each
  check establishes, the cost, the last recorded run.
* [`docs/PAPER-MAPPING.md`](docs/PAPER-MAPPING.md): paper ↔ mechanization, element by element.
* [`docs/GUARDED-SWITCHING.md`](docs/GUARDED-SWITCHING.md): the guarded automata (left and
  right), the mode-consistent region, the per-benchmark responses, the history.
* [`docs/WELLFORMED.md`](docs/WELLFORMED.md): Assumption 1 per benchmark (`WellFormedR`),
  the repaired defects, the tool check and its strict use in the recipe.
* [`docs/VERDICTS.md`](docs/VERDICTS.md): the verdict runner, its phases, counts and pins.
* [`docs/HANDOFF.md`](docs/HANDOFF.md): mode-dependent invariants and the handoff check.
* [`docs/SUITE-REDESIGN.md`](docs/SUITE-REDESIGN.md): the design record of suite_v2 and its
  mechanism matrix.
* [`benchmarks/README.md`](benchmarks/README.md): the input format and the suite.
* [`RelCertifier/Trusted/README.md`](RelCertifier/Trusted/README.md): the trusted surface,
  file by file.
* [`docs/history/`](docs/history/README.md): superseded records, indexed.
* `STATUS.md`: the current status in one page.
