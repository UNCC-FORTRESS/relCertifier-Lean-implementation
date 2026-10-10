# relCertifier-lean

A mechanized relational certifier for hybrid-system refinement, in Lean 4, and the
artifact that accompanies the paper.

Given two hybrid automata, an ideal system `L` and an implementation `R`, written in a
small textual format, the tool `relcert` certifies that `R` refines `L` up to a relational
invariant (bounds such as `x_L ≤ x_R + 3`). For each benchmark of the paper's suite the
repository contains a **kernel-checked Theorem 3** (the paper's relational ∀∃ statement)
whose only assumptions are a small trust base and a finite list of named Z3 `unsat`
verdicts, each of which the tool re-sends on demand.

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
* [The 19 carried-over theorems](#the-19-carried-over-theorems)
* [Further reading](#further-reading)

## What the artifact certifies

`benchmarks/suite_v2/` holds the paper's suite: **45 benchmarks** (adaptive cruise control,
quadrotor climb, battery charger, robot-arm plateau, vehicle platoons, satellite
detumbling, rover patrol, and the rover refinement ladders and story benchmarks up to 12
degrees of freedom; `benchmarks/README.md`). With the widened cut channel on
(`RELCERT_IMPLIED_CUT=1`) the tool CERTIFIES all 45; without it, 12 of them DECLINE.

The parts of the artifact:

| part | where |
|---|---|
| the suite | `benchmarks/suite_v2/<name>/input.txt` |
| the tool (certifier, verdict runner, emitters) | `relcert` (`Main.lean`, `RelCertifier/Trusted/`) |
| the trusted-layer tests | `relcert-test` (`Test.lean`) |
| the generic soundness development | `RelCertifier/Core/`, `Checker/`, `Proofs/`, `Trusted/` |
| the suite_v2 battery: one Theorem 3 per benchmark, axiom-audited on every build | `RelCertifier/InstancesV2/BatteryV2.lean` |
| the runner tables and the pins tying every hypothesis to the query the runner sends | `RelCertifier/VerdictsV2/` (and `Verdicts/` for the carried-over theorems) |
| the suite evaluation scripts | `scripts/suite_v2_matrix.py` (mechanism matrix), `scripts/domain_widening.py` (load-bearing domain bounds) |

## The headline claim

For each of the 45 suite_v2 benchmarks there is a Lean theorem

```lean
RFormula.rvalid (theorem3Form  L_program            -- the left system: its window family,
                               (rightAutomatonBody Gr mv)  -- the right mode automaton
                               Φ)                    -- the loop invariant
```

with `theorem3Form L R Φ = Φ → [|(L*, R*)⟩⟩ Φ`: from every state satisfying `Φ`, whatever
the left system does, the right system can respond so that `Φ` holds again, through every
round. `Φ` is the declared relational invariant (for mode-dependent rows, the mode-keyed
conjunction `⋀_m (u_L = m → φ_inv(m))`), the joint evolve domains, and the right mode
bookkeeping (for the 26 new instances: the right mode's kept cut atoms as its region,
pruned sink modes excluded).
The theorem's hypotheses are named Z3 verdict packs, and every one of them is re-sent by
`relcert --run-verdicts-v2` and comes back `unsat` (921 queries in four phases, against
declared counts; `docs/VERDICTS.md`). The axiom audit of every theorem is a subset of
`{propext, Classical.choice, Quot.sound, z3_unsat_sound}`; five theorems are Z3-free. No
`sorry`, no `admit`, no `native_decide`.

## Trust base

| item | why it cannot be removed |
|---|---|
| the **parser** (`Trusted/Parse.lean`, strict; unknown keys refused by `Trusted/KeyAudit.lean`) reads the benchmark file correctly | the file is the specification |
| the **lowering** (`Trusted/Run.lean`) means what it says | it fixes how the parsed model becomes formulas |
| the **printer** (`toScript`) renders formulas to SMT-LIB faithfully | Z3 reads text |
| **Z3's `unsat`** answers are correct | the one oracle: axiom `z3_unsat_sound` (`Trusted/Oracle.lean`) |
| the **Lean kernel** | checks everything else |
| **the model's transition semantics**: every right mode change enters a declared successor, and at that instant the successor's guard holds (successor-completeness with guard-gated switching); right flows inside the invariant are not blocked for a window's duration (the paper's Assumption 1, nonblocking) | facts about the modeled system, not about formulas |

The search (cover exploration, checked-cut search, route and λ selection) is untrusted: it
only proposes. Every accepted output is either re-decided in the kernel (the cover replay
`decideCovered`, the cut certificates' well-formedness) or becomes a named Z3 fact.

The certifier uses exactly two step kinds for the right system: **joint segments** (both
systems flow, the right time-stretched by λ) and the **dynamic right-only reposition** (the
right flows under its own field while the left is held: the paper's right-only segment).
There is no zero-duration right switch. The Lean right automaton carries `⊤` edge guards;
that abstraction is justified for these two step kinds under Assumption 1
(`docs/PAPER-MAPPING.md`, "The right automaton's ⊤ edge guards").

## Theorem families

All counts read off `InstancesV2/BatteryV2.lean` and its build output.

| family | count | which |
|---|---|---|
| Theorem 3, one per benchmark | **45** | 26 new instances (`InstancesV2/Modal/`); 19 carried over from the retired legacy suite ([below](#the-19-carried-over-theorems)) |
| mode-keyed (per-left-mode rows composed through handoffs, `ModeHandoff.theorem3_modeKeyed`) | **12** | `acc_spoof_limp`, `acc_tune_limp`, `platoon_delay_linkloss`, `platoon3_linkloss`, `rover_patrol_zones`, `rover_patrol_refine`, `sat_detumble_phases`, `sat3w_detumble_phases`, `story3_rollover_ladder_rung_b`; carried over: `rover3tier_rung12`, `story1_attdist_rung_a_6to8`, `story1_attdist_rung_b_12dof` |
| widened cut channel needed (`RELCERT_IMPLIED_CUT=1`; closures, implied contractions, linear-form chains; lifted to the kernel by `Proofs/Soundness/CutLiftX.lean`) | **12** | `acc_spoof_lag`, `arm_plateau_{crit,profiles,slow}`, `charger_fast_setpoints`, `platoon3_{linkloss,profiles}`, `platoon_delay_{linkloss,profiles}`, `rover_patrol_refine`, `story3_rollover_ladder_rung_b`, `watertank` (each DECLINES without the channel) |
| Z3-free (the three standard axioms only, no verdict hypothesis) | **5** | `arm_plateau_{crit,profiles,slow}`, `refinement_ladder_rover_rung2_6dof`, `refinement_ladder_rover_rung2b_6dof` |
| stated on the nonblocking region (a conserved-momentum band of the model in the right region; it enters no verdict query) | **6** | `sat_detumble_{nominal,weak,phases}`, `sat3w_detumble_{nominal,weak,phases}` (`docs/SUITE-REDESIGN.md` §19.2) |
| Theorem 2 (non-connection certificate of a pruned edge) | **1** | `match_multi_rate_nonconn`, the edge `DRIVE → STALL` |

The axiom audit has 51 lines: 46 benchmark theorems (45 Theorem 3 plus
`match_multi_rate_nonconn`) and 5 generic lemmas of the widened channel; 42 carry
`z3_unsat_sound`, 9 are at the three standard axioms alone (the 5 Z3-free benchmarks and
4 of the generic lemmas).

## Build and check

Requirements: the Lean toolchain of `lean-toolchain` (elan fetches it; the one Lean
dependency, dL-rel, is pinned by tag in `lakefile.toml`) and Z3 (the tool looks for
`/opt/homebrew/bin/z3`, `/usr/local/bin/z3`, `/usr/bin/z3`, or `RELCERT_Z3`).

```bash
# 1. kernel-check everything (see the note on heavy files below)
lake build
lake build relcert relcert-test

# 2. the axiom audit of the battery (51 lines)
lake build RelCertifier.InstancesV2.BatteryV2 2>&1 | grep -A3 "depends on axioms"

# 3. certify the 45 files and re-send every Z3 hypothesis, with declared counts
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt

# 4. the trusted-layer tests (IR drift of all 45 literals, parser, printer, Z3 layer,
#    determinism); the manifest lets the two determinism checks run
for d in benchmarks/suite_v2/*/; do
  printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"
done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test
```

Expected: `Build completed successfully`; 51 axiom lines, each a subset of the four axioms
above; `[suite_v2] 45 certified, 0 declined, 0 error(s)`, coverage `modal 262/262`,
`handoff 186/186`, `non-connection 88/88`, `pruned edges 44/44`, `copied benchmarks (legacy
packs) 385/385`, `SUITE_V2 QUICK CHECKS PASSED`; `relcert-test`: a bare `ALL PASS`.

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
    Encoding/   40 files   the ∀∃ chain: CSF/NFM'25 bridge, joint segments, dynamic
                           reposition prefixes, envelope and window chains, mode handoffs,
                           sink regions, the non-connection bridge
    Flow/       14 files   DI routes, Picard existence, viability faces
    Soundness/   7 files   the cut lift (CutLift; CutLiftX for the widened channel)
    Transfer/    5 files   scaled-model transfer (retired Faithful route)
  Trusted/      13 files   parser, key audit, lowering, printer, Z3 session, the certifier
                           (OracleAPI), handoff and non-connection queries, emitters
  InstancesV2/  the suite_v2 battery
    BenchIR/ BenchCovers/ Cuts/   45 files each   emitted data, one leaf per benchmark
    Modal/      26 files   the new Theorem 3 instances
    SameIR.lean, CoverReplay.lean, BatteryV2.lean
  VerdictsV2/    5 files   runner (RunV2), pins (PinsV2, NonConnPinV2), query rebuild
                           (ModalX), declared counts derived from the tables (CoveragePinsV2)
  Instances/    27 files   the 19 carried-over theorems and their dependencies, their 20
                           IR leaves, ModalSpecs, AxiomCheck (generic axiom audit)
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
| `RELCERT_Z3=<path>` | the Z3 binary |
| `RELCERT_Z3_TIMEOUT=<ms>` | per-query timeout, default 10000 |
| `RELCERT_Z3_RLIMIT=<n>` | per-query deterministic resource limit, default 64000000 |
| `RELCERT_MAX_QUERIES=<n>` | per-benchmark query budget, default 20000 |
| `RELCERT_TIME_BUDGET_MS=<ms>` | per-benchmark wall-clock budget, default 40000 |

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
(`VerdictsV2/NonConnPinV2.lean`). These proofs predate the 2026-10-09 removal of the static
reposition from the certifier, and 19 of the 24 legacy instance modules build their window
responses with zero-duration right hops along the `⊤`-guarded edges (`static_hop_existsR` or
a local `static_hop*` lemma), as do 10 of the 26 new instances. Whether each such switch
happens where the successor's guard holds is not checked by the kernel; this is an open
point about those witnesses, discussed in `docs/PAPER-MAPPING.md` §2e.

## Further reading

* [`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md): the check recipe, what each
  check establishes, the cost, the last recorded run.
* [`docs/PAPER-MAPPING.md`](docs/PAPER-MAPPING.md): paper ↔ mechanization, element by element.
* [`docs/VERDICTS.md`](docs/VERDICTS.md): the verdict runner, its phases, counts and pins.
* [`docs/HANDOFF.md`](docs/HANDOFF.md): mode-dependent invariants and the handoff check.
* [`docs/SUITE-REDESIGN.md`](docs/SUITE-REDESIGN.md): the design record of suite_v2 and its
  mechanism matrix.
* [`benchmarks/README.md`](benchmarks/README.md): the input format and the suite.
* [`RelCertifier/Trusted/README.md`](RelCertifier/Trusted/README.md): the trusted surface,
  file by file.
* [`docs/history/`](docs/history/README.md): superseded records, indexed.
* `STATUS.md`: the current status in one page.
