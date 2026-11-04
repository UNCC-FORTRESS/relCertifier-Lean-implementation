# relCertifier-lean

`relcert` certifies forall-exists relational invariants between two hybrid systems, and every
benchmark it certifies comes with a kernel-checked Lean theorem. This repository is the tool,
its Lean development and the benchmark suite of the paper *Certifying Forall-Exists Invariants
for Cyber-Physical Systems via Witness Construction* (HSCC+ICCPS 2027 submission).

* [What the tool does](#what-the-tool-does)
* [What is proved](#what-is-proved)
* [Trust base](#trust-base)
* [Build](#build)
* [Run](#run)
* [Reproduce the paper](#reproduce-the-paper)
* [Repository layout](#repository-layout)
* [Further reading](#further-reading)

## What the tool does

A model file describes two hybrid systems over a common clocked cycle, a left system `L` and a
right system `R` (each mode with its dynamics, evolution domain, guard and declared successors;
the paper's Eq. 1), a candidate relational invariant `φ` (a conjunction of polynomial
inequalities, possibly one row per left mode) and a stretch range. The tool decides whether
`φ` is a forall-exists invariant: for every execution of the left system, the right system
has an execution that keeps `φ` (Definition 1). It answers `CERTIFIED`, `DECLINED` or `ERROR`;
only an `unsat` answer of Z3 ever certifies an obligation.

It certifies by constructing a **witness strategy** (Definition 4): for each left mode and each
admissible initial right mode, a finite tree of right **segments** that answers every left
cycle.

* A **joint segment** runs both systems, the right at a constant **stretch** `λ ≥ 0` relative
  to the left (Lemma 1, Time Stretching); stretch 0 means the witness stands still while the
  left runs. A **right-only segment** freezes the left while the right repositions.
* A **flow certificate** (Definition 5) proves that a segment keeps the invariant from its
  **entry states**, discharged per invariant component by Lie-derivative conditions (Lemma 2).
* A **non-connection certificate** (Definition 6) proves that a declared right mode change is
  never taken; **pruning** drops it, so the **retained successors** are the exits a segment can
  reach.
* A **reposition certificate** (Definition 7) proves that a right-only segment reaches its
  **landing set**: a **stage list** (one or two stages, each a variable, a threshold and a
  rate) drives the right across the last threshold into the **landing target**. Its flow
  certificate is checked on the **restricted mode** (the right mode outside the landing target).
* **Mode facts** (Definition 2) are per-mode formulas implied by the mode's guard and kept by
  its flow, found in a preprocessing phase and assumed by every obligation of the mode.
* The **cover** (Definition 8) is the search: a depth-first recursion over configurations
  (right mode, budget, source setting) on the search graph of retained successors. When the
  retained successors do not close a cover, the right may commit to a **committed successor
  subset**, one query each.
* A **handoff** query checks every declared left mode change against a mode-dependent
  invariant (Eq. 13).
* **Assumption 1** (Well-Formedness): the right model is nonblocking and complete with respect
  to its declared successors. The tool checks it per right mode (`relcert --wellformed`), and the
  Lean development proves it per benchmark.

The suite's mechanism letters (Table 1 and Table 3): S stretching (including stretch 0), M
multi-step cover, R right-only segment, B branching, P pruning, D mode-dependent invariant, I
mode fact, X committed successor subset. A benchmark *uses* a mechanism when its certificate
contains it, and *needs* it when the tool declines with the mechanism switched off (D by the
uniform-row test; M and B have no switch and are marked used only).

The search (stretch values, Lie routes, mode-fact candidates, stage lists, covers) is
untrusted: it only proposes. Everything it proposes is either replayed by a kernel-verified
checker or becomes a Z3 query that the Lean theorem takes as a hypothesis.

## What is proved

One generic theorem, `theorem3_of_coverX` (`Proofs/Encoding/Theorem3General.lean`), is the
paper's Theorem 3 (Soundness of Synthesis): for a left and a right program in the shape of
Eq. 1, a formula `φ` and a cover from every admissible start, it concludes Eq. 10,
`str(φ) → [|(L*, R*)⟩⟩ str(φ)`, where `str(φ)` adds the operating region `op_R` (the right in
the guard of its stored mode, with its mode facts) and the domains. The forall-exists
modality is that of dL-rel (NFM'25), over the semantics of hybrid programs. The right program
is the clocked automaton `rightAutomatonBodyC`: each right cycle selects the stored mode,
flows for at most `ε_R` under its domain, then takes a declared edge whose target guard holds.

Every benchmark instantiates it through a record-level theorem, from the records the tool
emits (IR literal, mode-fact certificate, cover, reposition records, committed subsets):

| record theorem | invariant | suite benchmarks |
|---|---|---|
| `theorem3_window_of_records` (`windowClaim`) | mode-independent | 32 |
| `theorem3_keyed_of_records` (`keyedClaim`, rows keyed by the stored left mode, composed through the handoffs: Theorem 2, `theorem3_modeKeyed_gen`) | mode-dependent | 18 |
| the `_pl` variants of both | right-only nodes certified on the restricted mode | 41 of the 50 |

The generated instance `InstancesV2/Bridge/<B>.lean` states `<b>_bridge : Verdicts … → dt ≤ ε_L
→ windowClaim …` (or `keyedClaim …`). There are 52 instances: the 50 suite benchmarks and the
two committed-subset exhibits of `benchmarks/choice/`. Five further bridge files instantiate a
stretch-0 demo, a restricted-mode demo, a demo whose two reposition stages cross in opposite
directions, and two strict-invariant exhibits.

The hypotheses of an instance:

* `Verdicts`: the Z3 answers, grouped (mode-fact stays, the two non-connection checks per
  pruned edge, the joint and right-only flow packs, admissibility of dropped starts, handoffs,
  reposition progress, coverage of committed subsets). It is not written by hand:
  `bridgeGroups` rebuilds the groups from the records, `verdicts_of_groups` turns "every group
  has a member Z3 reports unsat" into `Verdicts`, and the runner `relcert-bridge-verdicts`
  executes the same Lean function, prints each member with the same printer and counts the
  groups against a declared total (13677 over the 52 instances).
* Structural facts about the records (well-formed structure, cover and reposition records,
  the padding of the right clock, equal rows where the invariant is mode-independent), decided
  by `decide +kernel` inside the instance.
* Assumption 1 (`WellFormedRIn`), discharged from the benchmark's own proof
  (`InstancesV2/WellFormed/<B>.lean`, written by hand, Z3-free), transported to the pruned
  graph (`wellFormedR_transport`) and lifted by one coordinate for the right clock
  (`wellFormedR_lift`).

Known-false inputs: 140 invariant variants of suite benchmarks (a flipped comparison, a
dropped conjunct, a left variable swapped for its right counterpart) are refuted in the
kernel: each instance in `InstancesV2/Refute/` concludes the negation of the clocked claim for
every cover, so under every pruning. The tool declines all 140 (`docs/REFUTATION-RESULTS.md`).

`docs/PAPER-MAPPING.md` maps every definition, lemma and theorem of the paper to its Lean
name.

## Trust base

| item | role |
|---|---|
| the **parser** (`Trusted/Parse.lean`, strict; unknown keys refused by `Trusted/KeyAudit.lean`) | the model file is the specification |
| the **lowering** (`Trusted/Run.lean` and the query builders under `Trusted/`) | turns the parsed model into the Lean formulas and the queries |
| the **printer** (`Trusted/Smt.lean`, `toScript`) | renders a query to SMT-LIB |
| **Z3's `unsat`** answers | the one extra axiom, `z3_unsat_sound` (`Trusted/Oracle.lean`): `z3solve q = unsat → ∀ σ, ¬ (σ ⊨ q)` |
| the **Lean kernel**, with the statement of Theorem 3 | checks everything else |

The development uses Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) and `z3_unsat_sound`, nothing else. Assumption 1 is not assumed: it is proved per
benchmark without Z3. The tool's own `--wellformed` check is untrusted and only ever
declines. The Z3 session (`Trusted/Z3.lean`) uses a pinned binary, `(reset)` before every
query, a 10 s timeout and a resource limit per query; `unknown` and errors are never counted
as verdicts. The trusted surface, file by file: `RelCertifier/Trusted/README.md`.

## Build

Requirements: the Lean toolchain of `lean-toolchain` (elan fetches it; the one Lean
dependency, dL-rel, is pinned by tag in `lakefile.toml` and brings dL-lean and Mathlib), and
Z3 4.15.1 (the tool looks for `/opt/homebrew/bin/z3`, `/usr/local/bin/z3`, `/usr/bin/z3`, or
`RELCERT_Z3`).

```bash
lake build    # the library: proof chain, Assumption 1 battery, 52 bridge instances,
              # 5 demo and strict bridge files, 140 refutation instances
lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts
```

`lakefile.toml` declares the library `RelCertifier` (the default target) and five executables:

| executable | root | what it does |
|---|---|---|
| `relcert` | `Main.lean` | the certifier, the emitters and the suite checks |
| `relcert-test` | `Test.lean` | trusted-layer tests: parser, printer, IR drift of the 50 literals, Z3 layer, determinism |
| `relcert-bridge-verdicts` | `BridgeVerdictsMain.lean` | sends every group of the 52 bridge instances to Z3 (declared total 13677) |
| `relcert-progress-verdicts` | `ProgressVerdictsMain.lean` | sends the reposition (progress) certificate groups (declared total 1009) |
| `relcert-refute-verdicts` | `RefuteVerdictsMain.lean` | sends the groups of the 140 refutations (declared total 416) |

On an Apple M2 Max a from-scratch build takes about 15 min. An edit to anything under
`Proofs/`, `Checker/` or `Trusted/` (comments included) rebuilds every instance downstream.

## Run

```bash
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/suite_v2/watertank/input.txt
./.lake/build/bin/relcert --help
```

`relcert <input.txt>...` prints one verdict per file (`CERTIFIED`, `DECLINED`, `ERROR`); the
verdict includes the handoff check. Other entry points: `--check-quick-v2` (the suite check
below), `--handoff` (the handoff check alone), `--wellformed` (the Assumption 1 check per right
mode), and the emitters `--emit-ir`, `--emit-cover`, `--emit-cuts` that regenerate the
committed Lean records (`scripts/gen_v2_data.py` drives them over the suite). The input format
is in `benchmarks/README.md`.

Switches (environment variables; `relcert --help` lists them all):

| variable | effect |
|---|---|
| `RELCERT_IMPLIED_CUT=1` | widen the mode-fact candidates (closures of strict guard conjuncts, set-point half-lines of contraction fields, linear-form chains); every suite run sets it |
| `RELCERT_SYNC=1` | the time-synchronous baseline: stretch 1 only, no right-only segments |
| `RELCERT_NO_PRUNE=1` | no pruning by non-connection certificates |
| `RELCERT_NO_CHOICE=1` | no committed successor subsets |
| `RELCERT_NO_STUTTER=1` | no stretch 0 (stretch 0 is tried last, and only when the declared range includes 0) |
| `RELCERT_NO_PRELANDING=1` | right-only flow certificates on the whole mode, not on the restricted mode |
| `RELCERT_NO_PROGRESS=1` | do not require reposition certificates at right-only nodes |
| `RELCERT_NO_CUT=1`, `RELCERT_NO_IMPLIED_CUT=1`, `RELCERT_NO_LINEAR_CUT=1` | switch the mode facts, the widened candidates, or the linear-form chain off |
| `RELCERT_WELLFORMED_STRICT=1` | decline a certified file whose right model has a mode the Assumption 1 check cannot show `ok` |
| `RELCERT_DEBUG=1` | per-mode diagnostics on stderr |
| `RELCERT_Z3`, `RELCERT_Z3_TIMEOUT`, `RELCERT_Z3_RLIMIT`, `RELCERT_MAX_QUERIES`, `RELCERT_TIME_BUDGET_MS` | the Z3 binary, per-query timeout (default 10000 ms) and resource limit, per-benchmark query and time budgets (defaults 20000 queries, 300000 ms) |

Stretch 0 and the restricted-mode right-only certificate are features of every run, not
per-benchmark options; their switches exist for the paper's ablations (`docs/STUTTER.md`,
`docs/PRELANDING.md`).

## Reproduce the paper

The full recipe, what each check establishes and the last recorded run are in
`docs/CERTIFICATION-CHECK.md` (the paper's Appendix B.7). In short:

```bash
# 1. kernel-check everything and build the executables
lake build
lake build relcert relcert-test relcert-bridge-verdicts relcert-refute-verdicts relcert-progress-verdicts

# 2. the axiom audits
lake build RelCertifier.InstancesV2.WellFormedBattery 2>&1 | grep -A3 "depends on axioms"
lake build RelCertifier.InstancesV2.AxiomCheck 2>&1 | grep -A3 "depends on axioms"

# 3. certify the 50 files in the strict well-formedness mode, re-send the tool's own queries,
#    and gate the Assumption 1 check, all against declared counts
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert --check-quick-v2 benchmarks/suite_v2/*/input.txt
python3 scripts/check_one_domain.py
RELCERT_IMPLIED_CUT=1 ./.lake/build/bin/relcert benchmarks/negative/*/input.txt

# 4. the trusted-layer tests (the manifest lets the two determinism checks run)
for d in benchmarks/suite_v2/*/; do printf '%s\t%s\n' "$(basename "$d")" "$PWD/${d}input.txt"; done > /tmp/bench-paths-v2.tsv
BENCH_PATHS=/tmp/bench-paths-v2.tsv ./.lake/build/bin/relcert-test

# 5. the verdict runners
./.lake/build/bin/relcert-bridge-verdicts
./.lake/build/bin/relcert-progress-verdicts
./.lake/build/bin/relcert-refute-verdicts
```

Expected:

| step | expected output |
|---|---|
| 1 | `Build completed successfully`, no `declaration uses 'sorry'` |
| 2 | 78 lines for the Assumption 1 battery (76 at the three standard axioms, 2 from the `CutLiftX` lift with `z3_unsat_sound`); 11 for the generic theorems (8 standard, 3 with `z3_unsat_sound`) |
| 3 | `[suite_v2] 50 certified, 0 declined, 0 error(s)`; modal 1421/1421, handoff 2846/2846, non-connection 32/32, pruned edges 16/16, reposition (dyn) 950/950; strict Assumption 1 gate 181/181 right modes `ok` (75 invariant, 106 exit), 0 `UNKNOWN`, 0 `BLOCKING`; `SUITE_V2 QUICK CHECKS PASSED`; `ONE DOMAIN: PASS (50 benchmarks: …)`; the three files of `benchmarks/negative/` `DECLINED` |
| 4 | `ok   all 50 suite_v2 IR literals match their files (50 files)`, a bare `ALL PASS` |
| 5 | bridge 13677/13677, progress 1009/1009, refute 416/416 |

The numbers of the paper's Section 6 (Table 1, the baseline, the ablations, the per-benchmark
Table 3, the run times) come from one frozen run:

```bash
scripts/paper_numbers.sh OUTDIR     # committed output: docs/paper-numbers/
```

It records the commit, Z3 version and flags (`MANIFEST.txt`), emits every cover twice and
requires them byte-identical, runs every configuration (`control`, `nochoice`, `sync`,
`sync_nochoice`, `noprune`, `noprune_nochoice`, `norepo`, `singlestep`, `opregion`,
`nostutter`, `noprelanding`, and the exhibits with committed subsets off, on, and on under the
baseline), runs the mechanism matrix
(`scripts/suite_v2_matrix.py`) and the letters (`scripts/suite_v2_letters.py`), and writes
`numbers.tex` (the macros the paper reads), `table1.tex` and `table_per_benchmark.tex`. At the
paper's state: 50 certified; 24 under the baseline (of the 26 declined, 19 need stretching and
7 right-only segments); with committed subsets off 12 decline, with pruning off 2, with both
off 16.

## Repository layout

```
RelCertifier/
  Core/            flow certificates (Lie routes), rational reification
  Checker/         verified cover checkers (decideCoveredX with committed subsets),
                   emitted-cover types, mode-fact certificates (EvolStrengthening(X)),
                   non-connection (Definition 6)
  Proofs/
    Encoding/      the forall-exists chain: joint and right-only segments, reposition
                   progress, mode handoffs, guarded switching, the clocked right automaton,
                   Assumption 1 (WellFormedR), the general Theorem 3 (Theorem3General,
                   CoverResp, Progress), Lemma 1 (Stretching)
      Emitted/     Theorem 3 of a benchmark from its emitted records (Window, Keyed, Run,
                   Transport, Lift, the strict and refutation layers)
    Flow/          differential-invariant routes, existence, viability
    Soundness/     the lift of the mode facts (CutLift, CutLiftX)
    Transfer/      scaled-model transfer
  Trusted/         parser, key audit, lowering, query builders, printer, Z3 session, the
                   untrusted certifier (OracleAPI), the Assumption 1 check; Trusted/README.md
  InstancesV2/
    BenchIR/ BenchCovers/ BenchProgress/ BenchPrelanding/ Cuts/ BenchChoice/
                   emitted records, one leaf per benchmark and demo
    Bridge/        the 52 generated bridge instances and the 5 demo and strict files
    WellFormed/    Assumption 1 per benchmark (right model and proof)
    Refute/        the 140 refutations, their records (Refute/Data/) and Table
    Choice/        the two committed-subset exhibits' records and Assumption 1 proofs
    AxiomCheck.lean, WellFormedBattery.lean, Bridge.lean, Refute.lean, the leaf aggregators
  VerdictsV2/      the runners (RunV2, RunBridge, RunProgress, RunRefute) and query rebuilds
  Verdicts/        shared verdict combinators and pins, the handoff runner
RelCertifier.lean  the library root; `lake build` builds its closure
Main.lean, Test.lean, BridgeVerdictsMain.lean, ProgressVerdictsMain.lean, RefuteVerdictsMain.lean
                   the five executables
benchmarks/
  suite_v2/        the 50 benchmarks (10 from the literature, `lit_*`)
  choice/          the 2 committed-subset exhibits
  negative/        3 expected DECLINEs; negative_wellformed/ 1 expected Assumption 1 failure
  stutter_demo/ prelanding_demo/ progress_demo/ strict_demo/   the demo and strict inputs
  refute_mutants/  the 140 refuted variants (sha256-pinned by docs/refute/witnesses.jsonl)
scripts/           generators (gen_v2_data.py, gen_bridge.py, gen_refute.py, gen_*_demo.py),
                   the frozen paper run (paper_numbers.sh, suite_v2_matrix.py,
                   suite_v2_letters.py), the refutation finder and experiment, tests
                   (stutter_tests.py, prelanding_tests.py, check_one_domain.py), demo verdict
                   runs (*_verdicts.lean, *_kernel_checks.lean)
docs/              the documents below; docs/paper-numbers/ the frozen run's output;
                   docs/refute/ the refutation experiment's data
```

The former `benchmarks/reserve/` and `benchmarks/skipped/` (designs outside the suite) were
removed; their last state is at git tag `pre-cleanup-2026-11`. The earlier route through
hand-written standalone Theorem 3 instances is archived on branch `archive/legacy-2026-10`.

## Further reading

* [`docs/PAPER-MAPPING.md`](docs/PAPER-MAPPING.md): start here with the paper open; every
  definition, lemma, theorem and assumption of the paper, its Lean name and file, and the
  vocabulary map (mode fact = checked cut, reposition certificate = progress certificate,
  committed subset = choice, operating region = `regionG`, witness strategy = cover).
* [`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md): the reproduction recipe, the
  expected output of every check, the per-benchmark inventory, the last run.
* [`docs/BRIDGE.md`](docs/BRIDGE.md): the generic bridge, Theorem 3 of a benchmark from its
  emitted records; [`docs/THEOREM3-GENERAL.md`](docs/THEOREM3-GENERAL.md): the general theorem
  with committed subsets and reposition progress;
  [`docs/CHOICE-SOUNDNESS.md`](docs/CHOICE-SOUNDNESS.md): the committed-subset argument.
* [`docs/WELLFORMED.md`](docs/WELLFORMED.md): Assumption 1 per benchmark and the tool check.
* [`docs/HANDOFF.md`](docs/HANDOFF.md): mode-dependent invariants and the handoff check.
* [`docs/STUTTER.md`](docs/STUTTER.md) and
  [`docs/STUTTER-SOUNDNESS.md`](docs/STUTTER-SOUNDNESS.md): stretch 0.
* [`docs/PRELANDING.md`](docs/PRELANDING.md): right-only certificates on the restricted mode,
  and two-stage reposition certificates in every direction.
* [`docs/REFUTATION-RESULTS.md`](docs/REFUTATION-RESULTS.md): the 140 kernel refutations.
* [`docs/GUARDED-SWITCHING.md`](docs/GUARDED-SWITCHING.md): the guarded automata and the
  operating region (a design record).
* [`docs/SUITE-REDESIGN.md`](docs/SUITE-REDESIGN.md), [`docs/SUITE-DEDUPE.md`](docs/SUITE-DEDUPE.md):
  the design record of the suite, its rules and the mechanism matrix.
* [`benchmarks/README.md`](benchmarks/README.md): the input format and the suite.
* [`RelCertifier/Trusted/README.md`](RelCertifier/Trusted/README.md): the trusted surface.
