# Status — 2026-10-08 (branch `dedupe-suite`)

Current state of `relCertifier-lean-implementation` in one page: what is proved, what is
assumed, what to run, and what is open. For *what the theorems say* read
[`README.md`](README.md); for *how to re-check them* read
[`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md).

**Branch head: see `git log`.** 378 Lean files, 41 benchmark inputs, 40 modal instances (+ 7 mode-keyed, + 2 declared-invariant leaves).

---

## Headline

Every one of the 40 certified benchmarks carries a kernel-checked relational-refinement
theorem of the paper's Theorem 3 shape (41 base theorems — `rover3tier_rung12` splits per
left mode; 50 theorems in `ModalBattery` with the 7 mode-keyed and the 2 cut-composed
ones). Their only assumptions are a five-item trust base and a finite list of Z3 `unsat`
verdicts, and **every one of those verdicts is re-run on demand against a query the kernel
certifies is the theorem's own**.

**New (2026-10-07/08): the DECLARED mode-dependent invariants.** Seven benchmarks declare
one invariant row per left mode. The tool now checks the cross-mode **handoff**
`φ_inv(m') ∧ evolve_{m'} ∧ guard_m ∧ evolve_R → φ_inv(m)` (domain-conditioned, the sound
form at a switch) at every declared left transition (215 over the suite, `relcert
--handoff`, phase 4 of `--run-verdicts`; `docs/HANDOFF.md`), and
`Proofs/Encoding/ModeHandoff.lean` mechanizes the paper's general Theorem 3: from
per-left-mode covers and the handoffs, `Φ ≡ ⋀_m (u_L = m → φ_inv(m))` is a ∀∃ invariant of
the full left automaton (`theorem3_modeKeyed`, `docs/PAPER-MAPPING.md` §2b). All seven
carry the composed theorem `…_modeKeyed` at their declared rows (54 theorems in
`ModalBattery`). `rover3tier_rung12` needed a repair first: with its original ACCEL row the
`ACCEL → COAST` handoff was satisfiable (countermodel recorded); the row was re-stated — rows
only — as the velocity envelope plus COAST's own functional bound (`docs/HANDOFF.md`).

**New (2026-10-08, branch `dedupe-suite`): the suite is deduplicated to 40
benchmarks.** Normalizing each `input.txt` (comments, blank lines and the `name =` line
removed) showed three groups of byte-identical models under several names
(`arm_chain_rung3` = `arm_fidelity_high` = `plant_fan_high`; `arm_fidelity_low` =
`arm_refinement` = `plant_fan_low`; `match_multi_eps` = `rover3tier_M1`) and one
near-duplicate (`plant_fan_mid` = `arm_fidelity_mid` with tolerance 0.3 instead of 0.25).
The six redundant names were removed with everything that referenced them (benchmark
directories, 9 instance leaves, 28 emitted-data leaves, `Archive/Mega.lean`, runner rows,
pins, coverage constants, generator lists). Declared coverage is now 6 / 97 / 504 / 191
(from 6 / 105 / 522 / 215), re-derived and pinned by `decide` in `CoveragePins`; the
battery has 50 theorems (41 base + 7 mode-keyed + 2 cut-composed), 40 with
`z3_unsat_sound` and 10 standard-three. Method, removals, and the per-benchmark
declared-invariant theorem table: `docs/SUITE-DEDUPE.md`.

**New (2026-10-08, branch `cut-composition`): the checked-cut benchmarks at their
DECLARED invariant.** `arm_chain_rung3`, `arm_fidelity_high`, `arm_fidelity_mid`,
`plant_fan_high`, `plant_fan_mid` (the latter three removed by the deduplication above;
two remain) carried Theorem 3 only with the `Hold` cut `θ_R ≥ 0.6`
conjoined to the invariant at every right mode. Each now also carries
`<name>_declared` (`Instances/<Name>Declared.lean`): the declared row itself, with the cut
carried as `Hold`'s mode region only (`mvRegionR`; `⊤` at the approach modes) — the
composition of the cut's two obligations, O1 entry and O2 invariance. Z3-free: right-only
catch-up responses (`Proofs/Encoding/CutComposition.lean`), standard three axioms, no
runner change. The plain-`mvValid` form (no region anywhere) is FALSE for these automata
(countermodel recorded). 59 theorems in `ModalBattery` at the time; 50 after the
deduplication. `docs/CUT-COMPOSITION.md`,
`docs/PAPER-MAPPING.md` §2c.

## Last full verification

Four checks, all green, from a **cold tree** (`lake clean` had wiped this package *and*
its dependencies). This run predates the 2026-10-08 deduplication (46-benchmark suite);
the current numbers are in *Branch run (`dedupe-suite`)* below:

| check | command | result |
|---|---|---|
| kernel | `lake build` | 8991 jobs, exit 0 — cold build measured **12h59m** at 8988 jobs |
| axioms | `lake build RelCertifier.Instances.ModalBattery` | 47 theorems: 5 standard-three, 42 `+z3_unsat_sound`, **0 other**, no `sorryAx` |
| hypotheses | `relcert --run-verdicts` | **594/594 `unsat`**, coverage 6 / 105 / 483, exit 0 (now 6 / 105 / 522 / 213 — see *Branch run* below) |
| trusted layer | `BENCH_PATHS=… relcert-test` | ALL PASS |
| suite | `relcert benchmarks/suite_uniform/*/input.txt` | 46 CERTIFIED, 0 DECLINED, `shield_unreachable` inconclusive as documented |

The middle two are bundled:

```bash
./.lake/build/bin/relcert --check-quick benchmarks/suite_uniform/*/input.txt
```

`relcert --help` lists every command and, importantly, what is *not* in that binary.

## Branch run (2026-10-08, `mode-handoff`)

All checks green on the branch head, from the warm tree (no file in `Proofs/` other than
the new leaf `ModeHandoff.lean` was touched, so the heavy instances did not re-elaborate;
the new 12-dof leaf `Story1AttdistRungBHandoff.lean` takes ~10 min on its own):

| check | command | result |
|---|---|---|
| kernel | `lake build` | exit 0 (see `docs/CERTIFICATION-CHECK.md` header for the job count) |
| axioms | `lake build RelCertifier.Instances.ModalBattery` | **54** theorems: 8 standard-three (the 5 before + the 3 composed rover theorems), 46 `+z3_unsat_sound`, 0 other, no `sorryAx` |
| hypotheses | `relcert --run-verdicts` | **848 `unsat`**, coverage 6 / 105 / **522** / **215**, no declared handoff failure, exit 0 |
| trusted layer | `BENCH_PATHS=… relcert-test` | ALL PASS (no skips) |
| suite + verdicts | `relcert --check-quick benchmarks/suite_uniform/*/input.txt` | 46 CERTIFIED, 0 DECLINED, 1 documented error; QUICK CHECKS PASSED |
| handoff alone | `relcert --handoff benchmarks/suite_uniform/*/input.txt` | 216/216 transitions checked, 215 unsat; the one FAIL is `shield_unreachable`'s self-loop, whose right evolve does not lower against the left variable list (the 47th, outside the emitted suite) |

## Branch run (2026-10-08, `dedupe-suite`) — the current numbers

All checks green on the branch head after the removal of the six duplicate benchmarks,
from the warm tree (the rebuild touched only the whole-suite aggregators, the pins and
runner, and the ≤ 6-dof leaves downstream of two `Proofs/` docstring edits; 8969 jobs,
1m27s):

| check | command | result |
|---|---|---|
| kernel | `lake build` | 8969 jobs, exit 0 |
| axioms | `lake build RelCertifier.Instances.ModalBattery` (`grep -A3`) | **50** theorems: 10 standard-three (the 5 Z3-free base instances, the 3 composed rover theorems, the 2 `…_declared`), 40 `+z3_unsat_sound`, 0 other, no `sorryAx` |
| hypotheses | `relcert --run-verdicts` | **798 `unsat`**, coverage 6 / 97 / 504 / 191, no declared handoff failure, `ALL HYPOTHESES DISCHARGED`, exit 0 |
| trusted layer | `BENCH_PATHS=… relcert-test` | `ALL PASS` (no skips; `all 40 IR literals match their files`) |
| suite + verdicts | `relcert --check-quick benchmarks/suite_uniform/*/input.txt` | `40 certified, 0 declined, 1 error(s) — matches the declared suite`; QUICK CHECKS PASSED |
| handoff alone | `relcert --handoff benchmarks/suite_uniform/*/input.txt` | 192/192 transitions checked over 41 inputs, 191 unsat; the one FAIL is `shield_unreachable`'s self-loop, as documented (exit 1 by design) |

## Branch run (2026-10-08, `cut-composition`)

All checks green on the branch head, from the warm tree (new leaves only — the
`CutComposition` proof leaf and the five `…Declared` instances — plus `ModalBattery`):

| check | command | result |
|---|---|---|
| kernel | `lake build` | 9007 jobs, exit 0 |
| axioms | `lake build RelCertifier.Instances.ModalBattery` (`grep -A3`) | **59** theorems: 13 standard-three (the 8 before + the 5 `…_declared`), 46 `+z3_unsat_sound`, 0 other, no `sorryAx` |
| hypotheses | `relcert --run-verdicts` | **848 `unsat`**, coverage 6 / 105 / 522 / 215, exit 0 (unchanged: the new theorems carry no verdict) |
| trusted layer | `BENCH_PATHS=… relcert-test` | ALL PASS (no skips) |
| suite + verdicts | `relcert --check-quick benchmarks/suite_uniform/*/input.txt` | 46 CERTIFIED, 0 DECLINED, 1 documented error; QUICK CHECKS PASSED |

One recipe defect fixed on the way: the documented axiom audit used `grep -A2`, which
drops the fourth line of a four-axiom block — the one naming `z3_unsat_sound` — so every
theorem read as standard-three. The recipe now says `-A3`.

## What is trusted

Exactly five things, unchanged and deliberately frozen:

1. the **parser** (benchmark text → IR) — the file is the spec;
2. the **printer** (`toScript`) — Z3 reads text;
3. **Z3's `unsat`** answers — the single oracle, axiom `z3_unsat_sound`;
4. the **Lean kernel**;
5. **successor-completeness with guard-gated switching** — a fact about the modeled
   system, not about formulas.

Everything else is proved or kernel-replayed. The search — cover exploration, cut
fixpoints, route selection, λ choice — is entirely untrusted: it only proposes.

## What was closed recently

The gap between *the hypothesis a theorem assumes* and *the query the runner sends Z3* is
now kernel-checked end to end, in 174 theorems under `RelCertifier/Verdicts/`:

| file | n | what it ties |
|---|---|---|
| `ModalPinTable` | 49 | each instance's `Verd…` **is** `modalVerd` at the runner's arguments (41 rows; 53 theorems before the deduplication) |
| `ModalTablePins` | 41 | the rest of the `RunInfo` row, incl. mode pairs via the runner's own `modalPairs` |
| `ModalCodePins` | 80 | the runner's **code**: λ from `(lamN, lamD)`, head terms from `ceilCo`/`ceilKs`, the three routes |
| `CoveragePins` | 4 | the declared query counts equal what the tables generate (modal, cut, handoff; the declared handoff-failure set) |

Each layer was verified by breaking what it pins: `/`→`*` in the λ fails 12 theorems,
dropping route C fails 3, shifting a head coordinate fails 24, corrupting a table field
fails the build, and bumping a declared count without touching the table fails too.
Before these files, every one of those edits compiled clean.

Also fixed along the way: six vacuous theorems (repaired — see
[`docs/VERDICT-EVIDENCE-AUDIT.md`](docs/VERDICT-EVIDENCE-AUDIT.md)), four defects in the
runner's table, and five places where a success path was reachable without doing the work.

## What is open

Nothing blocking. In rough order of interest:

* **`rover3tier_rung12`'s ACCEL row was re-stated** (rows only) to make its declared
  invariant mode-keyed; the original row and its countermodel are recorded in
  `docs/HANDOFF.md`. The regenerated `Throughout/rover3tier_rung12.lean` carries the first
  non-identity strata order in the battery (handled by `mem_equiv_of_index_perm`), and
  `scripts/gen_throughout.py` is still the stale monolith reader — the leaf-repointed,
  regex-fixed copy used for this regeneration lives only in the session record.
* **Handoff hypotheses are discharged in-kernel for all seven composed instances** (nested
  rows, constant offsets, or the evolve floor). The Z3 route (`handoff_of_unsat`, over
  exactly the runner's domain-conditioned `ihandoffQuery`) exists and is axiom-audited but
  no instance needs it yet.

* **One control-flow fact, stated not proved:** that `checkComp`'s loop reports success
  exactly when one of the three routes answered `unsat`. Deliberate — getting it wrong
  makes queries fail loudly, not pass quietly.
* **Declared constants need judgment when the suite changes.** Adding a benchmark fails
  the *build* (`CoveragePins`) and the *run* (`Coverage.expected`). That friction is the
  point; the errors name the file to edit. Update the table and the constant together.
* **`relcert-test` needs `BENCH_PATHS`** or it skips two Z3-determinism checks. It now
  says so in its final line (`ALL PASS (2 SKIPPED …)`), but the variable is not set by
  default.
* **Regenerating covers** (`--emit-cover`) invalidates the archived containment audit in
  `docs/archive/`. Nothing depends on it, but re-read that file's header before citing it.
* **Cold builds are ~13 h and ~30 GB.** Read the *Cost* section of
  `docs/CERTIFICATION-CHECK.md` first; killing `lake build` orphans its workers.

## Map

```
RelCertifier/
  Trusted/     the tool: parser, lowering, printer, Z3 session, search  (in the trust base)
  Core/        flow certificates, the DI routes
  Checker/     verified decideCovered — search proposes, this gates
  Proofs/      the ∀∃ calculus + the analytic facts, proved once for all benchmarks
  Instances/   per-benchmark data and theorems; ModalBattery imports every one
  Verdicts/    the empirical column: query mirrors, the 169 pins, the runner
  Archive/     superseded developments, kept for the record
docs/          CERTIFICATION-CHECK (the recipe), READING-GUIDE, audits, archive/
```
