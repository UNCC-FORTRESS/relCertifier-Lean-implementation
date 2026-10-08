# Status — 2026-10-07 (branch `mode-handoff`)

Current state of `relCertifier-lean-implementation` in one page: what is proved, what is
assumed, what to run, and what is open. For *what the theorems say* read
[`README.md`](README.md); for *how to re-check them* read
[`docs/CERTIFICATION-CHECK.md`](docs/CERTIFICATION-CHECK.md).

**Commit `ce487e6`.** 397 Lean files, 47 benchmark inputs, 46 modal instances.

---

## Headline

Every one of the 46 certified benchmarks carries a kernel-checked relational-refinement
theorem of the paper's Theorem 3 shape (47 theorems — `rover3tier_rung12` splits per left
mode). Their only assumptions are a five-item trust base and a finite list of Z3 `unsat`
verdicts, and **every one of those verdicts is re-run on demand against a query the kernel
certifies is the theorem's own**.

**New (2026-10-07): the DECLARED mode-dependent invariants.** Seven benchmarks declare one
invariant row per left mode. The tool now checks the cross-mode **handoff**
`φ_inv(m') ∧ guard_m → φ_inv(m)` at every declared left transition (215 over the suite,
`relcert --handoff`, phase 4 of `--run-verdicts`; `docs/HANDOFF.md`), and
`Proofs/Encoding/ModeHandoff.lean` mechanizes the paper's general Theorem 3: from
per-left-mode covers and the handoffs, `Φ ≡ ⋀_m (u_L = m → φ_inv(m))` is a ∀∃ invariant of
the full left automaton (`theorem3_modeKeyed`, `docs/PAPER-MAPPING.md` §2b). Six of the
seven carry the composed theorem `…_modeKeyed` at their declared rows (53 theorems in
`ModalBattery`); the seventh, `rover3tier_rung12`, fails the handoff in both directions
(countermodels recorded) and keeps its two per-left-mode theorems — the mode-keyed
invariant is genuinely not an invariant of that model as declared.

## Last full verification

Four checks, all green, from a **cold tree** (`lake clean` had wiped this package *and*
its dependencies):

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

## Branch run (2026-10-07, `mode-handoff`)

All checks green on the branch head, from the warm tree (no file in `Proofs/` other than
the new leaf `ModeHandoff.lean` was touched, so the heavy instances did not re-elaborate;
the new 12-dof leaf `Story1AttdistRungBHandoff.lean` takes ~10 min on its own):

| check | command | result |
|---|---|---|
| kernel | `lake build` | 9000 jobs, exit 0 |
| axioms | `lake build RelCertifier.Instances.ModalBattery` | **53** theorems: 8 standard-three (the 5 before + the 3 composed rover theorems), 45 `+z3_unsat_sound`, 0 other, no `sorryAx` |
| hypotheses | `relcert --run-verdicts` | **846 `unsat`**, coverage 6 / 105 / **522** / **213**, 2 declared handoff failures (`rover3tier_rung12`), exit 0, 10 s |
| trusted layer | `BENCH_PATHS=… relcert-test` | ALL PASS (no skips) |
| suite + verdicts | `relcert --check-quick benchmarks/suite_uniform/*/input.txt` | 46 CERTIFIED, 0 DECLINED, 1 documented error; QUICK CHECKS PASSED, 48 s |
| handoff alone | `relcert --handoff benchmarks/suite_uniform/*/input.txt` | 216/216 transitions checked (215 + `shield_unreachable`'s self-loop), 214 unsat, 2 sat (`docs/HANDOFF.md`), 2 s |

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
now kernel-checked end to end, in 169 theorems under `RelCertifier/Verdicts/`:

| file | n | what it ties |
|---|---|---|
| `ModalPinTable` | 53 | each instance's `Verd…` **is** `modalVerd` at the runner's arguments |
| `ModalTablePins` | 42 | the rest of the `RunInfo` row, incl. mode pairs via the runner's own `modalPairs` |
| `ModalCodePins` | 72 | the runner's **code**: λ from `(lamN, lamD)`, head terms from `ceilCo`/`ceilKs`, the three routes |
| `CoveragePins` | 2 | the declared query counts equal what the tables generate |

Each layer was verified by breaking what it pins: `/`→`*` in the λ fails 12 theorems,
dropping route C fails 3, shifting a head coordinate fails 24, corrupting a table field
fails the build, and bumping a declared count without touching the table fails too.
Before these files, every one of those edits compiled clean.

Also fixed along the way: six vacuous theorems (repaired — see
[`docs/VERDICT-EVIDENCE-AUDIT.md`](docs/VERDICT-EVIDENCE-AUDIT.md)), four defects in the
runner's table, and five places where a success path was reachable without doing the work.

## What is open

Nothing blocking. In rough order of interest:

* **`rover3tier_rung12` is not composable as declared.** Its ACCEL and COAST rows are
  incomparable and the handoff fails both ways (`docs/HANDOFF.md`); the benchmark's
  statement stays per left mode. Widening the COAST row to `3v[l] + a[l] ≤ 3v[r] + 2.3` (or
  tightening ACCEL's) would make it composable — a modelling decision, not taken here.
* **Handoff hypotheses are discharged in-kernel for all six composed instances** (nested
  or constant-offset rows). The Z3 route (`handoff_of_unsat`, over exactly the runner's
  `ihandoffQuery`) exists and is axiom-audited but no instance needs it yet.

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
