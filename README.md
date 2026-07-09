# relCertifier-lean

A **formally verified** relational-invariant certifier for pairs of hybrid programs,
mechanized in Lean 4 on top of [dL-lean](https://github.com/UNCC-FORTRESS/dL-formalization-Lean)
(`v0.1.0-DI`) and [dL-rel](https://github.com/UNCC-FORTRESS) (NFM'25 encoding).

It matches the functionality of the Python `relCertifier` prototype — certify a supplied
relational invariant between a left (deployed) and right (reasoning) hybrid system via
UNSAT-of-negation with Z3-NRA — but **every soundness-critical function is proven
correct**, each proof citing a mechanized theorem of the imported theory. The single
trusted assumption of the whole tool is that Z3's `unsat` verdict is sound
(`z3_unsat_sound`); everything else is kernel-checked.

## What is verified

The tool is built bottom-up as three verified local certificates plus their composition,
then a runnable front-end.

| Stage | File | Function(s) | Correctness theorem | Cites |
|---|---|---|---|---|
| **1. Flow certificate** | `FlowCert.lean` | `tderiv`, `lieDeriv`, `flowQuery` | `flow_cert_sound` / `_strict` / `_superlevel` | `DI_nonstrict_domain` / `DI_strict` / `DI_nonstrict_superlevel` |
| **2. Non-connection** | `NonConn.lean` | `lieAlong`, `sourceCheck`, `barrierCheck` | `nonconn_sound` | dL-lean `DI_strict` (Nagumo barrier) |
| **3. Cover / Theorem 3** | `Cover.lean`, `Cover/Encoding.lean` | `Covered`, `RightReach`, `cover_sound` | `cover_sound`, `theorem3_encoded` | flow + nonconn + dL-rel `encoding_correct` |
| **4. Runner** | `Parse.lean`, `Run.lean`, `Main.lean` | parser + Z3-driven cover | — (trusted IO) | uses the verified queries |

The load-bearing new proof is **`tderiv_correct`**: the syntactic partial derivative of a
term denotes its analytic partial derivative (`HasDerivAt`, by induction on `Term`,
product rule ↦ `HasDerivAt.mul`). It is what connects the computed Lie derivative to
dL-lean's semantic `Lie`, and thereby to the differential-invariant theorems `DI`.

**`cover_sound`** is the paper's Theorem 3 (`ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`): by induction
on the assembled right response, each segment preserves the invariant (`flow_cert_sound`,
a time-unbounded `BoxLe`), a jump cannot follow a pruned edge (`nonconn_sound`), and the
budget strictly decreases each step (`cover_budget_decreases` — the mechanized rejection
of budget-neutral cycles, the load-bearing finiteness argument).

### Trust boundary

```
#print axioms cover_sound          -- propext, Classical.choice, Quot.sound
#print axioms nonconn_certified    -- + z3_unsat_sound
#print axioms flow_certified       -- + z3_unsat_sound
```

The pure core depends only on the three standard Lean axioms. The IO-boundary theorems add
exactly one leaf, `z3_unsat_sound` (an `unsat` verdict from the opaque `z3solve` is sound),
isolated in `Oracle.lean`. **No subtangency axiom** — where the Python tool's boundary-only
non-strict flow check is unsound (dL-lean's `nonstrict_boundary_insufficient`, the `t²`
counterexample), the verified version takes the sound strict route (`DI_strict`).

## Soundness findings

Carried through every stage: a **boundary-only non-strict** check (`ẋ ≤ 0` on `{g=0}`
alone) is unsound without a regular-boundary hypothesis. The tool therefore certifies via
either the domain-wide non-strict route (`DI_nonstrict_domain`) or the strict-boundary
route (`DI_strict`), never the unsound one — declining where only the unsound route would
succeed. Pruning is one-sided: an edge is dropped only on a trusted UNSAT; failing to
prune is safe by default.

## The oracle (for invariant-synthesis search)

Built to be called thousands of times in a synthesis loop. Three **distinct, never-
conflated** outcomes — the honesty boundary a search depends on:

| outcome | meaning | synthesis reads it as |
|---|---|---|
| `CERTIFIED` | verified core produced UNSAT via a sound route | a real, sound YES |
| `DECLINED` | all queries definitive `sat`/`unsat`, no cover closes | a real, sound NO |
| `ERROR msg` | any harness/solver/env failure (missing Z3, crash, malformed, `unknown`/timeout, unlowerable) | retry / abort — never learn from it |

An `ERROR` can never masquerade as a verdict: `CERTIFIED` is only ever produced by actual
`unsat`; an inconclusive/failed query surfaces as `ERROR` when a covering route needed it.

**In-process API** (link the pipeline directly — no per-call process spawn):

```lean
open RelCertifier RelCertifier.Oracle
-- one warm, persistent Z3 session serves thousands of calls:
def loop (s : Z3Session) (cands : List PProblem) : IO (List Outcome) :=
  cands.mapM (certify s)          -- certify : Z3Session → PProblem → IO Outcome
```

Hermetic + deterministic: Z3 is a **pinned** absolute path (`RELCERT_Z3`, never
PATH-resolved), a **persistent** `z3 -in` process (warm), with `(reset)` + a per-query
`:timeout` + a machine-independent `:rlimit` + an `(echo)` **sentinel** that keeps the pipe
in sync so the same query always gives the same verdict. The cover DFS is memoized so a
large time-stretch can't blow up the pure search. **Warm per-call: mean 49 ms, median
26 ms, p90 101 ms, max 199 ms** (all 46 in ~2–3 s) — dominated by the Z3 solve. Every call
terminates (query / SMT-size / wall / rlimit bounds, all deterministic).

## Running it

```sh
lake build                      # verified library + `relcert` + `relcert-test`
lake exe relcert <input.txt> …  # oracle over each file on one warm session (3-way verdict + ms)
lake exe relcert                # no args: the Stage-1 flow-certificate demo
BENCH_PATHS=<name-tab-path-file> lake exe relcert-test   # trusted-layer test suite
```

Requires Lean 4 (`leanprover/lean4:v4.31.0`, pinned), a pinned Z3 (`RELCERT_Z3` or a
standard absolute path), and `dL-rel` at `../dL-rel` (transitively provides dL-lean
`v0.1.0-DI` and the encoding bridge). Env: `RELCERT_Z3_TIMEOUT` (ms, default 10000).

## Benchmark parity (`PARITY.md`)

Three-way, hermetic warm run over the 46 Python `relCertifier` benchmarks:
**45 CERTIFIED / 1 DECLINED / 0 ERROR** (deterministic; ~11 s). 4 gain-attack benchmarks are restated to their inductive conserved-certificate form (`CONSERVED.md`); the lone decline, `rover3_M1`, needs budget-aware reachability.
**Every `CERTIFIED` is sound** (`flow_cert_sound` / `_strict` / `_superlevel` composed by
`cover_sound`); Python VERIFIES all 46 via its boundary-only criterion, so Lean ⊆ Python.

The **superlevel (Lyapunov) route** `DI_nonstrict_superlevel` (`ġ ≤ 0` on `{g ≥ 0}` ⟹
invariance, proven from vendored Mathlib — no subtangency) lifts the contraction/energy
class (24 → 41) soundly, and a conserved-certificate restatement of 4 gain-attack benchmarks (24 → 45): it certifies the marginal `ġ = 0`-on-boundary invariants where the
strict route can't, and rejects the `t²` pathology (interior positivity) directly. See
`DIAGNOSIS.md` — the 22 earlier declines are all genuinely TRUE (**Cat-2 = 0**: Python
certifies no falsehood on the suite; its boundary-only criterion is unsound-in-general but
valid here because every boundary is regular or a harmless equilibrium).

The earlier 5 declines were all genuinely-true invariants, and none was a boundary or
soundness gap. Two "obvious" completeness moves were ruled out with evidence:
**non-connection pruning fires on nothing here** (checked via Z3 — the suspect bad
successors are genuinely reachable, so the time-unbounded Nagumo barrier can't prune them),
and a **naive `∧ v_L≤v_R` restatement is false** for the 4 gain-attack models (left gains
faster: `v_L(t)=0.3(1−e^{−3t}) > v_R(t)=0.3(1−e^{−2t})`) — the certifier *correctly declines*
that false conjunction (a false helper → DECLINE, never a false CERTIFIED).

The 4 are instead closed by their **inductive conserved-certificate form** (`CONSERVED.md`):
each has a conserved quantity `I` (`İ≤0`) whose sublevel `I≤I₀` flow-certifies and implies a
**finite, tight, derived safety bound** `s_L−s_R ≤ c` (each `c` Z3-`maximize`d from the
domains — not fitted, and *smaller* than the original stated bound). Restating the benchmark
to `{I≤I₀ ∧ s_L−s_R≤c}` certifies via the unchanged certifier → **24 → 45**. The lone
remaining decline, `rover3_M1`, has a genuinely-reachable bad successor and needs budget-aware
**reachability** (Strategy 2), out of scope. **45/46 is the honest ceiling; the 4 restatements
are benchmark-input changes, the certifier is untouched.**

Two trusted-layer (parser) bugs were found and fixed while validating: `dynOf` silently
defaulted an unlowerable dynamics term to `0` (a wrong field could falsely certify) — now
propagates to ERROR; and the tokenizer split `-` inside negative literals (`(* -1 psi)`
mis-parsed), corrupting damped dynamics — now `mergeSigns` re-glues signed literals. Neither
had produced a wrong CERTIFIED (re-run shows no benchmark flipped to ERROR).

The trusted layer is tested (`relcert-test`): determinism / oracle-consistency, outcome-
integrity (missing Z3 / unparsed / crash → ERROR), parser, lowering, and Z3-layer verdicts.

## Layout

```
RelCertifier/
  FlowCert.lean       Stage 1 — tderiv/lieDeriv + flow certificate soundness
  NonConn.lean        Stage 2 — Nagumo non-connection barrier
  Cover.lean          Stage 3 — cover relation, finiteness, cover_sound (Theorem 3)
  Cover/Encoding.lean Stage 3 — global ∀∃ encoding bridge (encoding_correct)
  Smt.lean            computable IR + SMT-LIB printer (pinned to lieDeriv by bridge lemmas)
  Oracle.lean         the single trusted leaf (z3_unsat_sound) + IO-boundary theorems
  Parse.lean          input.txt parser (trusted IO)
  Run.lean            end-to-end cover runner
Main.lean             `relcert` executable
STATUS.md             per-stage build notes
PARITY.md             the 46-benchmark parity table
```
