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
| **1. Flow certificate** | `FlowCert.lean` | `tderiv`, `lieDeriv`, `flowQuery` | `flow_cert_sound` / `flow_cert_sound_strict` | dL-lean `DI_nonstrict_domain` / `DI_strict` |
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

## Running it

```sh
lake build              # builds the verified library + the `relcert` executable
lake exe relcert <input.txt>     # certify a benchmark end-to-end (parse → Z3 → cover)
lake exe relcert                 # no args: the Stage-1 flow-certificate demo
```

Requires Lean 4 (`leanprover/lean4:v4.31.0`, pinned in `lean-toolchain`), Z3 on `PATH`,
and the `dL-rel` dependency available at `../dL-rel` (which transitively provides dL-lean
`v0.1.0-DI` and the encoding bridge).

## Benchmark parity

Run over the 46 Python `relCertifier` benchmarks (`PARITY.md` for the full table):

**Lean 22 / 46 VERIFIED** (Python 46 / 46), and **every Lean `VERIFIED` is sound** —
backed by `flow_cert_sound_strict` composed by `cover_sound`. By category: A (offset)
18/22, B (mode-scoped) 1/1, C (coupled) 2/14, D (pair-scoped) 1/3, E (quadratic) 0/3,
F (nonlinear) 0/3. The remainder `decline` (sound, one-sided): the runner's `invToG`
currently lowers only the primary offset component of a relational invariant, so coupled /
quadratic / nonlinear invariants are not yet certified — a completeness gap, never an
unsound claim.

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
