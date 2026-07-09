# relCertifier-lean — Stage 1: the verified flow certificate

A runnable Lean tool matching the Python `relCertifier.v1` flow-certificate
functionality (`src/lie_checker.py`), with every soundness-critical function
formally proven and anchored to **dL-lean v0.1.0-DI**.

## What is verified (pure core — axioms: `propext, Classical.choice, Quot.sound` only)

| Function | Correctness theorem | Anchor |
|---|---|---|
| `tderiv : Term V → V → Term V` | `tderiv_correct` : `HasDerivAt (fun r => ⟦t⟧(update ω x r)) ⟦tderiv t x⟧ (ω x)` | Mathlib `HasDerivAt` |
| — | `tderiv_fderiv` : `fderiv ℝ ⟦t⟧ ω (Pi.single x 1) = ⟦tderiv t x⟧` | the shape `Lie` consumes |
| — | `term_differentiable` : `Differentiable ℝ ⟦t⟧` | polynomial totality |
| `lieDeriv g fL fR lam` | `lieDeriv_correct` : `⟦lieDeriv …⟧ ω = Lie (jointSys …) ⟦g⟧ ω` | `tderiv_fderiv` + `jointSys` |
| `jointSys fL fR lam` | `jointSys_wellFormed` | dL-lean `WellFormed` |
| `flowQuery o` = `domain ∧ ġ>0` | `flow_cert_sound` : `(∀σ,¬sat(flowQuery)σ) → g≤0 preserved along the λ-flow` | **dL-lean `DI_nonstrict_domain`** |

`tderiv_correct` is the load-bearing new proof: the syntactic derivative denotes the
analytic partial derivative (induction on `Term`, product rule ↦ `HasDerivAt.mul`).

## Trust boundary

`flow_certified` (IO boundary) axioms: standard three **+ `z3_unsat_sound`** — the
single trusted leaf, isolated in `Oracle.lean`. `z3solve` is `opaque` so the pure core
never depends on it. The SMT-LIB text is pinned to the verified `flowQuery` by
`iflowQuery_toHost` (the IR mirror provably denotes the verified object).

## Soundness finding (route decision)

The Python query is `domain ∧ g=0 ∧ ġ>0` (**boundary-only** non-strict). dL-lean proves
this form **unsound** without a regular-boundary hypothesis (`nonstrict_boundary_insufficient`,
the `t²` counterexample). Stage 1 therefore uses **route A**: `flowQuery = domain ∧ ġ>0`
(drop `g=0`), whose UNSAT gives `ġ≤0` on the *whole* domain — exactly `DI_nonstrict_domain`'s
hypothesis. Sound, zero new axioms. (Route B `DI_strict` and route C boundary+axiom were the
alternatives; A was chosen.)

## Runnable validation (`lake exe relcert`)

`rover_position  Stop_L / Safe_R`, `g = L_px − R_px − 2`, `ġ = L_vx − 4·R_vx`:

| case | domain | z3 | verdict | Python |
|---|---|---|---|---|
| λ=4 | `vx∈[0.3,1]` | **unsat** | CERTIFIED | PASS ✓ |
| λ=1 | `vx∈[0,1]` | sat | not certified | FAIL ✓ |

---

# Stage 2: the verified non-connection certificate (Nagumo barrier)

Prunes a declared right transition `qR → qR'` by proving its scalar successor guard
`x OP c` unreachable. Left-independent (right flow only). Verified core in
`NonConn.lean`.

## What is verified (pure core — axioms: standard three only)

| Function | Correctness theorem | Anchor |
|---|---|---|
| `lieAlong g sys` (Lie along any `ODESystem`) | `lieAlong_correct` : `⟦lieAlong g sys⟧ = Lie sys ⟦g⟧` | Stage-1 `tderiv_fderiv` |
| `sourceCheck o` = `source ∧ guard` | (check a) UNSAT ⟹ starts strictly safe | — |
| `barrierCheck o` = `domain ∧ g=0 ∧ ẋ≥0` | (check b) UNSAT ⟹ `ẋ<0` on threshold | — |
| — | `nonconn_sound` : both UNSAT ⟹ `∀ reachable ω, ¬ sat guard ω` | **dL-lean `DI_strict`** |
| `scalarUpper/Lower x c …` | `scalar{Upper,Lower}_link` : `guard ⟺ {g>0}` | — |

## Trust boundary

`nonconn_certified` (IO boundary) axioms: standard three **+ `z3_unsat_sound`** — the
same single leaf as Stage 1 (oracle now generic over `V`). **No subtangency axiom.**

## Soundness finding (Stage-2 analogue of Stage 1)

Python's check (b) is `evolve ∧ x=c ∧ ẋ>0` UNSAT ⟹ `ẋ≤0` on `{x=c}` **only** =
boundary-only non-strict (Stage-1 unsound pattern; the design doc says "strictly
away"). Scalar guard ⟹ regular boundary (∇=eₓ≠0), so *mathematically* sound, but
dL-lean can't cite it without the missing subtangency lemma. **Verified version takes
route B (strict):** `barrierCheck` uses `ẋ≥0` UNSAT ⟹ `ẋ<0` ⟹ `DI_strict`. Boundary-
shaped like Python, strict like the doc, sound, no axiom. Declines only `ẋ=0`-exactly-
on-threshold.

## Scope (incompleteness, not unsoundness)

Prunes **strict** guards `x>c` / `x<c` (`{g>0}`, sound via `DI_strict`'s `g≤0`
conclusion). Closed guards `x≥c` need boundary exclusion (strict invariant `g<0`, not in
dL-lean's `≤`-DI) — conservatively retained. Non-scalar guards retained. Structures
(`NonConnObligation`: guard/domain/source `Formula`, dynamics `ODESystem`) shaped so a
Stage-3 parser can populate them.

---

---

# Stage 3: the verified cover (composition) + Theorem 3 + global ∀∃ encoding

Composes the local certificates into the paper's Theorem 3
`ϕ_inv → [|(L*, R*)⟩⟩ ϕ_inv`. Verified core in `Cover.lean` + `Cover/Encoding.lean`.
Dependency switched to **dL-rel** (path), which transitively provides dL-lean
v0.1.0-DI (Stages 1-2) AND `RFormula.encoding_correct` (Stage 3 bridge).

## What is verified (pure core — axioms: standard three only)

| Piece | Theorem | Cites |
|---|---|---|
| Search graph / `Config` / `Covered` (all-successors, budget-indexed) | (structures) | — |
| Right-response reachability | `RightReach` (evolve / jump) | — |
| **Finiteness** (budget-neutral-cycle rejection) | `cover_budget_decreases` : every step `B−weight < B` (needs `0 < weight`) | `Nat.sub_lt` |
| **Composition = Theorem 3 core** | `cover_sound` : Covered ∧ cert ⟹ invariant preserved on every right response | **`flow_cert_sound`** (evolve, via `segPres`/`BoxLe`) + **`nonconn_sound`** (jump, via `pruneSound`) |
| flow field ⟹ cert | `segPreserves_of_flow` | `flow_cert_sound` |
| prune field ⟹ cert | `prune_of_nonconn` | `nonconn_sound` |
| **Global ∀∃ encoding** | `theorem3_encoded` : Z3 UNSAT on encoded `¬(ϕ_inv→[|L*,R*⟩⟩ϕ_inv)` ⟹ `rvalid` | **dL-rel `encoding_correct_exists`** |

`cover_sound` proof: induction on `RightReach`. `evolve` preserves `g≤0` by the flow
`BoxLe` (time-unbounded — matches "forward invariance is time-unbounded"); `jump` on an
enabled edge can't be pruned (`nonconn_sound`: pruned guard unreachable), so its target
is a retained successor `Covered.cover` guarantees is covered; strictly smaller budget.
All-successors ⟹ existential = the paper's ∀∃.

## Trust boundary

`cover_sound` / `theorem3_encoded` / finiteness: **standard three only** (pure verified
logic — no new leaf). IO connectors `segPreserves_certified` / `prune_certified`:
standard three **+ `z3_unsat_sound`** — the whole trust story: local certificates
(Z3-backed, DI-cited) composed by a proven, finite cover into the global ∀∃ invariant
(`encoding_correct`-bridged). No subtangency axiom.

## Soundness discipline carried forward

Segments certify via Stage-1 route A / Stage-2 route B (sound). The Stage-2 closed-guard
retention shifts work here: where the barrier couldn't prune a closed `x≥c` edge, the
cover must **cover** that retained successor (sound, different route) — `RightReach.jump`
follows every enabled edge, and `cover_sound` requires all retained successors covered.
A benchmark needing closed-guard *pruning* that the cover can't absorb would signal a
dL-lean strict/open-DI extension (`g<0` preserved) — flagged, not pre-built.

## Verified core complete

All three certificates (flow, non-connection, cover) + composition are mechanized.
Parser-ready structures: `RMode`/`REdge`/`SearchGraph` (dynamics `ODESystem`, guards
`Formula`, budget `ℕ`).

---

# Stage 4: the end-to-end runner + 46-benchmark parity

`lake exe relcert <input.txt>` parses a benchmark, discharges the verified strict flow
query per sync pair with Z3, and runs the multi-segment all-successors cover.

- **`Parse.lean`** — trusted IO parser: INI sections + infix/`smt2:` expressions →
  string-keyed model IR (`PProblem`). Parse failure ⟹ reported unparsed, never certified.
- **`Run.lean`** — lowers a sync pair `(qL,qR,λ)` into the verified `flowQueryStrict`
  (pinned to `lieDeriv` via the `Smt` IR bridge), emits SMT-LIB, Z3. The flow domain
  conjoins **both mode guards** (a successor guard can push the invariant boundary
  outside the reachable box ⟹ vacuous, sound certification). Cover = `dfsCover`: the
  multi-segment `Covered` relation run with cached flow checks (budget `εR/λ` per
  segment, all retained successors + self-loop, fuel-bounded by `⌈εL/δL⌉`).
- **`flow_cert_sound_strict`** (added, axiom-clean) — the strict-boundary flow cert
  (`DI_strict`) the runner relies on; route-A `flow_cert_sound` can't see offset
  invariants (`g=L−R−d`, Lie<0 only *on* the boundary).

## Parity (see `PARITY.md`)

**Lean 22/46 VERIFIED** (Python 46/46). Every Lean `VERIFIED` is **sound** — segments by
`flow_cert_sound_strict`, composed by `cover_sound`; Z3 UNSAT the only trusted leaf.
By category: A 18/22, B 1/1, C 2/14, D 1/3, E 0/3, F 0/3. The 24 non-verified `decline`
(sound one-sided): coupled/quadratic/nonlinear invariants (C/E/F) — the runner's `invToG`
lowers only the primary offset component; a few A need a finer λ grid; one Z3 timeout.
Completeness gaps, never unsound claims. Next completeness step: full multi-conjunct
`invToG` + finer λ search.

**Whole project complete:** verified core (3 certificates + cover/Theorem 3, all
axiom-clean bar `z3_unsat_sound`) + runnable end-to-end tool with measured parity.

---

# Stage 5: hardened oracle (honesty boundary, determinism, in-process API, coverage, tests)

Turns the tool into foundational oracle tooling for invariant synthesis. **No verified-core
proof changes** — `#print axioms` on the core is byte-identical before/after (checked).

## P1 — honesty boundary + determinism (`Z3.lean`, `OracleAPI.lean`)

Three never-conflated outcomes: `CERTIFIED` (verified core UNSAT via a sound route),
`DECLINED` (all queries definitive `sat`/`unsat`, no cover — sound incompleteness),
`ERROR` (any harness/solver/env failure — unlowerable invariant, Z3 missing/crash/EOF,
malformed SMT, `unknown`/timeout). `error` can never masquerade as a verdict:
`certified` is only ever produced by real `unsat`; an `unknown`/process failure taints
only routes it touches and surfaces as `error` when a covering route needed it.

Hermetic + deterministic: Z3 binary is **pinned** (`RELCERT_Z3` or fixed absolute paths,
never PATH-resolved at spawn); a **persistent `z3 -in`** session with `(reset)` +
per-query `:timeout` + an `(echo)` **sentinel** that resynchronizes the pipe each call.
The sentinel fixed a real non-determinism bug (pipe desync shifting verdicts) the
determinism test caught. Cross-run + same-session verdicts are stable.

## P2 — oracle API + warm Z3

`RelCertifier.Oracle.certify : Z3Session → PProblem → IO Outcome` — the in-process entry
synthesis links directly (no per-call `lake exe` spawn). One warm session serves all
queries. **Measured warm per-call (45 fast benchmarks): mean 68 ms, median 32 ms,
p90 167 ms, max 230 ms** — dominated by the Z3 solve, not process/plumbing (all 45 in
~3 s total on one warm session). `certifyFile : Z3Config → String → IO Outcome` and the
CLI keep the file path. Timeout is `RELCERT_Z3_TIMEOUT` (default 10 s).

One pathological outlier, `rover3tier_rung12` (a large multi-tier DECLINE), issues
thousands of solver calls in the exhaustive all-successors search and takes minutes — the
one benchmark that would want a deterministic query-budget bound (future; the caller can
lower `RELCERT_Z3_TIMEOUT` or cap query count).

## P3 — broadened `invComponents` (multi-conjunct / quadratic / product)

Each `≤/<` atom ↦ `g = lhs − rhs ≤ 0`; conjunctions lower **every** component
(per-component flow certificates, same domain — sound, core-backed by
`flow_cert_sound_strict`; coupled components correctly decline). `lowerE` handles `+ − ×`
and folds constant `/`, so quadratic (`x*x`), energy (`(L−R)²`) and product/bilinear
(`v*r`) invariants lower into `Term` and **flow through the unchanged `lieDeriv`/
`flowQueryStrict`** (confirmed: E/F benchmarks now certify). Parser tokenizes tightly-
packed operators so `1.125*e*e` / `v[l]-v[r]` parse. Unlowerable shapes (var/var division,
disjunction) ⟹ `error`, never a silent decline.

## P4 — trusted-layer tests (`relcert-test`, `Test.lean`)

Z3-layer (known SAT/UNSAT, malformed→error, closed session→error, missing binary→error),
parser (fixtures per construct, malformed→none), lowering (each shape→component count),
outcome-integrity (missing Z3 / unparsed / unreadable → ERROR), determinism +
oracle-consistency (same candidate ×8 on a warm session → identical verdict). All pass.

## Parity (`PARITY.md`) — deterministic, trustworthy

**23 CERTIFIED / 22 DECLINED / 0 ERROR across the 45 fast benchmarks** (cross-run diff = 0),
plus `rover3tier_rung12` (slow outlier). Every CERTIFIED is sound; DECLINED = the
boundary-only-unsound gap Python accepts and the oracle refuses. Quadratic/product/
multi-conjunct coverage now flows through the unchanged core (E/F benchmarks certify).

**Key correction from the determinism test:** a pre-sentinel run reported 29 CERTIFIED —
that count was *inflated by the pipe-desync bug* (a stale `unsat` read for a query that was
actually `sat`). The `(echo)` sentinel fix makes reads deterministic; the honest,
reproducible count is 23. The determinism test caught a real over-certification — exactly
the anti-flakiness guarantee synthesis needs.
