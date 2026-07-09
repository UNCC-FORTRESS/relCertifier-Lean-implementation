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

Not in these stages: cover/composition + Theorem 3 + `encoding_correct` (Stage 3);
end-to-end benchmark runner + 46-case parity (post-Stage-3).
