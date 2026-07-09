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

Not in this stage: non-connection barrier (Stage 2); cover/composition + Theorem 3 +
`encoding_correct` (Stage 3).
