# Diagnosis of the 22 DECLINED — Cat-1 vs Cat-2

The oracle declines 22 of 46 (soundly). Splitting them into **Cat-1** (true invariant,
soundly unprovable — oracle incompleteness) vs **Cat-2** (actually false — Python
certified a falsehood via its boundary-only check).

## Headline

**Cat-2 = 0. Cat-1 = 22.** Contrary to the working hypothesis, **Python certified NO
falsehoods** in the declined set. Every declined invariant is genuinely true; every
component has a **regular boundary** (or an irregular point that is a harmless
equilibrium), so Python's boundary-only Nagumo check is *sound here*. The declines are
pure incompleteness: dL-lean lacks the sound theorem for "ġ ≤ 0 on a regular boundary ⟹
invariance" (`DI_nonstrict_boundary` / Nagumo for regular/polynomial boundaries).

The fix is therefore **all Path A** (mechanize `DI_nonstrict_boundary`); **no Path B**
(there is no false invariant to strengthen).

## Precise framing — do not overclaim

This is *not* "Python is wrong on the suite." Python's 46/46 are, as far as this diagnosis
shows, all **correct answers**. The accurate statement has three parts:

1. **Python's flow criterion is unsound as a general rule** — proven, independent of any
   benchmark: `nonstrict_boundary_insufficient` (the `t²` counterexample). `ẋ ≤ 0` on
   `{g=0}` alone does *not* imply invariance.
2. **On this suite it produces only correct certifications** — because the pathology the
   criterion is blind to (an **irregular boundary with outward flow**) never occurs here:
   every boundary is regular, and the one irregular point (`rung3_6to8`'s origin) is a
   **harmless equilibrium** (`∇=0`, but the flow is stationary — no escape). So the
   criterion is unsound-in-general but valid-on-every-benchmark.
3. **The oracle-relevant risk is not the current benchmarks — it is the regime.** Python's
   soundness here rests on a property — boundary regularity — that **the tool never
   checks**. Hand-crafted benchmarks stay inside the regular regime; **synthesis-generated
   candidates need not.** Synthesis explores invariant space freely and can propose a
   candidate with an irregular boundary and outward flow (exactly the `t²` shape), and
   Python would certify it **falsely**. The verified oracle is safe precisely because it
   never relies on regularity it has not checked — it declines rather than assume.

So the difference between Python's 46 and the oracle's 24 is **not 22 falsehoods Python
accepted** — it is 22 **true** invariants Python certified via an unsound-but-here-valid
shortcut, which the oracle soundly declines because it refuses to depend on the unchecked
regularity. That is the real argument for the sound oracle: Python is unsound in exactly
the regime synthesis will explore.

## Template 1 — `rover_dof_terrain_rung1` → **Cat-1 (confirmed)**

Invariant `v_L ≤ v_R ∧ s_L ≤ s_R + 0.2`. Both sides share `v' = 3(0.30 − v)`, so
`ġ(v_L−v_R) = 3(v_R − v_L) = −3·(v_L−v_R)` — a **contraction**: `g = g₀e^{−3t}`, `g ≤ 0`
preserved. On the boundary `{v_L=v_R}`, `ġ = 0`; the boundary is regular (`∇=(1,−1)≠0`).
`DI_strict` needs `ġ < 0` (fails at the `v=0.30` equilibrium where `ġ=0`);
`DI_nonstrict_domain` needs `ġ ≤ 0` off-boundary (fails: pick `v_L` small, `v_R` large).
True invariant, neither sound route in dL-lean proves it. **Cat-1.**

## Template 2 — `story3_rollover_ladder_rung_a` → **Cat-1 (hypothesis refuted)**

Hypothesized Cat-2 (false). **It is actually TRUE.** Three components:
- `v_L ≤ v_R`, `s_L ≤ s_R + 0.2` — matched dynamics ⟹ contraction/marginal (as above).
- `1.125 e_L² + 0.25 e_L r_L + 0.156 r_L² ≤ 0.33` — left-only rollover energy for
  `e'=r, r'=−4e−4r`. Its Lie form `AᵀQ+QA` is **negative definite** (`ġ ≈ −e² − r² < 0`);
  simulation from every boundary start keeps the energy `≤ 0.33`. A **strict Lyapunov
  barrier** — genuinely true, and would certify via `DI_strict` on its own.

Numerical co-evolution under the existential right response (right copies the left — same
modes/dynamics exist on both sides), from a valid initial state:
`worst g1 = +0.00000, g2 = −0.20000, g3 = −0.00058` — **invariant preserved.** Some right
response keeps it, so the ∀-left ∃-right invariant is **true. Python did not certify a
falsehood here.** The decline is the marginal `v`/`s` contraction (Cat-1). **Cat-1.**

## The one irregular-boundary candidate — `refinement_ladder_rover_rung3_6to8` → **Cat-1**

The only component with an irregular boundary (the t²-unsoundness shape):
`psi_R² ≤ psi_L² + 3·ω_psi_L²`. Left `psi'=ω, ω'=−psi−2ω` (2nd-order), right `psi'=−psi`.
`ġ = −2λ·psi_R² + 4·psi_L·ω_L + 12·ω_L²`; on the boundary this quadratic form is
negative-semidefinite for **λ ≥ 2.16** (`3λ² − 6λ − 1 ≥ 0`). Python's λ-search finds such
a λ ⟹ sound. The irregular point (`psi_R=psi_L=ω=0`, where `∇=0` and `g=0`) is a **harmless
equilibrium** (all derivatives zero) — no escape through it. Simulation: escapes at λ<2.16,
**holds exactly for λ≥2.16** (worst g = 0.00000). True invariant. **Cat-1.**

## All 22 — classification

Every invariant is built from components that are one of:
1. **Linear relational** (`v_L≤v_R`, `s_L≤s_R+d`, `px/vx/y`, and `a≤b ∧ b≤a` equalities) —
   `∇=(±1,∓1)≠0`, regular; matched dynamics ⟹ contraction/marginal (`ġ=0` on boundary).
2. **Convex-quadratic Lyapunov** energies (`psi²+ω²≤c`, the rollover PSD form, the
   `2(ψL−ψR)²+2(ψL−ψR)ω+ω²` relational-error form) — boundary regular, strictly decreasing.
3. **Regular bilinear** (`v·r≤1`, `−1≤v·r`) — `∇=(r,v)≠0` on those level sets.
4. **Irregular-but-equilibrium** (`psi_R²≤psi_L²+3ω²`, rung3) — irregular point is a fixed
   point, no escape.

| # | benchmark | cat | Cat | why declined (all sound incompleteness) |
|---|---|---|---|---|
| 1 | endurance_gain_M1 | A | 1 | s-gap `s_L≤s_R+1`, matched ⟹ `ġ=0` marginal |
| 2 | endurance_orderlift_1to2 | A | 1 | s-gap marginal |
| 3 | endurance_orderlift_2to3 | A | 1 | s-gap marginal |
| 4 | refinement_ladder_rover_rung1_2to3 | C | 1 | v-contraction + s-gap marginal |
| 5 | refinement_ladder_rover_rung2_3to6 | C | 1 | v/s + psi equality (matched, marginal) |
| 6 | refinement_ladder_rover_rung2c_6dof | C | 1 | full-equality (v=,s=,psi=,θ=) matched, marginal |
| 7 | refinement_ladder_rover_rung3_6to8 | E | 1 | irregular-boundary psi energy; equilibrium, true for λ≥2.16 |
| 8 | refinement_ladder_rover_rung4_8to12 | C | 1 | v-contraction + s-gap marginal |
| 9 | rover3_M1 | C | 1 | px-gap + vx-contraction marginal |
| 10 | rover_attitude_cone_12dof | E | 1 | left convex attitude energy + v/s marginal |
| 11 | rover_dof_terrain_rung1 | C | 1 | template 1 (v-contraction, marginal) |
| 12 | rover_dof_terrain_rung2 | C | 1 | v-contraction + s-gap marginal |
| 13 | rover_dof_terrain_rung3 | C | 1 | v-contraction + s-gap marginal |
| 14 | rover_dof_terrain_rung3_8d | C | 1 | v-contraction + s-gap marginal |
| 15 | rover_terrain_M1 | A | 1 | s-gap `s_L≤s_R+1` marginal |
| 16 | story1_attdist_rung_a_6to8 | D | 1 | relational-error PSD energy + v marginal |
| 17 | story1_attdist_rung_b_12dof | D | 1 | relational-error PSD energy (rates) + v marginal |
| 18 | story2_lateral_rung_a_8dof | C | 1 | v/y/s + psi,θ equality matched, marginal |
| 19 | story2_lateral_rung_b_12dof | C | 1 | as 18 + second lateral gap, marginal |
| 20 | story3_rollover_base_12dof | F | 1 | rollover energy (strict) + v/s marginal + bilinear |
| 21 | story3_rollover_ladder_rung_a | F | 1 | template 2 (rollover strict + v/s marginal) |
| 22 | story3_rollover_ladder_rung_b | F | 1 | relational-error PSD energy + v marginal |

**Cat-1: 22 / 22. Cat-2: 0 / 22.**

## Why the oracle declines them (the three faces of Cat-1)

1. **Marginal contraction** — matched dynamics give `ġ = 0` on a regular boundary
   (`v_L=v_R`, matched `s`, equilibria). `DI_strict` needs `< 0`; `DI_nonstrict_domain`
   needs `≤ 0` on the *whole* domain (fails off-boundary). The sound theorem is
   `DI_nonstrict_boundary`: `ġ ≤ 0` on a **regular** `{g=0}` ⟹ invariance. Missing from
   dL-lean; this is the natural contraction invariant synthesis will generate.
2. **Coupling** — components like `s_L≤s_R+d` need `v_L≤v_R` to hold; the per-component
   check on the full domain fails. Sound fix: invariant-relative domain (assume the other
   components) — still needs the boundary theorem.
3. **λ-coarseness** — rung3 needs `λ≥2.16`; the `{λmin, εR/εL, λmax}` grid can miss it. A
   finer search recovers the definite verdict but the marginal `ġ=0` still needs (1).

## Recommendation

- **No Path B is warranted** — there is no false benchmark to re-strengthen; every
  `−ε` margin would certify a *surrogate* of an already-true invariant, masking the real
  gap.
- **Path A is the whole fix and is now high priority**: mechanize `DI_nonstrict_boundary`
  (Nagumo for regular/polynomial boundaries) in dL-lean, so the oracle certifies the
  natural contraction/energy invariants soundly instead of declining them. This is exactly
  the class synthesis produces.

Path A is only a *usable oracle capability* (not a paper theorem) if two things are in the
mechanization — see `PATH_A_SCOPE.md` for the full scoping:

1. **A checkable regularity predicate.** "Regular boundary" must be dischargeable by Z3, so
   `flow_cert_sound_nonstrict` verifies it per-candidate instead of assuming it. Candidate:
   `∀x. g(x)=0 ∧ domain(x) → ∇g(x) ≠ 0`, i.e. the query `domain ∧ g=0 ∧ (⋀ᵢ ∂g/∂xᵢ = 0)`
   is UNSAT (all partials vanish nowhere on the boundary) — a polynomial Z3-NRA query
   built from the same `tderiv` the flow certificate already uses.
2. **The irregular-but-equilibrium case.** `rung3_6to8`'s origin has `∇g=0` on `{g=0}`, so
   the strict regularity query is SAT — yet the point is harmless because the field is
   stationary there. The theorem must admit "regular *except* at equilibria of the field,"
   with an equilibrium discharged by its own checkable query (`the field = 0` at every
   boundary point where `∇g=0`). The gate below states how.
