# Full-suite field-shape split (remaining-work map)

Loaded from `relCertifier-src/relCertifier.v1/examples/` — **46 benchmarks** (BENCHMARKS.md: all
46 VERIFIED) + 1 discriminator (`shield_unreachable`, negative control) = 47 inputs under
`benchmarks/suite/`. Format identical to the 4 pre-existing `restated/` ones **except the
`[relational_invariant]` section** (restated/strengthened for Lean certification — per-benchmark
work, separate from the field-shape classification below, which uses the ODEs only).

## RESOLVED — two metrics, both correct (adjudicated by inspection)

Python (degree over the **whole system**, L+R) and the Lean-side classifier (degree over **R only**)
disagreed by 7. Resolved: they measure different things, both right.

| metric | nonlinear count | breakdown |
|---|---|---|
| **whole-system** max degree (L,R) | **20** | 2 const + 24 linear + 1 quadratic (`rover_drag`) + 19 cubic |
| **R-only** degree (what `hExist`/`picard_isPL_of` sees) | **13** | 10 const + 23 linear + 1 quad + 12 cubic |

**The 7-benchmark gap = cubic-L, affine-R** (eyeball-confirmed): `refinement_ladder_rover_rung1_2to3`,
`rung2_6dof`, `rung2b_6dof`, `rover_dof_terrain_rung1`, `rung2`, `rung3`, `rung3_8d`. Each: L (deployed)
`s'=v(1−0.5ψ²−…)` CUBIC; R (reasoning, lifted) `s'=v` AFFINE.

**Adjudication for build order**: `hExist` constructs the **right** witness ⟹ the **R-field** is the
metric governing `picard_isPL_of` soundness. For these 7, R is genuinely affine ⟹ `picard_isPL_of`
(global Lipschitz) is **SOUND**. The left being cubic is irrelevant to right-witness existence (the
left run is *given* to `hExist`, not constructed); the cubic L enters only the joint flow-cert Lie,
handled by **Z3-NRA** (nonlinear-polynomial), not by `picard_isPL_of`. So **no mis-discharge**: the
degree that governs picard soundness (R) is confirmed affine for the 7.

**Net for the existence lemma**: the compactness-subcover uniform-`r₀` lemma is needed by the
**13 nonlinear-R** benchmarks (`rover_drag` + the 12 cubic-R: `rung2_3to6`, `rung2c_6dof`,
`rung3_6to8`, `rung4_8to12`, `rover_attitude_cone_12dof`, `story1_a/b`, `story2_a/b`,
`story3_base/a/b`). `picard_isPL_of` is sound for the 33 affine-R (including the 7 cubic-L). Neither 0
nor 20 — **13**.

## ⚠️ CORRECTION — earlier "0 nonlinear" was a FALSE NEGATIVE

An earlier grep-based classifier missed **nested** products (`(* psi psi)` doubly-nested inside
`(* v (- 1 (* 0.5 (* psi psi))))`). A recursive s-expr **degree parser** finds the truth:

**13/46 benchmarks have NONLINEAR right-fields** — `s'=v(1−0.5ψ²−0.3θ²)` (degree-3 `v·ψ²`),
`vx'=0.05−0.3·vx²` (drag). These are **NOT globally Lipschitz**, so `picard_isPL_of`'s global route
**fails** for them — the **compactness-subcover uniform-`r₀` lemma is on the critical path** (needed
by 13, not 0). The nonlinear-existence analytic piece **exists**.

Nonlinear-R (13): refinement_ladder_rover_rung2_3to6, rung2c_6dof, rung3_6to8, rung4_8to12,
rover_attitude_cone_12dof, rover_drag, story1_attdist_rung_a_6to8, story1_attdist_rung_b_12dof,
story2_lateral_rung_a_8dof, story2_lateral_rung_b_12dof, story3_rollover_base_12dof,
story3_rollover_ladder_rung_a, story3_rollover_ladder_rung_b.

**Corrected split: 33/46 affine-R, 13/46 nonlinear-R.** (In many of the 13, the nonlinearity is only
on the LEFT — but in these 13 it is on the RIGHT, which is what `hExist` constructs.)

Note: the nonlinear fields ARE locally Lipschitz on the compact domain (polynomial, smooth) — so the
subcover lemma (finite cover of compact `domR`, min `r₀`) discharges their existence; and the
INVARIANCE still works (`s'=v(1−0.5ψ²−…)≤v≤v_max`, so `growth_bound_raw` with `M=v_max` still bounds
`s`; `ψ,θ,v` asymptotic via linear parts). **Only the existence-Lipschitz step changes for nonlinear.**

## Classification by Rsys field shape (STALE — assumed affine; see correction above)

| class | count | face lemma | status |
|---|---|---|---|
| **affine-rover** (`v'=k(c−v)` asymptotic + `s'=v` growing) | **17** | `asymptotic_invariance_raw` + `growth_bound_raw` | **discharged** (`hExist_rover`/`hExist_multi`) |
| **other-affine = const-drift** (`θ'=const`) | **10** | `growth_bound_raw`/`growth_lower_bound_raw` (M=const) | **covered by toolkit** — only instantiation |
| **coupled-affine** (chains + cross-coupling) | **19** | 2 new face families (below) | **pending** |
| **nonlinear** (`var·var`, squares) | **0** | compactness-subcover uniform `r₀` | **EMPTY — not exercised suite-wide** |

**Existing toolkit covers 27/46** (17 rover discharged + 10 const-drift needing only instantiation).

## The nonlinear residual is empty
Direct grep for `var·var`/squares over all 46 benchmarks' ODEs returns nothing. Every RHS is affine
(products are `const·var`; `λ` constant). **The compactness-subcover uniform-`r₀` lemma is needed by
0 benchmarks.** The nonlinear tail I flagged as the one genuinely-analytic residual **does not exist
in this suite** — `picard_isPL_of`'s global-Lipschitz route (affine ⟹ global Lipschitz) suffices
everywhere.

## The coupled-affine 19 — two new face families
- **chain / integrator (nested growth)** ~ `rover3_M1`, `rover3tier_rung12`, `rover_coupled`,
  `rover_position`, `rover_tier_r1`, … — double-integrators (`px'=vx`, `vx'=const`): `vx` grows
  linearly, so `px'=vx` needs a **time-varying** growth bound (`px' ≤ vx₀+ct` ⟹ `px` quadratic).
  Generalize `growth_bound_raw` to non-constant `M(t)`.
- **cross-coupled (Lyapunov)** ~ `attitude_rate` (`p'=…+0.05q`, `q'=…+0.05p`),
  `endurance_orderlift_2to3`, `story3_rollover_ladder_rung_b`, … — genuinely coupled linear
  subsystems (stable, eigenvalues negative): invariance via a **Lyapunov sublevel** (or eigencoord
  decouple), then `strict_invariance_raw`/`nonstrict_antitone_raw` on the Lyapunov function.
- **mixed** (9) — need both (cross-coupled subsystem + integrator chain + asymptotic coord).

## Remaining-work map (honest)
1. **Instantiate** the 17 rover + 10 const-drift (27/46) — mechanical (parser → `hfv`/`hfs`/`K`/`L`/params).
2. **Build 2 face families** for the coupled 19: `growth_bound_timevarying` (chains) +
   `lyapunov_invariance_raw` (cross-coupled). Both slot into the same field-general pipeline
   (existence/chaining/packaging unchanged — all affine).
3. **Nonlinear subcover**: not needed for this suite (0 benchmarks).
