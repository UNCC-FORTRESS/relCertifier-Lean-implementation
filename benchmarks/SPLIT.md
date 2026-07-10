# Full-suite field-shape split (remaining-work map)

Loaded from `relCertifier-src/relCertifier.v1/examples/` — **46 benchmarks** (BENCHMARKS.md: all
46 VERIFIED) + 1 discriminator (`shield_unreachable`, negative control) = 47 inputs under
`benchmarks/suite/`. Format identical to the 4 pre-existing `restated/` ones **except the
`[relational_invariant]` section** (restated/strengthened for Lean certification — per-benchmark
work, separate from the field-shape classification below, which uses the ODEs only).

## Classification by Rsys field shape (ODEs are affine throughout)

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
