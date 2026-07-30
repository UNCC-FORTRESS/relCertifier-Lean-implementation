> **SUPERSEDED (2026-07).** This catalog addresses the early `tooling_sound` chain.
> The current per-benchmark guarantees are the settling battery (46), the throughout
> batteries (33 + 13 cut-lifted), and the modal flagship — see the README's
> "Theorem families" and docs/ROADMAP.md. Kept for the historical record.

# Benchmark instantiability against the end-to-end theorem

This catalogs how each suite benchmark relates to the **`tooling_sound`** meta-theorem (GAP 3 — the
∀∃ refinement modality over the *actual* programs `L, R`, via `graphOf`). The suite is
`benchmarks/suite_uniform/` (the uniform-evolution settling form — see README); the table below
applies unchanged, since the uniform restructuring altered only guards and evolution domains,
never the dynamics, the mode structure, or the verdicts (46/47 in both forms). (Later, the
cascade-coordinate program rewrote the second-order blocks of four benchmarks — and, for
ladder coherence, the matching lower-rung L sides — in their eigen-cascade charts: a linear
bijection of the same dynamics with the relational invariants substituted exactly, so the
table below is likewise unaffected; see docs/history/DEVELOPMENT-ARC.md.)

Scope note: this document addresses the **`tooling_sound`** chain and its `HExistSeg` boundary.
The newer landing/uniform chain (`theorem3_faithful_landing_clocked_uniform`,
`theorem3_faithful_settling` — README "The landing chain, intuitively";
`docs/history/DEVELOPMENT-ARC.md`) replaces that side-condition entirely: its per-segment obligation is
duration-bounded staying (`WellFormedFlowB` / `GuardSettlingB`), discharged by construction for
the settling classes — so the `∀ν HExistSeg` wall below is a boundary of the older chain, not of
the current canonical one.

It is the per-benchmark companion to the two concrete demonstrations:

| representative (`RelCertifier/GapThreeRoverTooling.lean`) | `HExistSeg` | carried boundaries |
|---|---|---|
| `rover_tooling_sound` | **carried** (parametric) | Z3 leaf, emit, HExistSeg-shape |
| `rover_tooling_sound_full` | **discharged** (`hExistSeg_affine_tt`, global existence at `domR = ⊤`) | Z3 leaf, emit |

Both are non-vacuous (freshness discharged via the `Aux` slots `mv = Av 1` / `tg = Av 0`; `hd`/`hddF`
disjointness hold by side split — contrast `ProbeMvHd.probe_hd_false`, where the frozen-`mv` route made
`hd` false). Axioms `[propext, Classical.choice, Quot.sound]`; `z3_unsat_sound` enters only through a
supplied concrete `cert`.

## The three boundaries no instantiation closes

1. **Z3 leaf** (`z3_unsat_sound`) — trusted, by design, at `cert`/`cert_repo` construction. Enters as
   a parametric hypothesis (`CoverCert`); the modality is sound *modulo* this one leaf.
2. **Transcription** (benchmark `input.txt` → Lean `HybridAut`) — the trust point no level closes
   without a **verified parser** (the nameable follow-on for file-level proof-linkage).
3. **`HExistSeg`-shape** — the per-segment duration-existence side-condition. See the finding below:
   at bounded `domR` it is *carried*; at `domR = ⊤` it is *dischargeable by global existence* (done
   for the affine field, extendable to the others — all suite fields are globally solvable).

## Finding — the `∀ν HExistSeg` wall

`hExist_from_rover` / `hExist_from_cubic` (the *banked field-shape* lemmas) prove `HExistSeg` at **one
region-admissible `ν`** — exactly what the single-flow leaf `segment_faModal` consumes (`hExist` at the
reachable invariant state). But `graphOfSide` / `EmitSegs` carry **`∀ν HExistSeg`**, which is *stronger*
and is **false for a bounded `domR`**: an out-of-box `ν` (e.g. velocity `> vmax`) is frozen by the left
run into `ΦR 0`, violating `domR` at `t = 0`. So the banked region lemmas **cannot** discharge
`tooling_sound`'s `∀ν HExistSeg`. The dischargeable route is `domR = ⊤` + **global existence**
(field-shape-independent) — a sound ∃-side over-approximation. Consequence: a benchmark having a
"banked" field shape (decay/cubic) does **not** make its `tooling_sound` `HExistSeg` easier; the ∀ν
discharge is by global existence regardless of shape.

## Per-benchmark table

Columns: **field** = right (∃-side) ODE shape; **R×L** = right-mode count × left-mode count
(`R≥2` = multi-flow, `L≥2` = multi-left-mode); **GAP** = maximal structural feature exercised
(all route through GAP 3 / `graphOf`); **glob** = right field globally solvable ⇒ `HExistSeg`
dischargeable at `domR = ⊤`; **status** = tool verdict.

| benchmark | field | R×L | GAP | glob | status |
|---|---|---|---|---|---|
| arm_chain_rung1 | affine | 2×3 | 2/3 | ✓ | CERTIFIED |
| arm_chain_rung2 | affine | 3×4 | 2/3 | ✓ | CERTIFIED |
| arm_chain_rung3 | affine | 4×2 | 2/3 | ✓ | CERTIFIED |
| arm_fidelity_high | affine | 4×2 | 2/3 | ✓ | CERTIFIED |
| arm_fidelity_low | affine | 2×2 | 2/3 | ✓ | CERTIFIED |
| arm_fidelity_mid | affine | 3×2 | 2/3 | ✓ | CERTIFIED |
| arm_refinement | affine | 2×2 | 2/3 | ✓ | CERTIFIED |
| attitude_rate | coupled-linear | 2×1 | 1/3 | ✓ | CERTIFIED |
| endurance_gain_M1 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| endurance_orderlift_1to2 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| endurance_orderlift_2to3 | 2nd-order damped | 3×3 | 2/3 | ✓ | CERTIFIED |
| match_multi_eps | decay | 2×2 | 2/3 | ✓ | CERTIFIED |
| match_multi_rate | decay | 1×4 | 2/3 (+reset) | ✓ | CERTIFIED |
| plant_fan_high | affine | 4×2 | 2/3 | ✓ | CERTIFIED |
| plant_fan_low | affine | 2×2 | 2/3 | ✓ | CERTIFIED |
| plant_fan_mid | affine | 3×2 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung1_2to3 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung2_3to6 | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung2_6dof | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung2b_6dof | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung2c_6dof | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung3_6to8 | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| refinement_ladder_rover_rung4_8to12 | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| robot_braking | decay | 3×1 | 1/3 | ✓ | CERTIFIED |
| rover3_M1 | affine | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover3tier_M1 | decay | 2×2 | 2/3 | ✓ | CERTIFIED |
| rover3tier_rung12 | affine | 2×2 | 2/3 | ✓ | CERTIFIED |
| rover_4d_box | decay | 2×1 | 1/3 | ✓ | CERTIFIED |
| rover_attitude_cone_12dof | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_coupled | affine | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_dof_terrain_rung1 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_dof_terrain_rung2 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_dof_terrain_rung3 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_dof_terrain_rung3_8d | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_drag | quadratic drag | 1×1 | 1/3 | ✓ | CERTIFIED |
| **rover_position** | **affine** | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_terrain_M1 | decay | 3×3 | 2/3 | ✓ | CERTIFIED |
| rover_tier_r1 | affine | 1×1 | 1/3 | ✓ | CERTIFIED |
| shield_unreachable | decay + shield | 3×1 | — | ✓ | **ERROR** |
| story1_attdist_rung_a_6to8 | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| story1_attdist_rung_b_12dof | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| story2_lateral_rung_a_8dof | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| story2_lateral_rung_b_12dof | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| story3_rollover_base_12dof | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| story3_rollover_ladder_rung_a | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| story3_rollover_ladder_rung_b | cubic | 3×3 | 2/3 | ✓ | CERTIFIED |
| watertank | decay | 3×3 | 2/3 | ✓ | CERTIFIED |

Field-shape distribution: **affine** 15, **decay** 17, **cubic** 12, **other** 3 (attitude_rate,
endurance_orderlift_2to3, rover_drag). `shield_unreachable` is decay-shaped but ERROR.

## Instantiability status

- **Structural discharge is field-independent.** The freshness (`mv`/`tg` in `Aux`), the disjointness
  `hd`/`hddF` (side split: left = `Lv`, right = `Rv ∪ Aux`), `graphOf`, and `RightProjAlign` (derived,
  Task 2) hold for *any* `Lv`/`Rv`-sided fields. So **every CERTIFIED benchmark is Level-A instantiable
  into `tooling_sound`** with `cert`/`EmitSegs` parametric (Z3 leaf + emit) — `HExistSeg` carried.
- **`HExistSeg` dischargeable at `domR = ⊤`** for every benchmark (all right fields are globally
  solvable: affine/decay are linear; the cubic `s' = v(1−0.5ψ²…)` has `v,ψ` decaying linearly so `s`
  grows sub-linearly; drag is dissipative; the 2nd-order forms are linear-damped). **Demonstrated for
  the affine field** (`hExistSeg_affine_tt` → `rover_tooling_sound_full`); the decay/cubic/other
  dischargers follow the same construct-the-solution pattern (not yet mechanized).
- **`rover_position`** (highlighted) is the benchmark whose **shape** the two representatives
  instantiate (affine right field); the demonstration is at a single-mode instance of that shape, not
  the full 3×3 mode structure (which needs the family assembly, structurally field-shared).
- **`shield_unreachable` — honestly declined.** ERROR: the cover does not close (inconclusive Z3), so
  there is no `cert` to supply. Not forced. This is *tool behavior* (a refusal to guess), not a
  soundness gap.

There is no DECLINED benchmark in the current suite: `endurance_orderlift_2to3` (formerly method-scope
DECLINED) was strengthened and folded in as CERTIFIED. (Verdicts re-verified on
`benchmarks/suite_uniform/` after the uniform-evolution restructuring: identical — 46 CERTIFIED,
`shield_unreachable` ERROR.)
