/-
# Terrain-model data terms — the EXT 3/3b checker-accepted instances

Each `def <name>T : TerrainModel _` is the RIGHT side of an s-guarded terrain benchmark
(`benchmarks/suite_uniform/`), and each `example : decideWellFormedT <name>T = true := rfl`
is the kernel-checked well-formedness certificate: by `wellformed_sound_terrain`, the
instance plus its per-run Z3 certificates yields `GuardSettlingH` with the terrain guard map
— hence `theorem3_faithful_settling` — with no per-benchmark proof.

UNITS as in `SettlingInstances`: values ×1000, time ×den(dt), integer data throughout.
The v-band is the guard cap when declared, else the envelope band, with the equilibrium
inside it; the s-bands partition the track, terminal segment unbounded (the terminal-band
fix). The one-step landing chain is `shi + ghi·dt ≤ shi'` per declared successor — checked
in ℤ, discharged by `settling_terrain`. The nonlinear-s' family (EXT 3b) uses
`CoordShape.drivenDamp`: `s' = v(1 − Σ a·ψ²)` with contract-to-0 dampers and the per-damper
budget `a·B²·L ≤ 1`; damper coefficients are stored /10⁶ per the value scaling, and
`settling_terrain_damp` discharges it by monotonicity from the integrand bounds.

Out of grammar (honest skips): refinement_ladder_rover_rung4_8to12 and
story1_attdist_rung_b_12dof (SECOND-ORDER dampers `ψ' = ω, ω' = −ψ − 2ω` — critically
damped, the linear-coupled closed-form class), story3_rollover_ladder_rung_b (a coupled
`(e, r)` pair — same class).
-/
import RelCertifier.TerrainChecker

namespace RelCertifier

/-- `refinement_ladder_rover_rung1_2to3` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def refinement_ladder_rover_rung1_2to3T : TerrainModel 2 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT refinement_ladder_rover_rung1_2to3T = true := rfl

/-- `rover_dof_terrain_rung1` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover_dof_terrain_rung1T : TerrainModel 3 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT rover_dof_terrain_rung1T = true := rfl

/-- `rover_dof_terrain_rung2` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover_dof_terrain_rung2T : TerrainModel 6 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT rover_dof_terrain_rung2T = true := rfl

/-- `rover_dof_terrain_rung3` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover_dof_terrain_rung3T : TerrainModel 12 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT rover_dof_terrain_rung3T = true := rfl

/-- `rover_dof_terrain_rung3_8d` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover_dof_terrain_rung3_8dT : TerrainModel 8 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.driven 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT rover_dof_terrain_rung3_8dT = true := rfl

/-- `refinement_ladder_rover_rung2_3to6` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def refinement_ladder_rover_rung2_3to6T : TerrainModel 6 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-50 : ℤ), hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT refinement_ladder_rover_rung2_3to6T = true := rfl

/-- `refinement_ladder_rover_rung2c_6dof` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def refinement_ladder_rover_rung2c_6dofT : TerrainModel 6 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-50 : ℤ), hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT refinement_ladder_rover_rung2c_6dofT = true := rfl

/-- `refinement_ladder_rover_rung3_6to8` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def refinement_ladder_rover_rung3_6to8T : TerrainModel 8 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT refinement_ladder_rover_rung3_6to8T = true := rfl

/-- `rover_attitude_cone_12dof` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def rover_attitude_cone_12dofT : TerrainModel 12 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-700 : ℤ), hi := some 150 }, { lo := some (-300 : ℤ), hi := some 400 }, { lo := some (-700 : ℤ), hi := some 150 }, { lo := some (-300 : ℤ), hi := some 400 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT rover_attitude_cone_12dofT = true := rfl

/-- `story1_attdist_rung_a_6to8` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def story1_attdist_rung_a_6to8T : TerrainModel 8 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-50 : ℤ), hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT story1_attdist_rung_a_6to8T = true := rfl

/-- `story2_lateral_rung_a_8dof` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def story2_lateral_rung_a_8dofT : TerrainModel 8 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-50 : ℤ), hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some 0, hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 150 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT story2_lateral_rung_a_8dofT = true := rfl

/-- `story2_lateral_rung_b_12dof` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def story2_lateral_rung_b_12dofT : TerrainModel 12 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (3, 3, 10000000)], CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-50 : ℤ), hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some 0, hi := some 150 }, { lo := some 0, hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 150 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT story2_lateral_rung_b_12dofT = true := rfl

/-- `story3_rollover_base_12dof` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def story3_rollover_base_12dofT : TerrainModel 12 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1500 : ℤ), hi := some 150 }, { lo := some (-1520 : ℤ), hi := some 1620 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT story3_rollover_base_12dofT = true := rfl

/-- `story3_rollover_ladder_rung_a` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
damper coefficients stored /10⁶ per the value scaling). -/
def story3_rollover_ladder_rung_aT : TerrainModel 12 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 3 300, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.contract 3 500, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.contract 3 650, CoordShape.drivenDamp 0 [(2, 1, 2000000), (4, 3, 10000000)], CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.contract 1 0, CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 650, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1500 : ℤ), hi := some 150 }, { lo := some (-1520 : ℤ), hi := some 1620 }, { lo := some (-500 : ℤ), hi := some 150 }, { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 600 },
      { sc := 1, slo := 600, shi := some 1400 },
      { sc := 1, slo := 1400, shi := none } ] }

example : decideWellFormedT story3_rollover_ladder_rung_aT = true := rfl

/-- `refinement_ladder_rover_rung2_6dof` (R side; units: v ×1000, s ×3000 (the driven
integrator carries the time scale), time ×3; dt = ε_R/λ at λ = 3 — the declared λ-range
starts at 1.001, and λ = 3 makes the scaled contract gain 3/3 = 1 integral). -/
def refinement_ladder_rover_rung2_6dofT : TerrainModel 4 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 1 300, CoordShape.driven 0,
          CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 1 500, CoordShape.driven 0,
          CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 1 650, CoordShape.driven 0,
          CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-150 : ℤ), hi := none },
        { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 1800 },
      { sc := 1, slo := 1800, shi := some 4200 },
      { sc := 1, slo := 4200, shi := none } ] }

example : decideWellFormedT refinement_ladder_rover_rung2_6dofT = true := rfl

/-- `refinement_ladder_rover_rung2b_6dof` (R side; units: v ×1000, s ×3000, time ×3;
dt = ε_R/λ at λ = 3, as in rung2_6dof). -/
def refinement_ladder_rover_rung2b_6dofT : TerrainModel 6 :=
  { core :=
    { modes :=
    [
      { shapes := ![CoordShape.contract 1 300, CoordShape.driven 0, CoordShape.frozen,
          CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [1] },
      { shapes := ![CoordShape.contract 1 500, CoordShape.driven 0, CoordShape.frozen,
          CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [2] },
      { shapes := ![CoordShape.contract 1 650, CoordShape.driven 0, CoordShape.frozen,
          CoordShape.frozen, CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 800, succs := [] } ]
      env := ![{ lo := some 0, hi := some 800 }, { lo := some (-150 : ℤ), hi := none },
        { lo := some (-500 : ℤ), hi := some 600 }, { lo := some (-500 : ℤ), hi := some 600 },
        { lo := some (-1000 : ℤ), hi := some 1100 }, { lo := some (-500 : ℤ), hi := some 600 }]
      dtQ := 1 }
    sbands :=
    [
      { sc := 1, slo := 0, shi := some 1800 },
      { sc := 1, slo := 1800, shi := some 4200 },
      { sc := 1, slo := 4200, shi := none } ] }

example : decideWellFormedT refinement_ladder_rover_rung2b_6dofT = true := rfl

end RelCertifier
