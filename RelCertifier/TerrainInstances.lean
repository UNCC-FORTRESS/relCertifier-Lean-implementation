/-
# Terrain-model data terms — the EXT 3 checker-accepted instances

Each `def <name>T : TerrainModel _` is the RIGHT side of an s-guarded terrain benchmark
(`benchmarks/suite_uniform/`), and each `example : decideWellFormedT <name>T = true := rfl`
is the kernel-checked well-formedness certificate: by `wellformed_sound_terrain`, the
instance plus its per-run Z3 certificates yields `GuardSettlingH` with the terrain guard map
— hence `theorem3_faithful_settling` — with no per-benchmark proof.

UNITS as in `SettlingInstances`: values ×1000, time ×den(dt), integer data throughout.
The v-band is `[envelope-lo, c]` (cap at the equilibrium); the s-bands partition the track,
terminal segment unbounded (the terminal-band fix). The guards' one-step landing chain is
`shi + c·dt ≤ shi'` per declared successor — checked in ℤ, discharged by `settling_terrain`.

The nonlinear-`s'` variants of this family (`s' = v(1 − 0.5ψ² − 0.3θ²)` and the cubic rungs)
remain phase D: their position field is outside every band grammar here.
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
end RelCertifier
