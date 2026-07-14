/-
# Affine-model data terms — the EXT 2b checker-accepted instances

The driven-active pair: the guarded velocity `v' = a` under a frozen nonneg acceleration.
Units as elsewhere (values ×1000, time ×den(dt)); a driven integrator's own scale is
`1000·den(dt)` — invisible below because those coordinates carry no finite bounds. The core
mode's `ghi` is a dummy (the affine guard map reads `glo` and the optional top instead).
-/
import RelCertifier.AffineChecker

namespace RelCertifier

/-- `rover_tier_r1` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1).
One topless self-loop mode: `v ∈ [0.3, ∞)`, `s' = v`, `a` frozen in `[0.3, 0.6]`. -/
def rover_tier_r1A : AffineModel 3 :=
  { core :=
    { modes :=
      [ { shapes := ![CoordShape.driven 1, CoordShape.driven 2, CoordShape.frozen],
          gcoord := 1, glo := 300, ghi := 300, succs := [] } ]
      env := ![{ lo := some 0, hi := none }, { lo := some 250, hi := none },
        { lo := some 300, hi := some 600 }]
      dtQ := 1 }
    vtops := [none] }

example : decideWellFormedA rover_tier_r1A = true := rfl

/-- `rover3tier_rung12` (R side; units: v ×1000, s and a ×10000 (the integrator scale),
time ×10; dt = ε_R/λ at λ = 1). ACCEL `v ∈ [0.3, 0.6)` hands to the topless COAST
`v ∈ [0.6, ∞)`. -/
def rover3tier_rung12A : AffineModel 3 :=
  { core :=
    { modes :=
      [ { shapes := ![CoordShape.driven 2, CoordShape.driven 0, CoordShape.frozen],
          gcoord := 0, glo := 300, ghi := 300, succs := [1] }
      , { shapes := ![CoordShape.driven 2, CoordShape.driven 0, CoordShape.frozen],
          gcoord := 0, glo := 600, ghi := 600, succs := [0] } ]
      env := ![{ lo := some 0, hi := none }, { lo := some 0, hi := none },
        { lo := some 5000, hi := some 10000 }]
      dtQ := 3 }
    vtops := [some 600, none] }

example : decideWellFormedA rover3tier_rung12A = true := rfl

end RelCertifier
