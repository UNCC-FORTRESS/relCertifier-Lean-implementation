/-
# Settling-model data terms — the checker-accepted benchmark instances

Each `def <name>M : SettlingModel _` below is the RIGHT side of a `benchmarks/suite_uniform/`
benchmark as integer data, and each `example : decideWellFormed <name>M = true := rfl` is the
kernel-checked well-formedness certificate: by `wellformed_sound`, this instance plus its
per-run Z3 certificates yields `GuardSettlingH` — hence `theorem3_faithful_settling` — with no
per-benchmark proof.

UNITS. Values are stored ×1000 and time ×den(dt) (noted per instance): kernel `rfl` cannot
reduce `Rat` division/normalization, so all literals must be integers. The checker's
inequalities are scale-invariant (margins and covers compare value×time products uniformly),
and the contract gain `k` — sign-only in the checker — is scaled to an integer independently.

THE SEGMENT BUDGET dt. `theorem3_faithful_settling` takes `dt` as a free parameter constrained
only by `hbudgetAll` (every left-run duration fits in `k·dt` segments for a free `k : ℕ`), so
each instance picks `dt = ε_R/λ` for an integer λ within the benchmark's declared
`[lambda_min, lambda_max]` — the smallest λ (largest dt) the checker accepts, noted per
instance. A TRANSIT mode's one-step image must fit the union of its own band and one successor
band (EXT 4), which bounds dt from above; the settling margins bound nothing from below.

A frozen ACTIVE coordinate with non-frozen (driven) others is transcribed as
`CoordShape.constRate 0` — the identical field (`Term.const 0`) — because the constRate branch
carries the flex-others grammar and lands in its own band by `c = 0`.

COVERAGE (21/47 data terms, generated from the benchmark files; 16 checker-ACCEPTED with
closed `rfl` certificates below). The remaining benchmarks map to named extension classes,
each a precise next step, none a gap in what is proven:

* **exp-bound transit contracts** (watertank, match_multi_eps, match_multi_rate, rover3tier_M1,
  robot_braking — the 5 parked data terms at the end of this file) — a contract mode whose
  equilibrium lies beyond the adjacent successor band, so the sound landing cap is the sharper
  `ghi + (c − ghi)·(1 − e^{−k·dt})`, not `c`. Deciding it needs a rational bound on
  `1 − e^{−k·dt}` with FRACTIONAL `k·dt` — the integer `SettlingModel` cannot express
  `k·dt < 1` (both factors are integers), so this class needs a rational-gain field
  (e.g. `contract kNum kDen c`) plus a `1 − e^{−x} ≤ x` discharge lemma. Designed, not built.
* **driven-active / multi-coordinate guards** (the s-guarded terrain/story/refinement family,
  ~14) — guards on the integrator coordinate (plus the `v ≤ eq` cut conjunct), so the active
  coordinate is `driven` and guards span two coordinates; needs banded-rate landing
  (`[a + v_lo·dt, cap + v_hi·dt]` covers) and multi-band guards (EXT 3).
* **coupled / higher-order / non-polynomial-shape** (attitude_rate, endurance_orderlift_2to3,
  rover_tier_r1, rover3tier_rung12, rover_drag, rover_4d_box's contract-driven `py`, the
  cubic-`s'` rungs) — phase D: the invariance half can ride the cut channel's Z3 route; flow
  existence needs `PicardBridge` generalized.
* shield_unreachable — the pre-existing inconclusive-Z3 ERROR benchmark (no guard band).

HISTORY. Under the pre-EXT 4 single-band landing rule only 3 of these terms were accepted; the
18 rejections shared one cause (TRANSIT modes crossing from their own band into a successor's),
mechanically confirmed by `#reduce` after an earlier "kernel-reduction quirk" misreading was
corrected — the kernel had been refusing a genuinely false proposition. EXT 4's union cover
plus per-instance dt selection closes 13 of them (arm_chain_rung2 additionally needed its
right `Return.next` corrected from the unreachable `ApproachFast` to the actual landing
successor `ApproachSlow` — a dead edge under partitioned guards; the benchmark re-certifies).
-/
import RelCertifier.WellFormedChecker

namespace RelCertifier

/-- `arm_chain_rung1` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def arm_chain_rung1M : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100], gcoord := 0,
        glo := 0, ghi := 700, succs := [1] },
      { shapes := ![CoordShape.constRate (-100 : ℤ)], gcoord := 0,
        glo := 700, ghi := 850, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1000 }]
    dtQ := 1 }

example : decideWellFormed arm_chain_rung1M = true := rfl

/-- `arm_chain_rung2` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def arm_chain_rung2M : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 250], gcoord := 0,
        glo := 0, ghi := 350, succs := [1] },
      { shapes := ![CoordShape.constRate 150], gcoord := 0,
        glo := 350, ghi := 700, succs := [2] },
      { shapes := ![CoordShape.constRate (-100 : ℤ)], gcoord := 0,
        glo := 700, ghi := 850, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 1000 }]
    dtQ := 1 }

example : decideWellFormed arm_chain_rung2M = true := rfl

/-- `arm_chain_rung3` (R side; units: values ×1000, time ×5; dt = ε_R/λ at λ = 5). -/
def arm_chain_rung3M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 350, succs := [1] },
      { shapes := ![CoordShape.constRate 70, CoordShape.frozen], gcoord := 0,
        glo := 350, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.constRate 40, CoordShape.frozen], gcoord := 0,
        glo := 500, ghi := 600, succs := [3] },
      { shapes := ![CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 600, ghi := 1150, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1200 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed arm_chain_rung3M = true := rfl

/-- `arm_fidelity_high` (R side; units: values ×1000, time ×5; dt = ε_R/λ at λ = 5). -/
def arm_fidelity_highM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 350, succs := [1] },
      { shapes := ![CoordShape.constRate 70, CoordShape.frozen], gcoord := 0,
        glo := 350, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.constRate 40, CoordShape.frozen], gcoord := 0,
        glo := 500, ghi := 600, succs := [3] },
      { shapes := ![CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 600, ghi := 1150, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1200 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed arm_fidelity_highM = true := rfl

/-- `arm_fidelity_low` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def arm_fidelity_lowM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 700, succs := [1] },
      { shapes := ![CoordShape.constRate (-100 : ℤ), CoordShape.frozen], gcoord := 0,
        glo := 700, ghi := 850, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1000 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed arm_fidelity_lowM = true := rfl

/-- `arm_fidelity_mid` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def arm_fidelity_midM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 250, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 350, succs := [1] },
      { shapes := ![CoordShape.constRate 150, CoordShape.frozen], gcoord := 0,
        glo := 350, ghi := 600, succs := [2] },
      { shapes := ![CoordShape.contract 1 600, CoordShape.frozen], gcoord := 0,
        glo := 600, ghi := 1150, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1200 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed arm_fidelity_midM = true := rfl

/-- `arm_refinement` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def arm_refinementM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 700, succs := [1] },
      { shapes := ![CoordShape.constRate (-100 : ℤ), CoordShape.frozen], gcoord := 0,
        glo := 700, ghi := 850, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1000 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed arm_refinementM = true := rfl

/-- `endurance_gain_M1` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 1). -/
def endurance_gain_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 4 300, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 400, succs := [1] },
      { shapes := ![CoordShape.contract 4 500, CoordShape.driven 0], gcoord := 0,
        glo := 400, ghi := 575, succs := [0, 2] },
      { shapes := ![CoordShape.contract 4 650, CoordShape.driven 0], gcoord := 0,
        glo := 575, ghi := 700, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }]
    dtQ := 1 }

example : decideWellFormed endurance_gain_M1M = true := rfl

/-- `endurance_orderlift_1to2` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 1). -/
def endurance_orderlift_1to2M : SettlingModel 3 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 6 300, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 400, succs := [1] },
      { shapes := ![CoordShape.contract 6 500, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 400, ghi := 575, succs := [0, 2] },
      { shapes := ![CoordShape.contract 6 650, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 575, ghi := 700, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 700 }]
    dtQ := 1 }

example : decideWellFormed endurance_orderlift_1to2M = true := rfl

/-- `plant_fan_high` (R side; units: values ×1000, time ×5; dt = ε_R/λ at λ = 5). -/
def plant_fan_highM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 350, succs := [1] },
      { shapes := ![CoordShape.constRate 70, CoordShape.frozen], gcoord := 0,
        glo := 350, ghi := 500, succs := [2] },
      { shapes := ![CoordShape.constRate 40, CoordShape.frozen], gcoord := 0,
        glo := 500, ghi := 600, succs := [3] },
      { shapes := ![CoordShape.frozen, CoordShape.frozen], gcoord := 0,
        glo := 600, ghi := 1150, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1200 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed plant_fan_highM = true := rfl

/-- `plant_fan_low` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def plant_fan_lowM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 100, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 700, succs := [1] },
      { shapes := ![CoordShape.constRate (-100 : ℤ), CoordShape.frozen], gcoord := 0,
        glo := 700, ghi := 850, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1000 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed plant_fan_lowM = true := rfl

/-- `plant_fan_mid` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 2). -/
def plant_fan_midM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.constRate 250, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 350, succs := [1] },
      { shapes := ![CoordShape.constRate 150, CoordShape.frozen], gcoord := 0,
        glo := 350, ghi := 600, succs := [2] },
      { shapes := ![CoordShape.contract 1 600, CoordShape.frozen], gcoord := 0,
        glo := 600, ghi := 1150, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1200 }, { lo := none, hi := none }]
    dtQ := 1 }

example : decideWellFormed plant_fan_midM = true := rfl

/-- `rover3_M1` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover3_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.driven 1, CoordShape.constRate 400], gcoord := 1,
        glo := 250, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.driven 1, CoordShape.constRate 200], gcoord := 1,
        glo := 300, ghi := 750, succs := [2] },
      { shapes := ![CoordShape.driven 1, CoordShape.constRate 0], gcoord := 1,
        glo := 750, ghi := 1000, succs := [] } ]
    env := ![{ lo := some (-50 : ℤ), hi := none }, { lo := some 250, hi := some 1100 }]
    dtQ := 1 }

example : decideWellFormed rover3_M1M = true := rfl

/-- `rover_coupled` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover_coupledM : SettlingModel 4 :=
  { modes :=
    [
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3, CoordShape.constRate 400, CoordShape.frozen], gcoord := 2,
        glo := 250, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3, CoordShape.constRate 200, CoordShape.frozen], gcoord := 2,
        glo := 300, ghi := 750, succs := [2] },
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3, CoordShape.constRate 0, CoordShape.frozen], gcoord := 2,
        glo := 750, ghi := 1000, succs := [] } ]
    env := ![{ lo := some (-50 : ℤ), hi := none }, { lo := none, hi := none }, { lo := some 250, hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }]
    dtQ := 1 }

example : decideWellFormed rover_coupledM = true := rfl

/-- `rover_position` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1). -/
def rover_positionM : SettlingModel 4 :=
  { modes :=
    [
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3, CoordShape.constRate 400, CoordShape.frozen], gcoord := 2,
        glo := 250, ghi := 300, succs := [1] },
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3, CoordShape.constRate 200, CoordShape.frozen], gcoord := 2,
        glo := 300, ghi := 750, succs := [2] },
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3, CoordShape.constRate 0, CoordShape.frozen], gcoord := 2,
        glo := 750, ghi := 1000, succs := [] } ]
    env := ![{ lo := some (-50 : ℤ), hi := none }, { lo := none, hi := none }, { lo := some 250, hi := some 1100 }, { lo := some (-1000 : ℤ), hi := some 1100 }]
    dtQ := 1 }

example : decideWellFormed rover_positionM = true := rfl

/-- `rover_terrain_M1` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 1). -/
def rover_terrain_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 4 400, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 600, succs := [1] },
      { shapes := ![CoordShape.contract 4 800, CoordShape.driven 0], gcoord := 0,
        glo := 600, ghi := 1000, succs := [0, 2] },
      { shapes := ![CoordShape.contract 4 1200, CoordShape.driven 0], gcoord := 0,
        glo := 1000, ghi := 1250, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 1350 }, { lo := some 0, hi := none }]
    dtQ := 1 }

example : decideWellFormed rover_terrain_M1M = true := rfl

/-! ### Parked data terms — the exp-bound transit-contract class (see header)

Checker-REJECTED, correctly: each has a contract mode whose equilibrium lies beyond the
adjacent successor band, and the integer checker cannot express the sharper finite-dt landing
cap. The data terms document the models for the rational-gain extension. -/

/-- `match_multi_eps` (R side; units: values ×1000, time ×10). -/
def match_multi_epsM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 20 1000, CoordShape.driven 0], gcoord := 0,
        glo := 300, ghi := 600, succs := [1] },
      { shapes := ![CoordShape.contract 20 200, CoordShape.driven 0], gcoord := 0,
        glo := 600, ghi := 650, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1150 }, { lo := some 0, hi := none }]
    dtQ := 3 }

-- checker-rejected pending the rational-gain (exp-bound) extension (see header):
-- example : decideWellFormed match_multi_epsM = true := rfl

/-- `match_multi_rate` (R side; units: values ×1000, time ×10). -/
def match_multi_rateM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 10 1000, CoordShape.driven 0], gcoord := 0,
        glo := 200, ghi := 950, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1150 }, { lo := some 0, hi := none }]
    dtQ := 3 }

-- checker-rejected pending the rational-gain (exp-bound) extension (see header):
-- example : decideWellFormed match_multi_rateM = true := rfl

/-- `robot_braking` (R side; units: values ×1000, time ×1). -/
def robot_brakingM : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 1 0], gcoord := 0,
        glo := 3500, ghi := 3550, succs := [1] },
      { shapes := ![CoordShape.contract 1 0], gcoord := 0,
        glo := 1500, ghi := 3500, succs := [2] },
      { shapes := ![CoordShape.contract 1 1000], gcoord := 0,
        glo := 0, ghi := 1500, succs := [] } ]
    env := ![{ lo := some 0, hi := some 3650 }]
    dtQ := 2 }

-- checker-rejected pending the rational-gain (exp-bound) extension (see header):
-- example : decideWellFormed robot_brakingM = true := rfl

/-- `rover3tier_M1` (R side; units: values ×1000, time ×10). -/
def rover3tier_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 20 1000, CoordShape.driven 0], gcoord := 0,
        glo := 300, ghi := 600, succs := [1] },
      { shapes := ![CoordShape.contract 20 200, CoordShape.driven 0], gcoord := 0,
        glo := 600, ghi := 650, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1150 }, { lo := some 0, hi := none }]
    dtQ := 3 }

-- checker-rejected pending the rational-gain (exp-bound) extension (see header):
-- example : decideWellFormed rover3tier_M1M = true := rfl

/-- `watertank` (R side; units: values ×1000, time ×1). -/
def watertankSuiteM : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 3 12500], gcoord := 0,
        glo := 0, ghi := 10000, succs := [1] },
      { shapes := ![CoordShape.contract 3 25000], gcoord := 0,
        glo := 10000, ghi := 17000, succs := [2] },
      { shapes := ![CoordShape.contract 3 2500], gcoord := 0,
        glo := 17000, ghi := 22450, succs := [1] } ]
    env := ![{ lo := some (-50 : ℤ), hi := some 25000 }]
    dtQ := 1 }

-- checker-rejected pending the rational-gain (exp-bound) extension (see header):
-- example : decideWellFormed watertankSuiteM = true := rfl

end RelCertifier
