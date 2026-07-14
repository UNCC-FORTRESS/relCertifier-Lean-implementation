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
and the contract gain is stored in SCALED TIME — `k/den(dt)`, as `contractQ` when fractional
— so every data term is the exact time-scaled benchmark (a driven integrator's own scale is
`1000·den(dt)`, invisible here because the integrator coordinates carry no finite bounds).

THE SEGMENT BUDGET dt. `theorem3_faithful_settling` takes `dt` as a free parameter constrained
only by `hbudgetAll` (every left-run duration fits in `k·dt` segments for a free `k : ℕ`), so
each instance picks `dt = ε_R/λ` for an integer λ within the benchmark's declared
`[lambda_min, lambda_max]` — the smallest λ (largest dt) the checker accepts, noted per
instance. A TRANSIT mode's one-step image must fit the union of its own band and one successor
band (EXT 4), which bounds dt from above; the settling margins bound nothing from below.

A frozen ACTIVE coordinate with non-frozen (driven) others is transcribed as
`CoordShape.constRate 0` — the identical field (`Term.const 0`) — because the constRate branch
carries the flex-others grammar and lands in its own band by `c = 0`.

COVERAGE (24/47 data terms; ALL 24 checker-ACCEPTED with closed `rfl` certificates —
rover_4d_box via EXT 4b, rover_drag via `riccati`, attitude_rate via the `pairSym` block). The remaining benchmarks map to named extension classes,
each a precise next step, none a gap in what is proven:

* **exp-bound transit contracts** (watertank, match_multi_eps, rover3tier_M1,
  robot_braking) — CLOSED by the rational-gain extension: `CoordShape.contractQ kn kd c`
  carries the fractional gain exactly, the checker's transit cover uses the finite-dt cap
  `ghi·kd + (c − ghi)·kn·dt ≤ ghi'·kd` (cross-multiplied to ℤ), and
  `settling_contractQ_above/_below` discharge it via `1 − e^{−x} ≤ x`
  (`Real.add_one_le_exp`). Their certificates are at the end of this file.
* **driven-active / multi-coordinate guards** (the s-guarded terrain/story/refinement family,
  ~14) — guards on the integrator coordinate (plus the `v ≤ eq` cut conjunct), so the active
  coordinate is `driven` and guards span two coordinates; needs banded-rate landing
  (`[a + v_lo·dt, cap + v_hi·dt]` covers) and multi-band guards (EXT 3). WARNING (from the
  numeric H-falsification audit, `scripts/h_audit.py`): as currently modeled these have a
  TERMINAL-BAND OVERFLOW — the last terrain segment's `s`-band is capped (`s < 899.95` under
  `evolve s ≤ 1000`) with positive drift and no successor beyond, so the settling hypothesis
  is genuinely FALSE at every dt, not merely undecided. EXT 3 must be preceded by a modeling
  decision (unbounded terminal segment, per the honest-envelope principle for positions, or a
  park mode); same overflow shape in rover3tier_rung12 / rover_tier_r1 (`match_multi_rate`
  had it too and is FIXED above — band extended to its equilibrium).
* **coupled / higher-order / non-polynomial-shape** (attitude_rate, endurance_orderlift_2to3,
  rover_tier_r1, rover3tier_rung12, rover_drag, the nonlinear-`s'` rungs) — phase D: the
  invariance half can ride the cut channel's Z3 route; flow existence needs `PicardBridge`
  generalized (linear-coupled members have closed forms — see the roadmap).
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
      { shapes := ![CoordShape.contractQ 1 4 600, CoordShape.frozen], gcoord := 0,
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

/-- `attitude_rate` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 2).
The weakly coupled symmetric `(p, q)` block (`pairSym`, coupling ε = 0.05) with the yaw rate
`r` contracting via `contractQ 4 5` and the three attitude integrators envelope-free; the
RECOVER band hands to the terminal TRACK band under the `PairConds` two-exponential covers. -/
def attitude_rateM : SettlingModel 6 :=
  { modes :=
    [
      { shapes := ![CoordShape.driven 1, CoordShape.pairSym 3 1000 50,
          CoordShape.driven 3, CoordShape.pairSym 1 1000 50,
          CoordShape.driven 5, CoordShape.contractQ 4 5 625], gcoord := 1,
        glo := 0, ghi := 500, succs := [1] },
      { shapes := ![CoordShape.driven 1, CoordShape.pairSym 3 1000 50,
          CoordShape.driven 3, CoordShape.pairSym 1 1000 50,
          CoordShape.driven 5, CoordShape.contractQ 4 5 625], gcoord := 1,
        glo := 500, ghi := 1150, succs := [] } ]
    env := ![{ lo := none, hi := none }, { lo := some (-50 : ℤ), hi := some 1200 },
      { lo := none, hi := none }, { lo := some 0, hi := some 1200 },
      { lo := none, hi := none }, { lo := some 0, hi := some 1000 }]
    dtQ := 1 }

example : decideWellFormed attitude_rateM = true := rfl

/-- `endurance_gain_M1` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 1). -/
def endurance_gain_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 1 300, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 400, succs := [1] },
      { shapes := ![CoordShape.contract 1 500, CoordShape.driven 0], gcoord := 0,
        glo := 400, ghi := 575, succs := [0, 2] },
      { shapes := ![CoordShape.contract 1 650, CoordShape.driven 0], gcoord := 0,
        glo := 575, ghi := 700, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }]
    dtQ := 1 }

example : decideWellFormed endurance_gain_M1M = true := rfl

/-- `endurance_orderlift_1to2` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 1). -/
def endurance_orderlift_1to2M : SettlingModel 3 :=
  { modes :=
    [
      { shapes := ![CoordShape.contractQ 3 2 300, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 400, succs := [1] },
      { shapes := ![CoordShape.contractQ 3 2 500, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 400, ghi := 575, succs := [0, 2] },
      { shapes := ![CoordShape.contractQ 3 2 650, CoordShape.driven 0, CoordShape.frozen], gcoord := 0,
        glo := 575, ghi := 700, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 800 }, { lo := some 0, hi := none }, { lo := some (-500 : ℤ), hi := some 700 }]
    dtQ := 1 }

example : decideWellFormed endurance_orderlift_1to2M = true := rfl

/-- `endurance_orderlift_2to3` (R side; units: values ×1000, time ×2 — dt = ε_R/λ = 0.5 at
λ = 1 stored as 1). The order-2 intermediate model rides in its eigen-cascade chart
(EXT G): the guard coordinate `v` is `chase w 2` against the driver slot `w := u/2 =
(a + 4v)/2` (contract-to-`w* = u*/2` at the same rate — the ×2 value scale keeps the chase
field's unit driver coefficient under the ×2 time scale), `s` the driven integrator, `j`
frozen slack. Landing runs the pair covers: FLAT's thrust-cut dip crosses MODER into STEEP
(the three-band chain), STEEP's overshoot lands in MODER by the single-corner discriminant
`62500 ≤ 385000`. -/
def endurance_orderlift_2to3M : SettlingModel 4 :=
  { modes :=
    [
      { shapes := ![CoordShape.chase 2 2, CoordShape.driven 0, CoordShape.contract 2 600, CoordShape.frozen], gcoord := 0,
        glo := 0, ghi := 400, succs := [1] },
      { shapes := ![CoordShape.chase 2 2, CoordShape.driven 0, CoordShape.contract 2 1000, CoordShape.frozen], gcoord := 0,
        glo := 400, ghi := 575, succs := [0, 2] },
      { shapes := ![CoordShape.chase 2 2, CoordShape.driven 0, CoordShape.contract 2 1300, CoordShape.frozen], gcoord := 0,
        glo := 575, ghi := 750, succs := [1, 0] } ]
    env := ![{ lo := some 0, hi := some 850 }, { lo := some 0, hi := none }, { lo := some 0, hi := some 1400 }, { lo := some (-1600 : ℤ), hi := some 1400 }]
    dtQ := 1 }

example : decideWellFormed endurance_orderlift_2to3M = true := rfl

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
      { shapes := ![CoordShape.contractQ 1 4 600, CoordShape.frozen], gcoord := 0,
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

/-- `rover_4d_box` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1).
APPROACH is a contract-below transit (`vx` toward 0.65 under the band [0.7, 1.5]) whose
non-guarded block needs the EXT 4b extended flex grammar: `py' = vy` with `vy` contracting
to 0 — a contract other (equilibrium inside `vy`'s envelope band) driving the envelope-free
`py`. SETTLE's frozen active is transcribed as `constRate 0` per the standing convention. -/
def rover_4d_boxM : SettlingModel 4 :=
  { modes :=
    [
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3,
          CoordShape.contract 1 650, CoordShape.contract 1 0], gcoord := 2,
        glo := 700, ghi := 1500, succs := [1] },
      { shapes := ![CoordShape.driven 2, CoordShape.driven 3,
          CoordShape.constRate 0, CoordShape.frozen], gcoord := 2,
        glo := 500, ghi := 700, succs := [] } ]
    env := ![{ lo := none, hi := none }, { lo := none, hi := none },
      { lo := some 500, hi := some 1500 }, { lo := some (-1000 : ℤ), hi := some 1000 }]
    dtQ := 1 }

example : decideWellFormed rover_4d_boxM = true := rfl

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

/-- `rover_drag` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1).
Quadratic drag `vx' = 0.05 − 0.3·vx²` toward `√(1/6) ≈ 0.408` — the `riccati` shape
(`b = 50`, `a = 300`, both real coefficient ×1000; the `10⁶` divisor in the field absorbs
the squared value scale); one self-loop mode, hull-of-base-and-equilibrium landing. -/
def rover_dragM : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.riccati 50 300], gcoord := 0,
        glo := 0, ghi := 1210, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1400 }]
    dtQ := 1 }

example : decideWellFormed rover_dragM = true := rfl

/-- `rover_terrain_M1` (R side; units: values ×1000, time ×2; dt = ε_R/λ at λ = 1). -/
def rover_terrain_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contract 1 400, CoordShape.driven 0], gcoord := 0,
        glo := 0, ghi := 600, succs := [1] },
      { shapes := ![CoordShape.contract 1 800, CoordShape.driven 0], gcoord := 0,
        glo := 600, ghi := 1000, succs := [0, 2] },
      { shapes := ![CoordShape.contract 1 1200, CoordShape.driven 0], gcoord := 0,
        glo := 1000, ghi := 1250, succs := [1] } ]
    env := ![{ lo := some 0, hi := some 1350 }, { lo := some 0, hi := none }]
    dtQ := 1 }

example : decideWellFormed rover_terrain_M1M = true := rfl

/-- `match_multi_rate` (R side; units: values ×1000, time ×10; dt = ε_R/λ at λ = 1).
The guard cap was 0.95 with the equilibrium at 1.0 and no successor — the settling hypothesis
was FALSE as originally modeled (H-falsification audit witness: base v = 0.95 exits the band at
every dt); the band now reaches the equilibrium (contract-inside, self-settling) and the
benchmark re-certifies. -/
def match_multi_rateM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contractQ 1 10 1000, CoordShape.driven 0], gcoord := 0,
        glo := 200, ghi := 1000, succs := [] } ]
    env := ![{ lo := some 0, hi := some 1150 }, { lo := some 0, hi := none }]
    dtQ := 3 }

example : decideWellFormed match_multi_rateM = true := rfl

/-! ### The rational-gain (`contractQ`) instances — the former exp-bound parked class

Each has a transit-contract mode whose equilibrium lies beyond the adjacent successor band, so
the landing needs the sharper finite-dt cap `ghi + (c − ghi)·(kn/kd)·dt` (sound by
`1 − e^{−x} ≤ x`); the integer `contract` shape cannot express the fractional gain, and
`CoordShape.contractQ kn kd c` can. Gains are stored exactly (`kn/kd` = the benchmark's gain
in scaled time), so these are faithful transcriptions, not sign-only approximations. -/

/-- `match_multi_eps` (R side; units: values ×1000, time ×50; dt = ε_R/λ at λ = 5;
gain 2/s = 1/25 per time unit). -/
def match_multi_epsM : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contractQ 1 25 1000, CoordShape.driven 0], gcoord := 0,
        glo := 300, ghi := 600, succs := [1] },
      { shapes := ![CoordShape.contractQ 1 25 200, CoordShape.driven 0], gcoord := 0,
        glo := 600, ghi := 650, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1150 }, { lo := some 0, hi := none }]
    dtQ := 3 }

example : decideWellFormed match_multi_epsM = true := rfl

/-- `robot_braking` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 2;
gain 1/2). -/
def robot_brakingM : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.contractQ 1 2 0], gcoord := 0,
        glo := 3500, ghi := 3550, succs := [1] },
      { shapes := ![CoordShape.contractQ 1 2 0], gcoord := 0,
        glo := 1500, ghi := 3500, succs := [2] },
      { shapes := ![CoordShape.contractQ 1 2 1000], gcoord := 0,
        glo := 0, ghi := 1500, succs := [] } ]
    env := ![{ lo := some 0, hi := some 3650 }]
    dtQ := 1 }

example : decideWellFormed robot_brakingM = true := rfl

/-- `rover3tier_M1` (R side; units: values ×1000, time ×50; dt = ε_R/λ at λ = 5;
gain 2/s = 1/25 per time unit). -/
def rover3tier_M1M : SettlingModel 2 :=
  { modes :=
    [
      { shapes := ![CoordShape.contractQ 1 25 1000, CoordShape.driven 0], gcoord := 0,
        glo := 300, ghi := 600, succs := [1] },
      { shapes := ![CoordShape.contractQ 1 25 200, CoordShape.driven 0], gcoord := 0,
        glo := 600, ghi := 650, succs := [0] } ]
    env := ![{ lo := some 0, hi := some 1150 }, { lo := some 0, hi := none }]
    dtQ := 3 }

example : decideWellFormed rover3tier_M1M = true := rfl

/-- `watertank` (R side; units: values ×1000, time ×1; dt = ε_R/λ at λ = 1;
gain 0.12 = 3/25). -/
def watertankSuiteM : SettlingModel 1 :=
  { modes :=
    [
      { shapes := ![CoordShape.contractQ 3 25 12500], gcoord := 0,
        glo := 0, ghi := 10000, succs := [1] },
      { shapes := ![CoordShape.contractQ 3 25 25000], gcoord := 0,
        glo := 10000, ghi := 17000, succs := [2] },
      { shapes := ![CoordShape.contractQ 3 25 2500], gcoord := 0,
        glo := 17000, ghi := 22450, succs := [1] } ]
    env := ![{ lo := some (-50 : ℤ), hi := some 25000 }]
    dtQ := 1 }

example : decideWellFormed watertankSuiteM = true := rfl

end RelCertifier
