/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Modal verdict specs — one source of truth for the verdict runner

Every modal instance's Z3 hypotheses are indexed by data that, until now, existed
only *implicitly* in the instance file: which `(left, right)` mode arguments the
theorem asserts (readable only from binder names) and the stratified-DC order of
the invariant components (readable only from the order `gs` happens to be written
in). A runner had to reverse-engineer both, and doing that by hand is error-prone
in exactly the ways `docs/VERDICT-EVIDENCE-AUDIT.md` §4 records.

This module makes both **data**, tied to the instances by kernel-checked facts:

* `spec_components` binds `spec.order` to the instance's actual component list by
  `rfl` — a spec whose order disagrees does not compile;
* `modal_from_spec` re-derives the instance's theorem from the argument-indexed
  hypothesis — a spec missing an argument the theorem needs does not compile.

Instance files are untouched: this module sits above them and the original
theorems are unchanged. `Verdicts/` iterates `specs` instead of hard-coding tables.

Shapes covered: **A** multi-component with a static component list (`spec.order`
pinned by `rfl`); **C** single-component (no strata, `order = []`). Shape **B**
(component list built per right mode, `ceilX m :: gsVX m`) carries `modeDep := true`
and no order pin — its component terms are instance-specific constructions rather
than plain invariant atoms. The six Z3-free theorems need no spec at all.
-/
import RelCertifier.Instances.ArmChainRung1Modal
import RelCertifier.Instances.ArmChainRung2Modal
import RelCertifier.Instances.ArmChainRung3Modal
import RelCertifier.Instances.ArmFidelityHighModal
import RelCertifier.Instances.ArmFidelityLowModal
import RelCertifier.Instances.ArmFidelityMidModal
import RelCertifier.Instances.ArmRefinementModal
import RelCertifier.Instances.AttitudeRateModal
import RelCertifier.Instances.EnduranceGainM1Modal
import RelCertifier.Instances.EnduranceOrderlift1to2Modal
import RelCertifier.Instances.EnduranceOrderlift2to3Modal
import RelCertifier.Instances.MatchMultiEpsModal
import RelCertifier.Instances.MatchMultiRateModal
import RelCertifier.Instances.PlantFanHighModal
import RelCertifier.Instances.PlantFanLowModal
import RelCertifier.Instances.PlantFanMidModal
import RelCertifier.Instances.RobotBrakingModal
import RelCertifier.Instances.Rover3tierM1Modal
import RelCertifier.Instances.Rover3tierRung12Modal
import RelCertifier.Instances.Rover4dBoxModal
import RelCertifier.Instances.RoverAttitudeConeModal
import RelCertifier.Instances.RoverDofTerrainRung1Modal
import RelCertifier.Instances.RoverDofTerrainRung2Modal
import RelCertifier.Instances.RoverDofTerrainRung38dModal
import RelCertifier.Instances.RoverDofTerrainRung3Modal
import RelCertifier.Instances.RoverDragModal
import RelCertifier.Instances.RoverLadderRung1Modal
import RelCertifier.Instances.RoverLadderRung2Modal
import RelCertifier.Instances.RoverLadderRung3Modal
import RelCertifier.Instances.RoverLadderRung4Modal
import RelCertifier.Instances.RoverRung2cModal
import RelCertifier.Instances.RoverTerrainM1Modal
import RelCertifier.Instances.RoverTierR1Modal
import RelCertifier.Instances.Story1AttdistRungAModal
import RelCertifier.Instances.Story1AttdistRungBModal
import RelCertifier.Instances.Story2LateralAModal
import RelCertifier.Instances.Story2LateralBModal
import RelCertifier.Instances.Story3RolloverBaseModal
import RelCertifier.Instances.Story3RolloverRungAModal
import RelCertifier.Instances.Story3RolloverRungBModal
import RelCertifier.Instances.WatertankModal
namespace RelCertifier.ModalSpecs

open RelCertifier DL DLRel

/-- What a runner needs to rebuild an instance's verdict queries. -/
structure VerdSpec where
  /-- Benchmark name as it appears in `benchIRTable`. -/
  bench   : String
  /-- Asserted `(left mode, right mode)` arguments, for two-argument `Verd` forms. -/
  pairs   : List (ℕ × ℕ) := []
  /-- Asserted single arguments, for one-argument `Verd` forms. -/
  singles : List ℕ := []
  /-- Invariant-component indices in stratified-DC order (shape A only). -/
  order   : List ℕ := []
  /-- The component list is built per right mode; `order` is not a plain `gAt` list. -/
  modeDep : Bool := false
  /-- The `Verd` form takes no arguments. -/
  nullary : Bool := false
  deriving Repr, DecidableEq

namespace ArmChainRung1
open RelCertifier.ArmChainRung1Modal

def spec : VerdSpec :=
  { bench := "arm_chain_rung1"
    singles := [0, 1, 2]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdC l

theorem modal_from_spec (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsC dt))
      (rightAutomatonBody GrC mvC)
      (RFormula.and (RFormula.and (canonInv gC) (envLR domLC domRC))
        (mvValidR mvC GrC.modes.length))) :=
  arm_chain_rung1_modal dt hdt0 hdt5
    (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide))

end ArmChainRung1

namespace ArmChainRung2
open RelCertifier.ArmChainRung2Modal

def spec : VerdSpec :=
  { bench := "arm_chain_rung2"
    singles := [0, 1, 2, 3]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdD l

theorem modal_from_spec (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsD dt))
      (rightAutomatonBody GrD mvD)
      (RFormula.and (RFormula.and (canonInv gD) (envLR domLD domRD))
        (mvValidR mvD GrD.modes.length))) :=
  arm_chain_rung2_modal dt hdt0 hdt5
    (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide)) (hv 3 (by decide))

end ArmChainRung2

namespace ArmChainRung3
open RelCertifier.ArmChainRung3Modal

/-- No order pin: this instance builds its invariant term directly from the IR
rather than through a `gAt` indexer, and its component list's head is the `Hold`
region `regA` (added when the vacuous statement was repaired — see the instance's
`regA` docstring and `docs/VERDICT-EVIDENCE-AUDIT.md` Part II). The pair set below
is still tied to the theorem by `modal_from_spec`. -/
def spec : VerdSpec :=
  { bench := "arm_chain_rung3"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM regA gsA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  arm_chain_rung3_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end ArmChainRung3

namespace ArmFidelityHigh
open RelCertifier.ArmFidelityHighModal

/-- No order pin: this instance builds its invariant term directly from the IR
rather than through a `gAt` indexer, and its component list's head is the `Hold`
region `regA` (added when the vacuous statement was repaired — see the instance's
`regA` docstring and `docs/VERDICT-EVIDENCE-AUDIT.md` Part II). The pair set below
is still tied to the theorem by `modal_from_spec`. -/
def spec : VerdSpec :=
  { bench := "arm_fidelity_high"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM regA gsA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  arm_fidelity_high_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end ArmFidelityHigh

namespace ArmFidelityLow
open RelCertifier.ArmFidelityLowModal

def spec : VerdSpec :=
  { bench := "arm_fidelity_low"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdF l

theorem modal_from_spec (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrF mvF)
      (RFormula.and (RFormula.and (canonInv gF) (envLR domLF domRF))
        (mvValidR mvF GrF.modes.length))) :=
  arm_fidelity_low_modal dt hdt0 hdt5
    (hv 0 (by decide)) (hv 1 (by decide))

end ArmFidelityLow

namespace ArmFidelityMid
open RelCertifier.ArmFidelityMidModal

/-- No order pin: this instance builds its invariant term directly from the IR
rather than through a `gAt` indexer, and its component list's head is the `Hold`
region `regA` (added when the vacuous statement was repaired — see the instance's
`regA` docstring and `docs/VERDICT-EVIDENCE-AUDIT.md` Part II). The pair set below
is still tied to the theorem by `modal_from_spec`. -/
def spec : VerdSpec :=
  { bench := "arm_fidelity_mid"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM regA gsA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  arm_fidelity_mid_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end ArmFidelityMid

namespace ArmRefinement
open RelCertifier.ArmRefinementModal

def spec : VerdSpec :=
  { bench := "arm_refinement"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdF l

theorem modal_from_spec (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrF mvF)
      (RFormula.and (RFormula.and (canonInv gF) (envLR domLF domRF))
        (mvValidR mvF GrF.modes.length))) :=
  arm_refinement_modal dt hdt0 hdt5
    (hv 0 (by decide)) (hv 1 (by decide))

end ArmRefinement

namespace AttitudeRate
open RelCertifier.AttitudeRateModal

def spec : VerdSpec :=
  { bench := "attitude_rate"
    singles := [0, 1]
    order := [0]
  }

theorem spec_components : (gW :: gsW) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdW l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvW)
      (RFormula.and (RFormula.and (canonInvM gW gsW) (envLR domLW domRW))
        (mvValidR mvW GrW.modes.length))) :=
  attitude_rate_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end AttitudeRate

namespace EnduranceGainM1
open RelCertifier.EnduranceGainM1Modal

def spec : VerdSpec :=
  { bench := "endurance_gain_M1"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0]
  }

theorem spec_components : (gG :: gsG) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdG p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsG dt))
      (rightAutomatonBody GrG mvG)
      (RFormula.and (RFormula.and (canonInvM gG gsG) (envLR domLG domRG))
        (mvValidR mvG GrG.modes.length))) :=
  endurance_gain_M1_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end EnduranceGainM1

namespace EnduranceOrderlift1to2
open RelCertifier.EnduranceOrderlift1to2Modal

/-- The six pairs are exactly the cover's `jointOK = true` set. The three `(l, STEEP)`
pairs are deliberately absent: the tool's joint attempt for them failed (empty strata
order), and Z3 returns SAT on all three routes, so asserting them would make the
theorem vacuous. See `docs/VERDICT-EVIDENCE-AUDIT.md` §5. -/
def spec : VerdSpec :=
  { bench := "endurance_orderlift_1to2"
    pairs := [(0,1), (0,2), (1,1), (1,2), (2,1), (2,2)]
    order := [0]
  }

theorem spec_components : (gO :: gsO) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdO p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsO dt))
      (rightAutomatonBody GrO mvO)
      (RFormula.and (RFormula.and (canonInvM gO gsO) (envLR domLO domRO))
        (mvValidR mvO GrO.modes.length))) :=
  endurance_orderlift_1to2_modal dt hdt
    (hv (0,1) (by decide)) (hv (0,2) (by decide)) (hv (1,1) (by decide))
    (hv (1,2) (by decide)) (hv (2,1) (by decide)) (hv (2,2) (by decide))

end EnduranceOrderlift1to2

namespace EnduranceOrderlift2to3
open RelCertifier.EnduranceOrderlift2to3Modal

def spec : VerdSpec :=
  { bench := "endurance_orderlift_2to3"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gJ :: gsJ) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdJ p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsJ dt))
      (rightAutomatonBody GrJ mvJ)
      (RFormula.and (RFormula.and (canonInvM gJ gsJ) (envLR domLJ domRJ))
        (mvValidR mvJ GrJ.modes.length))) :=
  endurance_orderlift_2to3_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end EnduranceOrderlift2to3

namespace MatchMultiEps
open RelCertifier.MatchMultiEpsModal

def spec : VerdSpec :=
  { bench := "match_multi_eps"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInv gA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  match_multi_eps_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end MatchMultiEps

namespace MatchMultiRate
open RelCertifier.MatchMultiRateModal

def spec : VerdSpec :=
  { bench := "match_multi_rate"
    singles := [0, 1, 2, 3]
    order := [0]
  }

theorem spec_components : (gM :: gsM) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdM l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsM dt))
      (rightAutomatonBody GrM mvM)
      (RFormula.and (RFormula.and (canonInvM gM gsM) (envLR domLM domRM))
        (mvValidR mvM GrM.modes.length))) :=
  match_multi_rate_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide)) (hv 3 (by decide))

end MatchMultiRate

namespace PlantFanHigh
open RelCertifier.PlantFanHighModal

/-- No order pin: this instance builds its invariant term directly from the IR
rather than through a `gAt` indexer, and its component list's head is the `Hold`
region `regA` (added when the vacuous statement was repaired — see the instance's
`regA` docstring and `docs/VERDICT-EVIDENCE-AUDIT.md` Part II). The pair set below
is still tied to the theorem by `modal_from_spec`. -/
def spec : VerdSpec :=
  { bench := "plant_fan_high"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM regA gsA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  plant_fan_high_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end PlantFanHigh

namespace PlantFanLow
open RelCertifier.PlantFanLowModal

def spec : VerdSpec :=
  { bench := "plant_fan_low"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdF l

theorem modal_from_spec (dt : ℝ) (hdt0 : 0 ≤ dt) (hdt5 : dt ≤ 1/5) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrF mvF)
      (RFormula.and (RFormula.and (canonInv gF) (envLR domLF domRF))
        (mvValidR mvF GrF.modes.length))) :=
  plant_fan_low_modal dt hdt0 hdt5
    (hv 0 (by decide)) (hv 1 (by decide))

end PlantFanLow

namespace PlantFanMid
open RelCertifier.PlantFanMidModal

/-- No order pin: this instance builds its invariant term directly from the IR
rather than through a `gAt` indexer, and its component list's head is the `Hold`
region `regA` (added when the vacuous statement was repaired — see the instance's
`regA` docstring and `docs/VERDICT-EVIDENCE-AUDIT.md` Part II). The pair set below
is still tied to the theorem by `modal_from_spec`. -/
def spec : VerdSpec :=
  { bench := "plant_fan_mid"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM regA gsA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  plant_fan_mid_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end PlantFanMid

namespace RobotBraking
open RelCertifier.RobotBrakingModal

def spec : VerdSpec :=
  { bench := "robot_braking"
    singles := [0]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInv gA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  robot_braking_modal dt hdt
    (hv 0 (by decide))

end RobotBraking

namespace Rover3tierM1
open RelCertifier.Rover3tierM1Modal

def spec : VerdSpec :=
  { bench := "rover3tier_M1"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInv gA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  rover3tier_M1_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end Rover3tierM1

namespace Rover3tierRung12Accel
open RelCertifier.Rover3tierRung12Modal

def spec : VerdSpec :=
  { bench := "rover3tier_rung12"
    singles := [0, 1]
    order := [0, 1]
  }

theorem spec_components : (gQ :: gsQ) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdQA l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsQ dt))
      (rightAutomatonBody GrQ mvQ)
      (RFormula.and (RFormula.and (canonInvM gQ gsQ) (envLR domLQ domRQ))
        (mvValidR mvQ GrQ.modes.length))) :=
  rover3tier_rung12_modal_ACCEL dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end Rover3tierRung12Accel

namespace Rover3tierRung12Coast
open RelCertifier.Rover3tierRung12Modal

def spec : VerdSpec :=
  { bench := "rover3tier_rung12"
    singles := [0, 1]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdQC l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsQC dt))
      (rightAutomatonBody GrQ mvQ)
      (RFormula.and (RFormula.and (canonInvM gQC gsQC) (envLR domLQ domRQ))
        (mvValidR mvQ GrQ.modes.length))) :=
  rover3tier_rung12_modal_COAST dt hdt
    (hv 0 (by decide)) (hv 1 (by decide))

end Rover3tierRung12Coast

namespace Rover4dBox
open RelCertifier.Rover4dBoxModal

def spec : VerdSpec :=
  { bench := "rover_4d_box"
    singles := [0]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, Verd3 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInv gA) (envLR domLA domRA))
        (mvValidR mvA GrA.modes.length))) :=
  rover_4d_box_modal dt hdt
    (hv 0 (by decide))

end Rover4dBox

namespace RoverAttitudeCone
open RelCertifier.RoverAttitudeConeModal

def spec : VerdSpec :=
  { bench := "rover_attitude_cone_12dof"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdC p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsC dt))
      (rightAutomatonBody GrC mvC)
      (RFormula.and (RFormula.and (canonInvM gC gsC) (envLR domLC domRC))
        (mvRegionR mvC regionC GrC.modes.length))) :=
  rover_attitude_cone_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverAttitudeCone

namespace RoverDofTerrainRung1
open RelCertifier.RoverDofTerrainRung1Modal

def spec : VerdSpec :=
  { bench := "rover_dof_terrain_rung1"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gE :: gsE) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdE p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsE dt))
      (rightAutomatonBody GrE mvE)
      (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
        (mvValidR mvE GrE.modes.length))) :=
  rover_dof_terrain_rung1_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverDofTerrainRung1

namespace RoverDofTerrainRung2
open RelCertifier.RoverDofTerrainRung2Modal

def spec : VerdSpec :=
  { bench := "rover_dof_terrain_rung2"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gT :: gsT) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdT p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsT dt))
      (rightAutomatonBody GrT mvT)
      (RFormula.and (RFormula.and (canonInvM gT gsT) (envLR domLT domRT))
        (mvValidR mvT GrT.modes.length))) :=
  rover_dof_terrain_rung2_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverDofTerrainRung2

namespace RoverDofTerrainRung38d
open RelCertifier.RoverDofTerrainRung38dModal

def spec : VerdSpec :=
  { bench := "rover_dof_terrain_rung3_8d"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gU :: gsU) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdU p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsU dt))
      (rightAutomatonBody GrU mvU)
      (RFormula.and (RFormula.and (canonInvM gU gsU) (envLR domLU domRU))
        (mvValidR mvU GrU.modes.length))) :=
  rover_dof_terrain_rung3_8d_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverDofTerrainRung38d

namespace RoverDofTerrainRung3
open RelCertifier.RoverDofTerrainRung3Modal

def spec : VerdSpec :=
  { bench := "rover_dof_terrain_rung3"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gW :: gsW) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdW p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvW)
      (RFormula.and (RFormula.and (canonInvM gW gsW) (envLR domLW domRW))
        (mvValidR mvW GrW.modes.length))) :=
  rover_dof_terrain_rung3_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverDofTerrainRung3

namespace RoverDrag
open RelCertifier.RoverDragModal

def spec : VerdSpec := { bench := "rover_drag", nullary := true }

def VerdAll : Prop := VerdRD

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsD dt))
      (rightAutomatonBody GrD mvD)
      (RFormula.and (RFormula.and (canonInv gD) (envLR domLD domRD))
        (mvValidR mvD GrD.modes.length))) :=
  rover_drag_modal dt hdt hv

end RoverDrag

namespace RoverLadderRung1
open RelCertifier.RoverLadderRung1Modal

def spec : VerdSpec :=
  { bench := "refinement_ladder_rover_rung1_2to3"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gE :: gsE) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdE p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsE dt))
      (rightAutomatonBody GrE mvE)
      (RFormula.and (RFormula.and (canonInvM gE gsE) (envLR domLE domRE))
        (mvValidR mvE GrE.modes.length))) :=
  rover_ladder_rung1_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverLadderRung1

namespace RoverLadderRung2
open RelCertifier.RoverLadderRung2Modal

def spec : VerdSpec :=
  { bench := "refinement_ladder_rover_rung2_3to6"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 2, 3, 1]
  }

theorem spec_components : (g6 :: gs6) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, Verd36 p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs6 dt))
      (rightAutomatonBody Gr6 mv6)
      (RFormula.and (RFormula.and (canonInvM g6 gs6) (envLR domL6 domR6))
        (mvValidR mv6 Gr6.modes.length))) :=
  rover_ladder_rung2_3to6_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverLadderRung2

namespace RoverLadderRung3
open RelCertifier.RoverLadderRung3Modal

def spec : VerdSpec :=
  { bench := "refinement_ladder_rover_rung3_6to8"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdR p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsR dt))
      (rightAutomatonBody GrR mvR)
      (RFormula.and (RFormula.and (canonInvM gR gsR) (envLR domLR domRR))
        (mvRegionR mvR regionR GrR.modes.length))) :=
  rover_ladder_rung3_6to8_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverLadderRung3

namespace RoverLadderRung4
open RelCertifier.RoverLadderRung4Modal

def spec : VerdSpec :=
  { bench := "refinement_ladder_rover_rung4_8to12"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdF p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrF mvF)
      (RFormula.and (RFormula.and (canonInvM gF gsF) (envLR domLF domRF))
        (mvRegionR mvF regionF GrF.modes.length))) :=
  rover_ladder_rung4_8to12_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverLadderRung4

namespace RoverRung2c
open RelCertifier.RoverRung2cModal

def spec : VerdSpec :=
  { bench := "refinement_ladder_rover_rung2c_6dof"
    singles := [0, 1, 2]
  }

def VerdAll : Prop := ∀ l ∈ spec.singles, VerdR6 l

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgs6 dt))
      (rightAutomatonBody Gr6 mv6)
      (RFormula.and (RFormula.and (canonInvM g6 gs6) (envLR domL6 domR6))
        (mvRegionR mv6 region6 Gr6.modes.length))) :=
  rover_rung2c_modal dt hdt
    (hv 0 (by decide)) (hv 1 (by decide)) (hv 2 (by decide))

end RoverRung2c

namespace RoverTerrainM1
open RelCertifier.RoverTerrainM1Modal

def spec : VerdSpec :=
  { bench := "rover_terrain_M1"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0]
  }

theorem spec_components : (gT :: gsT) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdT p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsT dt))
      (rightAutomatonBody GrT mvT)
      (RFormula.and (RFormula.and (canonInvM gT gsT) (envLR domLT domRT))
        (mvValidR mvT GrT.modes.length))) :=
  rover_terrain_M1_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end RoverTerrainM1

namespace RoverTierR1
open RelCertifier.RoverTierR1Modal

def spec : VerdSpec :=
  { bench := "rover_tier_r1"
    pairs := [(0,0)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdX p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsX dt))
      (rightAutomatonBody GrX mvX)
      (RFormula.and (RFormula.and (canonInvM gX gsX) (envLR domLX domRX))
        (mvRegionR mvX regionX GrX.modes.length))) :=
  rover_tier_r1_modal dt hdt
    (hv (0,0) (by decide))

end RoverTierR1

namespace Story1AttdistRungA
open RelCertifier.Story1AttdistRungAModal

def spec : VerdSpec :=
  { bench := "story1_attdist_rung_a_6to8"
    pairs := [(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gD :: gsD) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdD p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsD dt))
      (rightAutomatonBody GrD mvD)
      (RFormula.and (RFormula.and (canonInvM gD gsD) (envLR domLD domRD))
        (mvValidR mvD GrD.modes.length))) :=
  story1_attdist_rung_a_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,0) (by decide)) (hv (1,1) (by decide)) (hv (1,2) (by decide))
    (hv (2,0) (by decide)) (hv (2,1) (by decide)) (hv (2,2) (by decide))

end Story1AttdistRungA

namespace Story1AttdistRungB
open RelCertifier.Story1AttdistRungBModal

def spec : VerdSpec :=
  { bench := "story1_attdist_rung_b_12dof"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdF p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsF dt))
      (rightAutomatonBody GrF mvF)
      (RFormula.and (RFormula.and (canonInvM gF gsF) (envLR domLF domRF))
        (mvRegionR mvF regionF GrF.modes.length))) :=
  story1_attdist_rung_b_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end Story1AttdistRungB

namespace Story2LateralA
open RelCertifier.Story2LateralAModal

def spec : VerdSpec :=
  { bench := "story2_lateral_rung_a_8dof"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1, 3, 4, 5, 6, 2]
  }

theorem spec_components : (gY :: gsY) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdY p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsY dt))
      (rightAutomatonBody GrY mvY)
      (RFormula.and (RFormula.and (canonInvM gY gsY) (envLR domLY domRY))
        (mvValidR mvY GrY.modes.length))) :=
  story2_lateral_rung_a_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end Story2LateralA

namespace Story2LateralB
open RelCertifier.Story2LateralBModal

def spec : VerdSpec :=
  { bench := "story2_lateral_rung_b_12dof"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    order := [0, 1, 2, 4, 5, 6, 7, 3]
  }

theorem spec_components : (gZ :: gsZ) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdZ p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsZ dt))
      (rightAutomatonBody GrZ mvZ)
      (RFormula.and (RFormula.and (canonInvM gZ gsZ) (envLR domLZ domRZ))
        (mvValidR mvZ GrZ.modes.length))) :=
  story2_lateral_rung_b_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end Story2LateralB

namespace Story3RolloverBase
open RelCertifier.Story3RolloverBaseModal

def spec : VerdSpec :=
  { bench := "story3_rollover_base_12dof"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdB p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsB dt))
      (rightAutomatonBody GrB mvB)
      (RFormula.and (RFormula.and (canonInvM gB gsB) (envLR domLB domRB))
        (mvRegionR mvB regionB GrB.modes.length))) :=
  story3_rollover_base_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end Story3RolloverBase

namespace Story3RolloverRungA
open RelCertifier.Story3RolloverRungAModal

def spec : VerdSpec :=
  { bench := "story3_rollover_ladder_rung_a"
    pairs := [(0,0), (0,1), (0,2), (1,1), (1,2), (2,2)]
    modeDep := true
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdA p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsA dt))
      (rightAutomatonBody GrA mvA)
      (RFormula.and (RFormula.and (canonInvM gA gsA) (envLR domLA domRA))
        (mvRegionR mvA regionA GrA.modes.length))) :=
  story3_rollover_rung_a_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,1) (by decide)) (hv (1,2) (by decide)) (hv (2,2) (by decide))

end Story3RolloverRungA

namespace Story3RolloverRungB
open RelCertifier.Story3RolloverRungBModal

def spec : VerdSpec :=
  { bench := "story3_rollover_ladder_rung_b"
    pairs := [(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)]
    order := [0, 1]
  }

theorem spec_components : (gV :: gsV) = spec.order.map gAt := by rfl

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdV p.1 p.2

theorem modal_from_spec (dt : ℝ) (hdt : 0 ≤ dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsV dt))
      (rightAutomatonBody GrV mvV)
      (RFormula.and (RFormula.and (canonInvM gV gsV) (envLR domLV domRV))
        (mvValidR mvV GrV.modes.length))) :=
  story3_rollover_rung_b_modal dt hdt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (0,2) (by decide))
    (hv (1,0) (by decide)) (hv (1,1) (by decide)) (hv (1,2) (by decide))
    (hv (2,0) (by decide)) (hv (2,1) (by decide)) (hv (2,2) (by decide))

end Story3RolloverRungB

namespace Watertank
open RelCertifier.WatertankModal

def spec : VerdSpec :=
  { bench := "watertank"
    pairs := [(0,0), (0,1), (1,1), (2,0), (2,1), (2,2)]
    -- single-component invariant: no strata narrowing, so no order to pin
  }

def VerdAll : Prop := ∀ p ∈ spec.pairs, VerdW p.1 p.2

theorem modal_from_spec (dt : ℝ) (hES00 : ESW 0 0 dt) (hES01 : ESW 0 1 dt) (hES11 : ESW 1 1 dt) (hES20 : ESW 2 0 dt) (hES21 : ESW 2 1 dt) (hES22 : ESW 2 2 dt) (hv : VerdAll) :
    RFormula.rvalid (theorem3Form
      (bigChoice (leftProgsW dt))
      (rightAutomatonBody GrW mvM)
      (RFormula.and (RFormula.and (canonInv gW) (envLR domLW domRW))
        (mvValidR mvM GrW.modes.length))) :=
  watertank_modal dt
    (hv (0,0) (by decide)) (hv (0,1) (by decide)) (hv (1,1) (by decide))
    (hv (2,0) (by decide)) (hv (2,1) (by decide)) (hv (2,2) (by decide))
    hES00 hES01 hES11 hES20 hES21 hES22

end Watertank

/-- Every spec, for the runner to iterate. -/
def specs : List VerdSpec :=
  [EnduranceOrderlift1to2.spec, ArmChainRung1.spec, ArmChainRung2.spec, ArmChainRung3.spec, ArmFidelityHigh.spec, ArmFidelityLow.spec, ArmFidelityMid.spec, ArmRefinement.spec, AttitudeRate.spec, EnduranceGainM1.spec, EnduranceOrderlift2to3.spec, MatchMultiEps.spec, MatchMultiRate.spec, PlantFanHigh.spec, PlantFanLow.spec, PlantFanMid.spec, RobotBraking.spec, Rover3tierM1.spec, Rover3tierRung12Accel.spec, Rover3tierRung12Coast.spec, Rover4dBox.spec, RoverAttitudeCone.spec, RoverDofTerrainRung1.spec, RoverDofTerrainRung2.spec, RoverDofTerrainRung38d.spec, RoverDofTerrainRung3.spec, RoverDrag.spec, RoverLadderRung1.spec, RoverLadderRung2.spec, RoverLadderRung3.spec, RoverLadderRung4.spec, RoverRung2c.spec, RoverTerrainM1.spec, RoverTierR1.spec, Story1AttdistRungA.spec, Story1AttdistRungB.spec, Story2LateralA.spec, Story2LateralB.spec, Story3RolloverBase.spec, Story3RolloverRungA.spec, Story3RolloverRungB.spec, Watertank.spec]

end RelCertifier.ModalSpecs
