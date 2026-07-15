/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Tool-emitted covers (do not edit — `relcert --emit-cover`, drift-checked)

One `CoverEmitE` literal per certified benchmark: the search's successful cover
(λ, budget, certificate flags, admissible starts, strata orders, pruned edges).
Regenerate: `scripts/gen_covers.sh`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_chain_rung1` (emitted). -/
def arm_chain_rung1_cover : CoverEmitE :=
  ⟨"arm_chain_rung1", [], [
    ⟨"ApproachFast", (5 : ℚ) / 2, 3, [⟨"Approach", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"ApproachSlow", (3 : ℚ) / 2, 2, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Return", (1 : ℚ) / 1, 1, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", true, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", [0]⟩]⟩]⟩

/-- `arm_chain_rung2` (emitted). -/
def arm_chain_rung2_cover : CoverEmitE :=
  ⟨"arm_chain_rung2", [], [
    ⟨"ApproachA", (7 : ℚ) / 4, 2, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"ApproachB", (5 : ℚ) / 4, 2, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"ApproachC", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Hold", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `arm_chain_rung3` (emitted). -/
def arm_chain_rung3_cover : CoverEmitE :=
  ⟨"arm_chain_rung3", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, true, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0]⟩, ⟨"ApproachB", []⟩, ⟨"ApproachC", []⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, false, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0]⟩, ⟨"ApproachB", []⟩, ⟨"ApproachC", []⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `arm_fidelity_high` (emitted). -/
def arm_fidelity_high_cover : CoverEmitE :=
  ⟨"arm_fidelity_high", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, true, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0]⟩, ⟨"ApproachB", []⟩, ⟨"ApproachC", []⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, false, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0]⟩, ⟨"ApproachB", []⟩, ⟨"ApproachC", []⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `arm_fidelity_low` (emitted). -/
def arm_fidelity_low_cover : CoverEmitE :=
  ⟨"arm_fidelity_low", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `arm_fidelity_mid` (emitted). -/
def arm_fidelity_mid_cover : CoverEmitE :=
  ⟨"arm_fidelity_mid", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", false, true, false, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", []⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", false, true, false, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", []⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `arm_refinement` (emitted). -/
def arm_refinement_cover : CoverEmitE :=
  ⟨"arm_refinement", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `attitude_rate` (emitted). -/
def attitude_rate_cover : CoverEmitE :=
  ⟨"attitude_rate", [], [
    ⟨"CRUISE", (2 : ℚ) / 1, 2, [⟨"RECOVER", true, false, false, false, false⟩, ⟨"TRACK", true, true, true, false, false⟩], ["RECOVER", "TRACK"], [⟨"RECOVER", [0]⟩, ⟨"TRACK", [0]⟩]⟩]⟩

/-- `endurance_gain_M1` (emitted). -/
def endurance_gain_M1_cover : CoverEmitE :=
  ⟨"endurance_gain_M1", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0]⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (3 : ℚ) / 2, 3, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `endurance_orderlift_1to2` (emitted). -/
def endurance_orderlift_1to2_cover : CoverEmitE :=
  ⟨"endurance_orderlift_1to2", [], [
    ⟨"STEEP", (2 : ℚ) / 1, 4, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (2 : ℚ) / 1, 4, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (2 : ℚ) / 1, 4, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `endurance_orderlift_2to3` (emitted). -/
def endurance_orderlift_2to3_cover : CoverEmitE :=
  ⟨"endurance_orderlift_2to3", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (3 : ℚ) / 2, 3, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `match_multi_eps` (emitted). -/
def match_multi_eps_cover : CoverEmitE :=
  ⟨"match_multi_eps", [], [
    ⟨"ACCEL", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", false, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", []⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", true, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", [0]⟩]⟩]⟩

/-- `match_multi_rate` (emitted). -/
def match_multi_rate_cover : CoverEmitE :=
  ⟨"match_multi_rate", [], [
    ⟨"FAST", (3 : ℚ) / 1, 3, [⟨"DRIVE", true, false, false, true, true⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩,
    ⟨"MEDIUM", (2 : ℚ) / 1, 2, [⟨"DRIVE", true, false, false, true, true⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩,
    ⟨"SLOW", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, false, false, true, true⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩,
    ⟨"RESET", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, false, false, true, true⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩]⟩

/-- `plant_fan_high` (emitted). -/
def plant_fan_high_cover : CoverEmitE :=
  ⟨"plant_fan_high", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, true, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0]⟩, ⟨"ApproachB", []⟩, ⟨"ApproachC", []⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, false, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0]⟩, ⟨"ApproachB", []⟩, ⟨"ApproachC", []⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `plant_fan_low` (emitted). -/
def plant_fan_low_cover : CoverEmitE :=
  ⟨"plant_fan_low", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `plant_fan_mid` (emitted). -/
def plant_fan_mid_cover : CoverEmitE :=
  ⟨"plant_fan_mid", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", false, true, true, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", []⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", false, true, true, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", []⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung1_2to3` (emitted). -/
def refinement_ladder_rover_rung1_2to3_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung1_2to3", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2_3to6` (emitted). -/
def refinement_ladder_rover_rung2_3to6_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_3to6", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 2, 3, 1]⟩, ⟨"MODER", [0, 2, 3, 1]⟩, ⟨"FLAT", [0, 2, 3, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [0, 2, 3, 1]⟩, ⟨"FLAT", [0, 2, 3, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [2, 3]⟩, ⟨"FLAT", [0, 2, 3, 1]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2_6dof` (emitted). -/
def refinement_ladder_rover_rung2_6dof_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_6dof", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, true, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0]⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2b_6dof` (emitted). -/
def refinement_ladder_rover_rung2b_6dof_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2b_6dof", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, true, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0]⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2c_6dof` (emitted). -/
def refinement_ladder_rover_rung2c_6dof_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2c_6dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", false, false, false, false, false⟩], ["STEEP"], [⟨"STEEP", [0, 1, 4, 5, 6, 7, 2, 3]⟩, ⟨"MODER", [0, 4, 5, 6, 7, 2]⟩, ⟨"FLAT", [0, 4, 5, 6, 7, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", false, false, false, false, false⟩], ["MODER"], [⟨"STEEP", [1, 4, 5, 6, 7, 3]⟩, ⟨"MODER", [0, 1, 4, 5, 6, 7, 2, 3]⟩, ⟨"FLAT", [0, 4, 5, 6, 7, 2]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 4, 5, 6, 7, 3]⟩, ⟨"MODER", [1, 4, 5, 6, 7, 3]⟩, ⟨"FLAT", [0, 1, 4, 5, 6, 7, 2, 3]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung3_6to8` (emitted). -/
def refinement_ladder_rover_rung3_6to8_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung3_6to8", [], [
    ⟨"STEEP", (9 : ℚ) / 4, 3, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3]⟩]⟩,
    ⟨"MODER", (9 : ℚ) / 4, 3, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3]⟩]⟩,
    ⟨"FLAT", (9 : ℚ) / 4, 3, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung4_8to12` (emitted). -/
def refinement_ladder_rover_rung4_8to12_cover : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung4_8to12", [], [
    ⟨"STEEP", (17 : ℚ) / 10, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (17 : ℚ) / 10, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (17 : ℚ) / 10, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `robot_braking` (emitted). -/
def robot_braking_cover : CoverEmitE :=
  ⟨"robot_braking", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"FAST", false, true, true, false, false⟩, ⟨"MID", false, true, true, false, false⟩, ⟨"SLOW", true, false, false, false, false⟩], ["FAST", "MID", "SLOW"], [⟨"FAST", []⟩, ⟨"MID", []⟩, ⟨"SLOW", [0]⟩]⟩]⟩

/-- `rover3_M1` (emitted). -/
def rover3_M1_cover : CoverEmitE :=
  ⟨"rover3_M1", [], [
    ⟨"Drive", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Drift", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Stop", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩]⟩

/-- `rover3tier_M1` (emitted). -/
def rover3tier_M1_cover : CoverEmitE :=
  ⟨"rover_patrol_simple", [], [
    ⟨"ACCEL", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", false, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", []⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", true, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", [0]⟩]⟩]⟩

/-- `rover3tier_rung12` (emitted). -/
def rover3tier_rung12_cover : CoverEmitE :=
  ⟨"rover3tier_rung12", [], [
    ⟨"ACCEL", (2 : ℚ) / 1, 7, [⟨"ACCEL", true, false, false, true, true⟩, ⟨"COAST", true, true, false, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0, 1]⟩, ⟨"COAST", [0, 1]⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, true, true⟩, ⟨"COAST", true, false, false, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", [0]⟩]⟩]⟩

/-- `rover_4d_box` (emitted). -/
def rover_4d_box_cover : CoverEmitE :=
  ⟨"rover_4d_box", [], [
    ⟨"HOLD", (1 : ℚ) / 1, 1, [⟨"APPROACH", true, false, false, true, true⟩, ⟨"SETTLE", true, false, false, true, true⟩], ["APPROACH", "SETTLE"], [⟨"APPROACH", [0]⟩, ⟨"SETTLE", [0]⟩]⟩]⟩

/-- `rover_attitude_cone_12dof` (emitted). -/
def rover_attitude_cone_12dof_cover : CoverEmitE :=
  ⟨"rover_attitude_cone_12dof", [], [
    ⟨"STEEP", (17 : ℚ) / 10, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3]⟩]⟩,
    ⟨"MODER", (17 : ℚ) / 10, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3]⟩]⟩,
    ⟨"FLAT", (17 : ℚ) / 10, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3]⟩]⟩]⟩

/-- `rover_coupled` (emitted). -/
def rover_coupled_cover : CoverEmitE :=
  ⟨"rover_coupled", [], [
    ⟨"Drive", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Drift", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Stop", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩]⟩

/-- `rover_dof_terrain_rung1` (emitted). -/
def rover_dof_terrain_rung1_cover : CoverEmitE :=
  ⟨"rover_dof_terrain_rung1", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `rover_dof_terrain_rung2` (emitted). -/
def rover_dof_terrain_rung2_cover : CoverEmitE :=
  ⟨"rover_dof_terrain_rung2", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `rover_dof_terrain_rung3` (emitted). -/
def rover_dof_terrain_rung3_cover : CoverEmitE :=
  ⟨"rover_dof_terrain_rung3", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `rover_dof_terrain_rung3_8d` (emitted). -/
def rover_dof_terrain_rung3_8d_cover : CoverEmitE :=
  ⟨"rover_dof_terrain_rung3_8d", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `rover_drag` (emitted). -/
def rover_drag_cover : CoverEmitE :=
  ⟨"rover_drag", [], [
    ⟨"Cruise", (1 : ℚ) / 1, 1, [⟨"Track", true, false, false, false, false⟩], ["Track"], [⟨"Track", [0]⟩]⟩]⟩

/-- `rover_position` (emitted). -/
def rover_position_cover : CoverEmitE :=
  ⟨"rover_position", [], [
    ⟨"Drive", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Drift", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Stop", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", []⟩, ⟨"Drive", []⟩, ⟨"Safe", [0]⟩]⟩]⟩

/-- `rover_terrain_M1` (emitted). -/
def rover_terrain_M1_cover : CoverEmitE :=
  ⟨"rover_terrain_M1", [], [
    ⟨"ROUGH", (1 : ℚ) / 1, 2, [⟨"ROUGH", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", [0]⟩, ⟨"FLAT", [0]⟩, ⟨"SMOOTH", [0]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 2, [⟨"ROUGH", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", []⟩, ⟨"FLAT", [0]⟩, ⟨"SMOOTH", [0]⟩]⟩,
    ⟨"SMOOTH", (3 : ℚ) / 2, 3, [⟨"ROUGH", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", []⟩, ⟨"FLAT", [0]⟩, ⟨"SMOOTH", [0]⟩]⟩]⟩

/-- `rover_tier_r1` (emitted). -/
def rover_tier_r1_cover : CoverEmitE :=
  ⟨"rover_tier_r1", [], [
    ⟨"Cruise", (19 : ℚ) / 4, 5, [⟨"Cruise", true, false, false, true, true⟩], ["Cruise"], [⟨"Cruise", [0]⟩]⟩]⟩

/-- `story1_attdist_rung_a_6to8` (emitted). -/
def story1_attdist_rung_a_6to8_cover : CoverEmitE :=
  ⟨"story1_attdist_rung_a_6to8", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `story1_attdist_rung_b_12dof` (emitted). -/
def story1_attdist_rung_b_12dof_cover : CoverEmitE :=
  ⟨"story1_attdist_rung_b_12dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `story2_lateral_rung_a_8dof` (emitted). -/
def story2_lateral_rung_a_8dof_cover : CoverEmitE :=
  ⟨"story2_lateral_rung_a_8dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 3, 4, 5, 6, 2]⟩, ⟨"MODER", [0, 1, 3, 4, 5, 6, 2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [1, 3, 4, 5, 6]⟩, ⟨"MODER", [0, 1, 3, 4, 5, 6, 2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 3, 4, 5, 6]⟩, ⟨"MODER", [1, 3, 4, 5, 6]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2]⟩]⟩]⟩

/-- `story2_lateral_rung_b_12dof` (emitted). -/
def story2_lateral_rung_b_12dof_cover : CoverEmitE :=
  ⟨"story2_lateral_rung_b_12dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 4, 5, 6, 7, 3]⟩, ⟨"MODER", [0, 1, 2, 4, 5, 6, 7, 3]⟩, ⟨"FLAT", [0, 1, 2, 4, 5, 6, 7, 3]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [1, 2, 4, 5, 6, 7]⟩, ⟨"MODER", [0, 1, 2, 4, 5, 6, 7, 3]⟩, ⟨"FLAT", [0, 1, 2, 4, 5, 6, 7, 3]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 2, 4, 5, 6, 7]⟩, ⟨"MODER", [1, 2, 4, 5, 6, 7]⟩, ⟨"FLAT", [0, 1, 2, 4, 5, 6, 7, 3]⟩]⟩]⟩

/-- `story3_rollover_base_12dof` (emitted). -/
def story3_rollover_base_12dof_cover : CoverEmitE :=
  ⟨"story3_rollover_base_12dof", [], [
    ⟨"STEEP", (5 : ℚ) / 4, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3, 4]⟩, ⟨"MODER", [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4]⟩]⟩,
    ⟨"MODER", (5 : ℚ) / 4, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3, 4]⟩, ⟨"MODER", [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4]⟩]⟩,
    ⟨"FLAT", (5 : ℚ) / 4, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [4, 2, 3]⟩, ⟨"MODER", [4, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3, 4]⟩]⟩]⟩

/-- `story3_rollover_ladder_rung_a` (emitted). -/
def story3_rollover_ladder_rung_a_cover : CoverEmitE :=
  ⟨"story3_rollover_ladder_rung_a", [], [
    ⟨"STEEP", (27 : ℚ) / 20, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (27 : ℚ) / 20, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"FLAT", (27 : ℚ) / 20, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2]⟩, ⟨"MODER", [2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩]⟩

/-- `story3_rollover_ladder_rung_b` (emitted). -/
def story3_rollover_ladder_rung_b_cover : CoverEmitE :=
  ⟨"story3_rollover_ladder_rung_b", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `watertank` (emitted). -/
def watertank_cover : CoverEmitE :=
  ⟨"watertank", [], [
    ⟨"Low", (1 : ℚ) / 1, 1, [⟨"Low", true, false, false, false, false⟩, ⟨"Mid", true, true, false, true, true⟩, ⟨"High", false, true, false, false, false⟩], ["Low", "Mid", "High"], [⟨"Low", [0]⟩, ⟨"Mid", [0]⟩, ⟨"High", []⟩]⟩,
    ⟨"Mid", (1 : ℚ) / 1, 1, [⟨"Low", false, false, false, false, false⟩, ⟨"Mid", true, false, false, true, true⟩, ⟨"High", false, true, false, false, false⟩], ["Mid", "High"], [⟨"Low", []⟩, ⟨"Mid", [0]⟩, ⟨"High", []⟩]⟩,
    ⟨"High", (1 : ℚ) / 1, 1, [⟨"Low", true, false, false, false, false⟩, ⟨"Mid", true, false, false, true, true⟩, ⟨"High", true, false, false, false, false⟩], ["High"], [⟨"Low", [0]⟩, ⟨"Mid", [0]⟩, ⟨"High", [0]⟩]⟩]⟩

end RelCertifier
