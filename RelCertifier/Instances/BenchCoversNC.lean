/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Cut-free covers (RELCERT_NO_CUT=1) — the throughout-battery inputs (do not edit)

The 33 benchmarks certifiable without checked-cut narrowing: their strata queries run
over the bare `evolveL ∧ evolveR` domains, so `segPresAll_from_strata_verdicts` applies
DIRECTLY (no cut lift). The 13 cut-reliant benchmarks are the documented follow-up
(guard-threaded cut lifting). Regenerate: `scripts/gen_covers_nc.sh`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_chain_rung1` (cut-free emission). -/
def arm_chain_rung1_coverNC : CoverEmitE :=
  ⟨"arm_chain_rung1", [], [
    ⟨"ApproachFast", (5 : ℚ) / 2, 3, [⟨"Approach", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"ApproachSlow", (3 : ℚ) / 2, 2, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Return", (1 : ℚ) / 1, 1, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", true, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", [0]⟩]⟩]⟩

/-- `arm_chain_rung2` (cut-free emission). -/
def arm_chain_rung2_coverNC : CoverEmitE :=
  ⟨"arm_chain_rung2", [], [
    ⟨"ApproachA", (7 : ℚ) / 4, 2, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"ApproachB", (5 : ℚ) / 4, 2, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"ApproachC", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Hold", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Return"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `arm_fidelity_low` (cut-free emission). -/
def arm_fidelity_low_coverNC : CoverEmitE :=
  ⟨"arm_fidelity_low", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `arm_fidelity_mid` (cut-free emission). -/
def arm_fidelity_mid_coverNC : CoverEmitE :=
  ⟨"arm_fidelity_mid", [], [
    ⟨"Accelerate", (9 : ℚ) / 2, 5, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (9 : ℚ) / 2, 5, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `arm_refinement` (cut-free emission). -/
def arm_refinement_coverNC : CoverEmitE :=
  ⟨"arm_refinement", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `attitude_rate` (cut-free emission). -/
def attitude_rate_coverNC : CoverEmitE :=
  ⟨"attitude_rate", [], [
    ⟨"CRUISE", (2 : ℚ) / 1, 2, [⟨"RECOVER", true, false, false, false, false⟩, ⟨"TRACK", true, true, true, false, false⟩], ["RECOVER", "TRACK"], [⟨"RECOVER", [0]⟩, ⟨"TRACK", [0]⟩]⟩]⟩

/-- `endurance_gain_M1` (cut-free emission). -/
def endurance_gain_M1_coverNC : CoverEmitE :=
  ⟨"endurance_gain_M1", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0]⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (3 : ℚ) / 2, 3, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `endurance_orderlift_1to2` (cut-free emission). -/
def endurance_orderlift_1to2_coverNC : CoverEmitE :=
  ⟨"endurance_orderlift_1to2", [], [
    ⟨"STEEP", (2 : ℚ) / 1, 4, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (2 : ℚ) / 1, 4, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (2 : ℚ) / 1, 4, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `endurance_orderlift_2to3` (cut-free emission). -/
def endurance_orderlift_2to3_coverNC : CoverEmitE :=
  ⟨"endurance_orderlift_2to3", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (3 : ℚ) / 2, 3, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `match_multi_eps` (cut-free emission). -/
def match_multi_eps_coverNC : CoverEmitE :=
  ⟨"match_multi_eps", [], [
    ⟨"ACCEL", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", false, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", []⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", true, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", [0]⟩]⟩]⟩

/-- `match_multi_rate` (cut-free emission). -/
def match_multi_rate_coverNC : CoverEmitE :=
  ⟨"match_multi_rate", [], [
    ⟨"FAST", (3 : ℚ) / 1, 3, [⟨"DRIVE", true, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩,
    ⟨"MEDIUM", (2 : ℚ) / 1, 2, [⟨"DRIVE", true, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩,
    ⟨"SLOW", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩,
    ⟨"RESET", (1 : ℚ) / 1, 1, [⟨"DRIVE", true, false, false, false, false⟩], ["DRIVE"], [⟨"DRIVE", [0]⟩]⟩]⟩

/-- `plant_fan_low` (cut-free emission). -/
def plant_fan_low_coverNC : CoverEmitE :=
  ⟨"plant_fan_low", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0]⟩, ⟨"Return", []⟩]⟩]⟩

/-- `plant_fan_mid` (cut-free emission). -/
def plant_fan_mid_coverNC : CoverEmitE :=
  ⟨"plant_fan_mid", [], [
    ⟨"Accelerate", (15 : ℚ) / 4, 4, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, true, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Hold", [0]⟩]⟩,
    ⟨"Brake", (15 : ℚ) / 4, 4, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, true, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0]⟩, ⟨"ApproachSlow", [0]⟩, ⟨"Hold", [0]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2_3to6` (cut-free emission). -/
def refinement_ladder_rover_rung2_3to6_coverNC : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_3to6", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 2, 3, 1]⟩, ⟨"MODER", [0, 2, 3, 1]⟩, ⟨"FLAT", [0, 2, 3, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [0, 2, 3, 1]⟩, ⟨"FLAT", [0, 2, 3, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 3]⟩, ⟨"MODER", [2, 3]⟩, ⟨"FLAT", [0, 2, 3, 1]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2_6dof` (cut-free emission). -/
def refinement_ladder_rover_rung2_6dof_coverNC : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_6dof", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, true, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0]⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2b_6dof` (cut-free emission). -/
def refinement_ladder_rover_rung2b_6dof_coverNC : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2b_6dof", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, true, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0]⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", [0]⟩, ⟨"FLAT", [0]⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, false, false, true, true⟩, ⟨"MODER", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", []⟩, ⟨"MODER", []⟩, ⟨"FLAT", [0]⟩]⟩]⟩

/-- `refinement_ladder_rover_rung2c_6dof` (cut-free emission). -/
def refinement_ladder_rover_rung2c_6dof_coverNC : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2c_6dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", false, false, false, false, false⟩], ["STEEP"], [⟨"STEEP", [0, 1, 4, 5, 6, 7, 2, 3]⟩, ⟨"MODER", [0, 4, 5, 6, 7, 2]⟩, ⟨"FLAT", [0, 4, 5, 6, 7, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", false, false, false, false, false⟩], ["MODER"], [⟨"STEEP", [1, 4, 5, 6, 7, 3]⟩, ⟨"MODER", [0, 1, 4, 5, 6, 7, 2, 3]⟩, ⟨"FLAT", [0, 4, 5, 6, 7, 2]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 4, 5, 6, 7, 3]⟩, ⟨"MODER", [1, 4, 5, 6, 7, 3]⟩, ⟨"FLAT", [0, 1, 4, 5, 6, 7, 2, 3]⟩]⟩]⟩

/-- `robot_braking` (cut-free emission). -/
def robot_braking_coverNC : CoverEmitE :=
  ⟨"robot_braking", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"FAST", false, true, true, false, false⟩, ⟨"MID", false, true, true, false, false⟩, ⟨"SLOW", true, false, false, false, false⟩], ["FAST", "MID", "SLOW"], [⟨"FAST", []⟩, ⟨"MID", []⟩, ⟨"SLOW", [0]⟩]⟩]⟩

/-- `rover3_M1` (cut-free emission). -/
def rover3_M1_coverNC : CoverEmitE :=
  ⟨"rover3_M1", [], [
    ⟨"Drive", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Drift", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Stop", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩]⟩

/-- `rover3tier_M1` (cut-free emission). -/
def rover3tier_M1_coverNC : CoverEmitE :=
  ⟨"rover_patrol_simple", [], [
    ⟨"ACCEL", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", false, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", []⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, false, false⟩, ⟨"COAST", true, true, true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", [0]⟩]⟩]⟩

/-- `rover3tier_rung12` (cut-free emission). -/
def rover3tier_rung12_coverNC : CoverEmitE :=
  ⟨"rover3tier_rung12", [], [
    ⟨"ACCEL", (2 : ℚ) / 1, 7, [⟨"ACCEL", true, false, false, true, true⟩, ⟨"COAST", true, true, false, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0, 1]⟩, ⟨"COAST", [0, 1]⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, true, true⟩, ⟨"COAST", true, false, false, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0]⟩, ⟨"COAST", [0]⟩]⟩]⟩

/-- `rover_4d_box` (cut-free emission). -/
def rover_4d_box_coverNC : CoverEmitE :=
  ⟨"rover_4d_box", [], [
    ⟨"HOLD", (1 : ℚ) / 1, 1, [⟨"APPROACH", true, false, false, true, true⟩, ⟨"SETTLE", true, false, false, true, true⟩], ["APPROACH", "SETTLE"], [⟨"APPROACH", [0]⟩, ⟨"SETTLE", [0]⟩]⟩]⟩

/-- `rover_coupled` (cut-free emission). -/
def rover_coupled_coverNC : CoverEmitE :=
  ⟨"rover_coupled", [], [
    ⟨"Drive", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Drift", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Stop", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩]⟩

/-- `rover_drag` (cut-free emission). -/
def rover_drag_coverNC : CoverEmitE :=
  ⟨"rover_drag", [], [
    ⟨"Cruise", (1 : ℚ) / 1, 1, [⟨"Track", true, false, false, false, false⟩], ["Track"], [⟨"Track", [0]⟩]⟩]⟩

/-- `rover_position` (cut-free emission). -/
def rover_position_coverNC : CoverEmitE :=
  ⟨"rover_position", [], [
    ⟨"Drive", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Drift", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩,
    ⟨"Stop", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0]⟩, ⟨"Drive", [0]⟩, ⟨"Safe", [0]⟩]⟩]⟩

/-- `rover_terrain_M1` (cut-free emission). -/
def rover_terrain_M1_coverNC : CoverEmitE :=
  ⟨"rover_terrain_M1", [], [
    ⟨"ROUGH", (1 : ℚ) / 1, 2, [⟨"ROUGH", true, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", [0]⟩, ⟨"FLAT", [0]⟩, ⟨"SMOOTH", [0]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 2, [⟨"ROUGH", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", []⟩, ⟨"FLAT", [0]⟩, ⟨"SMOOTH", [0]⟩]⟩,
    ⟨"SMOOTH", (3 : ℚ) / 2, 3, [⟨"ROUGH", false, false, false, true, true⟩, ⟨"FLAT", true, false, false, true, true⟩, ⟨"SMOOTH", true, false, false, true, true⟩], ["ROUGH", "FLAT", "SMOOTH"], [⟨"ROUGH", []⟩, ⟨"FLAT", [0]⟩, ⟨"SMOOTH", [0]⟩]⟩]⟩

/-- `rover_tier_r1` (cut-free emission). -/
def rover_tier_r1_coverNC : CoverEmitE :=
  ⟨"rover_tier_r1", [], [
    ⟨"Cruise", (23 : ℚ) / 4, 6, [⟨"Cruise", true, false, false, true, true⟩], ["Cruise"], [⟨"Cruise", [0]⟩]⟩]⟩

/-- `story1_attdist_rung_a_6to8` (cut-free emission). -/
def story1_attdist_rung_a_6to8_coverNC : CoverEmitE :=
  ⟨"story1_attdist_rung_a_6to8", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `story1_attdist_rung_b_12dof` (cut-free emission). -/
def story1_attdist_rung_b_12dof_coverNC : CoverEmitE :=
  ⟨"story1_attdist_rung_b_12dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `story2_lateral_rung_a_8dof` (cut-free emission). -/
def story2_lateral_rung_a_8dof_coverNC : CoverEmitE :=
  ⟨"story2_lateral_rung_a_8dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 3, 4, 5, 6, 2]⟩, ⟨"MODER", [0, 1, 3, 4, 5, 6, 2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [1, 3, 4, 5, 6]⟩, ⟨"MODER", [0, 1, 3, 4, 5, 6, 2]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 3, 4, 5, 6]⟩, ⟨"MODER", [1, 3, 4, 5, 6]⟩, ⟨"FLAT", [0, 1, 3, 4, 5, 6, 2]⟩]⟩]⟩

/-- `story2_lateral_rung_b_12dof` (cut-free emission). -/
def story2_lateral_rung_b_12dof_coverNC : CoverEmitE :=
  ⟨"story2_lateral_rung_b_12dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 4, 5, 6, 7, 3]⟩, ⟨"MODER", [0, 1, 2, 4, 5, 6, 7, 3]⟩, ⟨"FLAT", [0, 1, 2, 4, 5, 6, 7, 3]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [1, 2, 4, 5, 6, 7]⟩, ⟨"MODER", [0, 1, 2, 4, 5, 6, 7, 3]⟩, ⟨"FLAT", [0, 1, 2, 4, 5, 6, 7, 3]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false, false, false⟩, ⟨"MODER", false, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 2, 4, 5, 6, 7]⟩, ⟨"MODER", [1, 2, 4, 5, 6, 7]⟩, ⟨"FLAT", [0, 1, 2, 4, 5, 6, 7, 3]⟩]⟩]⟩

/-- `story3_rollover_ladder_rung_b` (cut-free emission). -/
def story3_rollover_ladder_rung_b_coverNC : CoverEmitE :=
  ⟨"story3_rollover_ladder_rung_b", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false, false, false⟩, ⟨"MODER", true, false, false, false, false⟩, ⟨"FLAT", true, false, false, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1]⟩, ⟨"MODER", [0, 1]⟩, ⟨"FLAT", [0, 1]⟩]⟩]⟩

/-- `watertank` (cut-free emission). -/
def watertank_coverNC : CoverEmitE :=
  ⟨"watertank", [], [
    ⟨"Low", (1 : ℚ) / 1, 1, [⟨"Low", true, false, false, false, false⟩, ⟨"Mid", true, true, false, true, true⟩, ⟨"High", false, true, false, false, false⟩], ["Low", "Mid", "High"], [⟨"Low", [0]⟩, ⟨"Mid", [0]⟩, ⟨"High", []⟩]⟩,
    ⟨"Mid", (1 : ℚ) / 1, 1, [⟨"Low", false, false, false, false, false⟩, ⟨"Mid", true, false, false, true, true⟩, ⟨"High", false, true, false, false, false⟩], ["Mid", "High"], [⟨"Low", []⟩, ⟨"Mid", [0]⟩, ⟨"High", []⟩]⟩,
    ⟨"High", (1 : ℚ) / 1, 1, [⟨"Low", true, false, false, false, false⟩, ⟨"Mid", true, false, false, true, true⟩, ⟨"High", true, false, false, false, false⟩], ["High"], [⟨"Low", [0]⟩, ⟨"Mid", [0]⟩, ⟨"High", [0]⟩]⟩]⟩

end RelCertifier
