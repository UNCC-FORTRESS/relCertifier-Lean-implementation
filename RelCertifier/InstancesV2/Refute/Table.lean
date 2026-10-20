/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The refutation records (the runner's table) (GENERATED — `scripts/gen_refute.py`)

-/
import RelCertifier.InstancesV2.Refute.Data.acc_spoof_limp_m008
import RelCertifier.InstancesV2.Refute.Data.acc_tune_limp_m008
import RelCertifier.InstancesV2.Refute.Data.platoon3_linkloss_m072
import RelCertifier.InstancesV2.Refute.Data.platoon3_linkloss_m084
import RelCertifier.InstancesV2.Refute.Data.platoon3_linkloss_m096
import RelCertifier.InstancesV2.Refute.Data.rover3tier_rung12_m000
import RelCertifier.InstancesV2.Refute.Data.rover_patrol_refine_m009
import RelCertifier.InstancesV2.Refute.Data.rover_patrol_refine_m013
import RelCertifier.InstancesV2.Refute.Data.rover_patrol_zones_m008
import RelCertifier.InstancesV2.Refute.Data.rover_patrol_zones_m012
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m000
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m001
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m002
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m003
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m004
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m005
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m006
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m007
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m000
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m001
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m002
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m003
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m004
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m005
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m006
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m007
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m019
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m022
import RelCertifier.InstancesV2.Cuts.acc_spoof_limp
import RelCertifier.InstancesV2.Cuts.acc_tune_limp
import RelCertifier.InstancesV2.Cuts.platoon3_linkloss
import RelCertifier.InstancesV2.Cuts.rover3tier_rung12
import RelCertifier.InstancesV2.Cuts.rover_patrol_refine
import RelCertifier.InstancesV2.Cuts.rover_patrol_zones
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat_detumble_phases
import RelCertifier.Checker.EvolStrengtheningX

namespace RelCertifier.Refute

open RelCertifier.Parse RelCertifier.Oracle

/-- A refutation's records: the mutant's IR at its bridge dimension, the model's cut certificate, the witness. -/
structure RefRec where
  name : String
  dim : ℕ
  ir : PProblem
  cuts : EvolStrengtheningX
  wit : RefWitE

def refuteTable : List RefRec := [
  ⟨"acc_spoof_limp_m008", 3, acc_spoof_limp_m008_IRm, acc_spoof_limp_cutsV2X, acc_spoof_limp_m008_wit⟩,
  ⟨"acc_tune_limp_m008", 3, acc_tune_limp_m008_IRm, acc_tune_limp_cutsV2X, acc_tune_limp_m008_wit⟩,
  ⟨"platoon3_linkloss_m072", 6, platoon3_linkloss_m072_IRm, platoon3_linkloss_cutsV2X, platoon3_linkloss_m072_wit⟩,
  ⟨"platoon3_linkloss_m084", 6, platoon3_linkloss_m084_IRm, platoon3_linkloss_cutsV2X, platoon3_linkloss_m084_wit⟩,
  ⟨"platoon3_linkloss_m096", 6, platoon3_linkloss_m096_IRm, platoon3_linkloss_cutsV2X, platoon3_linkloss_m096_wit⟩,
  ⟨"rover3tier_rung12_m000", 3, rover3tier_rung12_m000_IRm, rover3tier_rung12_cutsV2X, rover3tier_rung12_m000_wit⟩,
  ⟨"rover_patrol_refine_m009", 3, rover_patrol_refine_m009_IRm, rover_patrol_refine_cutsV2X, rover_patrol_refine_m009_wit⟩,
  ⟨"rover_patrol_refine_m013", 3, rover_patrol_refine_m013_IRm, rover_patrol_refine_cutsV2X, rover_patrol_refine_m013_wit⟩,
  ⟨"rover_patrol_zones_m008", 3, rover_patrol_zones_m008_IRm, rover_patrol_zones_cutsV2X, rover_patrol_zones_m008_wit⟩,
  ⟨"rover_patrol_zones_m012", 3, rover_patrol_zones_m012_IRm, rover_patrol_zones_cutsV2X, rover_patrol_zones_m012_wit⟩,
  ⟨"sat3w_detumble_phases_m000", 6, sat3w_detumble_phases_m000_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m000_wit⟩,
  ⟨"sat3w_detumble_phases_m001", 6, sat3w_detumble_phases_m001_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m001_wit⟩,
  ⟨"sat3w_detumble_phases_m002", 6, sat3w_detumble_phases_m002_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m002_wit⟩,
  ⟨"sat3w_detumble_phases_m003", 6, sat3w_detumble_phases_m003_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m003_wit⟩,
  ⟨"sat3w_detumble_phases_m004", 6, sat3w_detumble_phases_m004_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m004_wit⟩,
  ⟨"sat3w_detumble_phases_m005", 6, sat3w_detumble_phases_m005_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m005_wit⟩,
  ⟨"sat3w_detumble_phases_m006", 6, sat3w_detumble_phases_m006_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m006_wit⟩,
  ⟨"sat3w_detumble_phases_m007", 6, sat3w_detumble_phases_m007_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m007_wit⟩,
  ⟨"sat_detumble_phases_m000", 4, sat_detumble_phases_m000_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m000_wit⟩,
  ⟨"sat_detumble_phases_m001", 4, sat_detumble_phases_m001_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m001_wit⟩,
  ⟨"sat_detumble_phases_m002", 4, sat_detumble_phases_m002_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m002_wit⟩,
  ⟨"sat_detumble_phases_m003", 4, sat_detumble_phases_m003_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m003_wit⟩,
  ⟨"sat_detumble_phases_m004", 4, sat_detumble_phases_m004_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m004_wit⟩,
  ⟨"sat_detumble_phases_m005", 4, sat_detumble_phases_m005_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m005_wit⟩,
  ⟨"sat_detumble_phases_m006", 4, sat_detumble_phases_m006_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m006_wit⟩,
  ⟨"sat_detumble_phases_m007", 4, sat_detumble_phases_m007_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m007_wit⟩,
  ⟨"sat_detumble_phases_m019", 4, sat_detumble_phases_m019_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m019_wit⟩,
  ⟨"sat_detumble_phases_m022", 4, sat_detumble_phases_m022_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m022_wit⟩ ]

/-- Declared: the number of query groups over the refutations (one per right mode each). -/
def expectedRefuteGroups : Nat := 76

end RelCertifier.Refute
