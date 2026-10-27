/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# The refutation records (the runner's table) (GENERATED — `scripts/gen_refute.py`)

-/
import RelCertifier.InstancesV2.Refute.Data.quad_light_lag_m021
import RelCertifier.InstancesV2.Refute.Data.quad_light_lag_m023
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_6to8_m006
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_6to8_m009
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m005
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m006
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m008
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m009
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m010
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m019
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m026
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_2to4_m008
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_2to4_m011
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_2to4_m012
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_2to4_m015
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m016
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m017
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m019
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m020
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m021
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m022
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m024
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_4to6_m028
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m020
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m021
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m023
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m024
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m025
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m026
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m028
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m029
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m030
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m032
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m035
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m037
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m039
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m040
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m041
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m042
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m043
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m044
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m045
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m046
import RelCertifier.InstancesV2.Refute.Data.rover_terrain_6to12_m047
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m002
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m003
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m004
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m005
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m006
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m007
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m002
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m003
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m005
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m006
import RelCertifier.InstancesV2.Refute.Data.platoon_latency_m040
import RelCertifier.InstancesV2.Refute.Data.platoon_latency_m043
import RelCertifier.InstancesV2.Refute.Data.platoon_linkloss_m036
import RelCertifier.InstancesV2.Refute.Data.platoon_linkloss_m039
import RelCertifier.InstancesV2.Refute.Data.engine_start_highidle_m003
import RelCertifier.InstancesV2.Refute.Data.platoon_profiles_m008
import RelCertifier.InstancesV2.Refute.Data.platoon_profiles_m011
import RelCertifier.InstancesV2.Refute.Data.hydro_rejection_gatecal_m024
import RelCertifier.InstancesV2.Refute.Data.hydro_rejection_gatecal_m028
import RelCertifier.InstancesV2.Refute.Data.ventilator_vc_cuffleak_m020
import RelCertifier.InstancesV2.Cuts.engine_start_highidle
import RelCertifier.InstancesV2.Cuts.hydro_rejection_gatecal
import RelCertifier.InstancesV2.Cuts.platoon_latency
import RelCertifier.InstancesV2.Cuts.platoon_linkloss
import RelCertifier.InstancesV2.Cuts.platoon_profiles
import RelCertifier.InstancesV2.Cuts.quad_light_lag
import RelCertifier.InstancesV2.Cuts.rover_ladder_6to8
import RelCertifier.InstancesV2.Cuts.rover_ladder_8to12
import RelCertifier.InstancesV2.Cuts.rover_terrain_2to4
import RelCertifier.InstancesV2.Cuts.rover_terrain_4to6
import RelCertifier.InstancesV2.Cuts.rover_terrain_6to12
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases
import RelCertifier.InstancesV2.Cuts.sat_detumble_phases
import RelCertifier.InstancesV2.Cuts.ventilator_vc_cuffleak
import RelCertifier.Checker.EvolStrengtheningX

namespace RelCertifier.Refute

open RelCertifier.Parse RelCertifier.Oracle

/-- A refutation's records: the mutant's IR at its bridge dimension (the Assumption 1 lemma's dimension plus one for the right clock, `bridgeDimV2`'s rule), the model's cut certificate, the witness. -/
structure RefRec where
  name : String
  dim : ℕ
  ir : PProblem
  cuts : EvolStrengtheningX
  wit : RefWitE

def refuteTable : List RefRec := [
  ⟨"quad_light_lag_m021", 3 + 1, quad_light_lag_m021_IRm, quad_light_lag_cutsV2X, quad_light_lag_m021_wit⟩,
  ⟨"quad_light_lag_m023", 3 + 1, quad_light_lag_m023_IRm, quad_light_lag_cutsV2X, quad_light_lag_m023_wit⟩,
  ⟨"rover_ladder_6to8_m006", 8 + 1, rover_ladder_6to8_m006_IRm, rover_ladder_6to8_cutsV2X, rover_ladder_6to8_m006_wit⟩,
  ⟨"rover_ladder_6to8_m009", 8 + 1, rover_ladder_6to8_m009_IRm, rover_ladder_6to8_cutsV2X, rover_ladder_6to8_m009_wit⟩,
  ⟨"rover_ladder_8to12_m005", 12 + 1, rover_ladder_8to12_m005_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m005_wit⟩,
  ⟨"rover_ladder_8to12_m006", 12 + 1, rover_ladder_8to12_m006_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m006_wit⟩,
  ⟨"rover_ladder_8to12_m008", 12 + 1, rover_ladder_8to12_m008_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m008_wit⟩,
  ⟨"rover_ladder_8to12_m009", 12 + 1, rover_ladder_8to12_m009_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m009_wit⟩,
  ⟨"rover_ladder_8to12_m010", 12 + 1, rover_ladder_8to12_m010_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m010_wit⟩,
  ⟨"rover_ladder_8to12_m019", 12 + 1, rover_ladder_8to12_m019_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m019_wit⟩,
  ⟨"rover_ladder_8to12_m026", 12 + 1, rover_ladder_8to12_m026_IRm, rover_ladder_8to12_cutsV2X, rover_ladder_8to12_m026_wit⟩,
  ⟨"rover_terrain_2to4_m008", 4 + 1, rover_terrain_2to4_m008_IRm, rover_terrain_2to4_cutsV2X, rover_terrain_2to4_m008_wit⟩,
  ⟨"rover_terrain_2to4_m011", 4 + 1, rover_terrain_2to4_m011_IRm, rover_terrain_2to4_cutsV2X, rover_terrain_2to4_m011_wit⟩,
  ⟨"rover_terrain_2to4_m012", 4 + 1, rover_terrain_2to4_m012_IRm, rover_terrain_2to4_cutsV2X, rover_terrain_2to4_m012_wit⟩,
  ⟨"rover_terrain_2to4_m015", 4 + 1, rover_terrain_2to4_m015_IRm, rover_terrain_2to4_cutsV2X, rover_terrain_2to4_m015_wit⟩,
  ⟨"rover_terrain_4to6_m016", 6 + 1, rover_terrain_4to6_m016_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m016_wit⟩,
  ⟨"rover_terrain_4to6_m017", 6 + 1, rover_terrain_4to6_m017_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m017_wit⟩,
  ⟨"rover_terrain_4to6_m019", 6 + 1, rover_terrain_4to6_m019_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m019_wit⟩,
  ⟨"rover_terrain_4to6_m020", 6 + 1, rover_terrain_4to6_m020_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m020_wit⟩,
  ⟨"rover_terrain_4to6_m021", 6 + 1, rover_terrain_4to6_m021_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m021_wit⟩,
  ⟨"rover_terrain_4to6_m022", 6 + 1, rover_terrain_4to6_m022_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m022_wit⟩,
  ⟨"rover_terrain_4to6_m024", 6 + 1, rover_terrain_4to6_m024_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m024_wit⟩,
  ⟨"rover_terrain_4to6_m028", 6 + 1, rover_terrain_4to6_m028_IRm, rover_terrain_4to6_cutsV2X, rover_terrain_4to6_m028_wit⟩,
  ⟨"rover_terrain_6to12_m020", 12 + 1, rover_terrain_6to12_m020_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m020_wit⟩,
  ⟨"rover_terrain_6to12_m021", 12 + 1, rover_terrain_6to12_m021_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m021_wit⟩,
  ⟨"rover_terrain_6to12_m023", 12 + 1, rover_terrain_6to12_m023_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m023_wit⟩,
  ⟨"rover_terrain_6to12_m024", 12 + 1, rover_terrain_6to12_m024_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m024_wit⟩,
  ⟨"rover_terrain_6to12_m025", 12 + 1, rover_terrain_6to12_m025_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m025_wit⟩,
  ⟨"rover_terrain_6to12_m026", 12 + 1, rover_terrain_6to12_m026_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m026_wit⟩,
  ⟨"rover_terrain_6to12_m028", 12 + 1, rover_terrain_6to12_m028_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m028_wit⟩,
  ⟨"rover_terrain_6to12_m029", 12 + 1, rover_terrain_6to12_m029_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m029_wit⟩,
  ⟨"rover_terrain_6to12_m030", 12 + 1, rover_terrain_6to12_m030_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m030_wit⟩,
  ⟨"rover_terrain_6to12_m032", 12 + 1, rover_terrain_6to12_m032_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m032_wit⟩,
  ⟨"rover_terrain_6to12_m035", 12 + 1, rover_terrain_6to12_m035_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m035_wit⟩,
  ⟨"rover_terrain_6to12_m037", 12 + 1, rover_terrain_6to12_m037_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m037_wit⟩,
  ⟨"rover_terrain_6to12_m039", 12 + 1, rover_terrain_6to12_m039_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m039_wit⟩,
  ⟨"rover_terrain_6to12_m040", 12 + 1, rover_terrain_6to12_m040_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m040_wit⟩,
  ⟨"rover_terrain_6to12_m041", 12 + 1, rover_terrain_6to12_m041_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m041_wit⟩,
  ⟨"rover_terrain_6to12_m042", 12 + 1, rover_terrain_6to12_m042_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m042_wit⟩,
  ⟨"rover_terrain_6to12_m043", 12 + 1, rover_terrain_6to12_m043_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m043_wit⟩,
  ⟨"rover_terrain_6to12_m044", 12 + 1, rover_terrain_6to12_m044_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m044_wit⟩,
  ⟨"rover_terrain_6to12_m045", 12 + 1, rover_terrain_6to12_m045_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m045_wit⟩,
  ⟨"rover_terrain_6to12_m046", 12 + 1, rover_terrain_6to12_m046_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m046_wit⟩,
  ⟨"rover_terrain_6to12_m047", 12 + 1, rover_terrain_6to12_m047_IRm, rover_terrain_6to12_cutsV2X, rover_terrain_6to12_m047_wit⟩,
  ⟨"sat3w_detumble_phases_m002", 6 + 1, sat3w_detumble_phases_m002_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m002_wit⟩,
  ⟨"sat3w_detumble_phases_m003", 6 + 1, sat3w_detumble_phases_m003_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m003_wit⟩,
  ⟨"sat3w_detumble_phases_m004", 6 + 1, sat3w_detumble_phases_m004_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m004_wit⟩,
  ⟨"sat3w_detumble_phases_m005", 6 + 1, sat3w_detumble_phases_m005_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m005_wit⟩,
  ⟨"sat3w_detumble_phases_m006", 6 + 1, sat3w_detumble_phases_m006_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m006_wit⟩,
  ⟨"sat3w_detumble_phases_m007", 6 + 1, sat3w_detumble_phases_m007_IRm, sat3w_detumble_phases_cutsV2X, sat3w_detumble_phases_m007_wit⟩,
  ⟨"sat_detumble_phases_m002", 4 + 1, sat_detumble_phases_m002_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m002_wit⟩,
  ⟨"sat_detumble_phases_m003", 4 + 1, sat_detumble_phases_m003_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m003_wit⟩,
  ⟨"sat_detumble_phases_m005", 4 + 1, sat_detumble_phases_m005_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m005_wit⟩,
  ⟨"sat_detumble_phases_m006", 4 + 1, sat_detumble_phases_m006_IRm, sat_detumble_phases_cutsV2X, sat_detumble_phases_m006_wit⟩,
  ⟨"platoon_latency_m040", 3 + 1, platoon_latency_m040_IRm, platoon_latency_cutsV2X, platoon_latency_m040_wit⟩,
  ⟨"platoon_latency_m043", 3 + 1, platoon_latency_m043_IRm, platoon_latency_cutsV2X, platoon_latency_m043_wit⟩,
  ⟨"platoon_linkloss_m036", 3 + 1, platoon_linkloss_m036_IRm, platoon_linkloss_cutsV2X, platoon_linkloss_m036_wit⟩,
  ⟨"platoon_linkloss_m039", 3 + 1, platoon_linkloss_m039_IRm, platoon_linkloss_cutsV2X, platoon_linkloss_m039_wit⟩,
  ⟨"engine_start_highidle_m003", 3 + 1, engine_start_highidle_m003_IRm, engine_start_highidle_cutsV2X, engine_start_highidle_m003_wit⟩,
  ⟨"platoon_profiles_m008", 3 + 1, platoon_profiles_m008_IRm, platoon_profiles_cutsV2X, platoon_profiles_m008_wit⟩,
  ⟨"platoon_profiles_m011", 3 + 1, platoon_profiles_m011_IRm, platoon_profiles_cutsV2X, platoon_profiles_m011_wit⟩,
  ⟨"hydro_rejection_gatecal_m024", 3 + 1, hydro_rejection_gatecal_m024_IRm, hydro_rejection_gatecal_cutsV2X, hydro_rejection_gatecal_m024_wit⟩,
  ⟨"hydro_rejection_gatecal_m028", 3 + 1, hydro_rejection_gatecal_m028_IRm, hydro_rejection_gatecal_cutsV2X, hydro_rejection_gatecal_m028_wit⟩,
  ⟨"ventilator_vc_cuffleak_m020", 3 + 1, ventilator_vc_cuffleak_m020_IRm, ventilator_vc_cuffleak_cutsV2X, ventilator_vc_cuffleak_m020_wit⟩ ]

/-- Declared: the number of query groups over the refutations (one per right mode each). -/
def expectedRefuteGroups : Nat := 181

end RelCertifier.Refute
