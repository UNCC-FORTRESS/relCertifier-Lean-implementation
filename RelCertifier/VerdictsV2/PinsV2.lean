/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 verdict pins — each instance's `Verd` IS a row of the runner's table

`RunV2.packsV2` is the data the runner rebuilds queries from. Without a pin, a wrong row
(benchmark, λ, order, mode pair) makes the runner test a lookalike query and report it
green. Each theorem below states that an instance's hypothesis is exactly `packVerd` of
one row (`irV2`/`cutV2` resolved by name in the emitted tables, λ as the row's rational),
so a wrong row does not compile; with `modalVerdX_of_queries` (the rebuild denotes
`modalVerdX`) the chain from the printed query to the theorem's hypothesis is
kernel-checked.
-/
import RelCertifier.VerdictsV2.RunV2
import RelCertifier.InstancesV2.Modal.RoverPatrolRefineGuarded
import RelCertifier.InstancesV2.Modal.RoverPatrolZonesGuarded
import RelCertifier.InstancesV2.Modal.ArmPlateauSlow
import RelCertifier.InstancesV2.Modal.ArmPlateauProfiles
import RelCertifier.InstancesV2.Modal.ArmPlateauCrit
import RelCertifier.Instances.MatchMultiRateGuarded
import RelCertifier.Instances.Rover3tierRung12Guarded
import RelCertifier.Instances.RoverRung2cGuarded
import RelCertifier.Instances.Story1AttdistRungBGuarded
import RelCertifier.Instances.Story1AttdistRungAGuarded
import RelCertifier.Instances.Story2LateralBGuarded
import RelCertifier.Instances.Story2LateralAGuarded
import RelCertifier.Instances.RoverLadderRung2Guarded
import RelCertifier.Instances.RoverRung2b6dofGuarded
import RelCertifier.Instances.RoverRung26dofGuarded
import RelCertifier.Instances.Story3RolloverRungAGuarded
import RelCertifier.Instances.Story3RolloverBaseGuarded
import RelCertifier.Instances.RoverLadderRung4Guarded
import RelCertifier.Instances.RoverLadderRung3Guarded
import RelCertifier.Instances.RoverLadderRung1Guarded
import RelCertifier.Instances.RoverDofTerrainRung38dGuarded
import RelCertifier.Instances.RoverDofTerrainRung3Guarded
import RelCertifier.Instances.RoverDofTerrainRung2Guarded
import RelCertifier.InstancesV2.Modal.RoverPatrolRefine
import RelCertifier.InstancesV2.Modal.RoverPatrolZones
import RelCertifier.InstancesV2.Modal.Sat3wDetumblePhases
import RelCertifier.InstancesV2.Modal.SatDetumblePhases
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleWeak
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleNominal
import RelCertifier.InstancesV2.Modal.SatDetumbleWeak
import RelCertifier.InstancesV2.Modal.Platoon3Linkloss
import RelCertifier.InstancesV2.Modal.Platoon3Profiles
import RelCertifier.InstancesV2.Modal.SatDetumbleNominal
import RelCertifier.InstancesV2.Modal.Story3RolloverRungB
import RelCertifier.InstancesV2.Modal.ChargerFastTapers
import RelCertifier.InstancesV2.Modal.AccSpoofLag
import RelCertifier.InstancesV2.Modal.AccTuneLag
import RelCertifier.InstancesV2.Modal.ChargerFastSetpoints
import RelCertifier.InstancesV2.Modal.QuadLightLag
import RelCertifier.InstancesV2.Modal.QuadLightProfiles
import RelCertifier.InstancesV2.Modal.QuadLightAirframe20
import RelCertifier.InstancesV2.Modal.PlatoonDelayLinkloss
import RelCertifier.InstancesV2.Modal.AccTuneLimp
import RelCertifier.InstancesV2.Modal.AccSpoofLimp
import RelCertifier.InstancesV2.Modal.Watertank
import RelCertifier.InstancesV2.Modal.PlatoonDelayProfiles
import RelCertifier.Instances.RoverDofTerrainRung1Guarded

set_option maxRecDepth 100000

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse

/-- Pin helper: same IR, same certificate, same λ (as reals), same arguments. -/
theorem pin_row {P : Prop} (r : PackV2) {p : PProblem} {c : Oracle.EvolStrengtheningX}
    {lam : ℝ} (hP : P = modalVerdX p c r.dim r.invRow r.order lam r.l r.m)
    (hp : irV2 r.bench = p) (hc : cutV2 r.bench = c) (hlam : lam = ((packLam r : ℚ) : ℝ)) :
    P = packVerd r := by
  rw [hP, packVerd, hp, hc, hlam]

/-- Pin helper for a reposition pack: same IR, same certificate, same arguments. -/
theorem pin_dyn_row {P : Prop} (r : DynPackV2) {p : PProblem} {c : Oracle.EvolStrengtheningX}
    (hP : P = modalVerdDynX p c r.dim r.invRow r.order r.pre r.l r.m)
    (hp : irV2 r.bench = p) (hc : cutV2 r.bench = c) : P = dynPackVerd r := by
  rw [hP, dynPackVerd, hp, hc]

theorem irV2_watertank : irV2 "watertank" = watertank_IRv2 := by decide
theorem cutV2_watertank : cutV2 "watertank" = Oracle.watertank_cutsV2X := by decide

theorem lam_wt2 : V2Watertank.lam 0 = (((2:ℚ) / 1 : ℚ) : ℝ) := by
  simp [V2Watertank.lam]
theorem lam_wt2' : V2Watertank.lam 1 = (((2:ℚ) / 1 : ℚ) : ℝ) := by
  simp [V2Watertank.lam]
theorem lam_wt1 : V2Watertank.lam 2 = (((1:ℚ) / 1 : ℚ) : ℝ) := by
  simp [V2Watertank.lam]

theorem pin_watertank_00 : V2Watertank.Verd 0 0 = packVerd (packsV2.getD 0 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_01 : V2Watertank.Verd 0 1 = packVerd (packsV2.getD 1 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_02 : V2Watertank.Verd 0 2 = packVerd (packsV2.getD 2 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_11 : V2Watertank.Verd 1 1 = packVerd (packsV2.getD 3 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_12 : V2Watertank.Verd 1 2 = packVerd (packsV2.getD 4 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_13 : V2Watertank.Verd 1 3 = packVerd (packsV2.getD 5 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_23 : V2Watertank.Verd 2 3 = packVerd (packsV2.getD 6 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])

theorem irV2_pdp : irV2 "platoon_delay_profiles" = platoon_delay_profiles_IRv2 := by decide
theorem cutV2_pdp : cutV2 "platoon_delay_profiles" = Oracle.platoon_delay_profiles_cutsV2X := by decide
theorem pin_platoon_delay_profiles_00 : V2PlatoonDelayProfiles.Verd 0 0 = packVerd (packsV2.getD 7 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_01 : V2PlatoonDelayProfiles.Verd 0 1 = packVerd (packsV2.getD 8 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_02 : V2PlatoonDelayProfiles.Verd 0 2 = packVerd (packsV2.getD 9 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_10 : V2PlatoonDelayProfiles.Verd 1 0 = packVerd (packsV2.getD 10 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_11 : V2PlatoonDelayProfiles.Verd 1 1 = packVerd (packsV2.getD 11 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_12 : V2PlatoonDelayProfiles.Verd 1 2 = packVerd (packsV2.getD 12 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])

theorem irV2_acc_spoof_limp : irV2 "acc_spoof_limp" = acc_spoof_limp_IRv2 := by decide
theorem cutV2_acc_spoof_limp : cutV2 "acc_spoof_limp" = Oracle.acc_spoof_limp_cutsV2X := by decide
theorem pin_acc_spoof_limp_0 : V2AccSpoofLimp.Verd 0 0 = packVerd (packsV2.getD 13 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_1 : V2AccSpoofLimp.Verd 0 1 = packVerd (packsV2.getD 14 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_2 : V2AccSpoofLimp.Verd 0 2 = packVerd (packsV2.getD 15 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_3 : V2AccSpoofLimp.Verd 1 0 = packVerd (packsV2.getD 16 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_4 : V2AccSpoofLimp.Verd 1 1 = packVerd (packsV2.getD 17 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_5 : V2AccSpoofLimp.Verd 1 2 = packVerd (packsV2.getD 18 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])

theorem irV2_acc_tune_limp : irV2 "acc_tune_limp" = acc_tune_limp_IRv2 := by decide
theorem cutV2_acc_tune_limp : cutV2 "acc_tune_limp" = Oracle.acc_tune_limp_cutsV2X := by decide
theorem pin_acc_tune_limp_0 : V2AccTuneLimp.Verd 0 0 = packVerd (packsV2.getD 19 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_1 : V2AccTuneLimp.Verd 0 1 = packVerd (packsV2.getD 20 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_2 : V2AccTuneLimp.Verd 0 2 = packVerd (packsV2.getD 21 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_3 : V2AccTuneLimp.Verd 1 0 = packVerd (packsV2.getD 22 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_4 : V2AccTuneLimp.Verd 1 1 = packVerd (packsV2.getD 23 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_5 : V2AccTuneLimp.Verd 1 2 = packVerd (packsV2.getD 24 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])

theorem irV2_platoon_delay_linkloss : irV2 "platoon_delay_linkloss" = platoon_delay_linkloss_IRv2 := by decide
theorem cutV2_platoon_delay_linkloss : cutV2 "platoon_delay_linkloss" = Oracle.platoon_delay_linkloss_cutsV2X := by decide
theorem pin_platoon_delay_linkloss_0 : V2PlatoonDelayLinkloss.Verd 0 0 = packVerd (packsV2.getD 25 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_1 : V2PlatoonDelayLinkloss.Verd 0 1 = packVerd (packsV2.getD 26 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_2 : V2PlatoonDelayLinkloss.Verd 1 0 = packVerd (packsV2.getD 27 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_3 : V2PlatoonDelayLinkloss.Verd 1 1 = packVerd (packsV2.getD 28 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_4 : V2PlatoonDelayLinkloss.Verd 2 0 = packVerd (packsV2.getD 29 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_5 : V2PlatoonDelayLinkloss.Verd 2 1 = packVerd (packsV2.getD 30 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])

theorem irV2_quad_light_airframe_20 : irV2 "quad_light_airframe_20" = quad_light_airframe_20_IRv2 := by decide
theorem cutV2_quad_light_airframe_20 : cutV2 "quad_light_airframe_20" = Oracle.quad_light_airframe_20_cutsV2X := by decide
theorem pin_quad_light_airframe_20_0 : V2QuadLightAirframe20.Verd 0 0 = packVerd (packsV2.getD 31 default) :=
  pin_row _ rfl irV2_quad_light_airframe_20 cutV2_quad_light_airframe_20 (by simp [packLam, packsV2, V2QuadLightAirframe20.lam])

theorem irV2_quad_light_profiles : irV2 "quad_light_profiles" = quad_light_profiles_IRv2 := by decide
theorem cutV2_quad_light_profiles : cutV2 "quad_light_profiles" = Oracle.quad_light_profiles_cutsV2X := by decide
theorem pin_quad_light_profiles_0 : V2QuadLightProfiles.Verd 0 0 = packVerd (packsV2.getD 32 default) :=
  pin_row _ rfl irV2_quad_light_profiles cutV2_quad_light_profiles (by simp [packLam, packsV2, V2QuadLightProfiles.lam])
theorem pin_quad_light_profiles_1 : V2QuadLightProfiles.Verd 0 1 = packVerd (packsV2.getD 33 default) :=
  pin_row _ rfl irV2_quad_light_profiles cutV2_quad_light_profiles (by simp [packLam, packsV2, V2QuadLightProfiles.lam])
theorem pin_quad_light_profiles_2 : V2QuadLightProfiles.Verd 0 2 = packVerd (packsV2.getD 34 default) :=
  pin_row _ rfl irV2_quad_light_profiles cutV2_quad_light_profiles (by simp [packLam, packsV2, V2QuadLightProfiles.lam])

theorem irV2_quad_light_lag : irV2 "quad_light_lag" = quad_light_lag_IRv2 := by decide
theorem cutV2_quad_light_lag : cutV2 "quad_light_lag" = Oracle.quad_light_lag_cutsV2X := by decide
theorem pin_quad_light_lag_0 : V2QuadLightLag.Verd 0 0 = packVerd (packsV2.getD 35 default) :=
  pin_row _ rfl irV2_quad_light_lag cutV2_quad_light_lag (by simp [packLam, packsV2, V2QuadLightLag.lam])

theorem irV2_charger_fast_setpoints : irV2 "charger_fast_setpoints" = charger_fast_setpoints_IRv2 := by decide
theorem cutV2_charger_fast_setpoints : cutV2 "charger_fast_setpoints" = Oracle.charger_fast_setpoints_cutsV2X := by decide
theorem pin_charger_fast_setpoints_0 : V2ChargerFastSetpoints.Verd 0 1 = packVerd (packsV2.getD 36 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_1 : V2ChargerFastSetpoints.Verd 0 2 = packVerd (packsV2.getD 37 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_2 : V2ChargerFastSetpoints.Verd 1 1 = packVerd (packsV2.getD 38 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_3 : V2ChargerFastSetpoints.Verd 1 2 = packVerd (packsV2.getD 39 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_5 : V2ChargerFastSetpoints.Verd 2 1 = packVerd (packsV2.getD 40 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_6 : V2ChargerFastSetpoints.Verd 2 2 = packVerd (packsV2.getD 41 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])

theorem irV2_acc_tune_lag : irV2 "acc_tune_lag" = acc_tune_lag_IRv2 := by decide
theorem cutV2_acc_tune_lag : cutV2 "acc_tune_lag" = Oracle.acc_tune_lag_cutsV2X := by decide
theorem pin_acc_tune_lag_0 : V2AccTuneLag.Verd 0 = packVerd (packsV2.getD 42 default) :=
  pin_row _ rfl irV2_acc_tune_lag cutV2_acc_tune_lag (by simp [packLam, packsV2])

theorem irV2_acc_spoof_lag : irV2 "acc_spoof_lag" = acc_spoof_lag_IRv2 := by decide
theorem cutV2_acc_spoof_lag : cutV2 "acc_spoof_lag" = Oracle.acc_spoof_lag_cutsV2X := by decide
theorem pin_acc_spoof_lag_0 : V2AccSpoofLag.Verd 0 = packVerd (packsV2.getD 43 default) :=
  pin_row _ rfl irV2_acc_spoof_lag cutV2_acc_spoof_lag (by simp [packLam, packsV2])

theorem irV2_charger_fast_tapers : irV2 "charger_fast_tapers" = charger_fast_tapers_IRv2 := by decide
theorem cutV2_charger_fast_tapers : cutV2 "charger_fast_tapers" = Oracle.charger_fast_tapers_cutsV2X := by decide
theorem pin_charger_fast_tapers_0 : V2ChargerFastTapers.Verd 0 3 = packVerd (packsV2.getD 44 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_1 : V2ChargerFastTapers.Verd 1 0 = packVerd (packsV2.getD 45 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_2 : V2ChargerFastTapers.Verd 1 1 = packVerd (packsV2.getD 46 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_3 : V2ChargerFastTapers.Verd 1 2 = packVerd (packsV2.getD 47 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_4 : V2ChargerFastTapers.Verd 1 3 = packVerd (packsV2.getD 48 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_6 : V2ChargerFastTapers.Verd 2 1 = packVerd (packsV2.getD 49 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_7 : V2ChargerFastTapers.Verd 2 2 = packVerd (packsV2.getD 50 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_8 : V2ChargerFastTapers.Verd 2 3 = packVerd (packsV2.getD 51 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])

theorem irV2_story3_rollover_ladder_rung_b : irV2 "story3_rollover_ladder_rung_b" = story3_rollover_ladder_rung_b_IRv2 := by decide
theorem cutV2_story3_rollover_ladder_rung_b : cutV2 "story3_rollover_ladder_rung_b" = Oracle.story3_rollover_ladder_rung_b_cutsV2X := by decide
theorem pin_story3_rollover_ladder_rung_b_0 : V2Story3RolloverRungB.Verd 0 0 = packVerd (packsV2.getD 52 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_1 : V2Story3RolloverRungB.Verd 0 1 = packVerd (packsV2.getD 53 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_2 : V2Story3RolloverRungB.Verd 0 2 = packVerd (packsV2.getD 54 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_3 : V2Story3RolloverRungB.Verd 1 0 = packVerd (packsV2.getD 55 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_4 : V2Story3RolloverRungB.Verd 1 1 = packVerd (packsV2.getD 56 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_5 : V2Story3RolloverRungB.Verd 1 2 = packVerd (packsV2.getD 57 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_6 : V2Story3RolloverRungB.Verd 2 0 = packVerd (packsV2.getD 58 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_7 : V2Story3RolloverRungB.Verd 2 1 = packVerd (packsV2.getD 59 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_8 : V2Story3RolloverRungB.Verd 2 2 = packVerd (packsV2.getD 60 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])

theorem irV2_sat_detumble_nominal : irV2 "sat_detumble_nominal" = sat_detumble_nominal_IRv2 := by decide
theorem cutV2_sat_detumble_nominal : cutV2 "sat_detumble_nominal" = Oracle.sat_detumble_nominal_cutsV2X := by decide
theorem pin_sat_detumble_nominal_0 : V2SatDetumbleNominal.Verd 0 0 = packVerd (packsV2.getD 61 default) :=
  pin_row _ rfl irV2_sat_detumble_nominal cutV2_sat_detumble_nominal (by simp [packLam, packsV2])

theorem irV2_platoon3_profiles : irV2 "platoon3_profiles" = platoon3_profiles_IRv2 := by decide
theorem cutV2_platoon3_profiles : cutV2 "platoon3_profiles" = Oracle.platoon3_profiles_cutsV2X := by decide
theorem pin_platoon3_profiles_0 : V2Platoon3Profiles.Verd 0 0 = packVerd (packsV2.getD 62 default) :=
  pin_row _ rfl irV2_platoon3_profiles cutV2_platoon3_profiles (by simp [packLam, packsV2])
theorem pin_platoon3_profiles_1 : V2Platoon3Profiles.Verd 0 1 = packVerd (packsV2.getD 63 default) :=
  pin_row _ rfl irV2_platoon3_profiles cutV2_platoon3_profiles (by simp [packLam, packsV2])
theorem pin_platoon3_profiles_2 : V2Platoon3Profiles.Verd 0 2 = packVerd (packsV2.getD 64 default) :=
  pin_row _ rfl irV2_platoon3_profiles cutV2_platoon3_profiles (by simp [packLam, packsV2])

theorem irV2_platoon3_linkloss : irV2 "platoon3_linkloss" = platoon3_linkloss_IRv2 := by decide
theorem cutV2_platoon3_linkloss : cutV2 "platoon3_linkloss" = Oracle.platoon3_linkloss_cutsV2X := by decide
theorem pin_platoon3_linkloss_0 : V2Platoon3Linkloss.Verd 0 0 = packVerd (packsV2.getD 65 default) :=
  pin_row _ rfl irV2_platoon3_linkloss cutV2_platoon3_linkloss (by simp [packLam, packsV2])
theorem pin_platoon3_linkloss_1 : V2Platoon3Linkloss.Verd 1 0 = packVerd (packsV2.getD 66 default) :=
  pin_row _ rfl irV2_platoon3_linkloss cutV2_platoon3_linkloss (by simp [packLam, packsV2])

theorem irV2_sat_detumble_weak : irV2 "sat_detumble_weak" = sat_detumble_weak_IRv2 := by decide
theorem cutV2_sat_detumble_weak : cutV2 "sat_detumble_weak" = Oracle.sat_detumble_weak_cutsV2X := by decide
theorem pin_sat_detumble_weak_0 : V2SatDetumbleWeak.Verd 0 0 = packVerd (packsV2.getD 67 default) :=
  pin_row _ rfl irV2_sat_detumble_weak cutV2_sat_detumble_weak (by simp [packLam, packsV2])
theorem pin_sat_detumble_weak_1 : V2SatDetumbleWeak.Verd 0 1 = packVerd (packsV2.getD 68 default) :=
  pin_row _ rfl irV2_sat_detumble_weak cutV2_sat_detumble_weak (by simp [packLam, packsV2])
theorem pin_sat_detumble_weak_2 : V2SatDetumbleWeak.Verd 0 2 = packVerd (packsV2.getD 69 default) :=
  pin_row _ rfl irV2_sat_detumble_weak cutV2_sat_detumble_weak (by simp [packLam, packsV2])

theorem irV2_sat3w_detumble_nominal : irV2 "sat3w_detumble_nominal" = sat3w_detumble_nominal_IRv2 := by decide
theorem cutV2_sat3w_detumble_nominal : cutV2 "sat3w_detumble_nominal" = Oracle.sat3w_detumble_nominal_cutsV2X := by decide
theorem pin_sat3w_detumble_nominal_0 : V2Sat3wDetumbleNominal.Verd 0 0 = packVerd (packsV2.getD 70 default) :=
  pin_row _ rfl irV2_sat3w_detumble_nominal cutV2_sat3w_detumble_nominal (by simp [packLam, packsV2])

theorem irV2_sat3w_detumble_weak : irV2 "sat3w_detumble_weak" = sat3w_detumble_weak_IRv2 := by decide
theorem cutV2_sat3w_detumble_weak : cutV2 "sat3w_detumble_weak" = Oracle.sat3w_detumble_weak_cutsV2X := by decide
theorem pin_sat3w_detumble_weak_0 : V2Sat3wDetumbleWeak.Verd 0 0 = packVerd (packsV2.getD 71 default) :=
  pin_row _ rfl irV2_sat3w_detumble_weak cutV2_sat3w_detumble_weak (by simp [packLam, packsV2])
theorem pin_sat3w_detumble_weak_1 : V2Sat3wDetumbleWeak.Verd 0 1 = packVerd (packsV2.getD 72 default) :=
  pin_row _ rfl irV2_sat3w_detumble_weak cutV2_sat3w_detumble_weak (by simp [packLam, packsV2])
theorem pin_sat3w_detumble_weak_2 : V2Sat3wDetumbleWeak.Verd 0 2 = packVerd (packsV2.getD 73 default) :=
  pin_row _ rfl irV2_sat3w_detumble_weak cutV2_sat3w_detumble_weak (by simp [packLam, packsV2])

theorem irV2_sat_detumble_phases : irV2 "sat_detumble_phases" = sat_detumble_phases_IRv2 := by decide
theorem cutV2_sat_detumble_phases : cutV2 "sat_detumble_phases" = Oracle.sat_detumble_phases_cutsV2X := by decide
theorem pin_sat_detumble_phases_0 : V2SatDetumblePhases.Verd 0 0 = packVerd (packsV2.getD 74 default) :=
  pin_row _ rfl irV2_sat_detumble_phases cutV2_sat_detumble_phases (by simp [packLam, packsV2])
theorem pin_sat_detumble_phases_1 : V2SatDetumblePhases.Verd 1 0 = packVerd (packsV2.getD 75 default) :=
  pin_row _ rfl irV2_sat_detumble_phases cutV2_sat_detumble_phases (by simp [packLam, packsV2])

theorem irV2_sat3w_detumble_phases : irV2 "sat3w_detumble_phases" = sat3w_detumble_phases_IRv2 := by decide
theorem cutV2_sat3w_detumble_phases : cutV2 "sat3w_detumble_phases" = Oracle.sat3w_detumble_phases_cutsV2X := by decide
theorem pin_sat3w_detumble_phases_0 : V2Sat3wDetumblePhases.Verd 0 0 = packVerd (packsV2.getD 76 default) :=
  pin_row _ rfl irV2_sat3w_detumble_phases cutV2_sat3w_detumble_phases (by simp [packLam, packsV2])
theorem pin_sat3w_detumble_phases_1 : V2Sat3wDetumblePhases.Verd 1 0 = packVerd (packsV2.getD 77 default) :=
  pin_row _ rfl irV2_sat3w_detumble_phases cutV2_sat3w_detumble_phases (by simp [packLam, packsV2])

theorem irV2_rover_patrol_zones : irV2 "rover_patrol_zones" = rover_patrol_zones_IRv2 := by decide
theorem cutV2_rover_patrol_zones : cutV2 "rover_patrol_zones" = Oracle.rover_patrol_zones_cutsV2X := by decide
theorem pin_rover_patrol_zones_0 : V2RoverPatrolZones.Verd 0 0 = packVerd (packsV2.getD 78 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_1 : V2RoverPatrolZones.Verd 0 1 = packVerd (packsV2.getD 79 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_2 : V2RoverPatrolZones.Verd 0 2 = packVerd (packsV2.getD 80 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_3 : V2RoverPatrolZones.Verd 0 3 = packVerd (packsV2.getD 81 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_4 : V2RoverPatrolZones.Verd 1 1 = packVerd (packsV2.getD 82 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_5 : V2RoverPatrolZones.Verd 1 2 = packVerd (packsV2.getD 83 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_6 : V2RoverPatrolZones.Verd 1 3 = packVerd (packsV2.getD 84 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_7 : V2RoverPatrolZones.Verd 2 2 = packVerd (packsV2.getD 85 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_8 : V2RoverPatrolZones.Verd 2 3 = packVerd (packsV2.getD 86 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])
theorem pin_rover_patrol_zones_9 : V2RoverPatrolZones.Verd 3 3 = packVerd (packsV2.getD 87 default) :=
  pin_row _ rfl irV2_rover_patrol_zones cutV2_rover_patrol_zones (by simp [packLam, packsV2])

theorem irV2_rover_patrol_refine : irV2 "rover_patrol_refine" = rover_patrol_refine_IRv2 := by decide
theorem cutV2_rover_patrol_refine : cutV2 "rover_patrol_refine" = Oracle.rover_patrol_refine_cutsV2X := by decide
theorem pin_rover_patrol_refine_0 : V2RoverPatrolRefine.Verd 0 0 = packVerd (packsV2.getD 88 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_1 : V2RoverPatrolRefine.Verd 0 1 = packVerd (packsV2.getD 89 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_2 : V2RoverPatrolRefine.Verd 0 2 = packVerd (packsV2.getD 90 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_3 : V2RoverPatrolRefine.Verd 0 3 = packVerd (packsV2.getD 91 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_4 : V2RoverPatrolRefine.Verd 1 1 = packVerd (packsV2.getD 92 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_5 : V2RoverPatrolRefine.Verd 1 2 = packVerd (packsV2.getD 93 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_6 : V2RoverPatrolRefine.Verd 1 3 = packVerd (packsV2.getD 94 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_7 : V2RoverPatrolRefine.Verd 2 2 = packVerd (packsV2.getD 95 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_8 : V2RoverPatrolRefine.Verd 2 3 = packVerd (packsV2.getD 96 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])
theorem pin_rover_patrol_refine_9 : V2RoverPatrolRefine.Verd 3 3 = packVerd (packsV2.getD 97 default) :=
  pin_row _ rfl irV2_rover_patrol_refine cutV2_rover_patrol_refine (by simp [packLam, packsV2])

/-! ## Cover replays of the carried-over benchmarks -/

theorem irV2_terrain1 : irV2 "rover_dof_terrain_rung1" = rover_dof_terrain_rung1_IRv2 := by decide
theorem cutV2_terrain1 : cutV2 "rover_dof_terrain_rung1" = Oracle.rover_dof_terrain_rung1_cutsV2X := by
  decide
theorem pin_terrain1_00 : RoverDofTerrainRung1Guarded.Verd 0 0 = packVerd (packsV2.getD 98 default) :=
  pin_row _ rfl irV2_terrain1 cutV2_terrain1 (by simp [packLam, packsV2])
theorem pin_terrain1_01 : RoverDofTerrainRung1Guarded.Verd 0 1 = packVerd (packsV2.getD 99 default) :=
  pin_row _ rfl irV2_terrain1 cutV2_terrain1 (by simp [packLam, packsV2])
theorem pin_terrain1_02 : RoverDofTerrainRung1Guarded.Verd 0 2 = packVerd (packsV2.getD 100 default) :=
  pin_row _ rfl irV2_terrain1 cutV2_terrain1 (by simp [packLam, packsV2])
theorem pin_terrain1_11 : RoverDofTerrainRung1Guarded.Verd 1 1 = packVerd (packsV2.getD 101 default) :=
  pin_row _ rfl irV2_terrain1 cutV2_terrain1 (by simp [packLam, packsV2])
theorem pin_terrain1_12 : RoverDofTerrainRung1Guarded.Verd 1 2 = packVerd (packsV2.getD 102 default) :=
  pin_row _ rfl irV2_terrain1 cutV2_terrain1 (by simp [packLam, packsV2])
theorem pin_terrain1_22 : RoverDofTerrainRung1Guarded.Verd 2 2 = packVerd (packsV2.getD 103 default) :=
  pin_row _ rfl irV2_terrain1 cutV2_terrain1 (by simp [packLam, packsV2])
theorem pin_terrain1_d10 : RoverDofTerrainRung1Guarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 0 default) :=
  pin_dyn_row _ rfl irV2_terrain1 cutV2_terrain1
theorem pin_terrain1_d21 : RoverDofTerrainRung1Guarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 1 default) :=
  pin_dyn_row _ rfl irV2_terrain1 cutV2_terrain1

theorem irV2_terrain2 : irV2 "rover_dof_terrain_rung2" = rover_dof_terrain_rung2_IRv2 := by decide
theorem cutV2_terrain2 : cutV2 "rover_dof_terrain_rung2" = Oracle.rover_dof_terrain_rung2_cutsV2X := by decide
theorem pin_terrain2_j0 : RoverDofTerrainRung2Guarded.Verd 0 0 = packVerd (packsV2.getD 104 default) :=
  pin_row _ rfl irV2_terrain2 cutV2_terrain2 (by simp [packLam, packsV2])
theorem pin_terrain2_j1 : RoverDofTerrainRung2Guarded.Verd 0 1 = packVerd (packsV2.getD 105 default) :=
  pin_row _ rfl irV2_terrain2 cutV2_terrain2 (by simp [packLam, packsV2])
theorem pin_terrain2_j2 : RoverDofTerrainRung2Guarded.Verd 0 2 = packVerd (packsV2.getD 106 default) :=
  pin_row _ rfl irV2_terrain2 cutV2_terrain2 (by simp [packLam, packsV2])
theorem pin_terrain2_j3 : RoverDofTerrainRung2Guarded.Verd 1 1 = packVerd (packsV2.getD 107 default) :=
  pin_row _ rfl irV2_terrain2 cutV2_terrain2 (by simp [packLam, packsV2])
theorem pin_terrain2_j4 : RoverDofTerrainRung2Guarded.Verd 1 2 = packVerd (packsV2.getD 108 default) :=
  pin_row _ rfl irV2_terrain2 cutV2_terrain2 (by simp [packLam, packsV2])
theorem pin_terrain2_j5 : RoverDofTerrainRung2Guarded.Verd 2 2 = packVerd (packsV2.getD 109 default) :=
  pin_row _ rfl irV2_terrain2 cutV2_terrain2 (by simp [packLam, packsV2])
theorem pin_terrain2_d0 : RoverDofTerrainRung2Guarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 2 default) :=
  pin_dyn_row _ rfl irV2_terrain2 cutV2_terrain2
theorem pin_terrain2_d1 : RoverDofTerrainRung2Guarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 3 default) :=
  pin_dyn_row _ rfl irV2_terrain2 cutV2_terrain2

theorem irV2_terrain3 : irV2 "rover_dof_terrain_rung3" = rover_dof_terrain_rung3_IRv2 := by decide
theorem cutV2_terrain3 : cutV2 "rover_dof_terrain_rung3" = Oracle.rover_dof_terrain_rung3_cutsV2X := by decide
theorem pin_terrain3_j0 : RoverDofTerrainRung3Guarded.Verd 0 0 = packVerd (packsV2.getD 110 default) :=
  pin_row _ rfl irV2_terrain3 cutV2_terrain3 (by simp [packLam, packsV2])
theorem pin_terrain3_j1 : RoverDofTerrainRung3Guarded.Verd 0 1 = packVerd (packsV2.getD 111 default) :=
  pin_row _ rfl irV2_terrain3 cutV2_terrain3 (by simp [packLam, packsV2])
theorem pin_terrain3_j2 : RoverDofTerrainRung3Guarded.Verd 0 2 = packVerd (packsV2.getD 112 default) :=
  pin_row _ rfl irV2_terrain3 cutV2_terrain3 (by simp [packLam, packsV2])
theorem pin_terrain3_j3 : RoverDofTerrainRung3Guarded.Verd 1 1 = packVerd (packsV2.getD 113 default) :=
  pin_row _ rfl irV2_terrain3 cutV2_terrain3 (by simp [packLam, packsV2])
theorem pin_terrain3_j4 : RoverDofTerrainRung3Guarded.Verd 1 2 = packVerd (packsV2.getD 114 default) :=
  pin_row _ rfl irV2_terrain3 cutV2_terrain3 (by simp [packLam, packsV2])
theorem pin_terrain3_j5 : RoverDofTerrainRung3Guarded.Verd 2 2 = packVerd (packsV2.getD 115 default) :=
  pin_row _ rfl irV2_terrain3 cutV2_terrain3 (by simp [packLam, packsV2])
theorem pin_terrain3_d0 : RoverDofTerrainRung3Guarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 4 default) :=
  pin_dyn_row _ rfl irV2_terrain3 cutV2_terrain3
theorem pin_terrain3_d1 : RoverDofTerrainRung3Guarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 5 default) :=
  pin_dyn_row _ rfl irV2_terrain3 cutV2_terrain3

theorem irV2_terrain38d : irV2 "rover_dof_terrain_rung3_8d" = rover_dof_terrain_rung3_8d_IRv2 := by decide
theorem cutV2_terrain38d : cutV2 "rover_dof_terrain_rung3_8d" = Oracle.rover_dof_terrain_rung3_8d_cutsV2X := by decide
theorem pin_terrain38d_j0 : RoverDofTerrainRung38dGuarded.Verd 0 0 = packVerd (packsV2.getD 116 default) :=
  pin_row _ rfl irV2_terrain38d cutV2_terrain38d (by simp [packLam, packsV2])
theorem pin_terrain38d_j1 : RoverDofTerrainRung38dGuarded.Verd 0 1 = packVerd (packsV2.getD 117 default) :=
  pin_row _ rfl irV2_terrain38d cutV2_terrain38d (by simp [packLam, packsV2])
theorem pin_terrain38d_j2 : RoverDofTerrainRung38dGuarded.Verd 0 2 = packVerd (packsV2.getD 118 default) :=
  pin_row _ rfl irV2_terrain38d cutV2_terrain38d (by simp [packLam, packsV2])
theorem pin_terrain38d_j3 : RoverDofTerrainRung38dGuarded.Verd 1 1 = packVerd (packsV2.getD 119 default) :=
  pin_row _ rfl irV2_terrain38d cutV2_terrain38d (by simp [packLam, packsV2])
theorem pin_terrain38d_j4 : RoverDofTerrainRung38dGuarded.Verd 1 2 = packVerd (packsV2.getD 120 default) :=
  pin_row _ rfl irV2_terrain38d cutV2_terrain38d (by simp [packLam, packsV2])
theorem pin_terrain38d_j5 : RoverDofTerrainRung38dGuarded.Verd 2 2 = packVerd (packsV2.getD 121 default) :=
  pin_row _ rfl irV2_terrain38d cutV2_terrain38d (by simp [packLam, packsV2])
theorem pin_terrain38d_d0 : RoverDofTerrainRung38dGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 6 default) :=
  pin_dyn_row _ rfl irV2_terrain38d cutV2_terrain38d
theorem pin_terrain38d_d1 : RoverDofTerrainRung38dGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 7 default) :=
  pin_dyn_row _ rfl irV2_terrain38d cutV2_terrain38d

theorem irV2_rung1 : irV2 "refinement_ladder_rover_rung1_2to3" = refinement_ladder_rover_rung1_2to3_IRv2 := by decide
theorem cutV2_rung1 : cutV2 "refinement_ladder_rover_rung1_2to3" = Oracle.refinement_ladder_rover_rung1_2to3_cutsV2X := by decide
theorem pin_rung1_j0 : RoverLadderRung1Guarded.Verd 0 0 = packVerd (packsV2.getD 122 default) :=
  pin_row _ rfl irV2_rung1 cutV2_rung1 (by simp [packLam, packsV2])
theorem pin_rung1_j1 : RoverLadderRung1Guarded.Verd 0 1 = packVerd (packsV2.getD 123 default) :=
  pin_row _ rfl irV2_rung1 cutV2_rung1 (by simp [packLam, packsV2])
theorem pin_rung1_j2 : RoverLadderRung1Guarded.Verd 0 2 = packVerd (packsV2.getD 124 default) :=
  pin_row _ rfl irV2_rung1 cutV2_rung1 (by simp [packLam, packsV2])
theorem pin_rung1_j3 : RoverLadderRung1Guarded.Verd 1 1 = packVerd (packsV2.getD 125 default) :=
  pin_row _ rfl irV2_rung1 cutV2_rung1 (by simp [packLam, packsV2])
theorem pin_rung1_j4 : RoverLadderRung1Guarded.Verd 1 2 = packVerd (packsV2.getD 126 default) :=
  pin_row _ rfl irV2_rung1 cutV2_rung1 (by simp [packLam, packsV2])
theorem pin_rung1_j5 : RoverLadderRung1Guarded.Verd 2 2 = packVerd (packsV2.getD 127 default) :=
  pin_row _ rfl irV2_rung1 cutV2_rung1 (by simp [packLam, packsV2])
theorem pin_rung1_d0 : RoverLadderRung1Guarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 8 default) :=
  pin_dyn_row _ rfl irV2_rung1 cutV2_rung1
theorem pin_rung1_d1 : RoverLadderRung1Guarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 9 default) :=
  pin_dyn_row _ rfl irV2_rung1 cutV2_rung1

theorem irV2_rung3 : irV2 "refinement_ladder_rover_rung3_6to8" = refinement_ladder_rover_rung3_6to8_IRv2 := by decide
theorem cutV2_rung3 : cutV2 "refinement_ladder_rover_rung3_6to8" = Oracle.refinement_ladder_rover_rung3_6to8_cutsV2X := by decide
theorem pin_rung3_j0 : RoverLadderRung3Guarded.Verd 0 0 = packVerd (packsV2.getD 128 default) :=
  pin_row _ rfl irV2_rung3 cutV2_rung3 (by simp [packLam, packsV2])
theorem pin_rung3_j1 : RoverLadderRung3Guarded.Verd 0 1 = packVerd (packsV2.getD 129 default) :=
  pin_row _ rfl irV2_rung3 cutV2_rung3 (by simp [packLam, packsV2])
theorem pin_rung3_j2 : RoverLadderRung3Guarded.Verd 0 2 = packVerd (packsV2.getD 130 default) :=
  pin_row _ rfl irV2_rung3 cutV2_rung3 (by simp [packLam, packsV2])
theorem pin_rung3_j3 : RoverLadderRung3Guarded.Verd 1 1 = packVerd (packsV2.getD 131 default) :=
  pin_row _ rfl irV2_rung3 cutV2_rung3 (by simp [packLam, packsV2])
theorem pin_rung3_j4 : RoverLadderRung3Guarded.Verd 1 2 = packVerd (packsV2.getD 132 default) :=
  pin_row _ rfl irV2_rung3 cutV2_rung3 (by simp [packLam, packsV2])
theorem pin_rung3_j5 : RoverLadderRung3Guarded.Verd 2 2 = packVerd (packsV2.getD 133 default) :=
  pin_row _ rfl irV2_rung3 cutV2_rung3 (by simp [packLam, packsV2])
theorem pin_rung3_d0 : RoverLadderRung3Guarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 10 default) :=
  pin_dyn_row _ rfl irV2_rung3 cutV2_rung3
theorem pin_rung3_d1 : RoverLadderRung3Guarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 11 default) :=
  pin_dyn_row _ rfl irV2_rung3 cutV2_rung3

theorem irV2_rung4 : irV2 "refinement_ladder_rover_rung4_8to12" = refinement_ladder_rover_rung4_8to12_IRv2 := by decide
theorem cutV2_rung4 : cutV2 "refinement_ladder_rover_rung4_8to12" = Oracle.refinement_ladder_rover_rung4_8to12_cutsV2X := by decide
theorem pin_rung4_j0 : RoverLadderRung4Guarded.Verd 0 0 = packVerd (packsV2.getD 134 default) :=
  pin_row _ rfl irV2_rung4 cutV2_rung4 (by simp [packLam, packsV2])
theorem pin_rung4_j1 : RoverLadderRung4Guarded.Verd 0 1 = packVerd (packsV2.getD 135 default) :=
  pin_row _ rfl irV2_rung4 cutV2_rung4 (by simp [packLam, packsV2])
theorem pin_rung4_j2 : RoverLadderRung4Guarded.Verd 0 2 = packVerd (packsV2.getD 136 default) :=
  pin_row _ rfl irV2_rung4 cutV2_rung4 (by simp [packLam, packsV2])
theorem pin_rung4_j3 : RoverLadderRung4Guarded.Verd 1 1 = packVerd (packsV2.getD 137 default) :=
  pin_row _ rfl irV2_rung4 cutV2_rung4 (by simp [packLam, packsV2])
theorem pin_rung4_j4 : RoverLadderRung4Guarded.Verd 1 2 = packVerd (packsV2.getD 138 default) :=
  pin_row _ rfl irV2_rung4 cutV2_rung4 (by simp [packLam, packsV2])
theorem pin_rung4_j5 : RoverLadderRung4Guarded.Verd 2 2 = packVerd (packsV2.getD 139 default) :=
  pin_row _ rfl irV2_rung4 cutV2_rung4 (by simp [packLam, packsV2])
theorem pin_rung4_d0 : RoverLadderRung4Guarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 12 default) :=
  pin_dyn_row _ rfl irV2_rung4 cutV2_rung4
theorem pin_rung4_d1 : RoverLadderRung4Guarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 13 default) :=
  pin_dyn_row _ rfl irV2_rung4 cutV2_rung4

theorem irV2_s3base : irV2 "story3_rollover_base_12dof" = story3_rollover_base_12dof_IRv2 := by decide
theorem cutV2_s3base : cutV2 "story3_rollover_base_12dof" = Oracle.story3_rollover_base_12dof_cutsV2X := by decide
theorem pin_s3base_j0 : Story3RolloverBaseGuarded.Verd 0 0 = packVerd (packsV2.getD 140 default) :=
  pin_row _ rfl irV2_s3base cutV2_s3base (by simp [packLam, packsV2])
theorem pin_s3base_j1 : Story3RolloverBaseGuarded.Verd 0 1 = packVerd (packsV2.getD 141 default) :=
  pin_row _ rfl irV2_s3base cutV2_s3base (by simp [packLam, packsV2])
theorem pin_s3base_j2 : Story3RolloverBaseGuarded.Verd 0 2 = packVerd (packsV2.getD 142 default) :=
  pin_row _ rfl irV2_s3base cutV2_s3base (by simp [packLam, packsV2])
theorem pin_s3base_j3 : Story3RolloverBaseGuarded.Verd 1 1 = packVerd (packsV2.getD 143 default) :=
  pin_row _ rfl irV2_s3base cutV2_s3base (by simp [packLam, packsV2])
theorem pin_s3base_j4 : Story3RolloverBaseGuarded.Verd 1 2 = packVerd (packsV2.getD 144 default) :=
  pin_row _ rfl irV2_s3base cutV2_s3base (by simp [packLam, packsV2])
theorem pin_s3base_j5 : Story3RolloverBaseGuarded.Verd 2 2 = packVerd (packsV2.getD 145 default) :=
  pin_row _ rfl irV2_s3base cutV2_s3base (by simp [packLam, packsV2])
theorem pin_s3base_d0 : Story3RolloverBaseGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 14 default) :=
  pin_dyn_row _ rfl irV2_s3base cutV2_s3base
theorem pin_s3base_d1 : Story3RolloverBaseGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 15 default) :=
  pin_dyn_row _ rfl irV2_s3base cutV2_s3base

theorem irV2_s3a : irV2 "story3_rollover_ladder_rung_a" = story3_rollover_ladder_rung_a_IRv2 := by decide
theorem cutV2_s3a : cutV2 "story3_rollover_ladder_rung_a" = Oracle.story3_rollover_ladder_rung_a_cutsV2X := by decide
theorem pin_s3a_j0 : Story3RolloverRungAGuarded.Verd 0 0 = packVerd (packsV2.getD 146 default) :=
  pin_row _ rfl irV2_s3a cutV2_s3a (by simp [packLam, packsV2])
theorem pin_s3a_j1 : Story3RolloverRungAGuarded.Verd 0 1 = packVerd (packsV2.getD 147 default) :=
  pin_row _ rfl irV2_s3a cutV2_s3a (by simp [packLam, packsV2])
theorem pin_s3a_j2 : Story3RolloverRungAGuarded.Verd 0 2 = packVerd (packsV2.getD 148 default) :=
  pin_row _ rfl irV2_s3a cutV2_s3a (by simp [packLam, packsV2])
theorem pin_s3a_j3 : Story3RolloverRungAGuarded.Verd 1 1 = packVerd (packsV2.getD 149 default) :=
  pin_row _ rfl irV2_s3a cutV2_s3a (by simp [packLam, packsV2])
theorem pin_s3a_j4 : Story3RolloverRungAGuarded.Verd 1 2 = packVerd (packsV2.getD 150 default) :=
  pin_row _ rfl irV2_s3a cutV2_s3a (by simp [packLam, packsV2])
theorem pin_s3a_j5 : Story3RolloverRungAGuarded.Verd 2 2 = packVerd (packsV2.getD 151 default) :=
  pin_row _ rfl irV2_s3a cutV2_s3a (by simp [packLam, packsV2])
theorem pin_s3a_d0 : Story3RolloverRungAGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 16 default) :=
  pin_dyn_row _ rfl irV2_s3a cutV2_s3a
theorem pin_s3a_d1 : Story3RolloverRungAGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 17 default) :=
  pin_dyn_row _ rfl irV2_s3a cutV2_s3a

theorem irV2_rung26 : irV2 "refinement_ladder_rover_rung2_6dof" = refinement_ladder_rover_rung2_6dof_IRv2 := by decide
theorem cutV2_rung26 : cutV2 "refinement_ladder_rover_rung2_6dof" = Oracle.refinement_ladder_rover_rung2_6dof_cutsV2X := by decide
theorem pin_rung26_j0 : RoverRung26dofGuarded.Verd 0 0 = packVerd (packsV2.getD 152 default) :=
  pin_row _ rfl irV2_rung26 cutV2_rung26 (by simp [packLam, packsV2])
theorem pin_rung26_j1 : RoverRung26dofGuarded.Verd 0 1 = packVerd (packsV2.getD 153 default) :=
  pin_row _ rfl irV2_rung26 cutV2_rung26 (by simp [packLam, packsV2])
theorem pin_rung26_j2 : RoverRung26dofGuarded.Verd 0 2 = packVerd (packsV2.getD 154 default) :=
  pin_row _ rfl irV2_rung26 cutV2_rung26 (by simp [packLam, packsV2])
theorem pin_rung26_j3 : RoverRung26dofGuarded.Verd 1 1 = packVerd (packsV2.getD 155 default) :=
  pin_row _ rfl irV2_rung26 cutV2_rung26 (by simp [packLam, packsV2])
theorem pin_rung26_j4 : RoverRung26dofGuarded.Verd 1 2 = packVerd (packsV2.getD 156 default) :=
  pin_row _ rfl irV2_rung26 cutV2_rung26 (by simp [packLam, packsV2])
theorem pin_rung26_j5 : RoverRung26dofGuarded.Verd 2 2 = packVerd (packsV2.getD 157 default) :=
  pin_row _ rfl irV2_rung26 cutV2_rung26 (by simp [packLam, packsV2])
theorem pin_rung26_d0 : RoverRung26dofGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 18 default) :=
  pin_dyn_row _ rfl irV2_rung26 cutV2_rung26
theorem pin_rung26_d1 : RoverRung26dofGuarded.VerdD 2 0 = dynPackVerd (dynPacksV2.getD 19 default) :=
  pin_dyn_row _ rfl irV2_rung26 cutV2_rung26
theorem pin_rung26_d2 : RoverRung26dofGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 20 default) :=
  pin_dyn_row _ rfl irV2_rung26 cutV2_rung26

theorem irV2_rung2b6 : irV2 "refinement_ladder_rover_rung2b_6dof" = refinement_ladder_rover_rung2b_6dof_IRv2 := by decide
theorem cutV2_rung2b6 : cutV2 "refinement_ladder_rover_rung2b_6dof" = Oracle.refinement_ladder_rover_rung2b_6dof_cutsV2X := by decide
theorem pin_rung2b6_j0 : RoverRung2b6dofGuarded.Verd 0 0 = packVerd (packsV2.getD 158 default) :=
  pin_row _ rfl irV2_rung2b6 cutV2_rung2b6 (by simp [packLam, packsV2])
theorem pin_rung2b6_j1 : RoverRung2b6dofGuarded.Verd 0 1 = packVerd (packsV2.getD 159 default) :=
  pin_row _ rfl irV2_rung2b6 cutV2_rung2b6 (by simp [packLam, packsV2])
theorem pin_rung2b6_j2 : RoverRung2b6dofGuarded.Verd 0 2 = packVerd (packsV2.getD 160 default) :=
  pin_row _ rfl irV2_rung2b6 cutV2_rung2b6 (by simp [packLam, packsV2])
theorem pin_rung2b6_j3 : RoverRung2b6dofGuarded.Verd 1 1 = packVerd (packsV2.getD 161 default) :=
  pin_row _ rfl irV2_rung2b6 cutV2_rung2b6 (by simp [packLam, packsV2])
theorem pin_rung2b6_j4 : RoverRung2b6dofGuarded.Verd 1 2 = packVerd (packsV2.getD 162 default) :=
  pin_row _ rfl irV2_rung2b6 cutV2_rung2b6 (by simp [packLam, packsV2])
theorem pin_rung2b6_j5 : RoverRung2b6dofGuarded.Verd 2 2 = packVerd (packsV2.getD 163 default) :=
  pin_row _ rfl irV2_rung2b6 cutV2_rung2b6 (by simp [packLam, packsV2])
theorem pin_rung2b6_d0 : RoverRung2b6dofGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 21 default) :=
  pin_dyn_row _ rfl irV2_rung2b6 cutV2_rung2b6
theorem pin_rung2b6_d1 : RoverRung2b6dofGuarded.VerdD 2 0 = dynPackVerd (dynPacksV2.getD 22 default) :=
  pin_dyn_row _ rfl irV2_rung2b6 cutV2_rung2b6
theorem pin_rung2b6_d2 : RoverRung2b6dofGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 23 default) :=
  pin_dyn_row _ rfl irV2_rung2b6 cutV2_rung2b6

theorem irV2_rung236 : irV2 "refinement_ladder_rover_rung2_3to6" = refinement_ladder_rover_rung2_3to6_IRv2 := by decide
theorem cutV2_rung236 : cutV2 "refinement_ladder_rover_rung2_3to6" = Oracle.refinement_ladder_rover_rung2_3to6_cutsV2X := by decide
theorem pin_rung236_j0 : RoverLadderRung2Guarded.Verd 0 0 = packVerd (packsV2.getD 164 default) :=
  pin_row _ rfl irV2_rung236 cutV2_rung236 (by simp [packLam, packsV2])
theorem pin_rung236_j1 : RoverLadderRung2Guarded.Verd 0 1 = packVerd (packsV2.getD 165 default) :=
  pin_row _ rfl irV2_rung236 cutV2_rung236 (by simp [packLam, packsV2])
theorem pin_rung236_j2 : RoverLadderRung2Guarded.Verd 0 2 = packVerd (packsV2.getD 166 default) :=
  pin_row _ rfl irV2_rung236 cutV2_rung236 (by simp [packLam, packsV2])
theorem pin_rung236_j3 : RoverLadderRung2Guarded.Verd 1 1 = packVerd (packsV2.getD 167 default) :=
  pin_row _ rfl irV2_rung236 cutV2_rung236 (by simp [packLam, packsV2])
theorem pin_rung236_j4 : RoverLadderRung2Guarded.Verd 1 2 = packVerd (packsV2.getD 168 default) :=
  pin_row _ rfl irV2_rung236 cutV2_rung236 (by simp [packLam, packsV2])
theorem pin_rung236_j5 : RoverLadderRung2Guarded.Verd 2 2 = packVerd (packsV2.getD 169 default) :=
  pin_row _ rfl irV2_rung236 cutV2_rung236 (by simp [packLam, packsV2])

theorem irV2_s2a : irV2 "story2_lateral_rung_a_8dof" = story2_lateral_rung_a_8dof_IRv2 := by decide
theorem cutV2_s2a : cutV2 "story2_lateral_rung_a_8dof" = Oracle.story2_lateral_rung_a_8dof_cutsV2X := by decide
theorem pin_s2a_j0 : Story2LateralAGuarded.Verd 0 0 = packVerd (packsV2.getD 170 default) :=
  pin_row _ rfl irV2_s2a cutV2_s2a (by simp [packLam, packsV2])
theorem pin_s2a_j1 : Story2LateralAGuarded.Verd 0 1 = packVerd (packsV2.getD 171 default) :=
  pin_row _ rfl irV2_s2a cutV2_s2a (by simp [packLam, packsV2])
theorem pin_s2a_j2 : Story2LateralAGuarded.Verd 0 2 = packVerd (packsV2.getD 172 default) :=
  pin_row _ rfl irV2_s2a cutV2_s2a (by simp [packLam, packsV2])
theorem pin_s2a_j3 : Story2LateralAGuarded.Verd 1 1 = packVerd (packsV2.getD 173 default) :=
  pin_row _ rfl irV2_s2a cutV2_s2a (by simp [packLam, packsV2])
theorem pin_s2a_j4 : Story2LateralAGuarded.Verd 1 2 = packVerd (packsV2.getD 174 default) :=
  pin_row _ rfl irV2_s2a cutV2_s2a (by simp [packLam, packsV2])
theorem pin_s2a_j5 : Story2LateralAGuarded.Verd 2 2 = packVerd (packsV2.getD 175 default) :=
  pin_row _ rfl irV2_s2a cutV2_s2a (by simp [packLam, packsV2])

theorem irV2_s2b : irV2 "story2_lateral_rung_b_12dof" = story2_lateral_rung_b_12dof_IRv2 := by decide
theorem cutV2_s2b : cutV2 "story2_lateral_rung_b_12dof" = Oracle.story2_lateral_rung_b_12dof_cutsV2X := by decide
theorem pin_s2b_j0 : Story2LateralBGuarded.Verd 0 0 = packVerd (packsV2.getD 176 default) :=
  pin_row _ rfl irV2_s2b cutV2_s2b (by simp [packLam, packsV2])
theorem pin_s2b_j1 : Story2LateralBGuarded.Verd 0 1 = packVerd (packsV2.getD 177 default) :=
  pin_row _ rfl irV2_s2b cutV2_s2b (by simp [packLam, packsV2])
theorem pin_s2b_j2 : Story2LateralBGuarded.Verd 0 2 = packVerd (packsV2.getD 178 default) :=
  pin_row _ rfl irV2_s2b cutV2_s2b (by simp [packLam, packsV2])
theorem pin_s2b_j3 : Story2LateralBGuarded.Verd 1 1 = packVerd (packsV2.getD 179 default) :=
  pin_row _ rfl irV2_s2b cutV2_s2b (by simp [packLam, packsV2])
theorem pin_s2b_j4 : Story2LateralBGuarded.Verd 1 2 = packVerd (packsV2.getD 180 default) :=
  pin_row _ rfl irV2_s2b cutV2_s2b (by simp [packLam, packsV2])
theorem pin_s2b_j5 : Story2LateralBGuarded.Verd 2 2 = packVerd (packsV2.getD 181 default) :=
  pin_row _ rfl irV2_s2b cutV2_s2b (by simp [packLam, packsV2])

theorem irV2_s1a : irV2 "story1_attdist_rung_a_6to8" = story1_attdist_rung_a_6to8_IRv2 := by decide
theorem cutV2_s1a : cutV2 "story1_attdist_rung_a_6to8" = Oracle.story1_attdist_rung_a_6to8_cutsV2X := by decide
theorem pin_s1a_j0 : Story1AttdistRungAGuarded.Verd 0 0 = packVerd (packsV2.getD 182 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j1 : Story1AttdistRungAGuarded.Verd 0 1 = packVerd (packsV2.getD 183 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j2 : Story1AttdistRungAGuarded.Verd 0 2 = packVerd (packsV2.getD 184 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j3 : Story1AttdistRungAGuarded.Verd 1 0 = packVerd (packsV2.getD 185 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j4 : Story1AttdistRungAGuarded.Verd 1 1 = packVerd (packsV2.getD 186 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j5 : Story1AttdistRungAGuarded.Verd 1 2 = packVerd (packsV2.getD 187 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j6 : Story1AttdistRungAGuarded.Verd 2 0 = packVerd (packsV2.getD 188 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j7 : Story1AttdistRungAGuarded.Verd 2 1 = packVerd (packsV2.getD 189 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])
theorem pin_s1a_j8 : Story1AttdistRungAGuarded.Verd 2 2 = packVerd (packsV2.getD 190 default) :=
  pin_row _ rfl irV2_s1a cutV2_s1a (by simp [packLam, packsV2])

theorem irV2_s1b : irV2 "story1_attdist_rung_b_12dof" = story1_attdist_rung_b_12dof_IRv2 := by decide
theorem cutV2_s1b : cutV2 "story1_attdist_rung_b_12dof" = Oracle.story1_attdist_rung_b_12dof_cutsV2X := by decide
theorem pin_s1b_j0 : Story1AttdistRungBGuarded.Verd 0 0 = packVerd (packsV2.getD 191 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j1 : Story1AttdistRungBGuarded.Verd 0 1 = packVerd (packsV2.getD 192 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j2 : Story1AttdistRungBGuarded.Verd 0 2 = packVerd (packsV2.getD 193 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j3 : Story1AttdistRungBGuarded.Verd 1 0 = packVerd (packsV2.getD 194 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j4 : Story1AttdistRungBGuarded.Verd 1 1 = packVerd (packsV2.getD 195 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j5 : Story1AttdistRungBGuarded.Verd 1 2 = packVerd (packsV2.getD 196 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j6 : Story1AttdistRungBGuarded.Verd 2 0 = packVerd (packsV2.getD 197 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j7 : Story1AttdistRungBGuarded.Verd 2 1 = packVerd (packsV2.getD 198 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])
theorem pin_s1b_j8 : Story1AttdistRungBGuarded.Verd 2 2 = packVerd (packsV2.getD 199 default) :=
  pin_row _ rfl irV2_s1b cutV2_s1b (by simp [packLam, packsV2])

theorem irV2_r2c : irV2 "refinement_ladder_rover_rung2c_6dof" = refinement_ladder_rover_rung2c_6dof_IRv2 := by decide
theorem cutV2_r2c : cutV2 "refinement_ladder_rover_rung2c_6dof" = Oracle.refinement_ladder_rover_rung2c_6dof_cutsV2X := by decide
theorem pin_r2c_j0 : RoverRung2cGuarded.Verd 0 0 = packVerd (packsV2.getD 200 default) :=
  pin_row _ rfl irV2_r2c cutV2_r2c (by simp [packLam, packsV2])
theorem pin_r2c_j1 : RoverRung2cGuarded.Verd 1 1 = packVerd (packsV2.getD 201 default) :=
  pin_row _ rfl irV2_r2c cutV2_r2c (by simp [packLam, packsV2])
theorem pin_r2c_j2 : RoverRung2cGuarded.Verd 2 2 = packVerd (packsV2.getD 202 default) :=
  pin_row _ rfl irV2_r2c cutV2_r2c (by simp [packLam, packsV2])

theorem irV2_r3t : irV2 "rover3tier_rung12" = rover3tier_rung12_IRv2 := by decide
theorem cutV2_r3t : cutV2 "rover3tier_rung12" = Oracle.rover3tier_rung12_cutsV2X := by decide
theorem pin_r3t_j0 : Rover3tierRung12Guarded.Verd 0 0 = packVerd (packsV2.getD 203 default) :=
  pin_row _ rfl irV2_r3t cutV2_r3t (by simp [packLam, packsV2])
theorem pin_r3t_j1 : Rover3tierRung12Guarded.Verd 0 1 = packVerd (packsV2.getD 204 default) :=
  pin_row _ rfl irV2_r3t cutV2_r3t (by simp [packLam, packsV2])
theorem pin_r3t_j2 : Rover3tierRung12Guarded.Verd 1 0 = packVerd (packsV2.getD 205 default) :=
  pin_row _ rfl irV2_r3t cutV2_r3t (by simp [packLam, packsV2])
theorem pin_r3t_j3 : Rover3tierRung12Guarded.Verd 1 1 = packVerd (packsV2.getD 206 default) :=
  pin_row _ rfl irV2_r3t cutV2_r3t (by simp [packLam, packsV2])

theorem irV2_mmr : irV2 "match_multi_rate" = match_multi_rate_IRv2 := by decide
theorem cutV2_mmr : cutV2 "match_multi_rate" = Oracle.match_multi_rate_cutsV2X := by decide
theorem pin_mmr_j0 : MatchMultiRateGuarded.Verd 0 0 = packVerd (packsV2.getD 207 default) :=
  pin_row _ rfl irV2_mmr cutV2_mmr (by simp [packLam, packsV2])
theorem pin_mmr_j1 : MatchMultiRateGuarded.Verd 1 0 = packVerd (packsV2.getD 208 default) :=
  pin_row _ rfl irV2_mmr cutV2_mmr (by simp [packLam, packsV2])
theorem pin_mmr_j2 : MatchMultiRateGuarded.Verd 2 0 = packVerd (packsV2.getD 209 default) :=
  pin_row _ rfl irV2_mmr cutV2_mmr (by simp [packLam, packsV2])
theorem pin_mmr_j3 : MatchMultiRateGuarded.Verd 3 0 = packVerd (packsV2.getD 210 default) :=
  pin_row _ rfl irV2_mmr cutV2_mmr (by simp [packLam, packsV2])

theorem irV2_armc : irV2 "arm_plateau_crit" = arm_plateau_crit_IRv2 := by decide
theorem cutV2_armc : cutV2 "arm_plateau_crit" = Oracle.arm_plateau_crit_cutsV2X := by decide
theorem pin_armc_j0 : V2ArmPlateauCrit.Verd 0 0 = packVerd (packsV2.getD 211 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_j1 : V2ArmPlateauCrit.Verd 0 1 = packVerd (packsV2.getD 212 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_j2 : V2ArmPlateauCrit.Verd 0 2 = packVerd (packsV2.getD 213 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_j3 : V2ArmPlateauCrit.Verd 0 3 = packVerd (packsV2.getD 214 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_j4 : V2ArmPlateauCrit.Verd 1 1 = packVerd (packsV2.getD 215 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_j5 : V2ArmPlateauCrit.Verd 1 2 = packVerd (packsV2.getD 216 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_j6 : V2ArmPlateauCrit.Verd 1 3 = packVerd (packsV2.getD 217 default) :=
  pin_row _ rfl irV2_armc cutV2_armc (by simp [packLam, packsV2])
theorem pin_armc_d0 : V2ArmPlateauCrit.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 24 default) :=
  pin_dyn_row _ rfl irV2_armc cutV2_armc

theorem irV2_armp : irV2 "arm_plateau_profiles" = arm_plateau_profiles_IRv2 := by decide
theorem cutV2_armp : cutV2 "arm_plateau_profiles" = Oracle.arm_plateau_profiles_cutsV2X := by decide
theorem pin_armp_j0 : V2ArmPlateauProfiles.Verd 0 0 = packVerd (packsV2.getD 218 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j1 : V2ArmPlateauProfiles.Verd 0 1 = packVerd (packsV2.getD 219 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j2 : V2ArmPlateauProfiles.Verd 0 2 = packVerd (packsV2.getD 220 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j3 : V2ArmPlateauProfiles.Verd 0 3 = packVerd (packsV2.getD 221 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j4 : V2ArmPlateauProfiles.Verd 0 4 = packVerd (packsV2.getD 222 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j5 : V2ArmPlateauProfiles.Verd 1 0 = packVerd (packsV2.getD 223 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j6 : V2ArmPlateauProfiles.Verd 1 1 = packVerd (packsV2.getD 224 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j7 : V2ArmPlateauProfiles.Verd 1 2 = packVerd (packsV2.getD 225 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j8 : V2ArmPlateauProfiles.Verd 1 3 = packVerd (packsV2.getD 226 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])
theorem pin_armp_j9 : V2ArmPlateauProfiles.Verd 1 4 = packVerd (packsV2.getD 227 default) :=
  pin_row _ rfl irV2_armp cutV2_armp (by simp [packLam, packsV2])

theorem irV2_arms : irV2 "arm_plateau_slow" = arm_plateau_slow_IRv2 := by decide
theorem cutV2_arms : cutV2 "arm_plateau_slow" = Oracle.arm_plateau_slow_cutsV2X := by decide
theorem pin_arms_j0 : V2ArmPlateauSlow.Verd 0 0 = packVerd (packsV2.getD 228 default) :=
  pin_row _ rfl irV2_arms cutV2_arms (by simp [packLam, packsV2])
theorem pin_arms_j1 : V2ArmPlateauSlow.Verd 0 2 = packVerd (packsV2.getD 229 default) :=
  pin_row _ rfl irV2_arms cutV2_arms (by simp [packLam, packsV2])
theorem pin_arms_j2 : V2ArmPlateauSlow.Verd 0 3 = packVerd (packsV2.getD 230 default) :=
  pin_row _ rfl irV2_arms cutV2_arms (by simp [packLam, packsV2])
theorem pin_arms_j3 : V2ArmPlateauSlow.Verd 1 1 = packVerd (packsV2.getD 231 default) :=
  pin_row _ rfl irV2_arms cutV2_arms (by simp [packLam, packsV2])
theorem pin_arms_j4 : V2ArmPlateauSlow.Verd 1 2 = packVerd (packsV2.getD 232 default) :=
  pin_row _ rfl irV2_arms cutV2_arms (by simp [packLam, packsV2])
theorem pin_arms_j5 : V2ArmPlateauSlow.Verd 1 3 = packVerd (packsV2.getD 233 default) :=
  pin_row _ rfl irV2_arms cutV2_arms (by simp [packLam, packsV2])
theorem pin_arms_d0 : V2ArmPlateauSlow.VerdD 0 1 = dynPackVerd (dynPacksV2.getD 25 default) :=
  pin_dyn_row _ rfl irV2_arms cutV2_arms

theorem irV2_cfs : irV2 "charger_fast_setpoints" = charger_fast_setpoints_IRv2 := by decide
theorem cutV2_cfs : cutV2 "charger_fast_setpoints" = Oracle.charger_fast_setpoints_cutsV2X := by decide
theorem pin_cfs_d0 : V2ChargerFastSetpoints.VerdD 0 0 = dynPackVerd (dynPacksV2.getD 26 default) :=
  pin_dyn_row _ rfl irV2_cfs cutV2_cfs
theorem pin_cfs_d1 : V2ChargerFastSetpoints.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 27 default) :=
  pin_dyn_row _ rfl irV2_cfs cutV2_cfs

theorem irV2_cft : irV2 "charger_fast_tapers" = charger_fast_tapers_IRv2 := by decide
theorem cutV2_cft : cutV2 "charger_fast_tapers" = Oracle.charger_fast_tapers_cutsV2X := by decide
theorem pin_cft_d0 : V2ChargerFastTapers.VerdD 0 0 = dynPackVerd (dynPacksV2.getD 28 default) :=
  pin_dyn_row _ rfl irV2_cft cutV2_cft
theorem pin_cft_d1 : V2ChargerFastTapers.VerdD 0 1 = dynPackVerd (dynPacksV2.getD 29 default) :=
  pin_dyn_row _ rfl irV2_cft cutV2_cft
theorem pin_cft_d2 : V2ChargerFastTapers.VerdD 0 2 = dynPackVerd (dynPacksV2.getD 30 default) :=
  pin_dyn_row _ rfl irV2_cft cutV2_cft

theorem irV2_rpz : irV2 "rover_patrol_zones" = rover_patrol_zones_IRv2 := by decide
theorem cutV2_rpz : cutV2 "rover_patrol_zones" = Oracle.rover_patrol_zones_cutsV2X := by decide
theorem pin_rpz_d0 : V2RoverPatrolZonesGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 31 default) :=
  pin_dyn_row _ rfl irV2_rpz cutV2_rpz
theorem pin_rpz_d1 : V2RoverPatrolZonesGuarded.VerdD 2 0 = dynPackVerd (dynPacksV2.getD 32 default) :=
  pin_dyn_row _ rfl irV2_rpz cutV2_rpz
theorem pin_rpz_d2 : V2RoverPatrolZonesGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 33 default) :=
  pin_dyn_row _ rfl irV2_rpz cutV2_rpz
theorem pin_rpz_d3 : V2RoverPatrolZonesGuarded.VerdD 3 1 = dynPackVerd (dynPacksV2.getD 34 default) :=
  pin_dyn_row _ rfl irV2_rpz cutV2_rpz
theorem pin_rpz_d4 : V2RoverPatrolZonesGuarded.VerdD 3 2 = dynPackVerd (dynPacksV2.getD 35 default) :=
  pin_dyn_row _ rfl irV2_rpz cutV2_rpz

theorem irV2_rpr : irV2 "rover_patrol_refine" = rover_patrol_refine_IRv2 := by decide
theorem cutV2_rpr : cutV2 "rover_patrol_refine" = Oracle.rover_patrol_refine_cutsV2X := by decide
theorem pin_rpr_d0 : V2RoverPatrolRefineGuarded.VerdD 1 0 = dynPackVerd (dynPacksV2.getD 36 default) :=
  pin_dyn_row _ rfl irV2_rpr cutV2_rpr
theorem pin_rpr_d1 : V2RoverPatrolRefineGuarded.VerdD 2 0 = dynPackVerd (dynPacksV2.getD 37 default) :=
  pin_dyn_row _ rfl irV2_rpr cutV2_rpr
theorem pin_rpr_d2 : V2RoverPatrolRefineGuarded.VerdD 2 1 = dynPackVerd (dynPacksV2.getD 38 default) :=
  pin_dyn_row _ rfl irV2_rpr cutV2_rpr
theorem pin_rpr_d3 : V2RoverPatrolRefineGuarded.VerdD 3 1 = dynPackVerd (dynPacksV2.getD 39 default) :=
  pin_dyn_row _ rfl irV2_rpr cutV2_rpr
theorem pin_rpr_d4 : V2RoverPatrolRefineGuarded.VerdD 3 2 = dynPackVerd (dynPacksV2.getD 40 default) :=
  pin_dyn_row _ rfl irV2_rpr cutV2_rpr

end RelCertifier.VerdictsV2
