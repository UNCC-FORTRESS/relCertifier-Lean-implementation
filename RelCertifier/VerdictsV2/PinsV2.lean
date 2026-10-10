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

namespace RelCertifier.VerdictsV2

open RelCertifier RelCertifier.Parse

/-- Pin helper: same IR, same certificate, same λ (as reals), same arguments. -/
theorem pin_row {P : Prop} (r : PackV2) {p : PProblem} {c : Oracle.EvolStrengtheningX}
    {lam : ℝ} (hP : P = modalVerdX p c r.dim r.invRow r.order lam r.l r.m)
    (hp : irV2 r.bench = p) (hc : cutV2 r.bench = c) (hlam : lam = ((packLam r : ℚ) : ℝ)) :
    P = packVerd r := by
  rw [hP, packVerd, hp, hc, hlam]

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
theorem pin_watertank_03 : V2Watertank.Verd 0 3 = packVerd (packsV2.getD 3 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_11 : V2Watertank.Verd 1 1 = packVerd (packsV2.getD 4 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_12 : V2Watertank.Verd 1 2 = packVerd (packsV2.getD 5 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_13 : V2Watertank.Verd 1 3 = packVerd (packsV2.getD 6 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_20 : V2Watertank.Verd 2 0 = packVerd (packsV2.getD 7 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_21 : V2Watertank.Verd 2 1 = packVerd (packsV2.getD 8 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_22 : V2Watertank.Verd 2 2 = packVerd (packsV2.getD 9 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])
theorem pin_watertank_23 : V2Watertank.Verd 2 3 = packVerd (packsV2.getD 10 default) :=
  pin_row _ rfl irV2_watertank cutV2_watertank (by simp [packLam, packsV2, V2Watertank.lam])

theorem irV2_pdp : irV2 "platoon_delay_profiles" = platoon_delay_profiles_IRv2 := by decide
theorem cutV2_pdp : cutV2 "platoon_delay_profiles" = Oracle.platoon_delay_profiles_cutsV2X := by decide
theorem pin_platoon_delay_profiles_00 : V2PlatoonDelayProfiles.Verd 0 0 = packVerd (packsV2.getD 11 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_01 : V2PlatoonDelayProfiles.Verd 0 1 = packVerd (packsV2.getD 12 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_02 : V2PlatoonDelayProfiles.Verd 0 2 = packVerd (packsV2.getD 13 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_10 : V2PlatoonDelayProfiles.Verd 1 0 = packVerd (packsV2.getD 14 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_11 : V2PlatoonDelayProfiles.Verd 1 1 = packVerd (packsV2.getD 15 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])
theorem pin_platoon_delay_profiles_12 : V2PlatoonDelayProfiles.Verd 1 2 = packVerd (packsV2.getD 16 default) :=
  pin_row _ rfl irV2_pdp cutV2_pdp (by simp [packLam, packsV2, V2PlatoonDelayProfiles.lam])

theorem irV2_acc_spoof_limp : irV2 "acc_spoof_limp" = acc_spoof_limp_IRv2 := by decide
theorem cutV2_acc_spoof_limp : cutV2 "acc_spoof_limp" = Oracle.acc_spoof_limp_cutsV2X := by decide
theorem pin_acc_spoof_limp_0 : V2AccSpoofLimp.Verd 0 0 = packVerd (packsV2.getD 17 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_1 : V2AccSpoofLimp.Verd 0 1 = packVerd (packsV2.getD 18 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_2 : V2AccSpoofLimp.Verd 0 2 = packVerd (packsV2.getD 19 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_3 : V2AccSpoofLimp.Verd 1 0 = packVerd (packsV2.getD 20 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_4 : V2AccSpoofLimp.Verd 1 1 = packVerd (packsV2.getD 21 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])
theorem pin_acc_spoof_limp_5 : V2AccSpoofLimp.Verd 1 2 = packVerd (packsV2.getD 22 default) :=
  pin_row _ rfl irV2_acc_spoof_limp cutV2_acc_spoof_limp (by simp [packLam, packsV2, V2AccSpoofLimp.lam])

theorem irV2_acc_tune_limp : irV2 "acc_tune_limp" = acc_tune_limp_IRv2 := by decide
theorem cutV2_acc_tune_limp : cutV2 "acc_tune_limp" = Oracle.acc_tune_limp_cutsV2X := by decide
theorem pin_acc_tune_limp_0 : V2AccTuneLimp.Verd 0 0 = packVerd (packsV2.getD 23 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_1 : V2AccTuneLimp.Verd 0 1 = packVerd (packsV2.getD 24 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_2 : V2AccTuneLimp.Verd 0 2 = packVerd (packsV2.getD 25 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_3 : V2AccTuneLimp.Verd 1 0 = packVerd (packsV2.getD 26 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_4 : V2AccTuneLimp.Verd 1 1 = packVerd (packsV2.getD 27 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])
theorem pin_acc_tune_limp_5 : V2AccTuneLimp.Verd 1 2 = packVerd (packsV2.getD 28 default) :=
  pin_row _ rfl irV2_acc_tune_limp cutV2_acc_tune_limp (by simp [packLam, packsV2, V2AccTuneLimp.lam])

theorem irV2_platoon_delay_linkloss : irV2 "platoon_delay_linkloss" = platoon_delay_linkloss_IRv2 := by decide
theorem cutV2_platoon_delay_linkloss : cutV2 "platoon_delay_linkloss" = Oracle.platoon_delay_linkloss_cutsV2X := by decide
theorem pin_platoon_delay_linkloss_0 : V2PlatoonDelayLinkloss.Verd 0 0 = packVerd (packsV2.getD 29 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_1 : V2PlatoonDelayLinkloss.Verd 0 1 = packVerd (packsV2.getD 30 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_2 : V2PlatoonDelayLinkloss.Verd 1 0 = packVerd (packsV2.getD 31 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_3 : V2PlatoonDelayLinkloss.Verd 1 1 = packVerd (packsV2.getD 32 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_4 : V2PlatoonDelayLinkloss.Verd 2 0 = packVerd (packsV2.getD 33 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])
theorem pin_platoon_delay_linkloss_5 : V2PlatoonDelayLinkloss.Verd 2 1 = packVerd (packsV2.getD 34 default) :=
  pin_row _ rfl irV2_platoon_delay_linkloss cutV2_platoon_delay_linkloss (by simp [packLam, packsV2])

theorem irV2_quad_light_airframe_20 : irV2 "quad_light_airframe_20" = quad_light_airframe_20_IRv2 := by decide
theorem cutV2_quad_light_airframe_20 : cutV2 "quad_light_airframe_20" = Oracle.quad_light_airframe_20_cutsV2X := by decide
theorem pin_quad_light_airframe_20_0 : V2QuadLightAirframe20.Verd 0 0 = packVerd (packsV2.getD 35 default) :=
  pin_row _ rfl irV2_quad_light_airframe_20 cutV2_quad_light_airframe_20 (by simp [packLam, packsV2, V2QuadLightAirframe20.lam])

theorem irV2_quad_light_profiles : irV2 "quad_light_profiles" = quad_light_profiles_IRv2 := by decide
theorem cutV2_quad_light_profiles : cutV2 "quad_light_profiles" = Oracle.quad_light_profiles_cutsV2X := by decide
theorem pin_quad_light_profiles_0 : V2QuadLightProfiles.Verd 0 0 = packVerd (packsV2.getD 36 default) :=
  pin_row _ rfl irV2_quad_light_profiles cutV2_quad_light_profiles (by simp [packLam, packsV2, V2QuadLightProfiles.lam])
theorem pin_quad_light_profiles_1 : V2QuadLightProfiles.Verd 0 1 = packVerd (packsV2.getD 37 default) :=
  pin_row _ rfl irV2_quad_light_profiles cutV2_quad_light_profiles (by simp [packLam, packsV2, V2QuadLightProfiles.lam])
theorem pin_quad_light_profiles_2 : V2QuadLightProfiles.Verd 0 2 = packVerd (packsV2.getD 38 default) :=
  pin_row _ rfl irV2_quad_light_profiles cutV2_quad_light_profiles (by simp [packLam, packsV2, V2QuadLightProfiles.lam])

theorem irV2_quad_light_lag : irV2 "quad_light_lag" = quad_light_lag_IRv2 := by decide
theorem cutV2_quad_light_lag : cutV2 "quad_light_lag" = Oracle.quad_light_lag_cutsV2X := by decide
theorem pin_quad_light_lag_0 : V2QuadLightLag.Verd 0 0 = packVerd (packsV2.getD 39 default) :=
  pin_row _ rfl irV2_quad_light_lag cutV2_quad_light_lag (by simp [packLam, packsV2, V2QuadLightLag.lam])

theorem irV2_charger_fast_setpoints : irV2 "charger_fast_setpoints" = charger_fast_setpoints_IRv2 := by decide
theorem cutV2_charger_fast_setpoints : cutV2 "charger_fast_setpoints" = Oracle.charger_fast_setpoints_cutsV2X := by decide
theorem pin_charger_fast_setpoints_0 : V2ChargerFastSetpoints.Verd 0 1 = packVerd (packsV2.getD 40 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_1 : V2ChargerFastSetpoints.Verd 0 2 = packVerd (packsV2.getD 41 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_2 : V2ChargerFastSetpoints.Verd 1 1 = packVerd (packsV2.getD 42 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_3 : V2ChargerFastSetpoints.Verd 1 2 = packVerd (packsV2.getD 43 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_4 : V2ChargerFastSetpoints.Verd 2 0 = packVerd (packsV2.getD 44 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_5 : V2ChargerFastSetpoints.Verd 2 1 = packVerd (packsV2.getD 45 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])
theorem pin_charger_fast_setpoints_6 : V2ChargerFastSetpoints.Verd 2 2 = packVerd (packsV2.getD 46 default) :=
  pin_row _ rfl irV2_charger_fast_setpoints cutV2_charger_fast_setpoints (by simp [packLam, packsV2, V2ChargerFastSetpoints.lam])

theorem irV2_acc_tune_lag : irV2 "acc_tune_lag" = acc_tune_lag_IRv2 := by decide
theorem cutV2_acc_tune_lag : cutV2 "acc_tune_lag" = Oracle.acc_tune_lag_cutsV2X := by decide
theorem pin_acc_tune_lag_0 : V2AccTuneLag.Verd 0 = packVerd (packsV2.getD 47 default) :=
  pin_row _ rfl irV2_acc_tune_lag cutV2_acc_tune_lag (by simp [packLam, packsV2])

theorem irV2_acc_spoof_lag : irV2 "acc_spoof_lag" = acc_spoof_lag_IRv2 := by decide
theorem cutV2_acc_spoof_lag : cutV2 "acc_spoof_lag" = Oracle.acc_spoof_lag_cutsV2X := by decide
theorem pin_acc_spoof_lag_0 : V2AccSpoofLag.Verd 0 = packVerd (packsV2.getD 48 default) :=
  pin_row _ rfl irV2_acc_spoof_lag cutV2_acc_spoof_lag (by simp [packLam, packsV2])

theorem irV2_charger_fast_tapers : irV2 "charger_fast_tapers" = charger_fast_tapers_IRv2 := by decide
theorem cutV2_charger_fast_tapers : cutV2 "charger_fast_tapers" = Oracle.charger_fast_tapers_cutsV2X := by decide
theorem pin_charger_fast_tapers_0 : V2ChargerFastTapers.Verd 0 3 = packVerd (packsV2.getD 49 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_1 : V2ChargerFastTapers.Verd 1 0 = packVerd (packsV2.getD 50 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_2 : V2ChargerFastTapers.Verd 1 1 = packVerd (packsV2.getD 51 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_3 : V2ChargerFastTapers.Verd 1 2 = packVerd (packsV2.getD 52 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_4 : V2ChargerFastTapers.Verd 1 3 = packVerd (packsV2.getD 53 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_5 : V2ChargerFastTapers.Verd 2 0 = packVerd (packsV2.getD 54 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_6 : V2ChargerFastTapers.Verd 2 1 = packVerd (packsV2.getD 55 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_7 : V2ChargerFastTapers.Verd 2 2 = packVerd (packsV2.getD 56 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])
theorem pin_charger_fast_tapers_8 : V2ChargerFastTapers.Verd 2 3 = packVerd (packsV2.getD 57 default) :=
  pin_row _ rfl irV2_charger_fast_tapers cutV2_charger_fast_tapers (by simp [packLam, packsV2, V2ChargerFastTapers.lam])

theorem irV2_story3_rollover_ladder_rung_b : irV2 "story3_rollover_ladder_rung_b" = story3_rollover_ladder_rung_b_IRv2 := by decide
theorem cutV2_story3_rollover_ladder_rung_b : cutV2 "story3_rollover_ladder_rung_b" = Oracle.story3_rollover_ladder_rung_b_cutsV2X := by decide
theorem pin_story3_rollover_ladder_rung_b_0 : V2Story3RolloverRungB.Verd 0 0 = packVerd (packsV2.getD 58 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_1 : V2Story3RolloverRungB.Verd 0 1 = packVerd (packsV2.getD 59 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_2 : V2Story3RolloverRungB.Verd 0 2 = packVerd (packsV2.getD 60 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_3 : V2Story3RolloverRungB.Verd 1 0 = packVerd (packsV2.getD 61 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_4 : V2Story3RolloverRungB.Verd 1 1 = packVerd (packsV2.getD 62 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_5 : V2Story3RolloverRungB.Verd 1 2 = packVerd (packsV2.getD 63 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_6 : V2Story3RolloverRungB.Verd 2 0 = packVerd (packsV2.getD 64 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_7 : V2Story3RolloverRungB.Verd 2 1 = packVerd (packsV2.getD 65 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])
theorem pin_story3_rollover_ladder_rung_b_8 : V2Story3RolloverRungB.Verd 2 2 = packVerd (packsV2.getD 66 default) :=
  pin_row _ rfl irV2_story3_rollover_ladder_rung_b cutV2_story3_rollover_ladder_rung_b (by simp [packLam, packsV2])

theorem irV2_sat_detumble_nominal : irV2 "sat_detumble_nominal" = sat_detumble_nominal_IRv2 := by decide
theorem cutV2_sat_detumble_nominal : cutV2 "sat_detumble_nominal" = Oracle.sat_detumble_nominal_cutsV2X := by decide
theorem pin_sat_detumble_nominal_0 : V2SatDetumbleNominal.Verd 0 0 = packVerd (packsV2.getD 67 default) :=
  pin_row _ rfl irV2_sat_detumble_nominal cutV2_sat_detumble_nominal (by simp [packLam, packsV2])

theorem irV2_platoon3_profiles : irV2 "platoon3_profiles" = platoon3_profiles_IRv2 := by decide
theorem cutV2_platoon3_profiles : cutV2 "platoon3_profiles" = Oracle.platoon3_profiles_cutsV2X := by decide
theorem pin_platoon3_profiles_0 : V2Platoon3Profiles.Verd 0 0 = packVerd (packsV2.getD 68 default) :=
  pin_row _ rfl irV2_platoon3_profiles cutV2_platoon3_profiles (by simp [packLam, packsV2])
theorem pin_platoon3_profiles_1 : V2Platoon3Profiles.Verd 0 1 = packVerd (packsV2.getD 69 default) :=
  pin_row _ rfl irV2_platoon3_profiles cutV2_platoon3_profiles (by simp [packLam, packsV2])
theorem pin_platoon3_profiles_2 : V2Platoon3Profiles.Verd 0 2 = packVerd (packsV2.getD 70 default) :=
  pin_row _ rfl irV2_platoon3_profiles cutV2_platoon3_profiles (by simp [packLam, packsV2])

theorem irV2_platoon3_linkloss : irV2 "platoon3_linkloss" = platoon3_linkloss_IRv2 := by decide
theorem cutV2_platoon3_linkloss : cutV2 "platoon3_linkloss" = Oracle.platoon3_linkloss_cutsV2X := by decide
theorem pin_platoon3_linkloss_0 : V2Platoon3Linkloss.Verd 0 0 = packVerd (packsV2.getD 71 default) :=
  pin_row _ rfl irV2_platoon3_linkloss cutV2_platoon3_linkloss (by simp [packLam, packsV2])
theorem pin_platoon3_linkloss_1 : V2Platoon3Linkloss.Verd 1 0 = packVerd (packsV2.getD 72 default) :=
  pin_row _ rfl irV2_platoon3_linkloss cutV2_platoon3_linkloss (by simp [packLam, packsV2])

end RelCertifier.VerdictsV2
