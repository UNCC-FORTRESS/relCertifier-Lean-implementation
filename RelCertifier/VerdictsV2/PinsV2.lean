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

end RelCertifier.VerdictsV2
