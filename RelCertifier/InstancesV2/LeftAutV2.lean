/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# suite_v2 mode-independent instances: Theorem 3 with the paper's left program

Each benchmark below declares one relational invariant for every left mode. Its guarded
Theorem 3 was first stated over the plain choice of its left windows (`bigChoice
(leftProgs dt)`, each window beginning with its own guard test). Here it is restated over
the paper's left program, the guard-gated LEFT AUTOMATON `leftAutomatonBody (AL dt) uLA`
(`?(u_L = m') ; ⋃_{t ∈ next m'} ?guard_t ; u_L := t ; window_t`, the declared successors
`next` read from the IR), with the same rows for every left mode (`psiK` with a constant
row), the same envelope and the same right side (guarded right automaton, the right in its
current mode's guard and cuts). The proof is the generic bridge
`theorem3_leftAut_of_choiceR` (`Proofs/Encoding/LeftAutUniform.lean`): the left automaton
only removes left runs and adds `u_L`, which nothing else reads. The packs are those of the
choice-form theorem.
-/
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.InstancesV2.Modal.AccSpoofLag
import RelCertifier.InstancesV2.Modal.AccTuneLag
import RelCertifier.InstancesV2.Modal.ArmPlateauCrit
import RelCertifier.InstancesV2.Modal.ArmPlateauProfiles
import RelCertifier.InstancesV2.Modal.ArmPlateauSlow
import RelCertifier.InstancesV2.Modal.ChargerFastSetpoints
import RelCertifier.InstancesV2.Modal.ChargerFastTapers
import RelCertifier.InstancesV2.Modal.PlatoonDelayProfiles
import RelCertifier.InstancesV2.Modal.QuadLightAirframe20
import RelCertifier.InstancesV2.Modal.QuadLightLag
import RelCertifier.InstancesV2.Modal.QuadLightProfiles
import RelCertifier.InstancesV2.Modal.Watertank
import RelCertifier.InstancesV2.Modal.SatDetumbleNominal
import RelCertifier.InstancesV2.Modal.SatDetumbleWeak
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleNominal
import RelCertifier.InstancesV2.Modal.Sat3wDetumbleWeak

namespace RelCertifier

namespace V2AccSpoofLag
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `acc_spoof_lag`: the file's left `next` lists, resolved to indices (CRUISE). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex acc_spoof_lag_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`acc_spoof_lag`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `acc_spoof_lag_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem acc_spoof_lag_leftAut (dt : ℝ) (h0 : Verd 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g []) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (acc_spoof_lag_modal dt h0)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2AccSpoofLag

namespace V2AccTuneLag
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `acc_tune_lag`: the file's left `next` lists, resolved to indices (CRUISE). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex acc_tune_lag_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`acc_tune_lag`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `acc_tune_lag_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem acc_tune_lag_leftAut (dt : ℝ) (h0 : Verd 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g []) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (acc_tune_lag_modal dt h0)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2AccTuneLag

namespace V2ArmPlateauCrit
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `arm_plateau_crit`: the file's left `next` lists, resolved to indices (Accelerate, Brake). -/
def nextLA : List (List ℕ) :=
  (List.range 2).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex arm_plateau_crit_IRv2))

theorem nextLA_eq : nextLA = [[1, 0], [0, 1]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 2).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 2 := rfl

/-- **`arm_plateau_crit`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `arm_plateau_crit_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem arm_plateau_crit_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (d10 : VerdD 1 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g []) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (arm_plateau_crit_modal dt h00 h01 h02 h03 h11 h12 h13 d10)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 2 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2ArmPlateauCrit

namespace V2ArmPlateauProfiles
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `arm_plateau_profiles`: the file's left `next` lists, resolved to indices (Accelerate, Brake). -/
def nextLA : List (List ℕ) :=
  (List.range 2).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex arm_plateau_profiles_IRv2))

theorem nextLA_eq : nextLA = [[1, 0], [0, 1]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 2).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 2 := rfl

/-- **`arm_plateau_profiles`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `arm_plateau_profiles_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem arm_plateau_profiles_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3) (h04 : Verd 0 4)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (h14 : Verd 1 4) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g []) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (arm_plateau_profiles_modal dt h00 h01 h02 h03 h04 h10 h11 h12 h13 h14)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 2 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2ArmPlateauProfiles

namespace V2ArmPlateauSlow
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `arm_plateau_slow`: the file's left `next` lists, resolved to indices (Accelerate, Brake). -/
def nextLA : List (List ℕ) :=
  (List.range 2).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex arm_plateau_slow_IRv2))

theorem nextLA_eq : nextLA = [[1, 0], [0, 1]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 2).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 2 := rfl

/-- **`arm_plateau_slow`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `arm_plateau_slow_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem arm_plateau_slow_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3) (d01 : VerdD 0 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g []) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (arm_plateau_slow_modal dt h00 h02 h03 h11 h12 h13 d01)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 2 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2ArmPlateauSlow

namespace V2ChargerFastSetpoints
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `charger_fast_setpoints`: the file's left `next` lists, resolved to indices (BULK, ABSORB, FULL). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex charger_fast_setpoints_IRv2))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

/-- **`charger_fast_setpoints`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `charger_fast_setpoints_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem charger_fast_setpoints_leftAut (dt : ℝ)
    (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h21 : Verd 2 1) (h22 : Verd 2 2) (d00 : VerdD 0 0) (d10 : VerdD 1 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (charger_fast_setpoints_modal dt h01 h02 h11 h12 h21 h22 d00 d10)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2ChargerFastSetpoints

namespace V2ChargerFastTapers
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `charger_fast_tapers`: the file's left `next` lists, resolved to indices (BULK, ABSORB, FULL). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex charger_fast_tapers_IRv2))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

/-- **`charger_fast_tapers`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `charger_fast_tapers_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem charger_fast_tapers_leftAut (dt : ℝ) (h03 : Verd 0 3)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3)
    (h21 : Verd 2 1) (h22 : Verd 2 2) (h23 : Verd 2 3)
    (d00 : VerdD 0 0) (d01 : VerdD 0 1) (d02 : VerdD 0 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (charger_fast_tapers_modal dt h03 h10 h11 h12 h13 h21 h22 h23 d00 d01 d02)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2ChargerFastTapers

namespace V2PlatoonDelayProfiles
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `platoon_delay_profiles`: the file's left `next` lists, resolved to indices (FOLLOW, GENTLE). -/
def nextLA : List (List ℕ) :=
  (List.range 2).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex platoon_delay_profiles_IRv2))

theorem nextLA_eq : nextLA = [[1, 0], [0, 1]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 2).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 2 := rfl

/-- **`platoon_delay_profiles`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `platoon_delay_profiles_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem platoon_delay_profiles_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2)
    (h10 : Verd 1 0) (h11 : Verd 1 1) (h12 : Verd 1 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (platoon_delay_profiles_modal dt h00 h01 h02 h10 h11 h12)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 2 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2PlatoonDelayProfiles

namespace V2QuadLightAirframe20
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `quad_light_airframe_20`: the file's left `next` lists, resolved to indices (CLIMB). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex quad_light_airframe_20_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`quad_light_airframe_20`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `quad_light_airframe_20_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem quad_light_airframe_20_leftAut (dt : ℝ) (h00 : Verd 0 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (quad_light_airframe_20_modal dt h00)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2QuadLightAirframe20

namespace V2QuadLightLag
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `quad_light_lag`: the file's left `next` lists, resolved to indices (CLIMB). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex quad_light_lag_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`quad_light_lag`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `quad_light_lag_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem quad_light_lag_leftAut (dt : ℝ) (h00 : Verd 0 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (quad_light_lag_modal dt h00)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2QuadLightLag

namespace V2QuadLightProfiles
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `quad_light_profiles`: the file's left `next` lists, resolved to indices (CLIMB). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex quad_light_profiles_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`quad_light_profiles`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `quad_light_profiles_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem quad_light_profiles_leftAut (dt : ℝ) (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (quad_light_profiles_modal dt h00 h01 h02)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2QuadLightProfiles

namespace V2Watertank
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `watertank`: the file's left `next` lists, resolved to indices (Low, Mid, High). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex watertank_IRv2))

theorem nextLA_eq : nextLA = [[0, 1], [1, 2], [2, 1]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vs 2 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

/-- **`watertank`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `watertank_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem watertank_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h03 : Verd 0 3)
    (h11 : Verd 1 1) (h12 : Verd 1 2) (h13 : Verd 1 3)
    (h20 : Verd 2 0) (h21 : Verd 2 1) (h22 : Verd 2 2) (h23 : Verd 2 3) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domL domR gregion _
    (watertank_modal dt h00 h01 h02 h03 h11 h12 h13 h20 h21 h22 h23)
    (fun q hq => gregion_fv q hq)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2Watertank

namespace V2SatDetumbleNominal
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `sat_detumble_nominal`: the file's left `next` lists, resolved to indices (DETUMBLE). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex sat_detumble_nominal_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 4 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 4 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 4 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`sat_detumble_nominal`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `sat_detumble_nominal_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem sat_detumble_nominal_leftAut (dt : ℝ) (h00 : Verd 0 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL domR gregion _
    (sat_detumble_nominal_modal dt h00)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2SatDetumbleNominal

namespace V2SatDetumbleWeak
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `sat_detumble_weak`: the file's left `next` lists, resolved to indices (DETUMBLE). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex sat_detumble_weak_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 4 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 4 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 4 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`sat_detumble_weak`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `sat_detumble_weak_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem sat_detumble_weak_leftAut (dt : ℝ) (h0 : Verd 0 0) (h1 : Verd 0 1) (h2 : Verd 0 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL domR gregion _
    (sat_detumble_weak_modal dt h0 h1 h2)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2SatDetumbleWeak

namespace V2Sat3wDetumbleNominal
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `sat3w_detumble_nominal`: the file's left `next` lists, resolved to indices (DETUMBLE). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex sat3w_detumble_nominal_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 6 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 6 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`sat3w_detumble_nominal`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `sat3w_detumble_nominal_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem sat3w_detumble_nominal_leftAut (dt : ℝ) (h00 : Verd 0 0) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL domR gregion _
    (sat3w_detumble_nominal_modal dt h00)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2Sat3wDetumbleNominal

namespace V2Sat3wDetumbleWeak
open DL DLCalTiming DLRel Parse Set RelCertifier.Oracle

/-- `sat3w_detumble_weak`: the file's left `next` lists, resolved to indices (DETUMBLE). -/
def nextLA : List (List ℕ) :=
  (List.range 1).map (fun l => (mL l).next.filterMap (Handoff.leftModeIndex sat3w_detumble_weak_IRv2))

theorem nextLA_eq : nextLA = [[0]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 6 := LeftAut.ofG leftData tg dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 1).map (fun l => hostGuard vs 6 Side.L (mL l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 1 := rfl

/-- **`sat3w_detumble_weak`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `sat3w_detumble_weak_modal` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem sat3w_detumble_weak_leftAut (dt : ℝ) (h00 : Verd 0 0) (h01 : Verd 0 1)
    (h02 : Verd 0 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody Gr mv)
      (psiK uLA (fun _ => canonInvM g gs) (AL dt).numModes domL domR
        (mvRegionR mv gregion Gr.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL domR gregion _
    (sat3w_detumble_weak_modal dt h00 h01 h02)
    (fun q hq => gregion_fv q)
      (canonInvM_varsL g gs comps_fv) (canonInvM_varsR g gs) hdomL hdomR
    (LeftAut.ofG_vars leftData 1 dt nextLA hL).1 (LeftAut.ofG_vars leftData 1 dt nextLA hL).2
    (LeftAut.ofG_hnext leftData tg dt nextLA 1 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData tg dt nextLA)

end V2Sat3wDetumbleWeak

end RelCertifier
