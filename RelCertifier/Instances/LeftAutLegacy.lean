/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# Carried-over benchmarks, mode-independent invariant: Theorem 3 with the paper's left program

The thirteen carried-over modules below state their guarded Theorem 3 over the plain choice of
their left windows (`bigChoice (leftProgs… dt)`; plain clock-capped windows, or guarded
windows whose own guard is `⊤`). Here each is restated over the paper's left program, the
guard-gated LEFT AUTOMATON `leftAutomatonBody (AL dt) uLA`: each left edge tests the entered
mode's lowered IR guard, the declared successors `next` are read from the IR. Same rows for
every left mode (`psiK` with a constant row), same envelope, same right side. Proof: the
generic bridge `theorem3_leftAut_of_choiceR` (`Proofs/Encoding/LeftAutUniform.lean`).
-/
import RelCertifier.Proofs.Encoding.LeftAutUniform
import RelCertifier.Proofs.Encoding.ReplayBridge
import RelCertifier.Instances.MatchMultiRateGuarded
import RelCertifier.Instances.RoverLadderRung1Guarded
import RelCertifier.Instances.RoverLadderRung3Guarded
import RelCertifier.Instances.RoverLadderRung4Guarded
import RelCertifier.Instances.RoverDofTerrainRung1Guarded
import RelCertifier.Instances.RoverDofTerrainRung2Guarded
import RelCertifier.Instances.RoverDofTerrainRung3Guarded
import RelCertifier.Instances.RoverDofTerrainRung38dGuarded
import RelCertifier.Instances.RoverRung26dofGuarded
import RelCertifier.Instances.RoverRung2b6dofGuarded
import RelCertifier.Instances.RoverRung2cGuarded
import RelCertifier.Instances.Story3RolloverBaseGuarded
import RelCertifier.Instances.Story3RolloverRungAGuarded

namespace RelCertifier

namespace MatchMultiRateGuarded
open DL DLCalTiming DLRel Parse Set MatchMultiRateModal MatchMultiRatePruned

/-- `match_multi_rate`: the file's left `next` lists, resolved to indices (FAST, MEDIUM, SLOW, RESET). -/
def nextLA : List (List ℕ) :=
  (List.range 4).map (fun l => (mLM l).next.filterMap (Handoff.leftModeIndex match_multi_rate_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [3, 2], [0, 3]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataM`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 2 :=
  LeftAut.ofP leftDataM ((List.range 4).map (fun l => hostGuard vsM 2 Side.L (mLM l))) tgM dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 0; the right execution's slot 0 is its `mv`, a different state). -/
abbrev uLA : Var 2 := (Side.Aux, 0)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 4).map (fun l => hostGuard vsM 2 Side.L (mLM l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 4 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 4).map (fun l => hostGuard vsM 2 Side.L (mLM l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsM (mLM l) (by interval_cases l <;> decide)

/-- **`match_multi_rate`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `match_multi_rate_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem match_multi_rate_leftAut (dt : ℝ) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrPG mvM)
      (psiK uLA (fun _ => canonInvM gM gsM) (AL dt).numModes domLM domRM
        (mvRegionR mvM gregionP GrPG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 0 (by decide) _ _ _ domLM domRM gregionP _
    (match_multi_rate_guarded dt)
    (fun q _ => regionG_fv_sub (hguardRM_all q) (sinkRegions_fv_sub _ q))
      (canonInvM_varsL gM gsM (by
        intro g' hg'
        simp only [gM, gsM, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gM gsM) hdomLM hdomRM
    (LeftAut.ofP_vars leftDataM _ 1 dt nextLA hLM hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataM _ 1 dt nextLA hLM hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataM _ tgM dt nextLA 4 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofP_hsim leftDataM _ tgM dt nextLA)

end MatchMultiRateGuarded

namespace RoverLadderRung1Guarded
open DL DLCalTiming DLRel Parse Set RoverLadderRung1Modal

/-- `refinement_ladder_rover_rung1_2to3`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLE l).next.filterMap (Handoff.leftModeIndex refinement_ladder_rover_rung1_2to3_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataE`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 3 :=
  LeftAut.ofP leftDataE ((List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l))) tgE dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 3 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsE (mLE l) (by interval_cases l <;> decide)

/-- **`refinement_ladder_rover_rung1_2to3`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_ladder_rung1_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_ladder_rung1_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvE)
      (psiK uLA (fun _ => canonInvM gE gsE) (AL dt).numModes domLE domRE
        (mvRegionR mvE gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLE domRE gregion _
    (rover_ladder_rung1_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gE gsE (by
        intro g' hg'
        simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gE gsE) hdomLE hdomRE
    (LeftAut.ofP_vars leftDataE _ 1 dt nextLA hLE hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataE _ 1 dt nextLA hLE hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataE _ tgE dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataE _ tgE dt nextLA rfl)

end RoverLadderRung1Guarded

namespace RoverLadderRung3Guarded
open DL DLCalTiming DLRel Parse Set RoverLadderRung3Modal GPins

/-- `refinement_ladder_rover_rung3_6to8`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLR l).next.filterMap (Handoff.leftModeIndex refinement_ladder_rover_rung3_6to8_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataR`, its own guard component
`⊤`), its lowered guard (the file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 8 :=
  LeftAut.ofGI leftDataR ((List.range 3).map (fun l => hostGuard vsR 8 Side.L (mLR l))) tgR dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 8 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsR 8 Side.L (mLR l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsR 8 Side.L (mLR l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsR (mLR l) (by interval_cases l <;> decide)

/-- **`refinement_ladder_rover_rung3_6to8`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_ladder_rung3_6to8_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_ladder_rung3_6to8_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvR)
      (psiK uLA (fun _ => canonInvM gR gsR) (AL dt).numModes domLR domRR
        (mvRegionR mvR gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLR domRR gregion _
    (rover_ladder_rung3_6to8_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gR gsR (by
        intro g' hg'
        simp only [gR, gsR, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gR gsR) hdomLR hdomRR
    (LeftAut.ofGI_vars leftDataR _ 1 dt nextLA hLR hgrdLA).1 (fun t _ => (LeftAut.ofGI_vars leftDataR _ 1 dt nextLA hLR hgrdLA).2 t)
    (LeftAut.ofGI_hnext leftDataR _ tgR dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofGI_hsim_gated leftDataR _ tgR dt nextLA rfl (by intro d hd; simp only [leftDataR, List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl <;> rfl))

end RoverLadderRung3Guarded

namespace RoverLadderRung4Guarded
open DL DLCalTiming DLRel Parse Set RoverLadderRung4Modal GPins

/-- `refinement_ladder_rover_rung4_8to12`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLF l).next.filterMap (Handoff.leftModeIndex refinement_ladder_rover_rung4_8to12_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataF`, its own guard component
`⊤`), its lowered guard (the file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 12 :=
  LeftAut.ofGI leftDataF ((List.range 3).map (fun l => hostGuard vsF 12 Side.L (mLF l))) tgF dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 12 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsF 12 Side.L (mLF l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsF 12 Side.L (mLF l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsF (mLF l) (by interval_cases l <;> decide)

/-- **`refinement_ladder_rover_rung4_8to12`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_ladder_rung4_8to12_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_ladder_rung4_8to12_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvF)
      (psiK uLA (fun _ => canonInvM gF gsF) (AL dt).numModes domLF domRF
        (mvRegionR mvF gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLF domRF gregion _
    (rover_ladder_rung4_8to12_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gF gsF (by
        intro g' hg'
        simp only [gF, gsF, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gF gsF) hdomLF hdomRF
    (LeftAut.ofGI_vars leftDataF _ 1 dt nextLA hLF hgrdLA).1 (fun t _ => (LeftAut.ofGI_vars leftDataF _ 1 dt nextLA hLF hgrdLA).2 t)
    (LeftAut.ofGI_hnext leftDataF _ tgF dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofGI_hsim_gated leftDataF _ tgF dt nextLA rfl (by intro d hd; simp only [leftDataF, List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl <;> rfl))

end RoverLadderRung4Guarded

namespace RoverDofTerrainRung1Guarded
open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung1Modal GPins

/-- `rover_dof_terrain_rung1`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLE l).next.filterMap (Handoff.leftModeIndex rover_dof_terrain_rung1_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataE`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 3 :=
  LeftAut.ofP leftDataE ((List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l))) tgE dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 3 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsE 3 Side.L (mLE l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsE (mLE l) (by interval_cases l <;> decide)

/-- **`rover_dof_terrain_rung1`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_dof_terrain_rung1_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_dof_terrain_rung1_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvE)
      (psiK uLA (fun _ => canonInvM gE gsE) (AL dt).numModes domLE domRE
        (mvRegionR mvE gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLE domRE gregion _
    (rover_dof_terrain_rung1_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gE gsE (by
        intro g' hg'
        simp only [gE, gsE, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gE gsE) hdomLE hdomRE
    (LeftAut.ofP_vars leftDataE _ 1 dt nextLA hLE hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataE _ 1 dt nextLA hLE hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataE _ tgE dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataE _ tgE dt nextLA rfl)

end RoverDofTerrainRung1Guarded

namespace RoverDofTerrainRung2Guarded
open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung2Modal GPins

/-- `rover_dof_terrain_rung2`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLT l).next.filterMap (Handoff.leftModeIndex rover_dof_terrain_rung2_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataT`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 6 :=
  LeftAut.ofP leftDataT ((List.range 3).map (fun l => hostGuard vsT 6 Side.L (mLT l))) tgT dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsT 6 Side.L (mLT l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsT 6 Side.L (mLT l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsT (mLT l) (by interval_cases l <;> decide)

/-- **`rover_dof_terrain_rung2`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_dof_terrain_rung2_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_dof_terrain_rung2_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvT)
      (psiK uLA (fun _ => canonInvM gT gsT) (AL dt).numModes domLT domRT
        (mvRegionR mvT gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLT domRT gregion _
    (rover_dof_terrain_rung2_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gT gsT (by
        intro g' hg'
        simp only [gT, gsT, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gT gsT) hdomLT hdomRT
    (LeftAut.ofP_vars leftDataT _ 1 dt nextLA hLT hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataT _ 1 dt nextLA hLT hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataT _ tgT dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataT _ tgT dt nextLA rfl)

end RoverDofTerrainRung2Guarded

namespace RoverDofTerrainRung3Guarded
open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung3Modal GPins

/-- `rover_dof_terrain_rung3`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLW l).next.filterMap (Handoff.leftModeIndex rover_dof_terrain_rung3_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataW`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 12 :=
  LeftAut.ofP leftDataW ((List.range 3).map (fun l => hostGuard vsW 12 Side.L (mLW l))) tgW dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 12 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsW 12 Side.L (mLW l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsW 12 Side.L (mLW l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsW (mLW l) (by interval_cases l <;> decide)

/-- **`rover_dof_terrain_rung3`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_dof_terrain_rung3_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_dof_terrain_rung3_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvW)
      (psiK uLA (fun _ => canonInvM gW gsW) (AL dt).numModes domLW domRW
        (mvRegionR mvW gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLW domRW gregion _
    (rover_dof_terrain_rung3_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gW gsW (by
        intro g' hg'
        simp only [gW, gsW, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gW gsW) hdomLW hdomRW
    (LeftAut.ofP_vars leftDataW _ 1 dt nextLA hLW hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataW _ 1 dt nextLA hLW hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataW _ tgW dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataW _ tgW dt nextLA rfl)

end RoverDofTerrainRung3Guarded

namespace RoverDofTerrainRung38dGuarded
open DL DLCalTiming DLRel Parse Set RoverDofTerrainRung38dModal GPins

/-- `rover_dof_terrain_rung3_8d`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLU l).next.filterMap (Handoff.leftModeIndex rover_dof_terrain_rung3_8d_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataU`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 8 :=
  LeftAut.ofP leftDataU ((List.range 3).map (fun l => hostGuard vsU 8 Side.L (mLU l))) tgU dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 8 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsU 8 Side.L (mLU l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsU 8 Side.L (mLU l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsU (mLU l) (by interval_cases l <;> decide)

/-- **`rover_dof_terrain_rung3_8d`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_dof_terrain_rung3_8d_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_dof_terrain_rung3_8d_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvU)
      (psiK uLA (fun _ => canonInvM gU gsU) (AL dt).numModes domLU domRU
        (mvRegionR mvU gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLU domRU gregion _
    (rover_dof_terrain_rung3_8d_guarded dt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gU gsU (by
        intro g' hg'
        simp only [gU, gsU, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gU gsU) hdomLU hdomRU
    (LeftAut.ofP_vars leftDataU _ 1 dt nextLA hLU hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataU _ 1 dt nextLA hLU hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataU _ tgU dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataU _ tgU dt nextLA rfl)

end RoverDofTerrainRung38dGuarded

namespace RoverRung26dofGuarded
open DL DLCalTiming DLRel Parse Set RoverRung26dofModal GPins

/-- `refinement_ladder_rover_rung2_6dof`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLQ2 l).next.filterMap (Handoff.leftModeIndex refinement_ladder_rover_rung2_6dof_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataQ2`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 4 :=
  LeftAut.ofP leftDataQ2 ((List.range 3).map (fun l => hostGuard vsQ2 4 Side.L (mLQ2 l))) tgQ2 dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 4 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsQ2 4 Side.L (mLQ2 l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsQ2 4 Side.L (mLQ2 l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsQ2 (mLQ2 l) (by interval_cases l <;> decide)

/-- **`refinement_ladder_rover_rung2_6dof`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rung2_6dof_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rung2_6dof_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d20 : VerdD 2 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvQ2)
      (psiK uLA (fun _ => canonInvM gQ2 gsQ2) (AL dt).numModes domLQ2 domRQ2
        (mvRegionR mvQ2 gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLQ2 domRQ2 gregion _
    (rung2_6dof_guarded dt h00 h01 h02 h11 h12 h22 d10 d20 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gQ2 gsQ2 (by
        intro g' hg'
        simp only [gQ2, gsQ2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gQ2 gsQ2) hdomLQ2 hdomRQ2
    (LeftAut.ofP_vars leftDataQ2 _ 1 dt nextLA hLQ2 hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataQ2 _ 1 dt nextLA hLQ2 hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataQ2 _ tgQ2 dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataQ2 _ tgQ2 dt nextLA rfl)

end RoverRung26dofGuarded

namespace RoverRung2b6dofGuarded
open DL DLCalTiming DLRel Parse Set RoverRung2b6dofModal GPins

/-- `refinement_ladder_rover_rung2b_6dof`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLB2 l).next.filterMap (Handoff.leftModeIndex refinement_ladder_rover_rung2b_6dof_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataB2`), its lowered guard (the
file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 6 :=
  LeftAut.ofP leftDataB2 ((List.range 3).map (fun l => hostGuard vsB2 6 Side.L (mLB2 l))) tgB2 dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsB2 6 Side.L (mLB2 l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsB2 6 Side.L (mLB2 l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsB2 (mLB2 l) (by interval_cases l <;> decide)

/-- **`refinement_ladder_rover_rung2b_6dof`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rung2b_6dof_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rung2b_6dof_leftAut (dt : ℝ)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d20 : VerdD 2 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvB2)
      (psiK uLA (fun _ => canonInvM gB2 gsB2) (AL dt).numModes domLB2 domRB2
        (mvRegionR mvB2 gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLB2 domRB2 gregion _
    (rung2b_6dof_guarded dt h00 h01 h02 h11 h12 h22 d10 d20 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gB2 gsB2 (by
        intro g' hg'
        simp only [gB2, gsB2, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl <;> exact hgAt _))
      (canonInvM_varsR gB2 gsB2) hdomLB2 hdomRB2
    (LeftAut.ofP_vars leftDataB2 _ 1 dt nextLA hLB2 hgrdLA).1 (fun t _ => (LeftAut.ofP_vars leftDataB2 _ 1 dt nextLA hLB2 hgrdLA).2 t)
    (LeftAut.ofP_hnext leftDataB2 _ tgB2 dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofP_hsim_gated leftDataB2 _ tgB2 dt nextLA rfl)

end RoverRung2b6dofGuarded

namespace RoverRung2cGuarded
open DL DLCalTiming DLRel Parse Set RoverRung2cModal GPins

/-- `refinement_ladder_rover_rung2c_6dof`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mL6 l).next.filterMap (Handoff.leftModeIndex refinement_ladder_rover_rung2c_6dof_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftData6`, its own guard test
first), its lowered guard, its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 6 := LeftAut.ofG leftData6 tg6 dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 6 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vs6 6 Side.L (mL6 l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

/-- **`refinement_ladder_rover_rung2c_6dof`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `rover_rung2c_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem rover_rung2c_leftAut (dt : ℝ) (hdt : 0 ≤ dt) (hdt1 : dt ≤ 1)
    (hv0 : VerdR6 0) (hv1 : VerdR6 1) (hv2 : VerdR6 2) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mv6)
      (psiK uLA (fun _ => canonInvM g6 gs6) (AL dt).numModes domL6 domR6
        (mvRegionR mv6 gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domL6 domR6 gregion _
    (rover_rung2c_guarded dt hdt hdt1 hv0 hv1 hv2)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL g6 gs6 (by
        intro g' hg'
        simp only [g6, gs6, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR g6 gs6) hdomL6 hdomR6
    (LeftAut.ofG_vars leftData6 1 dt nextLA hL6).1 (LeftAut.ofG_vars leftData6 1 dt nextLA hL6).2
    (LeftAut.ofG_hnext leftData6 tg6 dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (LeftAut.ofG_hsim leftData6 tg6 dt nextLA)

end RoverRung2cGuarded

namespace Story3RolloverBaseGuarded
open DL DLCalTiming DLRel Parse Set Story3RolloverBaseModal GPins

/-- `story3_rollover_base_12dof`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLB l).next.filterMap (Handoff.leftModeIndex story3_rollover_base_12dof_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataB`, its own guard component
`⊤`), its lowered guard (the file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 12 :=
  LeftAut.ofGI leftDataB ((List.range 3).map (fun l => hostGuard vsB 12 Side.L (mLB l))) tgB dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 12 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsB 12 Side.L (mLB l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsB 12 Side.L (mLB l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsB (mLB l) (by interval_cases l <;> decide)

/-- **`story3_rollover_base_12dof`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `story3_rollover_base_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem story3_rollover_base_leftAut (dt : ℝ) (hdt : 0 ≤ dt)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvB)
      (psiK uLA (fun _ => canonInvM gB gsB) (AL dt).numModes domLB domRB
        (mvRegionR mvB gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLB domRB gregion _
    (story3_rollover_base_guarded dt hdt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gB gsB (by
        intro g' hg'
        simp only [gB, gsB, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gB gsB) hdomLB hdomRB
    (LeftAut.ofGI_vars leftDataB _ 1 dt nextLA hLB hgrdLA).1 (fun t _ => (LeftAut.ofGI_vars leftDataB _ 1 dt nextLA hLB hgrdLA).2 t)
    (LeftAut.ofGI_hnext leftDataB _ tgB dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofGI_hsim_gated leftDataB _ tgB dt nextLA rfl (by intro d hd; simp only [leftDataB, List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl <;> rfl))

end Story3RolloverBaseGuarded

namespace Story3RolloverRungAGuarded
open DL DLCalTiming DLRel Parse Set Story3RolloverRungAModal GPins

/-- `story3_rollover_ladder_rung_a`: the file's left `next` lists, resolved to indices (STEEP, MODER, FLAT). -/
def nextLA : List (List ℕ) :=
  (List.range 3).map (fun l => (mLA l).next.filterMap (Handoff.leftModeIndex story3_rollover_ladder_rung_a_IR))

theorem nextLA_eq : nextLA = [[1, 0], [2, 1], [2]] := by decide

/-- The guard-gated left automaton: mode `l`'s window (`leftDataA`, its own guard component
`⊤`), its lowered guard (the file's, tested by the left edge), its declared successors. -/
noncomputable def AL (dt : ℝ) : LeftAut 12 :=
  LeftAut.ofGI leftDataA ((List.range 3).map (fun l => hostGuard vsA 12 Side.L (mLA l))) tgA dt nextLA

/-- The left mode variable (the left execution's auxiliary slot 2). -/
abbrev uLA : Var 12 := (Side.Aux, 2)

theorem AL_guards (dt : ℝ) : (AL dt).guards =
    (List.range 3).map (fun l => hostGuard vsA 12 Side.L (mLA l)) := rfl

theorem AL_numModes (dt : ℝ) : (AL dt).numModes = 3 := rfl

theorem hgrdLA : ∀ g ∈ (List.range 3).map (fun l => hostGuard vsA 12 Side.L (mLA l)),
    g.fv ⊆ range Lv := by
  intro g hg
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hg
  rw [List.mem_range] at hl
  exact hostGuard_fv_L vsA (mLA l) (by interval_cases l <;> decide)

/-- **`story3_rollover_ladder_rung_a`, Theorem 3 with the paper's left program**: the guard-gated left automaton
(jump, then flow) against the guarded right automaton, the declared rows for every left mode,
the right in its current mode's guard and cuts. From `story3_rollover_rung_a_guarded` by the generic bridge
`theorem3_leftAut_of_choiceR`. -/
theorem story3_rollover_rung_a_leftAut (dt : ℝ) (hdt : 0 ≤ dt)
    (h00 : Verd 0 0) (h01 : Verd 0 1) (h02 : Verd 0 2) (h11 : Verd 1 1) (h12 : Verd 1 2)
    (h22 : Verd 2 2) (d10 : VerdD 1 0) (d21 : VerdD 2 1) :
    RFormula.rvalid (theorem3Form (leftAutomatonBody (AL dt) uLA) (rightAutomatonBody GrG mvA)
      (psiK uLA (fun _ => canonInvM gA gsA) (AL dt).numModes domLA domRA
        (mvRegionR mvA gregion GrG.modes.length))) :=
  theorem3_leftAut_of_choiceR (AL dt) 0 1 2 (by decide) _ _ _ domLA domRA gregion _
    (story3_rollover_rung_a_guarded dt hdt h00 h01 h02 h11 h12 h22 d10 d21)
    (fun q _ => gregion_fv q)
      (canonInvM_varsL gA gsA (by
        intro g' hg'
        simp only [gA, gsA, List.mem_cons, List.not_mem_nil, or_false] at hg'
        rcases hg' with rfl | rfl | rfl <;> exact hgAt _))
      (canonInvM_varsR gA gsA) hdomLA hdomRA
    (LeftAut.ofGI_vars leftDataA _ 1 dt nextLA hLA hgrdLA).1 (fun t _ => (LeftAut.ofGI_vars leftDataA _ 1 dt nextLA hLA hgrdLA).2 t)
    (LeftAut.ofGI_hnext leftDataA _ tgA dt nextLA 3 rfl (by rw [nextLA_eq]; decide))
    (ofGI_hsim_gated leftDataA _ tgA dt nextLA rfl (by intro d hd; simp only [leftDataA, List.mem_cons, List.not_mem_nil, or_false] at hd; rcases hd with rfl | rfl | rfl <;> rfl))

end Story3RolloverRungAGuarded

end RelCertifier
