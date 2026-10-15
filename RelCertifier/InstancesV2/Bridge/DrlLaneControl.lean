/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_lane_control` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py drl_lane_control`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`), Assumption 1 transported from the
suite's lemma, the verdicts assumed (`Verdicts`: the groups `relcert-bridge-verdicts`
discharges, `Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.InstancesV2.WellFormed.DrlLaneControl
import RelCertifier.InstancesV2.Cuts.drl_lane_control
import RelCertifier.InstancesV2.BenchCovers.drl_lane_control
import RelCertifier.InstancesV2.BenchProgress.drl_lane_control
import RelCertifier.InstancesV2.BenchChoice.drl_lane_control

namespace RelCertifier.Bridge.DrlLaneControl

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.drl_lane_control_IRv2
abbrev cX := Oracle.drl_lane_control_cutsV2X
abbrev cov := drl_lane_control_coverV2
abbrev prog := Progress.drl_lane_control_coverV2_progress
abbrev ce := Choice.drl_lane_control_coverV2_choice

theorem struct_ok : structOK IR 3 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 3 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 3 cov ce = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 3) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 3 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton (`V2DrlLaneControl.drl_lane_control_wellFormedR_direct`). -/
theorem wellFormedR : WellFormedRIn (grOf IR 3 (prunedOf cov)) (guardR IR 3) reg (epsR IR) :=
  WellFormedRIn.of_tt (V2DrlLaneControl.drl_lane_control_wellFormedR_direct (prunedOf cov)) reg

/-- **Theorem 3 of `drl_lane_control`** (window form): every verdict group of the benchmark `unsat`. -/
theorem drl_lane_control_bridge (hv : Verdicts IR 3 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 3 cX cov reg 0 1 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 (by decide) dt hdt

end RelCertifier.Bridge.DrlLaneControl
