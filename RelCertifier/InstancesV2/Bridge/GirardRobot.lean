/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `girard_robot` (suite_v2) through the generic bridge (GENERATED — `scripts/gen_bridge.py girard_robot`)

Theorem 3 of the benchmark from its emitted records: the structural bundles decided in the
kernel (`struct_ok`, `prog_ok`, `covers_ok`, `rows_same`, `pad_ok`), Assumption 1 transported
from the suite's lemma at dimension 6 and lifted to 7 (the right clock), the verdicts
assumed (`Verdicts`: the groups `relcert-bridge-verdicts` discharges,
`Emitted.verdicts_of_groups`).
-/
import RelCertifier.Proofs.Encoding.Emitted.Window
import RelCertifier.Proofs.Encoding.Emitted.Transport
import RelCertifier.Proofs.Encoding.Emitted.Lift
import RelCertifier.InstancesV2.WellFormed.GirardRobot
import RelCertifier.InstancesV2.Cuts.girard_robot
import RelCertifier.InstancesV2.BenchCovers.girard_robot
import RelCertifier.InstancesV2.BenchProgress.girard_robot
import RelCertifier.InstancesV2.BenchChoice.girard_robot

namespace RelCertifier.Bridge.GirardRobot

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL Set

abbrev IR := Parse.girard_robot_IRv2
abbrev cX := Oracle.girard_robot_cutsV2X
abbrev cov := girard_robot_coverV2
abbrev prog := Progress.girard_robot_coverV2_progress
abbrev ce := Choice.girard_robot_coverV2_choice

theorem struct_ok : structOK IR 7 cov cX = true := by decide +kernel
theorem prog_ok : progOK IR 7 cov prog = true := by decide +kernel
theorem covers_ok : coversOK IR 7 cov ce = true := by decide +kernel
theorem pad_ok : padOK IR 6 = true := by decide +kernel
theorem rows_same : rowsSame IR = true := by decide +kernel
/-- Assumption 1 holds unconditionally: the region is `⊤`. -/
abbrev reg : Formula (Var 7) := Formula.tt
theorem reg_fv : reg.fv ⊆ range Rv := fun _ h => by simp [Formula.fv] at h
theorem reg_inv : RegionInvariant (grOf IR 7 (prunedOf cov)) reg := fun _ _ _ _ _ _ _ _ => trivial

/-- Assumption 1, proved directly over the bridge's automaton at dimension 6
(`V2GirardRobot.girard_robot_wellFormedR_direct`), lifted to 7. -/
theorem wellFormedR : WellFormedRIn (grOf IR 7 (prunedOf cov)) (guardR IR 7) reg (epsR IR) :=
  WellFormedRIn.of_tt (wellFormedR_lift (n := 6) pad_ok
    (V2GirardRobot.girard_robot_wellFormedR_direct (prunedOf cov))) reg

/-- **Theorem 3 of `girard_robot`** (window form): every verdict group of the benchmark `unsat`. -/
theorem girard_robot_bridge (hv : Verdicts IR 7 cX cov prog ce) (dt : ℝ) (hdt : dt ≤ epsL IR) :
    windowClaim IR 7 cX cov reg 0 1 2 dt :=
  theorem3_window_of_records struct_ok hv prog_ok covers_ok reg_fv reg_inv wellFormedR
    rows_same 0 1 2 (by decide) (by decide) (by decide) dt hdt

end RelCertifier.Bridge.GirardRobot
