/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine_m009`: Theorem 3's claim of a mutant of `rover_patrol_refine` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_s (+ R_s 1.0)) [<=->>=]`. Kind A (a component broken at the switch, right-rigid): the left switches
from mode 0 to mode 1 with a zero-duration flow, the right starts in mode 0.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.rover_patrol_refine_m009
import RelCertifier.InstancesV2.Cuts.rover_patrol_refine

namespace RelCertifier.Refute.RoverPatrolRefineM009

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.rover_patrol_refine_m009_IRm
abbrev cX := Oracle.rover_patrol_refine_cutsV2X
abbrev w := Refute.rover_patrol_refine_m009_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.rover_patrol_refine_IRv2.L ∧ IR.R = Parse.rover_patrol_refine_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 3 cX 0 1 2 w = true := by decide +kernel

/-- The broken component, decided in the kernel. -/
theorem pos_ok : compPosQ IR 3 (rowOf IR w.m) w.k (witState 3 0 2 w) = true := by
  decide +kernel

/-- **The claim of `rover_patrol_refine_m009` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 3 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 3 cX cov Formula.tt 0 1 2 dt :=
  refute_keyed_A pre_ok (by decide) pos_ok hv (by decide) (by decide) dt hdt cov

end RelCertifier.Refute.RoverPatrolRefineM009
