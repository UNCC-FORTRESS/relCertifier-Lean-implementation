/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung3_6to8_m013`: Theorem 3's claim of a mutant of `refinement_ladder_rover_rung3_6to8` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (* R_theta_p R_theta_p) (+ (* L_theta_p L_theta_p) (* (* 3.0 (- L_omega_theta L_theta_p)) (- L_omega_theta L_theta_p)))) [<=->>=]`. Kind B (a component pushed out by the left flow, right-rigid): the left takes the window of mode 0 with a short flow, the right starts in mode 0.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.refinement_ladder_rover_rung3_6to8_m013
import RelCertifier.InstancesV2.Cuts.refinement_ladder_rover_rung3_6to8

namespace RelCertifier.Refute.RefinementLadderRoverRung36to8M013

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.refinement_ladder_rover_rung3_6to8_m013_IRm
abbrev cX := Oracle.refinement_ladder_rover_rung3_6to8_cutsV2X
abbrev w := Refute.refinement_ladder_rover_rung3_6to8_m013_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.refinement_ladder_rover_rung3_6to8_IRv2.L ∧ IR.R = Parse.refinement_ladder_rover_rung3_6to8_IRv2.R := ⟨rfl, rfl⟩

/-- Every left mode declares the same row: the claim is the window form. -/
theorem window_form : rowsSame IR = true := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOKW IR 8 cX 0 1 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQW IR 8 0 1 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates. -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 8 cX = true := by decide +kernel

/-- **The claim of `refinement_ladder_rover_rung3_6to8_m013` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 8 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ windowClaim IR 8 cX cov Formula.tt 0 1 dt :=
  refute_window_B pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) dt hdt cov

end RelCertifier.Refute.RefinementLadderRoverRung36to8M013
