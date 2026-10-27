/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_8to12_m009`: Theorem 3's claim of a mutant of `rover_ladder_8to12` is false (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(and (and (<= L_phi_r 0.2) (<= (- 0 0.2) L_phi_r)) (and (<= L_omega_phi 0.2) (<= (- 0 0.2) L_omega_phi))) [L_omega_phi->R_omega_phi]`. Kind B (a component pushed out by the left flow, right-rigid): the left takes the window of mode 0 with a short flow, the right starts in mode 0. Dimension 13: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_8to12_m009
import RelCertifier.InstancesV2.Cuts.rover_ladder_8to12

namespace RelCertifier.Refute.RoverLadder8to12M009

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.rover_ladder_8to12_m009_IRm
abbrev cX := Oracle.rover_ladder_8to12_cutsV2X
abbrev w := Refute.rover_ladder_8to12_m009_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.rover_ladder_8to12_IRv2.L ∧ IR.R = Parse.rover_ladder_8to12_IRv2.R := ⟨rfl, rfl⟩

/-- Every left mode declares the same row: the claim is the window form. -/
theorem window_form : rowsSame IR = true := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOKW IR 13 cX 0 1 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQW IR 13 0 1 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 13 cX = true := by decide +kernel

/-- **The claim of `rover_ladder_8to12_m009` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 13 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ windowClaim IR 13 cX cov Formula.tt 0 1 2 dt :=
  refute_window_B_clocked pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) 2
    (by decide) dt hdt cov

end RelCertifier.Refute.RoverLadder8to12M009
