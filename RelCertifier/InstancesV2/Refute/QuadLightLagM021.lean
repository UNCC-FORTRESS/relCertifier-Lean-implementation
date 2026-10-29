/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_lag_m021`: Theorem 3's claim of a mutant of `quad_light_lag` is false (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= (* (- 6.13125) 0.45) (- (+ (* 6.13125 (- L_h R_h)) L_w (* 0.1 L_a)) (+ (* 1.25 R_w) (* 0.125 R_a) 0.14525))) [R_a->L_a]`. Kind B (a component pushed out by the left flow, right-rigid): the left takes the window of mode 0 with a short flow, the right starts in mode 0. Dimension 4: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.quad_light_lag_m021
import RelCertifier.InstancesV2.Cuts.quad_light_lag

namespace RelCertifier.Refute.QuadLightLagM021

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.quad_light_lag_m021_IRm
abbrev cX := Oracle.quad_light_lag_cutsV2X
abbrev w := Refute.quad_light_lag_m021_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.quad_light_lag_IRv2.L ∧ IR.R = Parse.quad_light_lag_IRv2.R := ⟨rfl, rfl⟩

/-- Every left mode declares the same row: the claim is the window form. -/
theorem window_form : rowsSame IR = true := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOKW IR 4 cX 0 1 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQW IR 4 0 1 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 4 cX = true := by decide +kernel

/-- **The claim of `quad_light_lag_m021` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 4 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ windowClaim IR 4 cX cov Formula.tt 0 1 2 dt :=
  refute_window_B_clocked pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) 2
    (by decide) dt hdt cov

end RelCertifier.Refute.QuadLightLagM021
