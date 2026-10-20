/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_weak_m003`: Theorem 3's claim of a mutant of `sat_detumble_weak` is false (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= (+ (+ (* (* L_w1 L_w1) 2.0) (* (* L_w2 L_w2) 4.0)) (* (* L_w3 L_w3) 5.0)) (+ (+ (+ (* (* R_w1 R_w1) 2.0) (* (* R_w2 R_w2) 4.0)) (* (* R_w3 R_w3) 5.0)) 0.205)) [L_w2->R_w2]`. Kind B (a component pushed out by the left flow, right-rigid): the left takes the window of mode 0 with a short flow, the right starts in mode 0.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_weak_m003
import RelCertifier.InstancesV2.Cuts.sat_detumble_weak

namespace RelCertifier.Refute.SatDetumbleWeakM003

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.sat_detumble_weak_m003_IRm
abbrev cX := Oracle.sat_detumble_weak_cutsV2X
abbrev w := Refute.sat_detumble_weak_m003_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.sat_detumble_weak_IRv2.L ∧ IR.R = Parse.sat_detumble_weak_IRv2.R := ⟨rfl, rfl⟩

/-- Every left mode declares the same row: the claim is the window form. -/
theorem window_form : rowsSame IR = true := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOKW IR 4 cX 0 1 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQW IR 4 0 1 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates. -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 4 cX = true := by decide +kernel

/-- **The claim of `sat_detumble_weak_m003` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 4 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ windowClaim IR 4 cX cov Formula.tt 0 1 dt :=
  refute_window_B pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) dt hdt cov

end RelCertifier.Refute.SatDetumbleWeakM003
