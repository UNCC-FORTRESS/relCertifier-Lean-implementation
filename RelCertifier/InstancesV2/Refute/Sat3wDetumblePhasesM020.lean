/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_phases_m020`: Theorem 3's claim of a mutant of `sat3w_detumble_phases` is false (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= (+ (+ (* (* L_w1 L_w1) 2.0) (* (* L_w2 L_w2) 4.0)) (* (* L_w3 L_w3) 5.0)) (+ (+ (+ (* (* R_w1 R_w1) 2.0) (* (* R_w2 R_w2) 4.0)) (* (* R_w3 R_w3) 5.0)) 0.08)) [L_w3->R_w3]`. Kind B (a component pushed out by the left flow, right-rigid): the left switches
from mode 1 to mode 1 with a short flow, the right starts in mode 0.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.sat3w_detumble_phases_m020
import RelCertifier.InstancesV2.Cuts.sat3w_detumble_phases

namespace RelCertifier.Refute.Sat3wDetumblePhasesM020

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.sat3w_detumble_phases_m020_IRm
abbrev cX := Oracle.sat3w_detumble_phases_cutsV2X
abbrev w := Refute.sat3w_detumble_phases_m020_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.sat3w_detumble_phases_IRv2.L ∧ IR.R = Parse.sat3w_detumble_phases_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 6 cX 0 1 2 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQ IR 6 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates. -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 6 cX = true := by decide +kernel

/-- **The claim of `sat3w_detumble_phases_m020` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 6 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 6 cX cov Formula.tt 0 1 2 dt :=
  refute_keyed_B pre_ok b_ok (by decide) hv names_ok cuts_ok (by decide) (by decide) dt hdt cov

end RelCertifier.Refute.Sat3wDetumblePhasesM020
