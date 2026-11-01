/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_lag_m035`: Theorem 3's claim of a mutant of `stopline_lag` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (+ (+ (* 6.0 L_p) (* 1.8 L_v)) (* 1 (* (- L_v (* 0.3 L_b)) (- L_v (* 0.3 L_b))))) (+ (+ (* 6 R_p) (* 1 (* R_v R_v))) 14.4)) [<=->>=]`. Kind C (no partner): the left switches
from mode 0 to mode 1 with a zero-duration flow, the right starts in mode 1. Dimension 6: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.stopline_lag_m035
import RelCertifier.InstancesV2.Cuts.stopline_lag

namespace RelCertifier.Refute.StoplineLagM035

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.stopline_lag_m035_IRm
abbrev cX := Oracle.stopline_lag_cutsV2X
abbrev w := Refute.stopline_lag_m035_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.stopline_lag_IRv2.L ∧ IR.R = Parse.stopline_lag_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 6 cX 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 6 cX = true := by decide +kernel

/-- **The claim of `stopline_lag_m035` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 6 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 6 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_C_clocked pre_ok rfl hv names_ok cuts_ok (by decide) (by decide) 3 (by decide)
    dt hdt cov

end RelCertifier.Refute.StoplineLagM035
