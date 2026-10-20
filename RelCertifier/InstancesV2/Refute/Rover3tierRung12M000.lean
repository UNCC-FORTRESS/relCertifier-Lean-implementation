/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12_m000`: Theorem 3's claim of a mutant of `rover3tier_rung12` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_v (+ R_v 0.5)) [<=->>=]`. Kind C (no partner): the left switches
from mode 1 to mode 0 with a zero-duration flow, the right starts in mode 0.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.rover3tier_rung12_m000
import RelCertifier.InstancesV2.Cuts.rover3tier_rung12

namespace RelCertifier.Refute.Rover3tierRung12M000

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.rover3tier_rung12_m000_IRm
abbrev cX := Oracle.rover3tier_rung12_cutsV2X
abbrev w := Refute.rover3tier_rung12_m000_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.rover3tier_rung12_IRv2.L ∧ IR.R = Parse.rover3tier_rung12_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 3 cX 0 1 2 w = true := by decide +kernel

/-- **The claim of `rover3tier_rung12_m000` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 3 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 3 cX cov Formula.tt 0 1 2 dt :=
  refute_keyed_C pre_ok rfl hv (by decide) (by decide) dt hdt cov

end RelCertifier.Refute.Rover3tierRung12M000
