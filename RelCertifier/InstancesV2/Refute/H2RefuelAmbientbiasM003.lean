/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `h2_refuel_ambientbias_m003`: Theorem 3's claim of a mutant of `h2_refuel_ambientbias` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_p (+ R_p 2.9)) [<=->>=]`. Kind C (no partner): the left switches
from mode 2 to mode 3 with a zero-duration flow, the right starts in mode 3. Dimension 4: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.h2_refuel_ambientbias_m003
import RelCertifier.InstancesV2.Cuts.h2_refuel_ambientbias

namespace RelCertifier.Refute.H2RefuelAmbientbiasM003

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.h2_refuel_ambientbias_m003_IRm
abbrev cX := Oracle.h2_refuel_ambientbias_cutsV2X
abbrev w := Refute.h2_refuel_ambientbias_m003_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.h2_refuel_ambientbias_IRv2.L ∧ IR.R = Parse.h2_refuel_ambientbias_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 4 cX 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 4 cX = true := by decide +kernel

/-- **The claim of `h2_refuel_ambientbias_m003` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 4 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 4 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_C_clocked pre_ok rfl hv names_ok cuts_ok (by decide) (by decide) 3 (by decide)
    dt hdt cov

end RelCertifier.Refute.H2RefuelAmbientbiasM003
