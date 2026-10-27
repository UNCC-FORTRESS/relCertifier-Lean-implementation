/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hydro_rejection_gatecal_m028`: Theorem 3's claim of a mutant of `hydro_rejection_gatecal` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= L_w (+ R_w 0.09)) [<=->>=]`. Kind C (no partner): the left switches
from mode 0 to mode 1 with a zero-duration flow, the right starts in mode 1. Dimension 4: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.hydro_rejection_gatecal_m028
import RelCertifier.InstancesV2.Cuts.hydro_rejection_gatecal

namespace RelCertifier.Refute.HydroRejectionGatecalM028

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.hydro_rejection_gatecal_m028_IRm
abbrev cX := Oracle.hydro_rejection_gatecal_cutsV2X
abbrev w := Refute.hydro_rejection_gatecal_m028_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.hydro_rejection_gatecal_IRv2.L ∧ IR.R = Parse.hydro_rejection_gatecal_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 4 cX 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 4 cX = true := by decide +kernel

/-- **The claim of `hydro_rejection_gatecal_m028` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 4 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 4 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_C_clocked pre_ok rfl hv names_ok cuts_ok (by decide) (by decide) 3 (by decide)
    dt hdt cov

end RelCertifier.Refute.HydroRejectionGatecalM028
