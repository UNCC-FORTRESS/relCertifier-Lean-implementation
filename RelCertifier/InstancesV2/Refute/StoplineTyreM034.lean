/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_tyre_m034`: Theorem 3's claim of a mutant of `stopline_tyre` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(>= R_p 100.0) [>=-><=]`. Kind C (no partner): the left switches
from mode 0 to mode 1 with a zero-duration flow, the right starts in mode 1. Dimension 5: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.stopline_tyre_m034
import RelCertifier.InstancesV2.Cuts.stopline_tyre

namespace RelCertifier.Refute.StoplineTyreM034

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.stopline_tyre_m034_IRm
abbrev cX := Oracle.stopline_tyre_cutsV2X
abbrev w := Refute.stopline_tyre_m034_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.stopline_tyre_IRv2.L ∧ IR.R = Parse.stopline_tyre_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 5 cX 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 5 cX = true := by decide +kernel

/-- **The claim of `stopline_tyre_m034` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 5 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 5 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_C_clocked pre_ok rfl hv names_ok cuts_ok (by decide) (by decide) 3 (by decide)
    dt hdt cov

end RelCertifier.Refute.StoplineTyreM034
