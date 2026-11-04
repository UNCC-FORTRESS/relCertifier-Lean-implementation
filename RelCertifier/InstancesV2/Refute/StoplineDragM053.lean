/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag_m053`: Theorem 3's claim of a mutant of `stopline_drag` is false (GENERATED — `scripts/gen_refute.py`)

Mutant MCO `(<= L_phi_r 0.2) [del]`. Kind B (a component pushed out by the left flow, right-rigid): the left switches
from mode 1 to mode 1 with a short flow, the right starts in mode 1. Dimension 16: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.stopline_drag_m053
import RelCertifier.InstancesV2.Cuts.stopline_drag

namespace RelCertifier.Refute.StoplineDragM053

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.stopline_drag_m053_IRm
abbrev cX := Oracle.stopline_drag_cutsV2X
abbrev w := Refute.stopline_drag_m053_wit

/-- The mutant changes only the invariant: the model, hence its mode-fact certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.stopline_drag_IRv2.L ∧ IR.R = Parse.stopline_drag_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 16 cX 0 1 2 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQ IR 16 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 16 cX = true := by decide +kernel

/-- **The claim of `stopline_drag_m053` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 16 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 16 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_B_clocked pre_ok b_ok (by decide) hv names_ok cuts_ok (by decide) (by decide) 3
    (by decide) dt hdt cov

end RelCertifier.Refute.StoplineDragM053
