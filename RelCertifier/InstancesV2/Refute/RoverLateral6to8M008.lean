/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_lateral_6to8_m008`: Theorem 3's claim of a mutant of `rover_lateral_6to8` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(<= (+ L_y L_w) (+ R_y 0.5)) [<=->>=]`. Kind B (a component pushed out by the left flow, right-rigid): the left takes the window of mode 0 with a short flow, the right starts in mode 0. Dimension 9: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.rover_lateral_6to8_m008
import RelCertifier.InstancesV2.Cuts.rover_lateral_6to8

namespace RelCertifier.Refute.RoverLateral6to8M008

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.rover_lateral_6to8_m008_IRm
abbrev cX := Oracle.rover_lateral_6to8_cutsV2X
abbrev w := Refute.rover_lateral_6to8_m008_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.rover_lateral_6to8_IRv2.L ∧ IR.R = Parse.rover_lateral_6to8_IRv2.R := ⟨rfl, rfl⟩

/-- Every left mode declares the same row: the claim is the window form. -/
theorem window_form : rowsSame IR = true := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOKW IR 9 cX 0 1 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQW IR 9 0 1 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 9 cX = true := by decide +kernel

/-- **The claim of `rover_lateral_6to8_m008` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 9 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ windowClaim IR 9 cX cov Formula.tt 0 1 2 dt :=
  refute_window_B_clocked pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) 2
    (by decide) dt hdt cov

end RelCertifier.Refute.RoverLateral6to8M008
