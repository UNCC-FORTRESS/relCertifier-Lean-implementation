/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_phases_m007`: Theorem 3's claim of a mutant of `sat_detumble_phases` is false (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(<= (+ (+ (* (* L_w1 L_w1) 2.0) (* (* L_w2 L_w2) 4.0)) (* (* L_w3 L_w3) 5.0)) (+ (+ (* (* R_w1 R_w1) 2.0) (* (* R_w2 R_w2) 4.0)) (* (* R_w3 R_w3) 5.0))) [R_w3->L_w3]`. Kind A (a component broken at the switch, right-rigid): the left switches
from mode 0 to mode 1 with a zero-duration flow, the right starts in mode 0. Dimension 5: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.sat_detumble_phases_m007
import RelCertifier.InstancesV2.Cuts.sat_detumble_phases

namespace RelCertifier.Refute.SatDetumblePhasesM007

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.sat_detumble_phases_m007_IRm
abbrev cX := Oracle.sat_detumble_phases_cutsV2X
abbrev w := Refute.sat_detumble_phases_m007_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.sat_detumble_phases_IRv2.L ∧ IR.R = Parse.sat_detumble_phases_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 5 cX 0 1 2 w = true := by decide +kernel

/-- The broken component, decided in the kernel. -/
theorem pos_ok : compPosQ IR 5 (rowOf IR w.m) w.k (witState 5 0 2 w) = true := by
  decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 5 cX = true := by decide +kernel

/-- **The claim of `sat_detumble_phases_m007` is false** for every cover record (every pruning), every `dt ≥ 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 5 cX w) (dt : ℝ) (hdt : 0 ≤ dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 5 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_A_clocked pre_ok (by decide) pos_ok hv names_ok cuts_ok (by decide) (by decide) 3
    (by decide) dt hdt cov

end RelCertifier.Refute.SatDetumblePhasesM007
