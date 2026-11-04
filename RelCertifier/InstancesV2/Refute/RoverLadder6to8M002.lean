/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_6to8_m002`: Theorem 3's claim of a mutant of `rover_ladder_6to8` is false (GENERATED — `scripts/gen_refute.py`)

Mutant ORO `(and (and (<= L_v R_v) (<= L_s R_s)) (and (and (<= L_psi 0.35) (<= (- 0 0.35) L_psi)) (and (<= L_omega_psi 0.35) (<= (- 0 0.35) L_omega_psi))) (and (and (<= L_theta_p 0.25) (<= (- 0 0.25) L_theta_p)) (and (<= L_omega_theta 0.25) (<= (- 0 0.25) L_omega_theta))) (and (<= L_phi_r 0.2) (<= (- 0 0.2) L_phi_r)) (and (<= (+ (* 0.101937 (* L_v (- L_omega_psi L_psi))) L_phi_r) 0.8) (<= (- 0 0.8) (+ (* 0.101937 (* L_v (- L_omega_psi L_psi))) L_phi_r))) (and (and (<= R_psi 0.35) (<= (- 0 0.35) R_psi)) (and (<= R_theta_p 0.25) (<= (- 0 0.25) R_theta_p)) (and (<= R_phi_r 0.2) (<= (- 0 0.2) R_phi_r)))) [L_omega_theta->R_omega_theta]`. Kind B (a component pushed out by the left flow, right-rigid): the left takes the window of mode 0 with a short flow, the right starts in mode 0. Dimension 9: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.rover_ladder_6to8_m002
import RelCertifier.InstancesV2.Cuts.rover_ladder_6to8

namespace RelCertifier.Refute.RoverLadder6to8M002

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.rover_ladder_6to8_m002_IRm
abbrev cX := Oracle.rover_ladder_6to8_cutsV2X
abbrev w := Refute.rover_ladder_6to8_m002_wit

/-- The mutant changes only the invariant: the model, hence its mode-fact certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.rover_ladder_6to8_IRv2.L ∧ IR.R = Parse.rover_ladder_6to8_IRv2.R := ⟨rfl, rfl⟩

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

/-- **The claim of `rover_ladder_6to8_m002` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 9 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ windowClaim IR 9 cX cov Formula.tt 0 1 2 dt :=
  refute_window_B_clocked pre_ok b_ok (by decide) hv window_form names_ok cuts_ok (by decide) 2
    (by decide) dt hdt cov

end RelCertifier.Refute.RoverLadder6to8M002
