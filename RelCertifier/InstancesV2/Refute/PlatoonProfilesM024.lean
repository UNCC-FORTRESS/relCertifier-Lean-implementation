/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_profiles_m024`: Theorem 3's claim of a mutant of `platoon_profiles` is false (GENERATED — `scripts/gen_refute.py`)

Mutant RRO/SNO `(>= L_g 5.0) [>=-><=]`. Kind B (a component pushed out by the left flow, right-rigid): the left switches
from mode 0 to mode 0 with a short flow, the right starts in mode 0. Dimension 4: the benchmark's bridge dimension, the last auxiliary coordinate the right clock.
-/
import RelCertifier.Proofs.Encoding.Emitted.RefuteFlow
import RelCertifier.InstancesV2.Refute.Data.platoon_profiles_m024
import RelCertifier.InstancesV2.Cuts.platoon_profiles

namespace RelCertifier.Refute.PlatoonProfilesM024

open RelCertifier RelCertifier.Emitted RelCertifier.Parse RelCertifier.Oracle DL

abbrev IR := Refute.platoon_profiles_m024_IRm
abbrev cX := Oracle.platoon_profiles_cutsV2X
abbrev w := Refute.platoon_profiles_m024_wit

/-- The mutant changes only the invariant: the model, hence its cut certificate, is the suite benchmark's. -/
theorem same_model : IR.L = Parse.platoon_profiles_IRv2.L ∧ IR.R = Parse.platoon_profiles_IRv2.R := ⟨rfl, rfl⟩

/-- The rows differ by mode: the claim is the mode-keyed one. -/
theorem keyed_form : rowsSame IR = false := by decide +kernel

/-- The witness's antecedent facts, decided in the kernel. -/
theorem pre_ok : preOK IR 4 cX 0 1 2 w = true := by decide +kernel

/-- The exit facts (interior of the left envelope, the component's sign and its left Lie
derivative's), decided in the kernel. -/
theorem b_ok : bQ IR 4 0 1 2 w = true := by decide +kernel

/-- The left and right lowerings read only their own side's coordinates (the clock
erasure's hygiene). -/
theorem names_ok : namesOK IR = true := by decide +kernel
theorem cuts_ok : cutsOK IR 4 cX = true := by decide +kernel

/-- **The claim of `platoon_profiles_m024` is false** for every cover record (every pruning), every `dt > 0`:
every query group `relcert-refute-verdicts` sends is `unsat`. -/
theorem refuted (hv : RefVerdicts IR 4 cX w) (dt : ℝ) (hdt : 0 < dt) (cov : CoverEmitE) :
    ¬ keyedClaim IR 4 cX cov Formula.tt 0 1 2 3 dt :=
  refute_keyed_B_clocked pre_ok b_ok (by decide) hv names_ok cuts_ok (by decide) (by decide) 3
    (by decide) dt hdt cov

end RelCertifier.Refute.PlatoonProfilesM024
