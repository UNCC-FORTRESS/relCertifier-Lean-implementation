/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_refinement` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_refinement` (cut-free emission). -/
def arm_refinement_coverNC : CoverEmitE :=
  ⟨"arm_refinement", [], [
    ⟨"Accelerate", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩,
    ⟨"Brake", (5 : ℚ) / 1, 5, [⟨"Approach", true, false, false, true, true⟩, ⟨"Return", false, true, true, false, false⟩], ["Approach", "Return"], [⟨"Approach", [0], [0], [0]⟩, ⟨"Return", [], [], []⟩]⟩]⟩

end RelCertifier
