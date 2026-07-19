/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_fidelity_mid` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_fidelity_mid` (cut-free emission). -/
def arm_fidelity_mid_coverNC : CoverEmitE :=
  ⟨"arm_fidelity_mid", [], [
    ⟨"Accelerate", (9 : ℚ) / 2, 5, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Hold", [0], [], []⟩]⟩,
    ⟨"Brake", (9 : ℚ) / 2, 5, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, false, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Hold", [0], [], []⟩]⟩]⟩

end RelCertifier
