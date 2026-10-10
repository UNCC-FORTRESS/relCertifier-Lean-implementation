/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_fidelity_mid` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_fidelity_mid` (emitted). -/
def arm_fidelity_mid_cover : CoverEmitE :=
  ⟨"arm_fidelity_mid", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, true, true⟩, ⟨"ApproachSlow", false, true, true⟩, ⟨"Hold", true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [], [0], [0]⟩, ⟨"Hold", [0], [], []⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachFast", true, true, true⟩, ⟨"ApproachSlow", false, true, true⟩, ⟨"Hold", true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [], [0], [0]⟩, ⟨"Hold", [0], [], []⟩]⟩]⟩

end RelCertifier
