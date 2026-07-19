/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_mid` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `plant_fan_mid` (cut-free emission). -/
def plant_fan_mid_coverNC : CoverEmitE :=
  ⟨"plant_fan_mid", [], [
    ⟨"Accelerate", (15 : ℚ) / 4, 4, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, true, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Hold", [0], [], []⟩]⟩,
    ⟨"Brake", (15 : ℚ) / 4, 4, [⟨"ApproachFast", true, false, false, true, true⟩, ⟨"ApproachSlow", true, true, true, true, true⟩, ⟨"Hold", true, true, true, false, false⟩], ["ApproachFast", "ApproachSlow", "Hold"], [⟨"ApproachFast", [0], [0], [0]⟩, ⟨"ApproachSlow", [0], [0], [0]⟩, ⟨"Hold", [0], [], []⟩]⟩]⟩

end RelCertifier
