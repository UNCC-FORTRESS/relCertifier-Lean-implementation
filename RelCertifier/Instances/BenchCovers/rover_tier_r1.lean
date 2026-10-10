/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_tier_r1` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_tier_r1` (emitted). -/
def rover_tier_r1_cover : CoverEmitE :=
  ⟨"rover_tier_r1", [], [
    ⟨"Cruise", (19 : ℚ) / 4, 5, [⟨"Cruise", true, true, true⟩], ["Cruise"], [⟨"Cruise", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
