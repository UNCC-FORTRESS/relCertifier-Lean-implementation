/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_tier_r1` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_tier_r1` (cut-free emission). -/
def rover_tier_r1_coverNC : CoverEmitE :=
  ⟨"rover_tier_r1", [], [
    ⟨"Cruise", (23 : ℚ) / 4, 6, [⟨"Cruise", true, true, true⟩], ["Cruise"], [⟨"Cruise", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
