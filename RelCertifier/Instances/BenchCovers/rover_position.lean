/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_position` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_position` (emitted). -/
def rover_position_cover : CoverEmitE :=
  ⟨"rover_position", [], [
    ⟨"Drive", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [], [0], [0]⟩, ⟨"Drive", [], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩,
    ⟨"Drift", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [], [0], [0]⟩, ⟨"Drive", [], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩,
    ⟨"Stop", (7 : ℚ) / 5, 2, [⟨"Recover", false, false, false, true, true⟩, ⟨"Drive", false, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [], [0], [0]⟩, ⟨"Drive", [], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
