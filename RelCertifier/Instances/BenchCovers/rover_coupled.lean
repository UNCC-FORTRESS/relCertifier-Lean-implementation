/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_coupled` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_coupled` (emitted). -/
def rover_coupled_cover : CoverEmitE :=
  ⟨"rover_coupled", [], [
    ⟨"Drive", (7 : ℚ) / 5, 2, [⟨"Recover", false, true, true⟩, ⟨"Drive", false, true, true⟩, ⟨"Safe", true, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [], [0], [0]⟩, ⟨"Drive", [], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩,
    ⟨"Drift", (7 : ℚ) / 5, 2, [⟨"Recover", false, true, true⟩, ⟨"Drive", false, true, true⟩, ⟨"Safe", true, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [], [0], [0]⟩, ⟨"Drive", [], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩,
    ⟨"Stop", (7 : ℚ) / 5, 2, [⟨"Recover", false, true, true⟩, ⟨"Drive", false, true, true⟩, ⟨"Safe", true, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [], [0], [0]⟩, ⟨"Drive", [], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
