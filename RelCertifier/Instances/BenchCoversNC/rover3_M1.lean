/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3_M1` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover3_M1` (cut-free emission). -/
def rover3_M1_coverNC : CoverEmitE :=
  ⟨"rover3_M1", [], [
    ⟨"Drive", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0], [0], [0]⟩, ⟨"Drive", [0], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩,
    ⟨"Drift", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0], [0], [0]⟩, ⟨"Drive", [0], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩,
    ⟨"Stop", (4 : ℚ) / 1, 4, [⟨"Recover", true, false, false, true, true⟩, ⟨"Drive", true, false, false, true, true⟩, ⟨"Safe", true, false, false, true, true⟩], ["Recover", "Drive", "Safe"], [⟨"Recover", [0], [0], [0]⟩, ⟨"Drive", [0], [0], [0]⟩, ⟨"Safe", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
