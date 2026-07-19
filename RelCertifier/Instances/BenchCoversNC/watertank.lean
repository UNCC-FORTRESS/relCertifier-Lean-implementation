/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `watertank` (cut-free emission). -/
def watertank_coverNC : CoverEmitE :=
  ⟨"watertank", [], [
    ⟨"Low", (1 : ℚ) / 1, 1, [⟨"Low", true, false, false, false, false⟩, ⟨"Mid", true, true, false, true, true⟩, ⟨"High", false, true, false, false, false⟩], ["Low", "Mid", "High"], [⟨"Low", [0], [], []⟩, ⟨"Mid", [0], [0], [0]⟩, ⟨"High", [], [], []⟩]⟩,
    ⟨"Mid", (1 : ℚ) / 1, 1, [⟨"Low", false, false, false, false, false⟩, ⟨"Mid", true, false, false, true, true⟩, ⟨"High", false, true, false, false, false⟩], ["Mid", "High"], [⟨"Low", [], [], []⟩, ⟨"Mid", [0], [0], [0]⟩, ⟨"High", [], [], []⟩]⟩,
    ⟨"High", (1 : ℚ) / 1, 1, [⟨"Low", true, false, false, false, false⟩, ⟨"Mid", true, false, false, true, true⟩, ⟨"High", true, false, false, false, false⟩], ["High"], [⟨"Low", [0], [], []⟩, ⟨"Mid", [0], [0], [0]⟩, ⟨"High", [0], [], []⟩]⟩]⟩

end RelCertifier
