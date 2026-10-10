/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_4d_box` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_4d_box` (cut-free emission). -/
def rover_4d_box_coverNC : CoverEmitE :=
  ⟨"rover_4d_box", [], [
    ⟨"HOLD", (1 : ℚ) / 1, 1, [⟨"APPROACH", true, true, true⟩, ⟨"SETTLE", true, true, true⟩], ["APPROACH", "SETTLE"], [⟨"APPROACH", [0], [0], [0]⟩, ⟨"SETTLE", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
