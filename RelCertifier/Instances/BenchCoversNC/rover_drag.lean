/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_drag` — cut-free emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `RELCERT_NO_CUT=1 relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_drag` (cut-free emission). -/
def rover_drag_coverNC : CoverEmitE :=
  ⟨"rover_drag", [], [
    ⟨"Cruise", (1 : ℚ) / 1, 1, [⟨"Track", true, false, false, false, false⟩], ["Track"], [⟨"Track", [0], [], []⟩]⟩]⟩

end RelCertifier
