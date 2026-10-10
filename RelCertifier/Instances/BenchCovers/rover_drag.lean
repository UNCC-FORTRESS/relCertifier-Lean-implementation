/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_drag` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_drag` (emitted). -/
def rover_drag_cover : CoverEmitE :=
  ⟨"rover_drag", [], [
    ⟨"Cruise", (1 : ℚ) / 1, 1, [⟨"Track", true, false, false⟩], ["Track"], [⟨"Track", [0], [], []⟩]⟩]⟩

end RelCertifier
