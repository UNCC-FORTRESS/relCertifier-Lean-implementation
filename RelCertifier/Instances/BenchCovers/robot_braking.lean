/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `robot_braking` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `robot_braking` (emitted). -/
def robot_braking_cover : CoverEmitE :=
  ⟨"robot_braking", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"FAST", false, true, true, false, false⟩, ⟨"MID", false, true, true, false, false⟩, ⟨"SLOW", true, false, false, false, false⟩], ["FAST", "MID", "SLOW"], [⟨"FAST", [], [], []⟩, ⟨"MID", [], [], []⟩, ⟨"SLOW", [0], [], []⟩]⟩]⟩

end RelCertifier
