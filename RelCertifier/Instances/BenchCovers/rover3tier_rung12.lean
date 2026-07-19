/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover3tier_rung12` (emitted). -/
def rover3tier_rung12_cover : CoverEmitE :=
  ⟨"rover3tier_rung12", [], [
    ⟨"ACCEL", (2 : ℚ) / 1, 7, [⟨"ACCEL", true, false, false, true, true⟩, ⟨"COAST", true, true, false, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0, 1], [0, 1], [0, 1]⟩, ⟨"COAST", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, false, false, true, true⟩, ⟨"COAST", true, false, false, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0], [0], [0]⟩, ⟨"COAST", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
