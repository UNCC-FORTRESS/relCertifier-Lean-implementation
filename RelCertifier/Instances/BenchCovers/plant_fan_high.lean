/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `plant_fan_high` — emitted cover (GENERATED leaf — do not edit)

Per-benchmark leaf module (X0 modularization): editing one benchmark no longer
re-elaborates the whole instance battery. Regenerate with `relcert --emit-cover`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `plant_fan_high` (emitted). -/
def plant_fan_high_cover : CoverEmitE :=
  ⟨"plant_fan_high", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, true, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0], [0], [0]⟩, ⟨"ApproachB", [], [0], [0]⟩, ⟨"ApproachC", [], [0], [0]⟩, ⟨"Hold", [0], [0], [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"ApproachA", true, false, false, true, true⟩, ⟨"ApproachB", false, false, false, true, true⟩, ⟨"ApproachC", false, true, true, true, true⟩, ⟨"Hold", true, true, true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0], [0], [0]⟩, ⟨"ApproachB", [], [0], [0]⟩, ⟨"ApproachC", [], [0], [0]⟩, ⟨"Hold", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
