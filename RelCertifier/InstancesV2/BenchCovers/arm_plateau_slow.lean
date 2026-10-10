/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_slow` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py arm_plateau_slow`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_plateau_slow` (emitted, suite_v2, widened cut channel on). -/
def arm_plateau_slow_coverV2 : CoverEmitE :=
  ⟨"arm_plateau_slow", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 2, [⟨"ApproachA", true, true, true⟩, ⟨"ApproachB", false, true, true⟩, ⟨"ApproachC", true, true, true⟩, ⟨"Hold", true, true, true⟩], ["ApproachA", "ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0], [0], [0]⟩, ⟨"ApproachB", [], [0], [0]⟩, ⟨"ApproachC", [0], [0], [0]⟩, ⟨"Hold", [0], [0], [0]⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 2, [⟨"ApproachA", true, true, true⟩, ⟨"ApproachB", true, true, true⟩, ⟨"ApproachC", true, true, true⟩, ⟨"Hold", true, true, true⟩], ["ApproachB", "ApproachC", "Hold"], [⟨"ApproachA", [0], [0], [0]⟩, ⟨"ApproachB", [0], [0], [0]⟩, ⟨"ApproachC", [0], [0], [0]⟩, ⟨"Hold", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
