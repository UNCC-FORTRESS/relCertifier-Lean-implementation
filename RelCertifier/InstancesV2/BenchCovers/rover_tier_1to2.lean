/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_tier_1to2` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_tier_1to2`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_tier_1to2` (emitted, suite_v2, widened cut channel on). -/
def rover_tier_1to2_coverV2 : CoverEmitE :=
  ⟨"rover_tier_1to2", [], [
    ⟨"ACCEL", (7 : ℚ) / 4, 6, [⟨"ACCEL", true, true, true⟩, ⟨"COAST", true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [1, 0], [0, 1], [0, 1], 7, 4⟩, ⟨"COAST", [1, 0], [0, 1], [0, 1], 7, 4⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, true, true⟩, ⟨"COAST", true, false, false⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0], [0], [0], 1, 1⟩, ⟨"COAST", [0], [0], [0], 1, 1⟩]⟩]⟩

end RelCertifier
