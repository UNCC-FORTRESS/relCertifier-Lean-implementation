/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_lag` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_lag`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_patrol_lag` (emitted, suite_v2, widened cut channel on). -/
def rover_patrol_lag_coverV2 : CoverEmitE :=
  ⟨"rover_patrol_lag", [], [
    ⟨"SLOW", (1 : ℚ) / 1, 1, [⟨"SLOW", true, true, true⟩, ⟨"MEDIUM_ECO", true, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [1, 0], [0, 1], [0, 1], 1, 1⟩, ⟨"MEDIUM_ECO", [1, 0], [0, 1], [0, 1], 1, 1⟩, ⟨"MEDIUM_BRISK", [1, 0], [0, 1], [0, 1], 1, 1⟩, ⟨"FAST", [1, 0], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"MEDIUM_ECO", (1 : ℚ) / 1, 1, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", true, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1], 1, 1⟩, ⟨"MEDIUM_ECO", [1, 0], [0, 1], [0, 1], 1, 1⟩, ⟨"MEDIUM_BRISK", [1, 0], [0, 1], [0, 1], 1, 1⟩, ⟨"FAST", [1, 0], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"MEDIUM_BRISK", (1 : ℚ) / 1, 1, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", false, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1], 1, 1⟩, ⟨"MEDIUM_ECO", [], [0, 1], [0, 1], 1, 1⟩, ⟨"MEDIUM_BRISK", [1, 0], [0, 1], [0, 1], 1, 1⟩, ⟨"FAST", [1, 0], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"FAST", (11 : ℚ) / 8, 2, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", false, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, false, false⟩], ["MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1], 11, 8⟩, ⟨"MEDIUM_ECO", [], [0, 1], [0, 1], 11, 8⟩, ⟨"MEDIUM_BRISK", [1, 0], [0, 1], [0, 1], 11, 8⟩, ⟨"FAST", [1, 0], [0, 1], [0, 1], 11, 8⟩]⟩]⟩

end RelCertifier
