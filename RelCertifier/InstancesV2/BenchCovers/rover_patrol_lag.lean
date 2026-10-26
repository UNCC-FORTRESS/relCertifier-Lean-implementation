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
    ⟨"SLOW", (1 : ℚ) / 1, 2, [⟨"SLOW", true, false, false⟩, ⟨"MEDIUM_ECO", true, false, false⟩, ⟨"MEDIUM_BRISK", true, false, false⟩, ⟨"FAST", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [0, 1, 2], [1, 2], [1, 2], 1, 1⟩, ⟨"MEDIUM_ECO", [0, 1, 2], [1, 2], [1, 2], 1, 1⟩, ⟨"MEDIUM_BRISK", [0, 1, 2], [1, 2], [1, 2], 1, 1⟩, ⟨"FAST", [0, 1, 2], [1, 2], [1, 2], 1, 1⟩]⟩,
    ⟨"MEDIUM_ECO", (5 : ℚ) / 4, 3, [⟨"SLOW", true, false, false⟩, ⟨"MEDIUM_ECO", true, false, false⟩, ⟨"MEDIUM_BRISK", true, false, false⟩, ⟨"FAST", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [0, 1, 2], [1, 2], [1, 2], 5, 4⟩, ⟨"MEDIUM_ECO", [0, 1, 2], [1, 2], [1, 2], 5, 4⟩, ⟨"MEDIUM_BRISK", [0, 1, 2], [1, 2], [1, 2], 5, 4⟩, ⟨"FAST", [0, 1, 2], [1, 2], [1, 2], 5, 4⟩]⟩,
    ⟨"MEDIUM_BRISK", (3 : ℚ) / 2, 3, [⟨"SLOW", true, false, false⟩, ⟨"MEDIUM_ECO", true, false, false⟩, ⟨"MEDIUM_BRISK", true, false, false⟩, ⟨"FAST", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩, ⟨"MEDIUM_ECO", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩, ⟨"MEDIUM_BRISK", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩, ⟨"FAST", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩]⟩,
    ⟨"FAST", (3 : ℚ) / 2, 3, [⟨"SLOW", false, false, false⟩, ⟨"MEDIUM_ECO", true, false, false⟩, ⟨"MEDIUM_BRISK", true, false, false⟩, ⟨"FAST", true, false, false⟩], ["MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [1, 2], [1, 2], 3, 2⟩, ⟨"MEDIUM_ECO", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩, ⟨"MEDIUM_BRISK", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩, ⟨"FAST", [0, 1, 2], [1, 2], [1, 2], 3, 2⟩]⟩]⟩

end RelCertifier
