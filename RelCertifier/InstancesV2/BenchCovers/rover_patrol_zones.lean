/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_zones` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_zones`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_patrol_zones` (emitted, suite_v2, widened cut channel on). -/
def rover_patrol_zones_coverV2 : CoverEmitE :=
  ⟨"rover_patrol_zones", [("SLOW", "STALL"), ("MEDIUM_ECO", "STALL"), ("MEDIUM_BRISK", "STALL"), ("FAST", "STALL")], [
    ⟨"SLOW", (1 : ℚ) / 1, 2, [⟨"SLOW", true, true, true⟩, ⟨"MEDIUM_ECO", true, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, true, true⟩, ⟨"STALL", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [0, 1], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [0, 1], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [0, 1], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩, ⟨"STALL", [0, 1], [1], [1]⟩]⟩,
    ⟨"MEDIUM_ECO", (1 : ℚ) / 1, 2, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", true, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, true, true⟩, ⟨"STALL", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [0, 1], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [0, 1], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩, ⟨"STALL", [0, 1], [1], [1]⟩]⟩,
    ⟨"MEDIUM_BRISK", (1 : ℚ) / 1, 2, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", false, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, true, true⟩, ⟨"STALL", true, false, false⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [0, 1], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩, ⟨"STALL", [0, 1], [1], [1]⟩]⟩,
    ⟨"FAST", (1 : ℚ) / 1, 2, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", false, true, true⟩, ⟨"MEDIUM_BRISK", false, true, true⟩, ⟨"FAST", true, true, true⟩, ⟨"STALL", true, false, false⟩], ["MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩, ⟨"STALL", [0, 1], [1], [1]⟩]⟩]⟩

end RelCertifier
