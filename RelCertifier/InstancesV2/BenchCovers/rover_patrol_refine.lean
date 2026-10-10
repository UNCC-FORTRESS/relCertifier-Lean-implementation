/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_patrol_refine` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_patrol_refine`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_patrol_refine` (emitted, suite_v2, widened cut channel on). -/
def rover_patrol_refine_coverV2 : CoverEmitE :=
  ⟨"rover_patrol_refine", [], [
    ⟨"SLOW", (9 : ℚ) / 4, 5, [⟨"SLOW", true, true, true⟩, ⟨"MEDIUM_ECO", true, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, true, true⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [0, 1], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [0, 1], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [0, 1], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MEDIUM_ECO", (9 : ℚ) / 4, 5, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", true, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, true, true⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [0, 1], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [0, 1], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MEDIUM_BRISK", (9 : ℚ) / 4, 5, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", false, true, true⟩, ⟨"MEDIUM_BRISK", true, true, true⟩, ⟨"FAST", true, true, true⟩], ["SLOW", "MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [0, 1], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"FAST", (9 : ℚ) / 4, 5, [⟨"SLOW", false, true, true⟩, ⟨"MEDIUM_ECO", false, true, true⟩, ⟨"MEDIUM_BRISK", false, true, true⟩, ⟨"FAST", true, true, true⟩], ["MEDIUM_ECO", "MEDIUM_BRISK", "FAST"], [⟨"SLOW", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_ECO", [], [0, 1], [0, 1]⟩, ⟨"MEDIUM_BRISK", [], [0, 1], [0, 1]⟩, ⟨"FAST", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
