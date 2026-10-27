/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `elevator_start_discbrake` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py elevator_start_discbrake`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `elevator_start_discbrake` (emitted, suite_v2, widened cut channel on). -/
def elevator_start_discbrake_coverV2 : CoverEmitE :=
  ⟨"elevator_start_discbrake", [], [
    ⟨"LIFT", (1 : ℚ) / 1, 1, [⟨"LIFT", true, false, false⟩, ⟨"UP", false, false, false⟩, ⟨"APP", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["LIFT"], [⟨"LIFT", [0, 1, 2, 3, 4], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"UP", [0, 2, 4], [0], [0], 1, 1⟩, ⟨"APP", [0, 1, 2, 3, 4], [0], [0], 1, 1⟩, ⟨"STOP", [0, 1, 2, 3, 4], [0, 3, 4, 1, 2], [0, 3, 4, 1, 2], 1, 1⟩]⟩,
    ⟨"UP", (1 : ℚ) / 1, 1, [⟨"LIFT", false, true, true⟩, ⟨"UP", true, false, false⟩, ⟨"APP", false, false, false⟩, ⟨"STOP", false, false, false⟩], ["LIFT", "UP"], [⟨"LIFT", [1, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"UP", [2, 3, 0, 1], [0], [0], 1, 1⟩, ⟨"APP", [3, 1], [0], [0], 1, 1⟩, ⟨"STOP", [3, 1], [0, 3], [0, 3], 1, 1⟩]⟩,
    ⟨"APP", (1 : ℚ) / 1, 1, [⟨"LIFT", true, true, true⟩, ⟨"UP", false, false, false⟩, ⟨"APP", true, false, false⟩, ⟨"STOP", false, false, false⟩], ["APP"], [⟨"LIFT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"UP", [2, 0], [0], [0], 1, 1⟩, ⟨"APP", [2, 3, 0, 1], [0], [0], 1, 1⟩, ⟨"STOP", [3, 1], [0, 3], [0, 3], 1, 1⟩]⟩,
    ⟨"STOP", (1 : ℚ) / 1, 1, [⟨"LIFT", true, true, true⟩, ⟨"UP", false, false, false⟩, ⟨"APP", false, false, false⟩, ⟨"STOP", true, false, false⟩], ["STOP"], [⟨"LIFT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩, ⟨"UP", [2, 0], [0], [0], 1, 1⟩, ⟨"APP", [2, 0], [0], [0], 1, 1⟩, ⟨"STOP", [2, 3, 0, 1], [0, 3], [0, 3], 1, 1⟩]⟩]⟩

end RelCertifier
