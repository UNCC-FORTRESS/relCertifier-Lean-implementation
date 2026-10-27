/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `salt_tank_sensor` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py salt_tank_sensor`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `salt_tank_sensor` (emitted, suite_v2, widened cut channel on). -/
def salt_tank_sensor_coverV2 : CoverEmitE :=
  ⟨"salt_tank_sensor", [], [
    ⟨"On", (1 : ℚ) / 1, 1, [⟨"On", true, false, false⟩, ⟨"Off", true, true, true⟩], ["On"], [⟨"On", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Off", [1, 2, 3, 0], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩]⟩,
    ⟨"Off", (1 : ℚ) / 1, 1, [⟨"On", true, false, false⟩, ⟨"Off", true, true, true⟩], ["On"], [⟨"On", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Off", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
