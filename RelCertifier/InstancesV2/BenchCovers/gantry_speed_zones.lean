/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `gantry_speed_zones` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py gantry_speed_zones`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `gantry_speed_zones` (emitted, suite_v2, widened cut channel on). -/
def gantry_speed_zones_coverV2 : CoverEmitE :=
  ⟨"gantry_speed_zones", [], [
    ⟨"FREE", (3 : ℚ) / 1, 3, [⟨"MOVE", true, false, false⟩], ["MOVE"], [⟨"MOVE", [0, 1, 2, 3], [], [], 3, 1⟩]⟩,
    ⟨"APPROACH", (2 : ℚ) / 1, 2, [⟨"MOVE", true, false, false⟩], ["MOVE"], [⟨"MOVE", [0, 1, 2, 3], [], [], 2, 1⟩]⟩,
    ⟨"PLACE", (1 : ℚ) / 1, 1, [⟨"MOVE", true, false, false⟩], ["MOVE"], [⟨"MOVE", [0, 1, 2, 3], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
