/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `zone_lightmass_schedule` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py zone_lightmass_schedule`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `zone_lightmass_schedule` (emitted, suite_v2, widened cut channel on). -/
def zone_lightmass_schedule_coverV2 : CoverEmitE :=
  ⟨"zone_lightmass_schedule", [], [
    ⟨"COMFORT", (2 : ℚ) / 1, 2, [⟨"COMFORT", true, false, false⟩, ⟨"STANDBY", false, false, false⟩, ⟨"ECONOMY", false, false, false⟩], ["COMFORT", "STANDBY", "ECONOMY"], [⟨"COMFORT", [0, 1], [0], [0], 2, 1⟩, ⟨"STANDBY", [1], [], [], 2, 1⟩, ⟨"ECONOMY", [1], [1], [1], 2, 1⟩]⟩,
    ⟨"ECONOMY", (2 : ℚ) / 1, 2, [⟨"COMFORT", false, false, false⟩, ⟨"STANDBY", false, false, false⟩, ⟨"ECONOMY", true, false, false⟩], ["COMFORT", "STANDBY", "ECONOMY"], [⟨"COMFORT", [0], [0], [0], 2, 1⟩, ⟨"STANDBY", [0], [], [], 2, 1⟩, ⟨"ECONOMY", [0, 1], [1], [1], 2, 1⟩]⟩]⟩

end RelCertifier
