/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `hvac_fan_staging` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py hvac_fan_staging`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `hvac_fan_staging` (emitted, suite_v2, widened cut channel on). -/
def hvac_fan_staging_coverV2 : CoverEmitE :=
  ⟨"hvac_fan_staging", [], [
    ⟨"LOW", (1 : ℚ) / 1, 1, [⟨"LOW", true, false, false⟩, ⟨"MED", false, false, false⟩, ⟨"HIGH", false, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [0, 1], [0], [0], 1, 1⟩, ⟨"MED", [1], [], [], 1, 1⟩, ⟨"HIGH", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"MED", (1 : ℚ) / 1, 1, [⟨"LOW", false, false, false⟩, ⟨"MED", true, false, false⟩, ⟨"HIGH", false, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [0], [0], [0], 1, 1⟩, ⟨"MED", [0, 1], [], [], 1, 1⟩, ⟨"HIGH", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"HIGH", (1 : ℚ) / 1, 1, [⟨"LOW", false, false, false⟩, ⟨"MED", false, false, false⟩, ⟨"HIGH", true, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [0], [0], [0], 1, 1⟩, ⟨"MED", [0], [], [], 1, 1⟩, ⟨"HIGH", [0, 1], [1], [1], 1, 1⟩]⟩]⟩

end RelCertifier
