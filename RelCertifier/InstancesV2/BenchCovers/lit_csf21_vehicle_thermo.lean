/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_csf21_vehicle_thermo` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_csf21_vehicle_thermo`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `lit_csf21_vehicle_thermo` (emitted, suite_v2, widened cut channel on). -/
def lit_csf21_vehicle_thermo_coverV2 : CoverEmitE :=
  ⟨"lit_csf21_vehicle_thermo", [], [
    ⟨"AccCool", (1 : ℚ) / 1, 1, [⟨"AccCool", true, false, false⟩, ⟨"AccHeat", true, false, false⟩, ⟨"CoastCool", false, false, false⟩, ⟨"CoastHeat", false, false, false⟩, ⟨"BrkCool", false, false, false⟩, ⟨"BrkHeat", false, false, false⟩], ["AccCool", "AccHeat", "CoastCool", "CoastHeat", "BrkCool", "BrkHeat"], [⟨"AccCool", [2, 3, 0, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"AccHeat", [2, 3, 0, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"CoastCool", [3, 0], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"CoastHeat", [3, 0], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"BrkCool", [3, 0], [1, 3], [1, 3], 1, 1⟩, ⟨"BrkHeat", [3, 0], [1, 3], [1, 3], 1, 1⟩]⟩,
    ⟨"AccHeat", (1 : ℚ) / 1, 1, [⟨"AccCool", true, false, false⟩, ⟨"AccHeat", true, false, false⟩, ⟨"CoastCool", false, false, false⟩, ⟨"CoastHeat", false, false, false⟩, ⟨"BrkCool", false, false, false⟩, ⟨"BrkHeat", false, false, false⟩], ["AccCool", "AccHeat", "CoastCool", "CoastHeat", "BrkCool", "BrkHeat"], [⟨"AccCool", [2, 3, 0, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"AccHeat", [2, 3, 0, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"CoastCool", [3, 0], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"CoastHeat", [3, 0], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"BrkCool", [3, 0], [1, 3], [1, 3], 1, 1⟩, ⟨"BrkHeat", [3, 0], [1, 3], [1, 3], 1, 1⟩]⟩,
    ⟨"CoastCool", (1 : ℚ) / 1, 1, [⟨"AccCool", false, false, false⟩, ⟨"AccHeat", false, false, false⟩, ⟨"CoastCool", true, false, false⟩, ⟨"CoastHeat", true, false, false⟩, ⟨"BrkCool", false, false, false⟩, ⟨"BrkHeat", false, false, false⟩], ["AccCool", "AccHeat", "CoastCool", "CoastHeat", "BrkCool", "BrkHeat"], [⟨"AccCool", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"AccHeat", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"CoastCool", [2, 3, 0, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"CoastHeat", [2, 3, 0, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"BrkCool", [3, 0], [1, 3], [1, 3], 1, 1⟩, ⟨"BrkHeat", [3, 0], [1, 3], [1, 3], 1, 1⟩]⟩,
    ⟨"CoastHeat", (1 : ℚ) / 1, 1, [⟨"AccCool", false, false, false⟩, ⟨"AccHeat", false, false, false⟩, ⟨"CoastCool", true, false, false⟩, ⟨"CoastHeat", true, false, false⟩, ⟨"BrkCool", false, false, false⟩, ⟨"BrkHeat", false, false, false⟩], ["AccCool", "AccHeat", "CoastCool", "CoastHeat", "BrkCool", "BrkHeat"], [⟨"AccCool", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"AccHeat", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"CoastCool", [2, 3, 0, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"CoastHeat", [2, 3, 0, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"BrkCool", [3, 0], [1, 3], [1, 3], 1, 1⟩, ⟨"BrkHeat", [3, 0], [1, 3], [1, 3], 1, 1⟩]⟩,
    ⟨"BrkCool", (1 : ℚ) / 1, 1, [⟨"AccCool", false, false, false⟩, ⟨"AccHeat", false, false, false⟩, ⟨"CoastCool", false, false, false⟩, ⟨"CoastHeat", false, false, false⟩, ⟨"BrkCool", true, false, false⟩, ⟨"BrkHeat", true, false, false⟩], ["AccCool", "AccHeat", "CoastCool", "CoastHeat", "BrkCool", "BrkHeat"], [⟨"AccCool", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"AccHeat", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"CoastCool", [2, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"CoastHeat", [2, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"BrkCool", [2, 3, 0, 1], [1, 3], [1, 3], 1, 1⟩, ⟨"BrkHeat", [2, 3, 0, 1], [1, 3], [1, 3], 1, 1⟩]⟩,
    ⟨"BrkHeat", (1 : ℚ) / 1, 1, [⟨"AccCool", false, false, false⟩, ⟨"AccHeat", false, false, false⟩, ⟨"CoastCool", false, false, false⟩, ⟨"CoastHeat", false, false, false⟩, ⟨"BrkCool", true, false, false⟩, ⟨"BrkHeat", true, false, false⟩], ["AccCool", "AccHeat", "CoastCool", "CoastHeat", "BrkCool", "BrkHeat"], [⟨"AccCool", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"AccHeat", [2, 1], [1, 2], [1, 2], 1, 1⟩, ⟨"CoastCool", [2, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"CoastHeat", [2, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"BrkCool", [2, 3, 0, 1], [1, 3], [1, 3], 1, 1⟩, ⟨"BrkHeat", [2, 3, 0, 1], [1, 3], [1, 3], 1, 1⟩]⟩]⟩

end RelCertifier
