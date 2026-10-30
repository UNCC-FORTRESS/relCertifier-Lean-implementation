/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `turbine_startup_gearratio` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py turbine_startup_gearratio`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `turbine_startup_gearratio` (emitted, suite_v2, widened cut channel on). -/
def turbine_startup_gearratio_coverV2 : CoverEmitE :=
  ⟨"turbine_startup_gearratio", [], [
    ⟨"SPINUP", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", false, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"REG", true, false, false⟩, ⟨"GUST", false, false, false⟩], ["SPINUP", "RAMP", "GEN", "REG", "GUST"], [⟨"SPINUP", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"RAMP", [1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"GEN", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"REG", [0, 1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"GUST", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"RAMP", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", true, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"REG", true, false, false⟩, ⟨"GUST", false, false, false⟩], ["RAMP", "GEN", "REG", "GUST"], [⟨"SPINUP", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"RAMP", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"GEN", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"REG", [0, 1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"GUST", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"GEN", (1 : ℚ) / 1, 1, [⟨"SPINUP", false, true, true⟩, ⟨"RAMP", false, true, true⟩, ⟨"GEN", true, false, false⟩, ⟨"REG", true, false, false⟩, ⟨"GUST", false, false, false⟩], ["GEN", "REG", "GUST"], [⟨"SPINUP", [1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"RAMP", [1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"GEN", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 1, 1⟩, ⟨"REG", [0, 1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"GUST", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"REG", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", true, true, true⟩, ⟨"GEN", false, true, true⟩, ⟨"REG", true, false, false⟩, ⟨"GUST", false, false, false⟩], ["REG", "GUST"], [⟨"SPINUP", [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 1, 1⟩, ⟨"RAMP", [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 1, 1⟩, ⟨"GEN", [1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 1, 1⟩, ⟨"REG", [0, 1, 2, 3, 4, 5], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"GUST", [0, 1, 2, 3, 5], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"GUST", (1 : ℚ) / 1, 1, [⟨"SPINUP", true, true, true⟩, ⟨"RAMP", true, true, true⟩, ⟨"GEN", false, true, true⟩, ⟨"REG", false, false, false⟩, ⟨"GUST", true, false, false⟩], ["REG", "GUST"], [⟨"SPINUP", [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 1, 1⟩, ⟨"RAMP", [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 1, 1⟩, ⟨"GEN", [1, 2, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 1, 1⟩, ⟨"REG", [1, 2, 4, 5], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"GUST", [1, 2, 3, 4, 5, 0], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
