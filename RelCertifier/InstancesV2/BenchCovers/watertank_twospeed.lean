/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_twospeed` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py watertank_twospeed`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `watertank_twospeed` (emitted, suite_v2, widened cut channel on). -/
def watertank_twospeed_coverV2 : CoverEmitE :=
  ⟨"watertank_twospeed", [], [
    ⟨"Low", (2 : ℚ) / 1, 2, [⟨"Fast", true, false, false⟩, ⟨"Slow", true, false, false⟩, ⟨"MidEco", true, false, false⟩, ⟨"MidBoost", true, false, false⟩, ⟨"High", true, true, false⟩, ⟨"PumpOff", false, false, false⟩], ["Fast", "Slow", "MidEco", "MidBoost"], [⟨"Fast", [0, 1], [0], [0], 1, 1⟩, ⟨"Slow", [0, 1], [0], [0], 2, 1⟩, ⟨"MidEco", [0, 1], [0], [0], 3, 2⟩, ⟨"MidBoost", [0, 1], [0], [0], 1, 1⟩, ⟨"High", [0, 1], [1, 0], [1, 0], 1, 1⟩, ⟨"PumpOff", [1], [0, 1], [0, 1], 2, 1⟩]⟩,
    ⟨"Mid", (2 : ℚ) / 1, 2, [⟨"Fast", false, false, false⟩, ⟨"Slow", false, false, false⟩, ⟨"MidEco", true, false, false⟩, ⟨"MidBoost", true, false, false⟩, ⟨"High", true, false, false⟩, ⟨"PumpOff", true, false, false⟩], ["MidEco", "MidBoost", "High"], [⟨"Fast", [1], [0], [0], 2, 1⟩, ⟨"Slow", [1], [0], [0], 2, 1⟩, ⟨"MidEco", [0, 1], [0], [0], 2, 1⟩, ⟨"MidBoost", [0, 1], [0], [0], 2, 1⟩, ⟨"High", [0, 1], [1], [1], 2, 1⟩, ⟨"PumpOff", [0, 1], [0, 1], [0, 1], 2, 1⟩]⟩,
    ⟨"High", (1 : ℚ) / 1, 1, [⟨"Fast", true, true, true⟩, ⟨"Slow", true, true, true⟩, ⟨"MidEco", true, true, true⟩, ⟨"MidBoost", true, true, true⟩, ⟨"High", true, false, false⟩, ⟨"PumpOff", true, false, false⟩], ["High"], [⟨"Fast", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"Slow", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"MidEco", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"MidBoost", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"High", [0, 1], [1], [1], 1, 1⟩, ⟨"PumpOff", [0, 1], [0, 1], [0, 1], 1, 1⟩]⟩]⟩

end RelCertifier
