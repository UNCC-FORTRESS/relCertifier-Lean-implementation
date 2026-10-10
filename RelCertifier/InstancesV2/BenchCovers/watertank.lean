/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py watertank`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `watertank` (emitted, suite_v2, widened cut channel on). -/
def watertank_coverV2 : CoverEmitE :=
  ⟨"watertank", [("Low", "PumpOff")], [
    ⟨"Low", (2 : ℚ) / 1, 2, [⟨"Low", true, false, false⟩, ⟨"MidEco", true, false, false⟩, ⟨"MidBoost", true, false, false⟩, ⟨"High", true, true, false⟩, ⟨"PumpOff", false, true, true⟩], ["Low", "MidEco", "MidBoost"], [⟨"Low", [0, 1], [0], [0]⟩, ⟨"MidEco", [0, 1], [0], [0]⟩, ⟨"MidBoost", [0, 1], [0], [0]⟩, ⟨"High", [0, 1], [1, 0], [1]⟩, ⟨"PumpOff", [1], [0, 1], [0, 1]⟩]⟩,
    ⟨"Mid", (2 : ℚ) / 1, 2, [⟨"Low", false, false, false⟩, ⟨"MidEco", true, false, false⟩, ⟨"MidBoost", true, false, false⟩, ⟨"High", true, false, false⟩, ⟨"PumpOff", true, true, true⟩], ["MidEco", "MidBoost", "High"], [⟨"Low", [1], [0], [0]⟩, ⟨"MidEco", [0, 1], [0], [0]⟩, ⟨"MidBoost", [0, 1], [0], [0]⟩, ⟨"High", [0, 1], [1], [1]⟩, ⟨"PumpOff", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"High", (1 : ℚ) / 1, 1, [⟨"Low", true, true, true⟩, ⟨"MidEco", true, true, true⟩, ⟨"MidBoost", true, true, true⟩, ⟨"High", true, false, false⟩, ⟨"PumpOff", true, true, true⟩], ["High"], [⟨"Low", [0, 1], [0, 1], [0, 1]⟩, ⟨"MidEco", [0, 1], [0, 1], [0, 1]⟩, ⟨"MidBoost", [0, 1], [0, 1], [0, 1]⟩, ⟨"High", [0, 1], [1], [1]⟩, ⟨"PumpOff", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
