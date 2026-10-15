/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `watertank_choice` (choice) — emitted cover, `RELCERT_IMPLIED_CUT=1 RELCERT_PROGRESS=1 RELCERT_CHOICE=1` (GENERATED leaf)
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

def watertank_choice_coverV2 : CoverEmitE :=
  ⟨"watertank_choice", [("Low", "PumpOff")], [
    ⟨"Low", (7 : ℚ) / 2, 4, [⟨"Low", true, false, false⟩, ⟨"MidEco", true, false, false⟩, ⟨"MidBoost", true, false, false⟩, ⟨"High", true, true, false⟩, ⟨"PumpOff", false, false, false⟩], ["Low", "MidEco", "MidBoost"], [⟨"Low", [0, 1], [0], [0], 2, 1⟩, ⟨"MidEco", [0, 1], [], [], 7, 2⟩, ⟨"MidBoost", [0, 1], [0], [0], 1, 1⟩, ⟨"High", [0, 1], [1, 0], [1], 1, 1⟩, ⟨"PumpOff", [1], [0, 1], [0, 1], 7, 2⟩]⟩,
    ⟨"Mid", (1 : ℚ) / 1, 1, [⟨"Low", false, false, false⟩, ⟨"MidEco", false, false, false⟩, ⟨"MidBoost", true, false, false⟩, ⟨"High", true, false, false⟩, ⟨"PumpOff", true, false, false⟩], ["MidEco", "MidBoost", "High"], [⟨"Low", [1], [0], [0], 1, 1⟩, ⟨"MidEco", [1], [], [], 1, 1⟩, ⟨"MidBoost", [0, 1], [0], [0], 1, 1⟩, ⟨"High", [0, 1], [1], [1], 1, 1⟩, ⟨"PumpOff", [0, 1], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"High", (1 : ℚ) / 1, 1, [⟨"Low", true, true, true⟩, ⟨"MidEco", false, false, false⟩, ⟨"MidBoost", true, true, true⟩, ⟨"High", true, false, false⟩, ⟨"PumpOff", true, false, false⟩], ["High"], [⟨"Low", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"MidEco", [1], [], [], 1, 1⟩, ⟨"MidBoost", [0, 1], [0, 1], [0, 1], 1, 1⟩, ⟨"High", [0, 1], [1], [1], 1, 1⟩, ⟨"PumpOff", [0, 1], [0, 1], [0, 1], 1, 1⟩]⟩]⟩


end RelCertifier
