/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_tyre` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, reposition certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_tyre`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `stopline_tyre` (emitted, suite_v2, implied mode-fact candidates on). -/
def stopline_tyre_coverV2 : CoverEmitE :=
  ⟨"stopline_tyre", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"CRUISE", true, false, false⟩, ⟨"BRAKE", false, false, false⟩, ⟨"STOP", false, false, false⟩], ["CRUISE"], [⟨"CRUISE", [2, 3, 5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 0, 1, 4, 10, 11, 12, 13], [], [], 1, 1⟩, ⟨"BRAKE", [3, 5, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 1, 4, 10, 11, 12, 13], [], [], 1, 1⟩, ⟨"STOP", [1, 2, 3, 5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 4, 10, 11, 12, 13], [], [], 1, 1⟩]⟩,
    ⟨"BRAKE", (1 : ℚ) / 1, 1, [⟨"CRUISE", false, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 2, 3, 4, 5], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 2, 3, 4, 5], [], [], 1, 1⟩, ⟨"STOP", [0, 1, 6, 7, 8, 9, 10, 11, 12, 13, 14, 2, 3, 4, 5], [], [], 1, 1⟩]⟩,
    ⟨"STOP", (1 : ℚ) / 1, 1, [⟨"CRUISE", false, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], [], [], 1, 1⟩, ⟨"STOP", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
