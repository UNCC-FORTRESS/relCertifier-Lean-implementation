/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_drag` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_drag`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `stopline_drag` (emitted, suite_v2, widened cut channel on). -/
def stopline_drag_coverV2 : CoverEmitE :=
  ⟨"stopline_drag", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"CRUISE", true, false, false⟩, ⟨"BRAKE", false, false, false⟩, ⟨"STOP", false, false, false⟩], ["CRUISE"], [⟨"CRUISE", [2, 3, 5, 7, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 28, 29, 30, 0, 1, 4, 6, 12, 13, 14, 15, 16, 17, 26, 27, 24, 25], [], [], 1, 1⟩, ⟨"BRAKE", [3, 5, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 28, 29, 30, 1, 4, 12, 13, 14, 15, 16, 17, 26, 27, 24, 25], [], [], 1, 1⟩, ⟨"STOP", [1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 18, 19, 20, 21, 22, 23, 26, 27, 28, 29, 30, 4, 12, 13, 14, 15, 16, 17, 24, 25], [], [], 1, 1⟩]⟩,
    ⟨"BRAKE", (1 : ℚ) / 1, 1, [⟨"CRUISE", false, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0, 3, 10, 11, 12, 13, 14, 15, 20, 21, 22, 2, 4, 5, 6, 7, 8, 9, 18, 19, 16, 17], [], [], 1, 1⟩, ⟨"BRAKE", [0, 3, 10, 11, 12, 13, 14, 15, 20, 21, 22, 2, 4, 5, 6, 7, 8, 9, 18, 19, 1, 16, 17], [], [], 1, 1⟩, ⟨"STOP", [0, 3, 10, 11, 12, 13, 14, 15, 20, 21, 22, 2, 4, 5, 6, 7, 8, 9, 18, 19, 1, 16, 17], [], [], 1, 1⟩]⟩,
    ⟨"STOP", (1 : ℚ) / 1, 1, [⟨"CRUISE", false, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], [], [], 1, 1⟩, ⟨"STOP", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
