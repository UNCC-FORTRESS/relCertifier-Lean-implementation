/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_tyre` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_tyre`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `stopline_tyre` (emitted, suite_v2, widened cut channel on). -/
def stopline_tyre_coverV2 : CoverEmitE :=
  ⟨"stopline_tyre", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"CRUISE", true, false, false⟩, ⟨"BRAKE", false, false, false⟩, ⟨"STOP", false, false, false⟩], ["CRUISE"], [⟨"CRUISE", [2, 3, 5, 6, 7, 8, 9, 0, 1, 4], [], [], 1, 1⟩, ⟨"BRAKE", [3, 5, 7, 8, 9, 1, 4], [], [], 1, 1⟩, ⟨"STOP", [1, 2, 3, 5, 6, 7, 8, 9, 4], [], [], 1, 1⟩]⟩,
    ⟨"BRAKE", (1 : ℚ) / 1, 1, [⟨"CRUISE", false, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1], [], [], 1, 1⟩, ⟨"STOP", [0, 1], [], [], 1, 1⟩]⟩,
    ⟨"STOP", (1 : ℚ) / 1, 1, [⟨"CRUISE", false, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1], [], [], 1, 1⟩, ⟨"STOP", [0, 1], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
