/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `stopline_lag` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py stopline_lag`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `stopline_lag` (emitted, suite_v2, widened cut channel on). -/
def stopline_lag_coverV2 : CoverEmitE :=
  ⟨"stopline_lag", [], [
    ⟨"CRUISE", (1 : ℚ) / 1, 1, [⟨"CRUISE", true, false, false⟩, ⟨"BRAKE", false, false, false⟩, ⟨"STOP", false, false, false⟩], ["CRUISE"], [⟨"CRUISE", [2, 3, 4, 5, 0, 1], [], [], 1, 1⟩, ⟨"BRAKE", [3, 4, 5, 1], [], [], 1, 1⟩, ⟨"STOP", [1, 2, 3, 4, 5], [], [], 1, 1⟩]⟩,
    ⟨"BRAKE", (1 : ℚ) / 1, 1, [⟨"CRUISE", true, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0, 1], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1], [], [], 1, 1⟩, ⟨"STOP", [0, 1], [], [], 1, 1⟩]⟩,
    ⟨"STOP", (1 : ℚ) / 1, 1, [⟨"CRUISE", true, false, false⟩, ⟨"BRAKE", true, false, false⟩, ⟨"STOP", true, false, false⟩], ["BRAKE", "STOP"], [⟨"CRUISE", [0, 1], [], [], 1, 1⟩, ⟨"BRAKE", [0, 1], [], [], 1, 1⟩, ⟨"STOP", [0, 1], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
