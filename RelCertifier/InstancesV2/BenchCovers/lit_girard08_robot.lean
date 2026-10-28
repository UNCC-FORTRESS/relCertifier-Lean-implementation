/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_girard08_robot` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_girard08_robot`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `lit_girard08_robot` (emitted, suite_v2, widened cut channel on). -/
def lit_girard08_robot_coverV2 : CoverEmitE :=
  ⟨"lit_girard08_robot", [], [
    ⟨"M1", (1 : ℚ) / 1, 1, [⟨"M1", true, false, false⟩, ⟨"M2", false, false, false⟩, ⟨"M3", false, false, false⟩, ⟨"M4", false, false, false⟩, ⟨"M5", false, false, false⟩, ⟨"M6", false, false, false⟩], ["M1", "M2", "M3", "M4", "M6"], [⟨"M1", [0, 1, 2, 3, 4], [0, 2, 3, 4], [0, 2, 3, 4], 1, 1⟩, ⟨"M2", [1, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩, ⟨"M3", [1, 3, 4], [1, 3, 4], [1, 3, 4], 1, 1⟩, ⟨"M4", [1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"M5", [1, 2, 4], [1, 2, 4], [1, 2, 4], 1, 1⟩, ⟨"M6", [1, 2, 4], [0, 2, 4], [0, 2, 4], 1, 1⟩]⟩,
    ⟨"M2", (1 : ℚ) / 1, 1, [⟨"M1", false, false, false⟩, ⟨"M2", true, false, false⟩, ⟨"M3", false, false, false⟩, ⟨"M4", false, false, false⟩, ⟨"M5", false, false, false⟩, ⟨"M6", false, false, false⟩], ["M1", "M2", "M3"], [⟨"M1", [0, 2, 4], [0, 2, 3, 4], [0, 2, 3, 4], 1, 1⟩, ⟨"M2", [0, 1, 2, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩, ⟨"M3", [1, 2, 3, 4], [1, 3, 4], [1, 3, 4], 1, 1⟩, ⟨"M4", [1, 2, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"M5", [1, 2, 4], [1, 2, 4], [1, 2, 4], 1, 1⟩, ⟨"M6", [0, 1, 2, 4], [0, 2, 4], [0, 2, 4], 1, 1⟩]⟩,
    ⟨"M3", (1 : ℚ) / 1, 1, [⟨"M1", false, false, false⟩, ⟨"M2", false, false, false⟩, ⟨"M3", true, false, false⟩, ⟨"M4", false, false, false⟩, ⟨"M5", false, false, false⟩, ⟨"M6", false, false, false⟩], ["M1", "M2", "M3", "M4", "M6"], [⟨"M1", [0, 2, 4], [0, 2, 3, 4], [0, 2, 3, 4], 1, 1⟩, ⟨"M2", [0, 2, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩, ⟨"M3", [0, 1, 2, 3, 4], [1, 3, 4], [1, 3, 4], 1, 1⟩, ⟨"M4", [1, 2, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"M5", [0, 1, 2, 4], [1, 2, 4], [1, 2, 4], 1, 1⟩, ⟨"M6", [0, 2, 4], [0, 2, 4], [0, 2, 4], 1, 1⟩]⟩,
    ⟨"M4", (1 : ℚ) / 1, 1, [⟨"M1", false, false, false⟩, ⟨"M2", false, false, false⟩, ⟨"M3", false, false, false⟩, ⟨"M4", true, false, false⟩, ⟨"M5", false, false, false⟩, ⟨"M6", false, false, false⟩], ["M1", "M3", "M4", "M5", "M6"], [⟨"M1", [0, 2, 3, 4], [0, 2, 3, 4], [0, 2, 3, 4], 1, 1⟩, ⟨"M2", [0, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩, ⟨"M3", [0, 3, 4], [1, 3, 4], [1, 3, 4], 1, 1⟩, ⟨"M4", [0, 1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"M5", [0, 2, 4], [1, 2, 4], [1, 2, 4], 1, 1⟩, ⟨"M6", [0, 2, 4], [0, 2, 4], [0, 2, 4], 1, 1⟩]⟩,
    ⟨"M5", (1 : ℚ) / 1, 1, [⟨"M1", false, false, false⟩, ⟨"M2", false, false, false⟩, ⟨"M3", false, false, false⟩, ⟨"M4", false, false, false⟩, ⟨"M5", true, false, false⟩, ⟨"M6", false, false, false⟩], ["M4", "M5", "M6"], [⟨"M1", [0, 3, 4], [0, 2, 3, 4], [0, 2, 3, 4], 1, 1⟩, ⟨"M2", [0, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩, ⟨"M3", [0, 1, 3, 4], [1, 3, 4], [1, 3, 4], 1, 1⟩, ⟨"M4", [1, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"M5", [0, 1, 2, 3, 4], [1, 2, 4], [1, 2, 4], 1, 1⟩, ⟨"M6", [0, 2, 3, 4], [0, 2, 4], [0, 2, 4], 1, 1⟩]⟩,
    ⟨"M6", (1 : ℚ) / 1, 1, [⟨"M1", false, false, false⟩, ⟨"M2", false, false, false⟩, ⟨"M3", false, false, false⟩, ⟨"M4", false, false, false⟩, ⟨"M5", false, false, false⟩, ⟨"M6", true, false, false⟩], ["M1", "M3", "M4", "M5", "M6"], [⟨"M1", [0, 3, 4], [0, 2, 3, 4], [0, 2, 3, 4], 1, 1⟩, ⟨"M2", [0, 1, 3, 4], [0, 3, 4], [0, 3, 4], 1, 1⟩, ⟨"M3", [1, 3, 4], [1, 3, 4], [1, 3, 4], 1, 1⟩, ⟨"M4", [1, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩, ⟨"M5", [1, 2, 3, 4], [1, 2, 4], [1, 2, 4], 1, 1⟩, ⟨"M6", [0, 1, 2, 3, 4], [0, 2, 4], [0, 2, 4], 1, 1⟩]⟩]⟩

end RelCertifier
