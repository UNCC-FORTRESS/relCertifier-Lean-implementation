/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_linkloss` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon3_linkloss`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `platoon3_linkloss` (emitted, suite_v2, widened cut channel on). -/
def platoon3_linkloss_coverV2 : CoverEmitE :=
  ⟨"platoon3_linkloss", [("FOLLOW", "BRAKE1"), ("FOLLOW", "BRAKE2"), ("FOLLOW", "BRAKE3")], [
    ⟨"FOLLOW", (1 : ℚ) / 1, 2, [⟨"FOLLOW", true, false, false⟩, ⟨"BRAKE1", true, true, true⟩, ⟨"BRAKE2", true, true, true⟩, ⟨"BRAKE3", true, true, true⟩], ["FOLLOW"], [⟨"FOLLOW", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [], []⟩, ⟨"BRAKE1", [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0], [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1], [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 0, 1]⟩, ⟨"BRAKE2", [0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 4], [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11, 0, 1, 2, 3, 4, 5]⟩, ⟨"BRAKE3", [0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 8], [10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9], [10, 11, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9]⟩]⟩,
    ⟨"LOST", (1 : ℚ) / 1, 2, [⟨"FOLLOW", true, false, false⟩, ⟨"BRAKE1", false, false, false⟩, ⟨"BRAKE2", true, true, true⟩, ⟨"BRAKE3", true, true, true⟩], ["FOLLOW"], [⟨"FOLLOW", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13], [], []⟩, ⟨"BRAKE1", [1, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13], [2, 3], [2, 3]⟩, ⟨"BRAKE2", [0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 6], [8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 0, 1, 2, 3, 4, 5, 6, 7]⟩, ⟨"BRAKE3", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 10], [12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], [12, 13, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]⟩]⟩]⟩

end RelCertifier
