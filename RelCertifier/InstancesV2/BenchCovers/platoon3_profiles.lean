/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon3_profiles` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon3_profiles`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `platoon3_profiles` (emitted, suite_v2, widened cut channel on). -/
def platoon3_profiles_coverV2 : CoverEmitE :=
  ⟨"platoon3_profiles", [("NORMAL", "BRAKE1"),
 ("NORMAL", "BRAKE2"),
 ("NORMAL", "BRAKE3"),
 ("CLOSE", "BRAKE1"),
 ("CLOSE", "BRAKE2"),
 ("CLOSE", "BRAKE3"),
 ("FAR", "BRAKE1"),
 ("FAR", "BRAKE2"),
 ("FAR", "BRAKE3")], [
    ⟨"FOLLOW", (1 : ℚ) / 1, 2, [⟨"NORMAL", true, false, false⟩, ⟨"CLOSE", true, false, false⟩, ⟨"FAR", true, false, false⟩, ⟨"BRAKE1", false, false, false⟩, ⟨"BRAKE2", false, false, false⟩, ⟨"BRAKE3", false, false, false⟩], ["NORMAL", "CLOSE", "FAR"], [⟨"NORMAL", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], [], []⟩, ⟨"CLOSE", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], [], []⟩, ⟨"FAR", [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17], [], []⟩, ⟨"BRAKE1", [1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 14, 15, 16, 17], [2, 3], [2, 3]⟩, ⟨"BRAKE2", [0, 1, 2, 3, 5, 7, 8, 9, 10, 11, 12, 13, 15, 16, 17], [6, 7], [6, 7]⟩, ⟨"BRAKE3", [0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 13, 14, 15, 17], [10, 11], [10, 11]⟩]⟩]⟩

end RelCertifier
