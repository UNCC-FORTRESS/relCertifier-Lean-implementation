/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_delay_linkloss` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_delay_linkloss`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `platoon_delay_linkloss` (emitted, suite_v2, widened cut channel on). -/
def platoon_delay_linkloss_coverV2 : CoverEmitE :=
  ⟨"platoon_delay_linkloss", [("FOLLOW", "BRAKE")], [
    ⟨"FOLLOW", (1 : ℚ) / 1, 2, [⟨"FOLLOW", true, false, false⟩, ⟨"CATCH", true, false, false⟩, ⟨"BRAKE", false, false, false⟩], ["FOLLOW", "CATCH"], [⟨"FOLLOW", [0, 1], [], []⟩, ⟨"CATCH", [0, 1], [1], [1]⟩, ⟨"BRAKE", [], [0], [0]⟩]⟩,
    ⟨"CATCH", (1 : ℚ) / 1, 2, [⟨"FOLLOW", true, false, false⟩, ⟨"CATCH", true, false, false⟩, ⟨"BRAKE", false, false, false⟩], ["FOLLOW", "CATCH"], [⟨"FOLLOW", [0, 1], [], []⟩, ⟨"CATCH", [0, 1], [1], [1]⟩, ⟨"BRAKE", [0], [0], [0]⟩]⟩,
    ⟨"LOST", (1 : ℚ) / 1, 2, [⟨"FOLLOW", true, false, false⟩, ⟨"CATCH", true, false, false⟩, ⟨"BRAKE", false, false, false⟩], ["FOLLOW", "CATCH"], [⟨"FOLLOW", [0, 1], [], []⟩, ⟨"CATCH", [0, 1], [1], [1]⟩, ⟨"BRAKE", [], [0], [0]⟩]⟩]⟩

end RelCertifier
