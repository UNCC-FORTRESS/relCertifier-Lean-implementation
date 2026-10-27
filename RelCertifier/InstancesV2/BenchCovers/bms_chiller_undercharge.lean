/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bms_chiller_undercharge` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py bms_chiller_undercharge`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `bms_chiller_undercharge` (emitted, suite_v2, widened cut channel on). -/
def bms_chiller_undercharge_coverV2 : CoverEmitE :=
  ⟨"bms_chiller_undercharge", [], [
    ⟨"COAST", (1 : ℚ) / 1, 1, [⟨"COAST", true, false, false⟩, ⟨"CHILL_LO", false, false, false⟩, ⟨"CHILL_HI", false, false, false⟩], ["COAST", "CHILL_LO", "CHILL_HI"], [⟨"COAST", [0, 1], [0], [0], 1, 1⟩, ⟨"CHILL_LO", [1], [], [], 1, 1⟩, ⟨"CHILL_HI", [1], [1], [1], 1, 1⟩]⟩,
    ⟨"CHILL", (1 : ℚ) / 1, 1, [⟨"COAST", false, false, false⟩, ⟨"CHILL_LO", true, false, false⟩, ⟨"CHILL_HI", false, false, false⟩], ["COAST", "CHILL_LO", "CHILL_HI"], [⟨"COAST", [0], [0], [0], 1, 1⟩, ⟨"CHILL_LO", [0, 1], [], [], 1, 1⟩, ⟨"CHILL_HI", [1], [1], [1], 1, 1⟩]⟩]⟩

end RelCertifier
