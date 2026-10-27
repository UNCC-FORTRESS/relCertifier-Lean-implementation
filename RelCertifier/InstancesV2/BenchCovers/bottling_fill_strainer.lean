/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `bottling_fill_strainer` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py bottling_fill_strainer`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `bottling_fill_strainer` (emitted, suite_v2, widened cut channel on). -/
def bottling_fill_strainer_coverV2 : CoverEmitE :=
  ⟨"bottling_fill_strainer", [], [
    ⟨"FILL", (17 : ℚ) / 20, 1, [⟨"FILL", true, false, false⟩, ⟨"CLOSE", false, false, false⟩], ["FILL"], [⟨"FILL", [0, 1, 2, 3, 4], [0, 2, 3], [0, 2, 3], 17, 20⟩, ⟨"CLOSE", [1, 4], [0, 1, 3], [0, 1, 3], 17, 20⟩]⟩,
    ⟨"CLOSE", (1 : ℚ) / 1, 1, [⟨"FILL", false, false, false⟩, ⟨"CLOSE", true, false, false⟩], ["CLOSE"], [⟨"FILL", [0, 2, 3], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"CLOSE", [0, 1, 2, 3, 4], [0, 1, 3], [0, 1, 3], 1, 1⟩]⟩]⟩

end RelCertifier
