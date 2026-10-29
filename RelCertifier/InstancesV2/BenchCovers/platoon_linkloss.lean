/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_linkloss` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_linkloss`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `platoon_linkloss` (emitted, suite_v2, widened cut channel on). -/
def platoon_linkloss_coverV2 : CoverEmitE :=
  ⟨"platoon_linkloss", [], [
    ⟨"CACC", (1 : ℚ) / 1, 2, [⟨"CACC", true, false, false⟩], ["CACC"], [⟨"CACC", [0, 1, 2, 3, 4, 5, 6, 7], [6, 7], [6, 7], 1, 1⟩]⟩,
    ⟨"ACC", (1 : ℚ) / 1, 2, [⟨"CACC", true, false, false⟩], ["CACC"], [⟨"CACC", [0, 1, 2, 3, 4, 5, 6, 7], [6, 7], [6, 7], 1, 1⟩]⟩]⟩

end RelCertifier
