/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `platoon_profiles` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py platoon_profiles`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `platoon_profiles` (emitted, suite_v2, widened cut channel on). -/
def platoon_profiles_coverV2 : CoverEmitE :=
  ⟨"platoon_profiles", [], [
    ⟨"SPORT", (6 : ℚ) / 5, 2, [⟨"CACC", true, false, false⟩], ["CACC"], [⟨"CACC", [2, 3, 4, 5, 6, 7, 0, 1], [6, 7], [6, 7], 6, 5⟩]⟩]⟩

end RelCertifier
