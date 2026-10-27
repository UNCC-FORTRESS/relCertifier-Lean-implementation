/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_profiles` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_profiles`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `quad_light_profiles` (emitted, suite_v2, widened cut channel on). -/
def quad_light_profiles_coverV2 : CoverEmitE :=
  ⟨"quad_light_profiles", [], [
    ⟨"CLIMB", (1 : ℚ) / 1, 1, [⟨"NORMAL", false, false, false⟩, ⟨"ECO", false, false, false⟩, ⟨"SPORT", true, false, false⟩], ["NORMAL", "ECO", "SPORT"], [⟨"NORMAL", [3, 0], [1, 2], [1, 2], 1, 1⟩, ⟨"ECO", [3, 0], [1, 2], [1, 2], 1, 1⟩, ⟨"SPORT", [2, 3, 0, 1], [1, 2], [1, 2], 1, 1⟩]⟩]⟩

end RelCertifier
