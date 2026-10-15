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
  ⟨"quad_light_profiles", [("NORMAL", "LIMIT"), ("ECO", "LIMIT"), ("SPORT", "LIMIT")], [
    ⟨"CLIMB", (5 : ℚ) / 2, 5, [⟨"NORMAL", true, false, false⟩, ⟨"ECO", true, false, false⟩, ⟨"SPORT", true, false, false⟩, ⟨"LIMIT", false, false, false⟩], ["NORMAL", "ECO", "SPORT"], [⟨"NORMAL", [0, 1], [], [], 5, 2⟩, ⟨"ECO", [0, 1], [], [], 5, 2⟩, ⟨"SPORT", [0, 1], [], [], 5, 2⟩, ⟨"LIMIT", [1], [1], [1], 5, 2⟩]⟩]⟩

end RelCertifier
