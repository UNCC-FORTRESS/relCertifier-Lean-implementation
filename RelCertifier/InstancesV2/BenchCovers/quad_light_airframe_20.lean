/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_airframe_20`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `quad_light_airframe_20` (emitted, suite_v2, widened cut channel on). -/
def quad_light_airframe_20_coverV2 : CoverEmitE :=
  ⟨"quad_light_airframe_20", [], [
    ⟨"CLIMB", (6 : ℚ) / 5, 2, [⟨"CLIMB", true, false, false⟩], ["CLIMB"], [⟨"CLIMB", [2, 3, 0, 1], [1, 2], [1, 2], 6, 5⟩]⟩]⟩

end RelCertifier
