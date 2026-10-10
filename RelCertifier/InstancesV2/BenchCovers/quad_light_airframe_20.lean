/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `quad_light_airframe_20` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py quad_light_airframe_20`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `quad_light_airframe_20` (emitted, suite_v2, widened cut channel on). -/
def quad_light_airframe_20_coverV2 : CoverEmitE :=
  ⟨"quad_light_airframe_20", [("CLIMB", "LIMIT")], [
    ⟨"CLIMB", (7 : ℚ) / 4, 4, [⟨"CLIMB", true, false, false⟩, ⟨"LIMIT", false, false, false⟩], ["CLIMB"], [⟨"CLIMB", [0, 1], [], []⟩, ⟨"LIMIT", [1], [1], [1]⟩]⟩]⟩

end RelCertifier
