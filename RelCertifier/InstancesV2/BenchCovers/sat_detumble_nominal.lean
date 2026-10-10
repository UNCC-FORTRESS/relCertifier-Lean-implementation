/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_nominal` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py sat_detumble_nominal`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `sat_detumble_nominal` (emitted, suite_v2, widened cut channel on). -/
def sat_detumble_nominal_coverV2 : CoverEmitE :=
  ⟨"sat_detumble_nominal", [("DETUMBLE", "SAFE")], [
    ⟨"DETUMBLE", (1 : ℚ) / 1, 2, [⟨"DETUMBLE", true, false, false⟩, ⟨"SAFE", false, true, true⟩], ["DETUMBLE"], [⟨"DETUMBLE", [0, 1], [1], [1]⟩, ⟨"SAFE", [0], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
