/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat_detumble_weak` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py sat_detumble_weak`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `sat_detumble_weak` (emitted, suite_v2, widened cut channel on). -/
def sat_detumble_weak_coverV2 : CoverEmitE :=
  ⟨"sat_detumble_weak", [("NOMINAL", "SAFE"), ("ECONOMY", "SAFE"), ("SURVIVAL", "SAFE")], [
    ⟨"DETUMBLE", (4 : ℚ) / 5, 2, [⟨"NOMINAL", true, false, false⟩, ⟨"ECONOMY", false, false, false⟩, ⟨"SURVIVAL", false, false, false⟩, ⟨"SAFE", false, false, false⟩], ["NOMINAL", "ECONOMY", "SURVIVAL"], [⟨"NOMINAL", [0, 1], [1], [1], 4, 5⟩, ⟨"ECONOMY", [0], [1], [1], 4, 5⟩, ⟨"SURVIVAL", [0], [1], [1], 4, 5⟩, ⟨"SAFE", [0], [0, 1], [0, 1], 4, 5⟩]⟩]⟩

end RelCertifier
