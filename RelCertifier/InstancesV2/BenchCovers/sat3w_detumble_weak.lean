/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `sat3w_detumble_weak` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py sat3w_detumble_weak`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `sat3w_detumble_weak` (emitted, suite_v2, widened cut channel on). -/
def sat3w_detumble_weak_coverV2 : CoverEmitE :=
  ⟨"sat3w_detumble_weak", [("NOMINAL", "SAFE"), ("ECONOMY", "SAFE"), ("SURVIVAL", "SAFE")], [
    ⟨"DETUMBLE", (1 : ℚ) / 1, 2, [⟨"NOMINAL", true, false, false⟩, ⟨"ECONOMY", true, false, false⟩, ⟨"SURVIVAL", true, false, false⟩, ⟨"SAFE", false, true, true⟩], ["NOMINAL", "ECONOMY", "SURVIVAL"], [⟨"NOMINAL", [0, 1], [1], [1]⟩, ⟨"ECONOMY", [0, 1], [1], [1]⟩, ⟨"SURVIVAL", [0, 1], [1], [1]⟩, ⟨"SAFE", [0], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
