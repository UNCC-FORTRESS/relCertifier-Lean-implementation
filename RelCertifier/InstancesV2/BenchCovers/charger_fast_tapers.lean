/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_tapers` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py charger_fast_tapers`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `charger_fast_tapers` (emitted, suite_v2, widened cut channel on). -/
def charger_fast_tapers_coverV2 : CoverEmitE :=
  ⟨"charger_fast_tapers", [], [
    ⟨"PRECHARGE", (5 : ℚ) / 4, 3, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", true, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩], ["PRECHARGE", "BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 5, 4⟩, ⟨"BULK", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_SLOW", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_FAST", [0], [0], [0], 5, 4⟩, ⟨"FULL", [0], [0], [0], 5, 4⟩]⟩,
    ⟨"BULK", (5 : ℚ) / 4, 3, [⟨"PRECHARGE", false, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", false, true, true⟩, ⟨"ABSORB_FAST", false, true, true⟩, ⟨"FULL", true, false, false⟩], ["PRECHARGE", "BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [], [0], [0], 5, 4⟩, ⟨"BULK", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_SLOW", [], [0], [0], 5, 4⟩, ⟨"ABSORB_FAST", [], [0], [0], 5, 4⟩, ⟨"FULL", [0], [0], [0], 5, 4⟩]⟩,
    ⟨"ABSORB", (5 : ℚ) / 4, 3, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", true, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩], ["BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 5, 4⟩, ⟨"BULK", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_SLOW", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_FAST", [0], [0], [0], 5, 4⟩, ⟨"FULL", [0], [0], [0], 5, 4⟩]⟩,
    ⟨"FULL", (5 : ℚ) / 4, 3, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", true, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩], ["ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 5, 4⟩, ⟨"BULK", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_SLOW", [0], [0], [0], 5, 4⟩, ⟨"ABSORB_FAST", [0], [0], [0], 5, 4⟩, ⟨"FULL", [0], [0], [0], 5, 4⟩]⟩]⟩

end RelCertifier
