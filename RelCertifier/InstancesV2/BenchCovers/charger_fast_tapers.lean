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
  ⟨"charger_fast_tapers", [("PRECHARGE", "FAULT"), ("BULK", "FAULT")], [
    ⟨"PRECHARGE", (1 : ℚ) / 1, 1, [⟨"PRECHARGE", false, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", true, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", false, false, false⟩], ["PRECHARGE", "BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_SLOW", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_FAST", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [], [], [], 1, 1⟩]⟩,
    ⟨"BULK", (1 : ℚ) / 1, 1, [⟨"PRECHARGE", false, true, true⟩, ⟨"BULK", false, true, true⟩, ⟨"ABSORB_SLOW", false, true, true⟩, ⟨"ABSORB_FAST", false, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["PRECHARGE", "BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [], [0], [0], 1, 1⟩, ⟨"BULK", [], [0], [0], 1, 1⟩, ⟨"ABSORB_SLOW", [], [0], [0], 1, 1⟩, ⟨"ABSORB_FAST", [], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩,
    ⟨"ABSORB", (1 : ℚ) / 1, 1, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", false, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_SLOW", [], [0], [0], 1, 1⟩, ⟨"ABSORB_FAST", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩,
    ⟨"FULL", (1 : ℚ) / 1, 1, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", true, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["ABSORB_SLOW", "ABSORB_FAST", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_SLOW", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_FAST", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩,
    ⟨"FAULT", (1 : ℚ) / 1, 1, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB_SLOW", true, true, true⟩, ⟨"ABSORB_FAST", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["PRECHARGE", "BULK", "ABSORB_SLOW", "ABSORB_FAST", "FULL", "FAULT"], [⟨"PRECHARGE", [0], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_SLOW", [0], [0], [0], 1, 1⟩, ⟨"ABSORB_FAST", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
