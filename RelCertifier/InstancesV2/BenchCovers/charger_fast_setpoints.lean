/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py charger_fast_setpoints`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `charger_fast_setpoints` (emitted, suite_v2, widened cut channel on). -/
def charger_fast_setpoints_coverV2 : CoverEmitE :=
  ⟨"charger_fast_setpoints", [("PRECHARGE", "FAULT"), ("BULK", "FAULT")], [
    ⟨"PRECHARGE", (1 : ℚ) / 1, 2, [⟨"PRECHARGE", false, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", false, false, false⟩], ["PRECHARGE", "BULK", "ABSORB", "FULL"], [⟨"PRECHARGE", [], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [], [], [], 1, 1⟩]⟩,
    ⟨"BULK", (1 : ℚ) / 1, 2, [⟨"PRECHARGE", false, true, true⟩, ⟨"BULK", false, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["PRECHARGE", "BULK", "ABSORB", "FULL"], [⟨"PRECHARGE", [], [0], [0], 1, 1⟩, ⟨"BULK", [], [0], [0], 1, 1⟩, ⟨"ABSORB", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩,
    ⟨"ABSORB", (1 : ℚ) / 1, 2, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", false, true, true⟩, ⟨"ABSORB", false, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["BULK", "ABSORB", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 1, 1⟩, ⟨"BULK", [], [0], [0], 1, 1⟩, ⟨"ABSORB", [], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩,
    ⟨"FULL", (1 : ℚ) / 1, 2, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["ABSORB", "FULL"], [⟨"PRECHARGE", [0], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩,
    ⟨"FAULT", (1 : ℚ) / 1, 2, [⟨"PRECHARGE", true, true, true⟩, ⟨"BULK", true, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, false, false⟩, ⟨"FAULT", true, false, false⟩], ["PRECHARGE", "BULK", "ABSORB", "FULL", "FAULT"], [⟨"PRECHARGE", [0], [0], [0], 1, 1⟩, ⟨"BULK", [0], [0], [0], 1, 1⟩, ⟨"ABSORB", [0], [0], [0], 1, 1⟩, ⟨"FULL", [0], [0], [0], 1, 1⟩, ⟨"FAULT", [0], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
