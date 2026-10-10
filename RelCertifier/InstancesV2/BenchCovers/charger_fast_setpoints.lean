/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `charger_fast_setpoints` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py charger_fast_setpoints`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `charger_fast_setpoints` (emitted, suite_v2, widened cut channel on). -/
def charger_fast_setpoints_coverV2 : CoverEmitE :=
  ⟨"charger_fast_setpoints", [("BULK", "FAULT")], [
    ⟨"BULK", (1 : ℚ) / 1, 2, [⟨"BULK", false, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, true, true⟩, ⟨"FAULT", false, false, false⟩], ["BULK", "ABSORB", "FULL"], [⟨"BULK", [], [0], [0]⟩, ⟨"ABSORB", [0], [0], [0]⟩, ⟨"FULL", [0], [0], [0]⟩, ⟨"FAULT", [], [], []⟩]⟩,
    ⟨"ABSORB", (1 : ℚ) / 1, 2, [⟨"BULK", false, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, true, true⟩, ⟨"FAULT", true, false, false⟩], ["BULK", "ABSORB", "FULL"], [⟨"BULK", [], [0], [0]⟩, ⟨"ABSORB", [0], [0], [0]⟩, ⟨"FULL", [0], [0], [0]⟩, ⟨"FAULT", [0], [], []⟩]⟩,
    ⟨"FULL", (1 : ℚ) / 1, 2, [⟨"BULK", true, true, true⟩, ⟨"ABSORB", true, true, true⟩, ⟨"FULL", true, true, true⟩, ⟨"FAULT", true, false, false⟩], ["ABSORB", "FULL"], [⟨"BULK", [0], [0], [0]⟩, ⟨"ABSORB", [0], [0], [0]⟩, ⟨"FULL", [0], [0], [0]⟩, ⟨"FAULT", [0], [], []⟩]⟩]⟩

end RelCertifier
