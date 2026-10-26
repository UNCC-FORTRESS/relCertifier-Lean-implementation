/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `tank_dos_3to1` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py tank_dos_3to1`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `tank_dos_3to1` (emitted, suite_v2, widened cut channel on). -/
def tank_dos_3to1_coverV2 : CoverEmitE :=
  ⟨"tank_dos_3to1", [], [
    ⟨"HIGH", (1 : ℚ) / 1, 3, [⟨"HIGH", true, false, false⟩, ⟨"LOW", true, false, false⟩], ["HIGH", "LOW"], [⟨"HIGH", [0, 1], [0], [0], 1, 1⟩, ⟨"LOW", [0, 1], [1], [1], 1, 1⟩]⟩,
    ⟨"LOW", (1 : ℚ) / 1, 3, [⟨"HIGH", true, false, false⟩, ⟨"LOW", true, false, false⟩], ["HIGH", "LOW"], [⟨"HIGH", [0, 1], [0], [0], 1, 1⟩, ⟨"LOW", [0, 1], [1], [1], 1, 1⟩]⟩]⟩

end RelCertifier
