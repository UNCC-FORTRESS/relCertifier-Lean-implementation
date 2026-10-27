/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `fuelcell_chp_dos` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py fuelcell_chp_dos`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `fuelcell_chp_dos` (emitted, suite_v2, widened cut channel on). -/
def fuelcell_chp_dos_coverV2 : CoverEmitE :=
  ⟨"fuelcell_chp_dos", [("LOW", "HIGH"), ("HIGH", "LOW")], [
    ⟨"LOW", (1 : ℚ) / 1, 2, [⟨"LOW", true, false, false⟩, ⟨"MED", true, false, false⟩, ⟨"HIGH", false, false, false⟩], ["LOW", "MED"], [⟨"LOW", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"MED", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"HIGH", [0, 2, 3], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"MED", (1 : ℚ) / 1, 2, [⟨"LOW", true, false, false⟩, ⟨"MED", true, false, false⟩, ⟨"HIGH", true, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"MED", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"HIGH", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"HIGH", (1 : ℚ) / 1, 2, [⟨"LOW", false, false, false⟩, ⟨"MED", true, false, false⟩, ⟨"HIGH", true, false, false⟩], ["MED", "HIGH"], [⟨"LOW", [1, 2, 3], [2, 3], [2, 3], 1, 1⟩, ⟨"MED", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"HIGH", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
