/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `extruder_pe100_manualstart` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py extruder_pe100_manualstart`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `extruder_pe100_manualstart` (emitted, suite_v2, widened cut channel on). -/
def extruder_pe100_manualstart_coverV2 : CoverEmitE :=
  ⟨"extruder_pe100_manualstart", [("N1", "N4"), ("N2", "N4"), ("N3", "N1"), ("N4", "N1")], [
    ⟨"N1", (1 : ℚ) / 1, 2, [⟨"N1", true, false, false⟩, ⟨"N2", true, false, false⟩, ⟨"N3", true, false, false⟩, ⟨"N4", false, false, false⟩], ["N1", "N2"], [⟨"N1", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N4", [2, 3, 0], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"N2", (1 : ℚ) / 1, 2, [⟨"N1", true, false, false⟩, ⟨"N2", true, false, false⟩, ⟨"N3", true, false, false⟩, ⟨"N4", true, false, false⟩], ["N1", "N2", "N3"], [⟨"N1", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N4", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"N3", (1 : ℚ) / 1, 2, [⟨"N1", true, false, false⟩, ⟨"N2", true, false, false⟩, ⟨"N3", true, false, false⟩, ⟨"N4", true, false, false⟩], ["N2", "N3", "N4"], [⟨"N1", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N4", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"N4", (1 : ℚ) / 1, 2, [⟨"N1", false, false, false⟩, ⟨"N2", true, false, false⟩, ⟨"N3", true, false, false⟩, ⟨"N4", true, false, false⟩], ["N3", "N4"], [⟨"N1", [2, 3, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"N4", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
