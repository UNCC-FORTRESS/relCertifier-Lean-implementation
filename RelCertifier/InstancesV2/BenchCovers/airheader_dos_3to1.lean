/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `airheader_dos_3to1` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py airheader_dos_3to1`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `airheader_dos_3to1` (emitted, suite_v2, widened cut channel on). -/
def airheader_dos_3to1_coverV2 : CoverEmitE :=
  ⟨"airheader_dos_3to1", [("NORMAL", "TRIP"), ("ALARM", "TRIP")], [
    ⟨"NORMAL", (1 : ℚ) / 1, 3, [⟨"NORMAL", true, false, false⟩, ⟨"ALARM", true, false, false⟩, ⟨"TRIP", false, false, false⟩], ["NORMAL"], [⟨"NORMAL", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"ALARM", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"TRIP", [1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"ALARM", (1 : ℚ) / 1, 3, [⟨"NORMAL", true, false, false⟩, ⟨"ALARM", true, false, false⟩, ⟨"TRIP", false, false, false⟩], ["ALARM"], [⟨"NORMAL", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"ALARM", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"TRIP", [1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"TRIP", (1 : ℚ) / 1, 3, [⟨"NORMAL", false, false, false⟩, ⟨"ALARM", false, false, false⟩, ⟨"TRIP", true, false, false⟩], ["TRIP"], [⟨"NORMAL", [0, 2, 3], [2, 3], [2, 3], 1, 1⟩, ⟨"ALARM", [0, 2, 3], [2, 3], [2, 3], 1, 1⟩, ⟨"TRIP", [2, 3, 0, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
