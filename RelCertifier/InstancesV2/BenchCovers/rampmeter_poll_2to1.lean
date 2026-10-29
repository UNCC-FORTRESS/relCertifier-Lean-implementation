/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rampmeter_poll_2to1` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rampmeter_poll_2to1`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rampmeter_poll_2to1` (emitted, suite_v2, widened cut channel on). -/
def rampmeter_poll_2to1_coverV2 : CoverEmitE :=
  ⟨"rampmeter_poll_2to1", [("R1440", "R1800")], [
    ⟨"R1800", (1 : ℚ) / 1, 2, [⟨"R1800", true, false, false⟩, ⟨"R1440", true, false, false⟩, ⟨"R1200", true, false, false⟩, ⟨"R960", true, false, false⟩, ⟨"R720", false, false, false⟩, ⟨"R480", false, false, false⟩], ["R1800", "R1440", "R1200"], [⟨"R1800", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1440", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1200", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R960", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R720", [0, 1, 2, 3, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R480", [0, 1, 2, 3, 5], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"R1440", (1 : ℚ) / 1, 2, [⟨"R1800", true, false, false⟩, ⟨"R1440", true, false, false⟩, ⟨"R1200", true, false, false⟩, ⟨"R960", true, false, false⟩, ⟨"R720", true, false, false⟩, ⟨"R480", true, false, false⟩], ["R1800", "R1440", "R1200", "R960"], [⟨"R1800", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1440", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1200", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R960", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R720", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R480", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"R1200", (1 : ℚ) / 1, 2, [⟨"R1800", true, false, false⟩, ⟨"R1440", true, false, false⟩, ⟨"R1200", true, false, false⟩, ⟨"R960", true, false, false⟩, ⟨"R720", true, false, false⟩, ⟨"R480", true, false, false⟩], ["R1800", "R1440", "R1200", "R960", "R720"], [⟨"R1800", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1440", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1200", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R960", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R720", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R480", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"R960", (1 : ℚ) / 1, 2, [⟨"R1800", true, false, false⟩, ⟨"R1440", true, false, false⟩, ⟨"R1200", true, false, false⟩, ⟨"R960", true, false, false⟩, ⟨"R720", true, false, false⟩, ⟨"R480", true, false, false⟩], ["R1440", "R1200", "R960", "R720", "R480"], [⟨"R1800", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1440", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1200", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R960", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R720", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R480", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"R720", (1 : ℚ) / 1, 2, [⟨"R1800", false, false, false⟩, ⟨"R1440", true, false, false⟩, ⟨"R1200", true, false, false⟩, ⟨"R960", true, false, false⟩, ⟨"R720", true, false, false⟩, ⟨"R480", true, false, false⟩], ["R1200", "R960", "R720", "R480"], [⟨"R1800", [0, 1, 2, 3, 4], [0, 1], [0, 1], 1, 1⟩, ⟨"R1440", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1200", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R960", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R720", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R480", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩]⟩,
    ⟨"R480", (1 : ℚ) / 1, 2, [⟨"R1800", false, false, false⟩, ⟨"R1440", true, false, false⟩, ⟨"R1200", true, false, false⟩, ⟨"R960", true, false, false⟩, ⟨"R720", true, false, false⟩, ⟨"R480", true, false, false⟩], ["R960", "R720", "R480"], [⟨"R1800", [0, 1, 2, 3, 4], [0, 1], [0, 1], 1, 1⟩, ⟨"R1440", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R1200", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R960", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R720", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩, ⟨"R480", [0, 1, 2, 3, 4, 5], [0, 1], [0, 1], 1, 1⟩]⟩]⟩

end RelCertifier
