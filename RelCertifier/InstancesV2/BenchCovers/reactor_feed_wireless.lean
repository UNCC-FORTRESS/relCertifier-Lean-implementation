/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `reactor_feed_wireless` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py reactor_feed_wireless`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `reactor_feed_wireless` (emitted, suite_v2, widened cut channel on). -/
def reactor_feed_wireless_coverV2 : CoverEmitE :=
  ⟨"reactor_feed_wireless", [("F1", "F4"), ("F2", "F4"), ("F3", "F1"), ("F4", "F1")], [
    ⟨"F1", (1 : ℚ) / 1, 2, [⟨"F1", true, false, false⟩, ⟨"F2", true, false, false⟩, ⟨"F3", true, false, false⟩, ⟨"F4", false, false, false⟩], ["F1", "F2"], [⟨"F1", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F4", [0, 2, 3], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"F2", (1 : ℚ) / 1, 2, [⟨"F1", true, false, false⟩, ⟨"F2", true, false, false⟩, ⟨"F3", true, false, false⟩, ⟨"F4", true, false, false⟩], ["F1", "F2", "F3"], [⟨"F1", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F4", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"F3", (1 : ℚ) / 1, 2, [⟨"F1", true, false, false⟩, ⟨"F2", true, false, false⟩, ⟨"F3", true, false, false⟩, ⟨"F4", true, false, false⟩], ["F2", "F3", "F4"], [⟨"F1", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F4", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩,
    ⟨"F4", (1 : ℚ) / 1, 2, [⟨"F1", false, false, false⟩, ⟨"F2", true, false, false⟩, ⟨"F3", true, false, false⟩, ⟨"F4", true, false, false⟩], ["F3", "F4"], [⟨"F1", [1, 2, 3], [2, 3], [2, 3], 1, 1⟩, ⟨"F2", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F3", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩, ⟨"F4", [2, 3, 0, 1], [2, 3], [2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
