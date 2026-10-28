/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `lit_lz21_vehicle_position` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py lit_lz21_vehicle_position`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `lit_lz21_vehicle_position` (emitted, suite_v2, widened cut channel on). -/
def lit_lz21_vehicle_position_coverV2 : CoverEmitE :=
  ⟨"lit_lz21_vehicle_position", [], [
    ⟨"Um", (1 : ℚ) / 1, 1, [⟨"Um", true, false, false⟩, ⟨"U0", false, false, false⟩, ⟨"Up", false, false, false⟩], ["Um", "U0", "Up"], [⟨"Um", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"U0", [0, 2], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Up", [0, 2], [0, 2], [0, 2], 1, 1⟩]⟩,
    ⟨"U0", (1 : ℚ) / 1, 1, [⟨"Um", false, false, false⟩, ⟨"U0", true, false, false⟩, ⟨"Up", false, false, false⟩], ["Um", "U0", "Up"], [⟨"Um", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"U0", [0, 1, 2, 3], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Up", [0, 2], [0, 2], [0, 2], 1, 1⟩]⟩,
    ⟨"Up", (1 : ℚ) / 1, 1, [⟨"Um", false, false, false⟩, ⟨"U0", false, false, false⟩, ⟨"Up", true, false, false⟩], ["Um", "U0", "Up"], [⟨"Um", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"U0", [1, 3], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Up", [0, 1, 2, 3], [0, 2], [0, 2], 1, 1⟩]⟩]⟩

end RelCertifier
