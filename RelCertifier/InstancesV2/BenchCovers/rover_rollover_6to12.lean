/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_6to12` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_rollover_6to12`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_rollover_6to12` (emitted, suite_v2, widened cut channel on). -/
def rover_rollover_6to12_coverV2 : CoverEmitE :=
  ⟨"rover_rollover_6to12", [], [
    ⟨"STEEP", (5 : ℚ) / 4, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩, ⟨"MODER", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩]⟩,
    ⟨"MODER", (5 : ℚ) / 4, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩, ⟨"MODER", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩]⟩,
    ⟨"FLAT", (5 : ℚ) / 4, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩, ⟨"MODER", [2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], 5, 4⟩]⟩]⟩

end RelCertifier
