/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_3to6` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_ladder_3to6`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_ladder_3to6` (emitted, suite_v2, widened cut channel on). -/
def rover_ladder_3to6_coverV2 : CoverEmitE :=
  ⟨"rover_ladder_3to6", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 2, 3, 4, 5, 1], [1, 4, 5], [1, 4, 5], 1, 1⟩, ⟨"MODER", [0, 2, 3, 4, 5, 1], [1, 4, 5], [1, 4, 5], 1, 1⟩, ⟨"FLAT", [0, 2, 3, 4, 5, 1], [1, 4, 5], [1, 4, 5], 1, 1⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3, 4, 5], [1, 4, 5], [1, 4, 5], 1, 1⟩, ⟨"MODER", [0, 2, 3, 4, 5, 1], [1, 4, 5], [1, 4, 5], 1, 1⟩, ⟨"FLAT", [0, 2, 3, 4, 5, 1], [1, 4, 5], [1, 4, 5], 1, 1⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 3, 4, 5], [1, 4, 5], [1, 4, 5], 1, 1⟩, ⟨"MODER", [2, 3, 4, 5], [1, 4, 5], [1, 4, 5], 1, 1⟩, ⟨"FLAT", [0, 2, 3, 4, 5, 1], [1, 4, 5], [1, 4, 5], 1, 1⟩]⟩]⟩

end RelCertifier
