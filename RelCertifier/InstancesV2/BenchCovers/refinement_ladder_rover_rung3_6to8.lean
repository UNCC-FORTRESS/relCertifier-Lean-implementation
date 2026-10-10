/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung3_6to8` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung3_6to8`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung3_6to8` (emitted, suite_v2, widened cut channel on). -/
def refinement_ladder_rover_rung3_6to8_coverV2 : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung3_6to8", [], [
    ⟨"STEEP", (9 : ℚ) / 4, 3, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩,
    ⟨"MODER", (9 : ℚ) / 4, 3, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩,
    ⟨"FLAT", (9 : ℚ) / 4, 3, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"MODER", [2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩, ⟨"FLAT", [0, 1, 2, 3], [0, 1, 2, 3], [0, 1, 2, 3]⟩]⟩]⟩

end RelCertifier
