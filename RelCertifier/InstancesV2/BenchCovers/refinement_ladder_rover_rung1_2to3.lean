/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung1_2to3` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung1_2to3`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung1_2to3` (emitted, suite_v2, widened cut channel on). -/
def refinement_ladder_rover_rung1_2to3_coverV2 : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung1_2to3", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
