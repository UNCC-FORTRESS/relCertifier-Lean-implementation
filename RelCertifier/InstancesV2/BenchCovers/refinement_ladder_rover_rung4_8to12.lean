/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung4_8to12` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung4_8to12`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung4_8to12` (emitted, suite_v2, widened cut channel on). -/
def refinement_ladder_rover_rung4_8to12_coverV2 : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung4_8to12", [], [
    ⟨"STEEP", (17 : ℚ) / 10, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MODER", (17 : ℚ) / 10, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"FLAT", (17 : ℚ) / 10, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
