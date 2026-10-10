/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2_6dof` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung2_6dof`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung2_6dof` (emitted, suite_v2, widened cut channel on). -/
def refinement_ladder_rover_rung2_6dof_coverV2 : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2_6dof", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [0], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0]⟩, ⟨"MODER", [], [0], [0]⟩, ⟨"FLAT", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
