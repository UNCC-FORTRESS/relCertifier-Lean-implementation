/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `refinement_ladder_rover_rung2c_6dof` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py refinement_ladder_rover_rung2c_6dof`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `refinement_ladder_rover_rung2c_6dof` (emitted, suite_v2, widened cut channel on). -/
def refinement_ladder_rover_rung2c_6dof_coverV2 : CoverEmitE :=
  ⟨"refinement_ladder_rover_rung2c_6dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", false, false, false⟩], ["STEEP"], [⟨"STEEP", [0, 1, 4, 5, 6, 7, 2, 3], [2], [2]⟩, ⟨"MODER", [0, 4, 5, 6, 7, 2], [2], [2]⟩, ⟨"FLAT", [0, 4, 5, 6, 7, 2], [2], [2]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", false, false, false⟩], ["MODER"], [⟨"STEEP", [1, 4, 5, 6, 7, 3], [2], [2]⟩, ⟨"MODER", [0, 1, 4, 5, 6, 7, 2, 3], [2], [2]⟩, ⟨"FLAT", [0, 4, 5, 6, 7, 2], [2], [2]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [1, 4, 5, 6, 7, 3], [2], [2]⟩, ⟨"MODER", [1, 4, 5, 6, 7, 3], [2], [2]⟩, ⟨"FLAT", [0, 1, 4, 5, 6, 7, 2, 3], [2], [2]⟩]⟩]⟩

end RelCertifier
