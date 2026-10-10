/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_dof_terrain_rung2` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_dof_terrain_rung2`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_dof_terrain_rung2` (emitted, suite_v2, widened cut channel on). -/
def rover_dof_terrain_rung2_coverV2 : CoverEmitE :=
  ⟨"rover_dof_terrain_rung2", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1]⟩, ⟨"MODER", [], [0, 1], [0, 1]⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1]⟩]⟩]⟩

end RelCertifier
