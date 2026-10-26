/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_2to4` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_terrain_2to4`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_terrain_2to4` (emitted, suite_v2, widened cut channel on). -/
def rover_terrain_2to4_coverV2 : CoverEmitE :=
  ⟨"rover_terrain_2to4", [], [
    ⟨"MUD", (1 : ℚ) / 1, 1, [⟨"MUD", true, false, false⟩, ⟨"GRAVEL", true, false, false⟩, ⟨"PAVED", true, false, false⟩], ["MUD", "GRAVEL", "PAVED"], [⟨"MUD", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"GRAVEL", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"PAVED", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"GRAVEL", (3 : ℚ) / 2, 2, [⟨"MUD", false, false, false⟩, ⟨"GRAVEL", true, false, false⟩, ⟨"PAVED", true, false, false⟩], ["GRAVEL", "PAVED"], [⟨"MUD", [2, 3], [1, 2, 3], [1, 2, 3], 3, 2⟩, ⟨"GRAVEL", [2, 3, 0, 1], [1, 2, 3], [1, 2, 3], 3, 2⟩, ⟨"PAVED", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 3, 2⟩]⟩,
    ⟨"PAVED", (11 : ℚ) / 4, 3, [⟨"MUD", false, false, false⟩, ⟨"GRAVEL", false, false, false⟩, ⟨"PAVED", true, false, false⟩], ["PAVED"], [⟨"MUD", [2, 3], [1, 2, 3], [1, 2, 3], 11, 4⟩, ⟨"GRAVEL", [2, 3], [1, 2, 3], [1, 2, 3], 11, 4⟩, ⟨"PAVED", [0, 1, 2, 3], [1, 2, 3], [1, 2, 3], 11, 4⟩]⟩]⟩

end RelCertifier
