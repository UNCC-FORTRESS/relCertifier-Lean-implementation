/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_terrain_6to12` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_terrain_6to12`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_terrain_6to12` (emitted, suite_v2, widened cut channel on). -/
def rover_terrain_6to12_coverV2 : CoverEmitE :=
  ⟨"rover_terrain_6to12", [], [
    ⟨"MUD", (1 : ℚ) / 1, 1, [⟨"MUD", true, false, false⟩, ⟨"GRAVEL", true, false, false⟩, ⟨"PAVED", true, false, false⟩], ["MUD", "GRAVEL", "PAVED"], [⟨"MUD", [2, 3, 4, 6, 7, 11, 12, 0, 1, 5, 9, 10, 8], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩, ⟨"GRAVEL", [2, 3, 4, 6, 7, 11, 12, 5, 9, 10, 0, 1, 8], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩, ⟨"PAVED", [2, 3, 4, 6, 7, 11, 12, 5, 9, 10, 0, 1, 8], [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩]⟩,
    ⟨"GRAVEL", (1 : ℚ) / 1, 1, [⟨"MUD", false, false, false⟩, ⟨"GRAVEL", true, false, false⟩, ⟨"PAVED", true, false, false⟩], ["GRAVEL", "PAVED"], [⟨"MUD", [6, 7, 11, 12, 5, 9, 10, 8], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩, ⟨"GRAVEL", [2, 3, 4, 6, 7, 11, 12, 0, 1, 5, 9, 10, 8], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩, ⟨"PAVED", [2, 3, 4, 6, 7, 11, 12, 5, 9, 10, 0, 1, 8], [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩]⟩,
    ⟨"PAVED", (1 : ℚ) / 1, 1, [⟨"MUD", false, false, false⟩, ⟨"GRAVEL", false, false, false⟩, ⟨"PAVED", true, false, false⟩], ["PAVED"], [⟨"MUD", [6, 7, 10, 11, 12, 5, 8, 9], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩, ⟨"GRAVEL", [6, 7, 10, 11, 12, 5, 8, 9], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩, ⟨"PAVED", [2, 3, 4, 6, 7, 10, 11, 12, 0, 1, 5, 8, 9], [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12], [1, 2, 4, 5, 6, 7, 8, 9, 10, 11, 12], 1, 1⟩]⟩]⟩

end RelCertifier
