/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_lateral_6to8` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_lateral_6to8`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_lateral_6to8` (emitted, suite_v2, widened cut channel on). -/
def rover_lateral_6to8_coverV2 : CoverEmitE :=
  ⟨"rover_lateral_6to8", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 2, 4, 5, 6, 7, 1, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"MODER", [0, 2, 4, 5, 6, 7, 1, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"FLAT", [0, 2, 4, 5, 6, 7, 1, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 4, 5, 6, 7, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"MODER", [0, 2, 4, 5, 6, 7, 1, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"FLAT", [0, 2, 4, 5, 6, 7, 1, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", false, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 4, 5, 6, 7, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"MODER", [2, 4, 5, 6, 7, 1], [1, 2, 3], [1, 2, 3], 1, 1⟩, ⟨"FLAT", [0, 2, 4, 5, 6, 7, 1, 3], [1, 2, 3], [1, 2, 3], 1, 1⟩]⟩]⟩

end RelCertifier
