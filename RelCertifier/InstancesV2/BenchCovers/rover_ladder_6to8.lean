/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_6to8` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_ladder_6to8`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_ladder_6to8` (emitted, suite_v2, widened cut channel on). -/
def rover_ladder_6to8_coverV2 : CoverEmitE :=
  ⟨"rover_ladder_6to8", [], [
    ⟨"STEEP", (3 : ℚ) / 2, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [0, 1], [0, 1], 3, 2⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1], 3, 2⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1], 3, 2⟩]⟩,
    ⟨"MODER", (3 : ℚ) / 2, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [], [0, 1], [0, 1], 3, 2⟩, ⟨"MODER", [0, 1], [0, 1], [0, 1], 3, 2⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1], 3, 2⟩]⟩,
    ⟨"FLAT", (3 : ℚ) / 2, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [], [0, 1], [0, 1], 3, 2⟩, ⟨"MODER", [], [0, 1], [0, 1], 3, 2⟩, ⟨"FLAT", [0, 1], [0, 1], [0, 1], 3, 2⟩]⟩]⟩

end RelCertifier
