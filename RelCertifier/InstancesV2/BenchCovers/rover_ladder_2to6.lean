/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_ladder_2to6` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_ladder_2to6`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_ladder_2to6` (emitted, suite_v2, widened cut channel on). -/
def rover_ladder_2to6_coverV2 : CoverEmitE :=
  ⟨"rover_ladder_2to6", [], [
    ⟨"STEEP", (1001 : ℚ) / 1000, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0], [0], [0], 1001, 1000⟩, ⟨"MODER", [0], [0], [0], 1001, 1000⟩, ⟨"FLAT", [0], [0], [0], 1001, 1000⟩]⟩,
    ⟨"MODER", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0], 1001, 1000⟩, ⟨"MODER", [0], [0], [0], 1001, 1000⟩, ⟨"FLAT", [0], [0], [0], 1001, 1000⟩]⟩,
    ⟨"FLAT", (1001 : ℚ) / 1000, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [], [0], [0], 1001, 1000⟩, ⟨"MODER", [], [0], [0], 1001, 1000⟩, ⟨"FLAT", [0], [0], [0], 1001, 1000⟩]⟩]⟩

end RelCertifier
