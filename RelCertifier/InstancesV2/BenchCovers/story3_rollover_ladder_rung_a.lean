/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_a` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py story3_rollover_ladder_rung_a`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story3_rollover_ladder_rung_a` (emitted, suite_v2, widened cut channel on). -/
def story3_rollover_ladder_rung_a_coverV2 : CoverEmitE :=
  ⟨"story3_rollover_ladder_rung_a", [], [
    ⟨"STEEP", (27 : ℚ) / 20, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2], [0, 1, 2], [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2], [0, 1, 2], [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2], [0, 1, 2], [0, 1, 2]⟩]⟩,
    ⟨"MODER", (27 : ℚ) / 20, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2], [0, 1, 2], [0, 1, 2]⟩, ⟨"MODER", [0, 1, 2], [0, 1, 2], [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2], [0, 1, 2], [0, 1, 2]⟩]⟩,
    ⟨"FLAT", (27 : ℚ) / 20, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [2], [0, 1, 2], [0, 1, 2]⟩, ⟨"MODER", [2], [0, 1, 2], [0, 1, 2]⟩, ⟨"FLAT", [0, 1, 2], [0, 1, 2], [0, 1, 2]⟩]⟩]⟩

end RelCertifier
