/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_ladder_rung_b` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py story3_rollover_ladder_rung_b`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story3_rollover_ladder_rung_b` (emitted, suite_v2, widened cut channel on). -/
def story3_rollover_ladder_rung_b_coverV2 : CoverEmitE :=
  ⟨"story3_rollover_ladder_rung_b", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2], [], []⟩, ⟨"MODER", [0, 1, 2], [], []⟩, ⟨"FLAT", [0, 1, 2], [], []⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], []⟩, ⟨"MODER", [0, 1], [], []⟩, ⟨"FLAT", [0, 1], [], []⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], []⟩, ⟨"MODER", [0, 1], [], []⟩, ⟨"FLAT", [0, 1], [], []⟩]⟩]⟩

end RelCertifier
