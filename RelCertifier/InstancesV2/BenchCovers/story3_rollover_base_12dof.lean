/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story3_rollover_base_12dof` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py story3_rollover_base_12dof`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story3_rollover_base_12dof` (emitted, suite_v2, widened cut channel on). -/
def story3_rollover_base_12dof_coverV2 : CoverEmitE :=
  ⟨"story3_rollover_base_12dof", [], [
    ⟨"STEEP", (5 : ℚ) / 4, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"MODER", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩]⟩,
    ⟨"MODER", (5 : ℚ) / 4, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, true, true⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"MODER", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩]⟩,
    ⟨"FLAT", (5 : ℚ) / 4, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, true, true⟩], ["MODER", "FLAT"], [⟨"STEEP", [4, 2, 3], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"MODER", [4, 2, 3], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩, ⟨"FLAT", [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 1, 2, 3, 4]⟩]⟩]⟩

end RelCertifier
