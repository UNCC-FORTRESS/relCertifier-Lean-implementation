/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `story1_attdist_rung_b_12dof` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py story1_attdist_rung_b_12dof`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `story1_attdist_rung_b_12dof` (emitted, suite_v2, widened cut channel on). -/
def story1_attdist_rung_b_12dof_coverV2 : CoverEmitE :=
  ⟨"story1_attdist_rung_b_12dof", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2], [], []⟩, ⟨"MODER", [0, 1, 2], [], []⟩, ⟨"FLAT", [0, 1, 2], [], []⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], []⟩, ⟨"MODER", [0, 1], [], []⟩, ⟨"FLAT", [0, 1], [], []⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], []⟩, ⟨"MODER", [0, 1], [], []⟩, ⟨"FLAT", [0, 1], [], []⟩]⟩]⟩

end RelCertifier
