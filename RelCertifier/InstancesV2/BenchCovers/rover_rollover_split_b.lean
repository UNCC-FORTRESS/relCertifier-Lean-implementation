/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_split_b` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_rollover_split_b`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_rollover_split_b` (emitted, suite_v2, widened cut channel on). -/
def rover_rollover_split_b_coverV2 : CoverEmitE :=
  ⟨"rover_rollover_split_b", [], [
    ⟨"STEEP", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2], [], [], 1, 1⟩, ⟨"MODER", [0, 1, 2], [], [], 1, 1⟩, ⟨"FLAT", [0, 1, 2], [], [], 1, 1⟩]⟩,
    ⟨"MODER", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], [], 1, 1⟩, ⟨"MODER", [0, 1], [], [], 1, 1⟩, ⟨"FLAT", [0, 1], [], [], 1, 1⟩]⟩,
    ⟨"FLAT", (1 : ℚ) / 1, 1, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1], [], [], 1, 1⟩, ⟨"MODER", [0, 1], [], [], 1, 1⟩, ⟨"FLAT", [0, 1], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
