/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_split_a` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_rollover_split_a`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_rollover_split_a` (emitted, suite_v2, widened cut channel on). -/
def rover_rollover_split_a_coverV2 : CoverEmitE :=
  ⟨"rover_rollover_split_a", [], [
    ⟨"STEEP", (27 : ℚ) / 20, 2, [⟨"STEEP", true, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2], [0, 1, 2], [0, 1, 2], 27, 20⟩, ⟨"MODER", [0, 1, 2], [0, 1, 2], [0, 1, 2], 27, 20⟩, ⟨"FLAT", [0, 1, 2], [0, 1, 2], [0, 1, 2], 27, 20⟩]⟩,
    ⟨"MODER", (27 : ℚ) / 20, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", true, true, true⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [2], [0, 1, 2], [0, 1, 2], 27, 20⟩, ⟨"MODER", [0, 1, 2], [0, 1, 2], [0, 1, 2], 27, 20⟩, ⟨"FLAT", [0, 1, 2], [0, 1, 2], [0, 1, 2], 27, 20⟩]⟩,
    ⟨"FLAT", (27 : ℚ) / 20, 2, [⟨"STEEP", false, true, true⟩, ⟨"MODER", false, true, true⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2], [0, 1, 2], [0, 1, 2], 27, 20⟩, ⟨"MODER", [2], [0, 1, 2], [0, 1, 2], 27, 20⟩, ⟨"FLAT", [0, 1, 2], [0, 1, 2], [0, 1, 2], 27, 20⟩]⟩]⟩

end RelCertifier
