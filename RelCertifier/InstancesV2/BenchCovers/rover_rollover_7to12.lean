/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover_rollover_7to12` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover_rollover_7to12`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover_rollover_7to12` (emitted, suite_v2, widened cut channel on). -/
def rover_rollover_7to12_coverV2 : CoverEmitE :=
  ⟨"rover_rollover_7to12", [], [
    ⟨"STEEP", (27 : ℚ) / 20, 2, [⟨"STEEP", true, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["STEEP", "MODER", "FLAT"], [⟨"STEEP", [0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩, ⟨"MODER", [0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩, ⟨"FLAT", [0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩]⟩,
    ⟨"MODER", (27 : ℚ) / 20, 2, [⟨"STEEP", false, false, false⟩, ⟨"MODER", true, false, false⟩, ⟨"FLAT", true, false, false⟩], ["MODER", "FLAT"], [⟨"STEEP", [2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩, ⟨"MODER", [0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩, ⟨"FLAT", [0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩]⟩,
    ⟨"FLAT", (27 : ℚ) / 20, 2, [⟨"STEEP", false, false, false⟩, ⟨"MODER", false, false, false⟩, ⟨"FLAT", true, false, false⟩], ["FLAT"], [⟨"STEEP", [2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩, ⟨"MODER", [2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩, ⟨"FLAT", [0, 1, 2, 3, 4, 5, 6], [1, 2, 3, 4], [1, 2, 3, 4], 27, 20⟩]⟩]⟩

end RelCertifier
