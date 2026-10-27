/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `furnace_program_timebase` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py furnace_program_timebase`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `furnace_program_timebase` (emitted, suite_v2, widened cut channel on). -/
def furnace_program_timebase_coverV2 : CoverEmitE :=
  ⟨"furnace_program_timebase", [], [
    ⟨"PREHEAT", (4 : ℚ) / 5, 1, [⟨"PREHEAT", true, false, false⟩, ⟨"HEAT", false, false, false⟩, ⟨"SOAK", true, false, false⟩], ["PREHEAT"], [⟨"PREHEAT", [0, 1, 4, 5, 2, 3], [0], [0], 4, 5⟩, ⟨"HEAT", [0, 4, 5, 2], [0], [0], 4, 5⟩, ⟨"SOAK", [0, 1, 2, 3, 4, 5], [0], [0], 4, 5⟩]⟩,
    ⟨"HEAT", (4 : ℚ) / 5, 1, [⟨"PREHEAT", false, false, false⟩, ⟨"HEAT", true, false, false⟩, ⟨"SOAK", false, false, false⟩], ["HEAT"], [⟨"PREHEAT", [1, 4, 5, 3], [0], [0], 4, 5⟩, ⟨"HEAT", [0, 1, 4, 5, 2, 3], [0], [0], 4, 5⟩, ⟨"SOAK", [0, 4, 5, 2], [0], [0], 4, 5⟩]⟩,
    ⟨"SOAK", (4 : ℚ) / 5, 1, [⟨"PREHEAT", true, true, true⟩, ⟨"HEAT", false, false, false⟩, ⟨"SOAK", true, false, false⟩], ["SOAK"], [⟨"PREHEAT", [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], 4, 5⟩, ⟨"HEAT", [1, 3, 4, 5], [0], [0], 4, 5⟩, ⟨"SOAK", [0, 1, 3, 4, 5, 2], [0], [0], 4, 5⟩]⟩]⟩

end RelCertifier
