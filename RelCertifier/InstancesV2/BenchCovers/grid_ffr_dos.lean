/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `grid_ffr_dos` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py grid_ffr_dos`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `grid_ffr_dos` (emitted, suite_v2, widened cut channel on). -/
def grid_ffr_dos_coverV2 : CoverEmitE :=
  ⟨"grid_ffr_dos", [("NORMAL", "TRIP"), ("FFR", "TRIP")], [
    ⟨"NORMAL", (1 : ℚ) / 1, 3, [⟨"NORMAL", true, false, false⟩, ⟨"FFR", true, false, false⟩, ⟨"TRIP", false, false, false⟩], ["NORMAL", "FFR"], [⟨"NORMAL", [2, 3, 4, 0, 1], [2, 3, 4], [2, 3, 4], 1, 1⟩, ⟨"FFR", [2, 3, 4, 0, 1], [2, 3, 4], [2, 3, 4], 1, 1⟩, ⟨"TRIP", [1, 2, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩]⟩,
    ⟨"FFR", (1 : ℚ) / 1, 3, [⟨"NORMAL", false, false, false⟩, ⟨"FFR", true, false, false⟩, ⟨"TRIP", false, false, false⟩], ["FFR"], [⟨"NORMAL", [3, 4, 1], [2, 3, 4], [2, 3, 4], 1, 1⟩, ⟨"FFR", [2, 3, 4, 0, 1], [2, 3, 4], [2, 3, 4], 1, 1⟩, ⟨"TRIP", [1, 3, 4], [1, 2, 3, 4], [1, 2, 3, 4], 1, 1⟩]⟩]⟩

end RelCertifier
