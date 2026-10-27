/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `compressor_station_recycle` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py compressor_station_recycle`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `compressor_station_recycle` (emitted, suite_v2, widened cut channel on). -/
def compressor_station_recycle_coverV2 : CoverEmitE :=
  ⟨"compressor_station_recycle", [], [
    ⟨"HIGH", (1 : ℚ) / 1, 1, [⟨"LOW", false, false, false⟩, ⟨"MED", true, false, false⟩, ⟨"HIGH", false, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [0, 3], [], [], 1, 1⟩, ⟨"MED", [0, 1, 2, 3], [], [], 1, 1⟩, ⟨"HIGH", [1, 2], [], [], 1, 1⟩]⟩,
    ⟨"MED", (1 : ℚ) / 1, 1, [⟨"LOW", false, false, false⟩, ⟨"MED", true, false, false⟩, ⟨"HIGH", false, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [0, 3], [], [], 1, 1⟩, ⟨"MED", [0, 1, 2, 3], [], [], 1, 1⟩, ⟨"HIGH", [1, 2], [], [], 1, 1⟩]⟩,
    ⟨"LOW", (1 : ℚ) / 1, 1, [⟨"LOW", true, false, false⟩, ⟨"MED", false, false, false⟩, ⟨"HIGH", false, false, false⟩], ["LOW", "MED", "HIGH"], [⟨"LOW", [0, 1, 2, 3], [], [], 1, 1⟩, ⟨"MED", [1, 2], [], [], 1, 1⟩, ⟨"HIGH", [1, 2], [], [], 1, 1⟩]⟩]⟩

end RelCertifier
