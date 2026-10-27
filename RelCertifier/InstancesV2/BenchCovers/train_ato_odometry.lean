/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `train_ato_odometry` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py train_ato_odometry`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `train_ato_odometry` (emitted, suite_v2, widened cut channel on). -/
def train_ato_odometry_coverV2 : CoverEmitE :=
  ⟨"train_ato_odometry", [], [
    ⟨"PL1", (6 : ℚ) / 5, 2, [⟨"PL1", true, false, false⟩, ⟨"PL2", true, false, false⟩, ⟨"PL3", true, false, false⟩], ["PL1", "PL2", "PL3"], [⟨"PL1", [0, 1], [], [], 39, 40⟩, ⟨"PL2", [0, 1], [], [], 43, 40⟩, ⟨"PL3", [0, 1], [], [], 6, 5⟩]⟩,
    ⟨"PL2", (11 : ℚ) / 10, 2, [⟨"PL1", true, false, false⟩, ⟨"PL2", true, false, false⟩, ⟨"PL3", true, false, false⟩], ["PL1", "PL2", "PL3"], [⟨"PL1", [0, 1], [], [], 7, 8⟩, ⟨"PL2", [0, 1], [], [], 39, 40⟩, ⟨"PL3", [0, 1], [], [], 11, 10⟩]⟩,
    ⟨"PL3", (39 : ℚ) / 40, 1, [⟨"PL1", true, false, false⟩, ⟨"PL2", true, false, false⟩, ⟨"PL3", true, false, false⟩], ["PL1", "PL2", "PL3"], [⟨"PL1", [0, 1], [], [], 31, 40⟩, ⟨"PL2", [0, 1], [], [], 7, 8⟩, ⟨"PL3", [0, 1], [], [], 39, 40⟩]⟩]⟩

end RelCertifier
