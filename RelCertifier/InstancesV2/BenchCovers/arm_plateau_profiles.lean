/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `arm_plateau_profiles` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1 RELCERT_PROGRESS=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py arm_plateau_profiles`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `arm_plateau_profiles` (emitted, suite_v2, widened cut channel on). -/
def arm_plateau_profiles_coverV2 : CoverEmitE :=
  ⟨"arm_plateau_profiles", [], [
    ⟨"Accelerate", (1 : ℚ) / 1, 2, [⟨"ApproachA", true, true, true⟩, ⟨"ApproachB", true, true, true⟩, ⟨"ApproachCfast", true, true, true⟩, ⟨"ApproachCslow", true, true, true⟩, ⟨"Hold", true, false, false⟩], ["ApproachA", "ApproachB", "ApproachCfast", "ApproachCslow", "Hold"], [⟨"ApproachA", [0], [0], [0], 1, 1⟩, ⟨"ApproachB", [0], [0], [0], 1, 1⟩, ⟨"ApproachCfast", [0], [0], [0], 1, 1⟩, ⟨"ApproachCslow", [0], [0], [0], 1, 1⟩, ⟨"Hold", [0], [0], [0], 1, 1⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 2, [⟨"ApproachA", true, true, true⟩, ⟨"ApproachB", true, true, true⟩, ⟨"ApproachCfast", true, true, true⟩, ⟨"ApproachCslow", true, true, true⟩, ⟨"Hold", true, false, false⟩], ["ApproachA", "ApproachB", "ApproachCfast", "ApproachCslow", "Hold"], [⟨"ApproachA", [0], [0], [0], 1, 1⟩, ⟨"ApproachB", [0], [0], [0], 1, 1⟩, ⟨"ApproachCfast", [0], [0], [0], 1, 1⟩, ⟨"ApproachCslow", [0], [0], [0], 1, 1⟩, ⟨"Hold", [0], [0], [0], 1, 1⟩]⟩]⟩

end RelCertifier
