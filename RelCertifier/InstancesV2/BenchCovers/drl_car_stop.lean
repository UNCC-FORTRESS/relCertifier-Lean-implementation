/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `drl_car_stop` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py drl_car_stop`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `drl_car_stop` (emitted, suite_v2, widened cut channel on). -/
def drl_car_stop_coverV2 : CoverEmitE :=
  ⟨"drl_car_stop", [], [
    ⟨"Accel", (1 : ℚ) / 1, 1, [⟨"Accel", true, false, false⟩, ⟨"Coast", false, false, false⟩, ⟨"Brake", false, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [2, 3, 0, 1], [0, 2], [0, 2], 1, 1⟩, ⟨"Coast", [3, 1], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"Brake", [3, 1], [0, 3], [0, 3], 1, 1⟩]⟩,
    ⟨"Coast", (1 : ℚ) / 1, 1, [⟨"Accel", false, false, false⟩, ⟨"Coast", true, false, false⟩, ⟨"Brake", false, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [2, 0], [0, 2], [0, 2], 1, 1⟩, ⟨"Coast", [2, 3, 0, 1], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"Brake", [3, 1], [0, 3], [0, 3], 1, 1⟩]⟩,
    ⟨"Brake", (1 : ℚ) / 1, 1, [⟨"Accel", false, false, false⟩, ⟨"Coast", false, false, false⟩, ⟨"Brake", true, false, false⟩], ["Accel", "Coast", "Brake"], [⟨"Accel", [2, 0], [0, 2], [0, 2], 1, 1⟩, ⟨"Coast", [2, 0], [0, 2, 3], [0, 2, 3], 1, 1⟩, ⟨"Brake", [2, 3, 0, 1], [0, 3], [0, 3], 1, 1⟩]⟩]⟩

end RelCertifier
