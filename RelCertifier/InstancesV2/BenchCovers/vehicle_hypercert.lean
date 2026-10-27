/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `vehicle_hypercert` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1`, progress certificates by default (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py vehicle_hypercert`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `vehicle_hypercert` (emitted, suite_v2, widened cut channel on). -/
def vehicle_hypercert_coverV2 : CoverEmitE :=
  ⟨"vehicle_hypercert", [], [
    ⟨"Am4", (1 : ℚ) / 1, 1, [⟨"Am4", true, false, false⟩, ⟨"Am2", false, false, false⟩, ⟨"A0", false, false, false⟩, ⟨"Ap2", false, false, false⟩, ⟨"Ap4", false, false, false⟩], ["Am4", "Am2", "A0", "Ap2", "Ap4"], [⟨"Am4", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Am2", [0, 2], [1, 2], [1, 2], 1, 1⟩, ⟨"A0", [0, 2], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Ap2", [0, 2], [0, 2], [0, 2], 1, 1⟩, ⟨"Ap4", [0, 2], [0, 2], [0, 2], 1, 1⟩]⟩,
    ⟨"Am2", (1 : ℚ) / 1, 1, [⟨"Am4", false, false, false⟩, ⟨"Am2", true, false, false⟩, ⟨"A0", false, false, false⟩, ⟨"Ap2", false, false, false⟩, ⟨"Ap4", false, false, false⟩], ["Am4", "Am2", "A0", "Ap2", "Ap4"], [⟨"Am4", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Am2", [0, 1, 2, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"A0", [0, 2], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Ap2", [0, 2], [0, 2], [0, 2], 1, 1⟩, ⟨"Ap4", [0, 2], [0, 2], [0, 2], 1, 1⟩]⟩,
    ⟨"A0", (1 : ℚ) / 1, 1, [⟨"Am4", false, false, false⟩, ⟨"Am2", false, false, false⟩, ⟨"A0", true, false, false⟩, ⟨"Ap2", false, false, false⟩, ⟨"Ap4", false, false, false⟩], ["Am4", "Am2", "A0", "Ap2", "Ap4"], [⟨"Am4", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Am2", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"A0", [0, 1, 2, 3], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Ap2", [0, 2], [0, 2], [0, 2], 1, 1⟩, ⟨"Ap4", [0, 2], [0, 2], [0, 2], 1, 1⟩]⟩,
    ⟨"Ap2", (1 : ℚ) / 1, 1, [⟨"Am4", false, false, false⟩, ⟨"Am2", false, false, false⟩, ⟨"A0", false, false, false⟩, ⟨"Ap2", true, false, false⟩, ⟨"Ap4", false, false, false⟩], ["Am4", "Am2", "A0", "Ap2", "Ap4"], [⟨"Am4", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Am2", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"A0", [1, 3], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Ap2", [0, 1, 2, 3], [0, 2], [0, 2], 1, 1⟩, ⟨"Ap4", [0, 2], [0, 2], [0, 2], 1, 1⟩]⟩,
    ⟨"Ap4", (1 : ℚ) / 1, 1, [⟨"Am4", false, false, false⟩, ⟨"Am2", false, false, false⟩, ⟨"A0", false, false, false⟩, ⟨"Ap2", false, false, false⟩, ⟨"Ap4", true, false, false⟩], ["Am4", "Am2", "A0", "Ap2", "Ap4"], [⟨"Am4", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"Am2", [1, 3], [1, 2], [1, 2], 1, 1⟩, ⟨"A0", [1, 3], [0, 1, 2], [0, 1, 2], 1, 1⟩, ⟨"Ap2", [1, 3], [0, 2], [0, 2], 1, 1⟩, ⟨"Ap4", [0, 1, 2, 3], [0, 2], [0, 2], 1, 1⟩]⟩]⟩

end RelCertifier
