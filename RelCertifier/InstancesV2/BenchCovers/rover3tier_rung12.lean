/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `rover3tier_rung12` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py rover3tier_rung12`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `rover3tier_rung12` (emitted, suite_v2, widened cut channel on). -/
def rover3tier_rung12_coverV2 : CoverEmitE :=
  ⟨"rover3tier_rung12", [], [
    ⟨"ACCEL", (7 : ℚ) / 4, 6, [⟨"ACCEL", true, true, true⟩, ⟨"COAST", true, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [1, 0], [0, 1], [0, 1]⟩, ⟨"COAST", [1, 0], [0, 1], [0, 1]⟩]⟩,
    ⟨"COAST", (1 : ℚ) / 1, 4, [⟨"ACCEL", true, true, true⟩, ⟨"COAST", true, true, true⟩], ["ACCEL", "COAST"], [⟨"ACCEL", [0], [0], [0]⟩, ⟨"COAST", [0], [0], [0]⟩]⟩]⟩

end RelCertifier
