/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_limp` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_tune_limp`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `acc_tune_limp` (emitted, suite_v2, widened cut channel on). -/
def acc_tune_limp_coverV2 : CoverEmitE :=
  ⟨"acc_tune_limp", [("NORMAL", "DISENGAGE"), ("COMFORT", "DISENGAGE"), ("SPORT", "DISENGAGE")], [
    ⟨"CRUISE", (3 : ℚ) / 2, 3, [⟨"NORMAL", true, false, false⟩, ⟨"COMFORT", true, false, false⟩, ⟨"SPORT", true, false, false⟩, ⟨"DISENGAGE", false, false, false⟩], ["NORMAL", "COMFORT", "SPORT"], [⟨"NORMAL", [0, 1], [], []⟩, ⟨"COMFORT", [0, 1], [], []⟩, ⟨"SPORT", [0, 1], [], []⟩, ⟨"DISENGAGE", [1], [1], [1]⟩]⟩,
    ⟨"LIMP", (1 : ℚ) / 1, 2, [⟨"NORMAL", true, false, false⟩, ⟨"COMFORT", true, false, false⟩, ⟨"SPORT", true, false, false⟩, ⟨"DISENGAGE", false, false, false⟩], ["NORMAL", "COMFORT", "SPORT"], [⟨"NORMAL", [0, 1], [], []⟩, ⟨"COMFORT", [0, 1], [], []⟩, ⟨"SPORT", [0, 1], [], []⟩, ⟨"DISENGAGE", [1], [1], [1]⟩]⟩]⟩

end RelCertifier
