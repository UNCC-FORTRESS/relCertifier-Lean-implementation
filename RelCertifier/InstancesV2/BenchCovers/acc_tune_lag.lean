/-
Copyright (c) 2026 relCertifier-lean contributors.
Released under Apache 2.0 license.

# `acc_tune_lag` (suite_v2) — emitted cover, `RELCERT_IMPLIED_CUT=1` (GENERATED leaf — do not edit)

Regenerate with `scripts/gen_v2_data.py acc_tune_lag`.
-/
import RelCertifier.Checker.CoverEmit

namespace RelCertifier

/-- `acc_tune_lag` (emitted, suite_v2, widened cut channel on). -/
def acc_tune_lag_coverV2 : CoverEmitE :=
  ⟨"acc_tune_lag", [("CRUISE", "DISENGAGE")], [
    ⟨"CRUISE", (5 : ℚ) / 4, 3, [⟨"CRUISE", true, false, false⟩, ⟨"DISENGAGE", false, false, false⟩], ["CRUISE"], [⟨"CRUISE", [0], [], []⟩, ⟨"DISENGAGE", [], [], []⟩]⟩]⟩

end RelCertifier
